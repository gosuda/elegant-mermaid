import Elegant.Layered.RegionPlacement

set_option autoImplicit false

/-! The family entry for concurrent regions. `layoutR` is the base-level layout of
`PipelineImpl.layoutX` with the region sets threaded to every component run; `layoutFamilyR`
recurses over independent groups on top of it, re-resolving the sets against each sub-input's
boxes, so a set survives exactly where its parent and its regions all remain. -/

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

def componentTrialR (P : Params) (exactIds : List String) (spec : Option RegionSpec)
    (inp : Input) (o : Options) (g : Graph) (comp : List Nat) (labels : List MeasuredLabel)
    (index : Nat) : Except LayoutError (Portfolio.Candidate (Graph × Run)) := do
  let rs ← newComponentRegions spec P inp (componentGraph g comp)
  let spec := if rs.isSome then spec else none
  let cg := componentCandidateR spec g comp index
  let (cg, run) ← componentRunR P (exactDecls exactIds inp) spec inp cg labels
    (candidateOrder index)
  let scene ← componentScene P inp o cg run labels (@placeComponentExact)
  pure { value := (cg, run), scene := scene, budgetExhausted := run.budget }

def layoutComponentR (P : Params) (exactIds : List String) (spec : Option RegionSpec)
    (inp : Input) (o : Options) (g : Graph) (acc : Acc) (comp : List Nat)
    (labels : List MeasuredLabel := []) : Except LayoutError Acc := do
  let chosen ← Portfolio.portfolio o.thoroughness
    (componentTrialR P exactIds spec inp o g comp labels)
  let result ← placePart comp chosen.value.1 chosen.value.2 P acc labels (@placeComponentExact) true
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let metric ← metricOf o.profile o.fontFamily
  let titleAreas ← (inp.boxes.zipIdx.filter fun q =>
    q.1.role == .group && chosen.scene.boxes.any (fun box => box.id == q.1.id)).mapM fun q => do
      let lines ← StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD q.2 q.1.id).toList
      pure ((lines.foldl (fun width line => max width line.width) 0) *
        ((max 1 lines.length : Int) * P.lineH))
  pure { result with
    budget := acc.budget || chosen.budgetExhausted
    parts := acc.parts ++ ((result.parts.drop acc.parts.length).map fun placed =>
      (placed.1, { placed.2 with area := placed.2.area + childArea + titleAreas.sum })) }

/-- The base layout with regions: `layoutX` with the region spec handed to every component. -/
def layoutRIds (exactIds : List String) (idSets : List (String × List String))
    (inp : Input) (o : Options) : Except LayoutError FamilyResult := do
  let P ← checkedParams o.profile inp.kind
  let m ← metricOf o.profile o.fontFamily
  let lines ← boxLines m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp
  let measured ← measureLabels P m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp o.direction
  let g ← measuredGraph P inp o lines
  let g ← exactGraph P exactIds inp o measured g
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  let spec : Option RegionSpec :=
    if idSets.isEmpty then none else some { sets := idSets, titles := titles }
  let start : Acc :=
    ⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [],
      Array.replicate inp.labels.length default, false, [], []⟩
  let acc ← (components g).foldlM
    (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp measured) start
  let acc ← packAcc P o acc
  let acc ← straightenAcc inp acc
  let scene := sceneOf P inp o lines acc measured
  if I32_MAX < scene.canvas.w ∨ I32_MAX < scene.canvas.h then throw .overflow
  else pure ⟨scene, acc.budget, acc.parts.foldl (fun area part => area + part.2.area) 0⟩

/-- The region sets of an input resolved against the group boxes it kept. -/
def reindexRegionSets (idSets : List (String × List String)) (inp : Input) :
    List (String × List String) :=
  let ids := inp.boxes.map (·.id)
  idSets.filter fun s =>
    ids.contains s.1 && s.2.all fun r => ids.contains r

/-- The base-level region layout: `layoutR` resolves the model sets against `inp`'s group
boxes, so it runs unchanged on any sub-input whose region parent and regions are all present. -/
def layoutR (exactIds : List String) (sets : List ModelRegionSet) (inp : Input)
    (o : Options) : Except LayoutError FamilyResult := do
  let idSets ← graphRegions inp sets
  layoutRIds exactIds idSets inp o

end PipelineImpl

/-- The family entry with exact boxes and concurrent regions. -/
def layoutFamilyR (exactIds : List String) (sets : List ModelRegionSet) (inp : Input)
    (o : Options) : Except LayoutFailure FamilyResult :=
  match RegionImpl.graphRegions inp sets with
  | .error e => .error (.geometry e)
  | .ok idSets =>
    layoutFamilyB
      (fun sub o' => PipelineImpl.layoutRIds exactIds (PipelineImpl.reindexRegionSets idSets sub) sub o')
      inp o

end Layered
end Elegant
