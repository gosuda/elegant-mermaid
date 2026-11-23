import Elegant.Layered.ExactPipeline
import Elegant.Layered.VisibilityRoute

set_option autoImplicit false

/-! Layered family with attached notes. A note box carries the side of its target in its
direction (`left` or `right`) and is named `<target>.note`. Each target that is not nested in
another target becomes a bundle: the target with everything inside it, and each of its notes,
are laid out on their own; the target is replaced by one exact box that holds the fragments
side by side, the remaining graph is laid out, the fragments are placed into their boxes, and
every route that touches a bundle is routed again on the visibility grid. Nested targets are
handled by the layout of their enclosing fragment. -/

namespace Elegant
namespace Layered
namespace PipelineImpl

structure Attach where
  target : Nat
  note : Nat
  right : Bool

structure Bundle where
  target : Nat
  notes : List Attach

def dropSuffix (cs suffix : List Char) : Option (List Char) :=
  if suffix.isSuffixOf cs then some (cs.take (cs.length - suffix.length)) else none

def noteTargetId (id : String) : Option String :=
  let cs := id.toList
  let note := ".note".toList
  let found :=
    match dropSuffix cs note with
    | some target => some target
    | none =>
      let reversed := cs.reverse
      if (reversed.takeWhile Char.isDigit).isEmpty then none
      else (dropSuffix (reversed.dropWhile Char.isDigit).reverse ['.']).bind (dropSuffix · note)
  found.map String.ofList

def attachmentsOf (boxes : List ModelBox) : List Attach :=
  boxes.zipIdx.filterMap fun q =>
    if q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right") then
      (noteTargetId q.1.id).bind fun target =>
        (boxes.findIdx? (·.id == target)).map fun t => ⟨t, q.2, q.1.direction == "right"⟩
    else none

def isNested (boxes : List ModelBox) (atts : List Attach) (target : Nat) : Bool :=
  match boxes[target]? with
  | none => false
  | some box => (Compound.path boxes box).any fun a => atts.any (·.target == a)

def bundlesOf (boxes : List ModelBox) (atts : List Attach) : List Bundle :=
  atts.foldl
    (fun acc a =>
      if isNested boxes atts a.target || acc.any (·.target == a.target) then acc
      else acc ++ [⟨a.target, atts.filter (·.target == a.target)⟩])
    []

structure Footprint where
  size : Size
  target : Rect
  notes : List Rect

def footprint (gap : Int) (target : Size) (notes : List (Size × Bool)) : Footprint :=
  let left := notes.foldl (fun l n => if n.2 then l else l + n.1.w + gap) gap
  let right := notes.foldl (fun r n => if n.2 then r + n.1.w + gap else r) gap
  let height := notes.foldl (fun h n => max h n.1.h) target.h
  let total := height + 2 * gap
  let placed := notes.foldl
    (fun (acc : Int × Int × List Rect) n =>
      let rect : Rect :=
        ⟨if n.2 then acc.2.1 else acc.1, Int.fdiv (total - n.1.h) 2, n.1.w, n.1.h⟩
      if n.2 then (acc.1, acc.2.1 + n.1.w + gap, acc.2.2 ++ [rect])
      else (acc.1 + n.1.w + gap, acc.2.1, acc.2.2 ++ [rect]))
    (gap, left + target.w + gap, [])
  ⟨⟨left + target.w + right, total⟩, ⟨left, Int.fdiv (total - target.h) 2, target.w, target.h⟩,
    placed.2.2⟩

def subInput (inp : Input) (keep : ModelBox → Bool) (top : String) : Input :=
  let selected := selectInput inp keep
  { selected with boxes := selected.boxes.map fun b =>
      if b.id == top then { b with parent := "" } else b }

def sceneSize (margin : Int) (s : Scene) : Size :=
  ⟨s.canvas.w - 2 * margin, s.canvas.h - 2 * margin⟩

structure BundleLayout where
  top : ModelBox
  bundle : Bundle
  part : FamilyResult
  notes : List (ModelBox × FamilyResult)
  footprint : Footprint

def bundleLayout (recur base : Input → Options → Except LayoutError FamilyResult)
    (inp : Input) (o : Options) (margin gap : Int) (b : Bundle) :
    Except LayoutError BundleLayout := do
  let some top := inp.boxes[b.target]? | throw .domain
  let part ← recur (subInput inp (fun x => x.id == top.id || Compound.inside inp.boxes top.id x.id)
    top.id) o
  let notes ← b.notes.mapM fun a => do
    let some box := inp.boxes[a.note]? | throw .domain
    let r ← base (subInput inp (fun x => x.id == box.id) box.id) o
    pure (box, r)
  pure ⟨top, b, part, notes,
    footprint gap (sceneSize margin part.scene)
      ((notes.zip b.notes).map fun q => (sceneSize margin q.1.2.scene, q.2.right))⟩

def contractOne (inp : Input) (l : BundleLayout) : Input :=
  let top := l.top
  let inside (id : String) : Bool := Compound.inside inp.boxes top.id id
  let noteIds := l.notes.map (·.1.id)
  let kept := inp.boxes.zipIdx.filter fun q => !(inside q.1.id || noteIds.contains q.1.id)
  let internal (r : ModelRoute) : Bool :=
    (inside r.fromId || r.fromId == top.id) && (inside r.toId || r.toId == top.id)
  let remap (id : String) : String := if inside id then top.id else id
  let routes := inp.routes.zipIdx.filter fun q => !internal q.1
  { inp with
    boxes := kept.map fun q =>
      if q.1.id == top.id then { q.1 with role := .node, direction := "" } else q.1
    texts := kept.map fun q => inp.texts.getD q.2 q.1.id
    routes := routes.map fun q => { q.1 with fromId := remap q.1.fromId, toId := remap q.1.toId }
    edges := routes.map fun q => inp.edges.getD q.2 EdgeOptions.plain
    labels := inp.labels.filter fun label =>
      kept.any (·.1.id == label.owner) || routes.any (·.1.id == label.owner)
    fixedSizes := inp.fixedSizes.filter (·.1 != top.id) ++ [(top.id, l.footprint.size)] }

structure Frame where
  direction : Direction
  height : Int
  margin : Int

def Frame.rect (f : Frame) (r : Rect) : Rect :=
  let q : Rect := ⟨r.x - f.margin, r.y - f.margin, r.w, r.h⟩
  match f.direction with
  | .TB => q
  | .BT => ⟨q.x, f.height - q.y - q.h, q.w, q.h⟩
  | .LR => ⟨q.y, q.x, q.h, q.w⟩
  | .RL => ⟨q.y, f.height - q.x - q.w, q.h, q.w⟩

def Frame.output (f : Frame) (p : Point) : Point :=
  let q := orientPoint f.direction f.height p
  ⟨q.x + f.margin, q.y + f.margin⟩

def reachFrom (adj : String → List String) : Nat → List String → List String → List String
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, x :: rest, seen =>
    let fresh := ((adj x).filter fun y => !seen.contains y).eraseDups
    reachFrom adj fuel (rest ++ fresh) (seen ++ fresh)

def componentIds (inp : Input) (atts : List Attach) (start : String) : List String :=
  let adj (id : String) : List String :=
    (inp.boxes.filter (·.parent == id)).map (·.id) ++
    (match inp.boxes.find? (·.id == id) with
      | some b => if b.parent == "" then [] else [b.parent]
      | none => []) ++
    inp.routes.flatMap (fun r =>
      if r.fromId == id then [r.toId] else if r.toId == id then [r.fromId] else []) ++
    atts.flatMap (fun a =>
      let target := (inp.boxes[a.target]?).map (·.id)
      let note := (inp.boxes[a.note]?).map (·.id)
      if target == some id then note.toList else if note == some id then target.toList else [])
  reachFrom adj (inp.boxes.length + 1) [start] [start]

structure Placed where
  scene : Scene
  dx : Int
  dy : Int

def Placed.rect (p : Placed) (id : String) : Option Rect :=
  (p.scene.boxes.find? (·.id == id)).map fun b => shiftRect p.dx p.dy b.rect

def Placed.route (p : Placed) (id : String) : Option (List Point) :=
  (p.scene.routes.find? (·.id == id)).map fun r => r.points.map (shiftPoint p.dx p.dy)

def Placed.label (p : Placed) (id : String) : Option SceneLabel :=
  (p.scene.labels.find? (·.id == id)).map fun l => { l with rect := shiftRect p.dx p.dy l.rect }

def Placed.titles (p : Placed) : List (String × Rect) :=
  (groupTitles p.scene.items).map fun t => (t.1, shiftRect p.dx p.dy t.2)

def placedFragments (margin : Int) (contracted : Scene) (l : BundleLayout) :
    Except LayoutError (List Placed) := do
  let some envelope := contracted.boxes.find? (·.id == l.top.id) | throw .domain
  let place (r : Rect) (s : Scene) : Placed :=
    ⟨s, envelope.rect.x + r.x - margin, envelope.rect.y + r.y - margin⟩
  pure (place l.footprint.target l.part.scene ::
    (l.notes.zip l.footprint.notes).map fun q => place q.2 q.1.2.scene)

/-- Visibility routing permits obstacle-boundary segments. This one-cell reservation keeps
the closed painted text rectangle in the obstacle's open interior. -/
def expandedTextRect (rect : Rect) : Rect :=
  ⟨rect.x - 1, rect.y - 1, rect.w + 2, rect.h + 2⟩

theorem expandedTextRect_contains_closed {rect : Rect} {point : Point}
    (hx : rect.x ≤ point.x ∧ point.x ≤ rect.x + rect.w)
    (hy : rect.y ≤ point.y ∧ point.y ≤ rect.y + rect.h) :
    (expandedTextRect rect).x < point.x ∧
    point.x < (expandedTextRect rect).x + (expandedTextRect rect).w ∧
    (expandedTextRect rect).y < point.y ∧
    point.y < (expandedTextRect rect).y + (expandedTextRect rect).h := by
  simp only [expandedTextRect]
  omega

def attachmentTextObstacle (profile : Profile) (rect : Rect) : Except LayoutError Rect :=
  if profile == .vector || rect.w == 0 || rect.h == 0 then pure rect
  else
    let expanded := expandedTextRect rect
    if expanded.w < 0 ∨ expanded.h < 0 then throw .domain
    else if InI32 expanded.x ∧ InI32 expanded.y ∧ InI32 expanded.w ∧
        InI32 expanded.h ∧ InI32 (expanded.x + expanded.w) ∧
        InI32 (expanded.y + expanded.h) then pure expanded
    else throw .overflow

theorem attachmentTextObstacle_cell {rect obstacle : Rect} (hw : rect.w ≠ 0)
    (hh : rect.h ≠ 0) (h : attachmentTextObstacle .cell rect = .ok obstacle) :
    obstacle = expandedTextRect rect := by
  have skip : (Profile.cell == .vector || rect.w == 0 || rect.h == 0) = false := by
    simp [hw, hh]
  simp only [attachmentTextObstacle, skip, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h

#guard (attachmentTextObstacle .vector ⟨3, 4, 5, 1⟩).toOption = some ⟨3, 4, 5, 1⟩
#guard (attachmentTextObstacle .cell ⟨3, 4, 5, 1⟩).toOption = some ⟨2, 3, 7, 3⟩
#guard (attachmentTextObstacle .cell ⟨3, 4, 0, 1⟩).toOption = some ⟨3, 4, 0, 1⟩
#guard match attachmentTextObstacle .cell ⟨I32_MIN, 0, 1, 1⟩ with
  | .error .overflow => true
  | _ => false
#guard match attachmentTextObstacle .cell ⟨I32_MAX - 1, 0, 1, 1⟩ with
  | .error .overflow => true
  | _ => false

def routeAround (profile : Profile) (inp : Input) (atts : List Attach) (frame : Frame)
    (rects : List (String × Rect)) (labels : List SceneLabel) (titles : List (String × Rect))
    (r : ModelRoute) : Except LayoutError (List Point) := do
  let some from_ := rects.lookup r.fromId | throw .domain
  let some to_ := rects.lookup r.toId | throw .domain
  let comp := componentIds inp atts r.fromId
  let boxObstacles := inp.boxes.filterMap fun b =>
    if b.exclusive && comp.contains b.id then rects.lookup b.id else none
  let labelObstacles := labels.filterMap fun l =>
    match inp.routes.find? (·.id == l.owner) with
    | some owner => if comp.contains owner.fromId then some l.rect else none
    | none => none
  let titleObstacles := titles.filterMap fun t => if comp.contains t.1 then some t.2 else none
  let textObstacles ← (labelObstacles ++ titleObstacles).mapM fun rect =>
    attachmentTextObstacle profile (frame.rect rect)
  let obstacles := boxObstacles.map frame.rect ++ textObstacles
  let starts := Visibility.ports (frame.rect from_)
  let ends := Visibility.ports (frame.rect to_)
  let grid := Visibility.newGrid obstacles (starts ++ ends) none
  match grid.shortest starts ends with
  | none => throw .domain
  | some points => pure (points.map frame.output)

def composeNotes (P : Params) (inp : Input) (o : Options) (margin : Int)
    (lines : List (List Measure.Line)) (contracted : FamilyResult)
    (layouts : List BundleLayout) (atts : List Attach) : Except LayoutError Scene := do
  let placed ← layouts.mapM (placedFragments margin contracted.scene)
  let fragments := placed.flatten
  let rectOf (id : String) : Option Rect :=
    match fragments.findSome? (·.rect id) with
    | some r => some r
    | none => (contracted.scene.boxes.find? (·.id == id)).map (·.rect)
  let boxes ← inp.boxes.mapM fun b => do
    let some rect := rectOf b.id | throw .domain
    pure (Box.mk b.id b.role.id rect b.parent b.exclusive)
  let bundleOf (id : String) : Option Nat :=
    layouts.findIdx? fun l => l.top.id == id || Compound.inside inp.boxes l.top.id id
  let labels := inp.labels.filterMap fun l =>
    match fragments.findSome? (·.label l.id) with
    | some label => some label
    | none => contracted.scene.labels.find? (·.id == l.id)
  let titles := fragments.flatMap (·.titles) ++ groupTitles contracted.scene.items
  let height : Int :=
    match o.direction with
    | .TB | .BT => contracted.scene.canvas.h - 2 * margin
    | .LR | .RL => contracted.scene.canvas.w - 2 * margin
  let frame : Frame := ⟨o.direction, height, margin⟩
  let rects := boxes.map fun b => (b.id, b.rect)
  let routes ← inp.routes.mapM fun r => do
    let points ←
      match bundleOf r.fromId, bundleOf r.toId with
      | some a, some b =>
        if a == b then
          match (placed.getD a []).findSome? (·.route r.id) with
          | some points => pure points
          | none => throw .domain
        else routeAround o.profile inp atts frame rects labels titles r
      | none, none =>
        match contracted.scene.routes.find? (·.id == r.id) with
        | some route => pure route.points
        | none => throw .domain
      | _, _ => routeAround o.profile inp atts frame rects labels titles r
    pure (Route.mk r.id r.fromId r.toId r.orthogonal points)
  let items := applyTitles titles (sceneItems P inp boxes routes lines labels)
  pure { contracted.scene with boxes := boxes, routes := routes, labels := labels, items := items }

def layoutNotes (base : List String → Input → Options → Except LayoutError FamilyResult)
    (exactIds : List String) : Nat → Input → Options → Except LayoutError FamilyResult
  | 0, inp, o => base exactIds inp o
  | fuel + 1, inp, o => do
    let atts := attachmentsOf inp.boxes
    let bundles := bundlesOf inp.boxes atts
    if bundles.isEmpty then base exactIds inp o
    else
      let P ← checkedParams o.profile inp.kind
      let metric ← metricOf o.profile o.fontFamily
      let margin := P.canvasMargin
      let layouts ← bundles.mapM
        (bundleLayout (layoutNotes base exactIds fuel) (base exactIds) inp o margin (2 * P.slot + 2))
      let contractedInput := layouts.foldl contractOne inp
      let contracted ← base (exactIds ++ layouts.map (·.top.id)) contractedInput o
      let lines ← boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp
      let scene ← composeNotes P inp o margin lines contracted layouts atts
      pure ⟨scene,
        contracted.budgetExhausted || layouts.any fun l =>
          l.part.budgetExhausted || l.notes.any (·.2.budgetExhausted),
        contracted.itemArea + layouts.foldl
          (fun area l => area + l.part.itemArea + l.notes.foldl (fun a n => a + n.2.itemArea) 0) 0⟩

end PipelineImpl

/-- The family entry with exact boxes and attached notes. -/
def layoutFamilyN (exactIds : List String) (inp : Input) (o : Options) :
    Except LayoutFailure FamilyResult :=
  layoutFamilyB (PipelineImpl.layoutNotes PipelineImpl.layoutX exactIds (inp.boxes.length + 1)) inp o

end Layered
end Elegant
