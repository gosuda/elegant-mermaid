import Elegant.Layered.RegionFlatC8b
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.FallbackCaptionClearProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region fallback caption clearance (`R_fallbackCaptionClearB8W_closed`).

Twin of `X_fallbackCaptionClearBW_closed`
(`ExactFallbackCaptionFactsProof.lean:479`) replayed over `SceneExecutionR`:
the fallback caption of an owner box with no installed title clears every
group frame once the fixed-size fit premise holds.

Six region premises (W form: local `WellFormed`/`framedParents` directly
after the execution binder exactly where the exact proof consumes them):

* `R_OwnerCaptionContainFallbackFit` (geometric, open): the owner caption
  lies inside the owner frame under fit;
* `R_FixedOwnerFit` (structural, proved below): a fixed-size entry naming a
  non-exclusive label-owning box fits that box's output rect;
* `R_NonfixedGroupTitle` (structural, proved below): a non-fixed group owner
  always records an installed title;
* `R_OwnerFrameDisjoint` (geometric, open): the C8a instance for the
  fallback owner frame;
* `R_AncestorFrameStrictW` (geometric, open): ancestor groups strictly
  contain the descendant frame under local admission;
* `R_FallbackOwnerCasesW` (structural, proved below): an owner with no
  installed title is a node-role box or a fixed-size box.

Probe evidence (`#eval`s below, vector profile, `layoutRIds` recomputed
phases): the non-`W` conclusion holds on the fitting rows and holds
vacuously where `InputFixedFit` fails; the ill-formed duplicate-id row
breaks it, so the `W` form is stated. -/

/-- R twin of `X_OwnerCaptionContainFallbackFit`
(`ExactCaptionFallbackProof.lean:113`): the owner caption lies inside the
owner frame under fit. Geometric residual, stays open. -/
def R_OwnerCaptionContainFallbackFit (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    InputFixedFit inp o →
    ∀ (ownerIndex : Nat) (obox : ModelBox),
      inp.boxes[ownerIndex]? = some obox →
      (sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
      obox.exclusive = false →
      (∃ l ∈ inp.labels, l.owner = obox.id) →
      let ownerBox : Box :=
        (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
          ownerIndex ⟨"", "", default, "", false⟩
      ownerBox.rect.Contained
        (ownedTextRect execution.params ownerBox
          (execution.lines.getD ownerIndex []))

/-- R twin of `X_FixedOwnerFitX` (`ExactCaptionFitFactsProof.lean:168`): a
fixed-size entry naming a non-exclusive label-owning box fits that box's
output rect. Structural, proved below from `InputFixedFit`. -/
def R_FixedOwnerFit (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hfit : InputFixedFit inp o)
    {i : Nat} {box : Box} {source : ModelBox}
    (_hbox : res.scene.boxes[i]? = some box)
    (_hsource : inp.boxes[i]? = some source)
    (_hany : inp.fixedSizes.any (fun e => e.1 == source.id) = true)
    (_hex : source.exclusive = false)
    (_hown : ∃ l ∈ inp.labels, l.owner = source.id),
    FixedSizeFit execution.params source.role (execution.lines.getD i [])
      ⟨box.rect.w, box.rect.h⟩

/-- R twin of `X_NonfixedGroupTitleX`
(`ExactFallbackCaptionFactsProof.lean:60`): a non-fixed group owner always
records an installed title. Structural, proved below. -/
def R_NonfixedGroupTitle (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {k : Nat} {obox : ModelBox},
    inp.boxes[k]? = some obox →
    obox.role = .group →
    inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false →
    ((sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id)).isSome = true

 /-- R twin of `X_OwnerFrameDisjointX`
 (`ExactFallbackCaptionFactsProof.lean:70`): the C8a instance the owner-frame
 proof needs. Geometric residual, stays open. -/
 def R_OwnerFrameDisjoint (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (ownerIndex : Nat) (obox : ModelBox) (g : Box),
     inp.boxes[ownerIndex]? = some obox →
     (sceneTitlesExpr execution.params inp o execution.lines
       execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
     g ∈ res.scene.boxes → g.role = "group" →
     g.id ≠ obox.id →
     g.id ∉ res.scene.layoutDump.ancestors obox.id →
     obox.id ∉ res.scene.layoutDump.ancestors g.id →
     Disjoint g.rect
       ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
         ownerIndex ⟨"", "", default, "", false⟩).rect

 /-- R twin of `X_AncestorFrameStrictW`
 (`ExactFallbackCaptionFactsProof.lean:94`): ancestor groups strictly contain
 the descendant frame under local admission. Geometric residual, stays open. -/
 def R_AncestorFrameStrictW (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (_execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true)
     (g ob : Box),
     g ∈ res.scene.boxes → ob ∈ res.scene.boxes →
     g.role = "group" →
     g.id ∈ res.scene.layoutDump.ancestors ob.id →
     g.rect.StrictInside ob.rect

 /-- R twin of `X_FallbackOwnerCasesX`
 (`ExactCaptionFitFactsProof.lean:186`): an owner with no installed title is a
 node-role box or a fixed-size box. Structural, proved below. -/
 def R_FallbackOwnerCasesW (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o))
     {k : Nat} {obox : ModelBox} (_hbox : inp.boxes[k]? = some obox)
     (_hnone : (sceneTitlesExpr execution.params inp o execution.lines
       execution.packedAcc).find? (fun title => title.1 == obox.id) = none),
     obox.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true

 /-- R twin of `X_FallbackCaptionClearBW`
 (`ExactFallbackCaptionFactsProof.lean:154`): the `W` fallback-caption
 conclusion over executed region scenes. -/
 def R_FallbackCaptionClearBW (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true),
     InputFixedFit inp o →
     ∀ (source : ModelLabel) (index ownerIndex : Nat) (g : Box),
       inp.labels[index]? = some source →
       inp.boxes.findIdx? (fun box : ModelBox =>
         box.id == source.owner && !box.exclusive) = some ownerIndex →
       (sceneTitlesExpr execution.params inp o execution.lines
           execution.packedAcc).find? (fun t => t.1 == source.owner) = none →
       g ∈ res.scene.boxes → g.role = "group" →
       let l := ownedTextRect execution.params
         ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
           ownerIndex ⟨"", "", default, "", false⟩)
         (execution.lines.getD ownerIndex [])
       Disjoint g.rect l ∨ g.rect.StrictInside l

 /-! ## Probe evidence: five executed `layoutRIds` rows plus ill-formed rows. -/

 /-- Shared options for the probes (vector profile, top-to-bottom). -/
 private def rfbOpts : Options := { profile := .vector, direction := .TB }

 /-- Flat two groups with a fallback label owned by node `a1`. -/
 private def rfbFitInp : Input :=
   { kind := "state"
     boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
       { id := "A", role := .group, parent := "G1", exclusive := false },
       { id := "B", role := .group, parent := "G1", exclusive := false },
       { id := "G2", role := .group, parent := "", exclusive := false },
       { id := "C", role := .group, parent := "G2", exclusive := false },
       { id := "D", role := .group, parent := "G2", exclusive := false },
       { id := "a1", parent := "A", exclusive := false },
       { id := "b1", parent := "B", exclusive := false },
       { id := "c1", parent := "C", exclusive := false },
       { id := "d1", parent := "D", exclusive := false }]
     routes := [{ id := "e1", fromId := "a1", toId := "c1" },
       { id := "e2", fromId := "b1", toId := "d1" },
       { id := "e3", fromId := "c1", toId := "b1" }]
     texts := ["G1", "A", "B", "G2", "C", "D", "a1", "b1", "c1", "d1"]
     edges := [.plain, .plain, .plain]
     labels := [{ id := "L1", owner := "a1", text := "hi" }] }

 /-- Nested groups with a fallback label owned by the innermost node. -/
 private def rfbNestInp : Input :=
   { kind := "state"
     boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
       { id := "H", role := .group, parent := "G", exclusive := false },
       { id := "h", parent := "H", exclusive := false }]
     routes := []
     texts := ["G", "H", "h"]
     edges := []
     labels := [{ id := "L1", owner := "h", text := "deep" }] }

 /-- Self-loop route with a fallback label on the looping node. -/
 private def rfbSelfInp : Input :=
   { kind := "state"
     boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
       { id := "a", parent := "G", exclusive := false }]
     routes := [{ id := "e0", fromId := "a", toId := "a" }]
     texts := ["G", "a"]
     edges := [.plain]
     labels := [{ id := "L1", owner := "a", text := "loop" }] }

 /-- Zero-size and wide fixed boxes owning fallback labels. -/
 private def rfbFixedInp : Input :=
   { kind := "state"
     boxes := [{ id := "Z", parent := "", exclusive := false },
       { id := "W", parent := "", exclusive := false }]
     routes := []
     texts := ["Z", "W"]
     edges := []
     fixedSizes := [("Z", { w := 0, h := 0 }), ("W", { w := 5000, h := 5000 })]
     labels := [{ id := "L1", owner := "Z", text := "zero" },
       { id := "L2", owner := "W", text := "wide" }] }

 /-- Ill-formed row: duplicate box id `A` (second box parented elsewhere). -/
 private def rfbDupInp : Input :=
   { kind := "state"
     boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
       { id := "A", parent := "G", exclusive := false },
       { id := "A", parent := "", exclusive := false }]
     routes := []
     texts := ["G", "A", "A"]
     edges := []
     labels := [{ id := "L1", owner := "A", text := "dup" }] }

 /-- Ill-formed row: self-parented group with a fallback label inside. -/
 private def rfbSelfParInp : Input :=
   { kind := "state"
     boxes := [{ id := "G", role := .group, parent := "G", exclusive := false },
       { id := "a", parent := "G", exclusive := false }]
     routes := []
     texts := ["G", "a"]
     edges := []
     labels := [{ id := "L1", owner := "a", text := "selfpar" }] }

 /-- Region sets for the flat probe (copy of `r8bProbeIdSets`). -/
 private def rfbFitIdSets : List (String × List String) :=
   [("G1", ["A", "B"]), ("G2", ["C", "D"])]

 /-- Layout success mirror. -/
 private def rfbOk (inp : Input) (idSets : List (String × List String)) : Bool :=
   match layoutRIds [] idSets inp rfbOpts with
   | .ok _ => true
   | .error _ => false

 #eval rfbOk rfbFitInp rfbFitIdSets
 #eval rfbOk rfbNestInp []
 #eval rfbOk rfbSelfInp []
 #eval rfbOk rfbFixedInp []
 #eval rfbOk rfbDupInp []
 #eval rfbOk rfbSelfParInp []

 /-- Recomputed region phases for the mirror (same equations as `layoutRIds`). -/
 private def rfbPhases (inp : Input) (idSets : List (String × List String))
     (o : Options) : Except LayoutError (Params × List (List Measure.Line) × Acc) := do
   let P ← checkedParams o.profile inp.kind
   let m ← metricOf o.profile
   let target := Measure.wrapTarget m.profile P.wrapWidth
     (if o.profile == .cell then o.maxWidth else 0)
   let lines ← boxLines m target inp
   let measured ← measureLabels P m target inp o.direction
   let g0 ← measuredGraph P inp o lines
   let g ← exactGraph P [] inp o measured g0
   let titles := lines.map fun ls =>
     let width := ls.foldl (fun w line => max w line.width) 0
     let height := (max 1 ls.length : Int) * P.lineH
     match o.direction with
     | .LR | .RL => (height, width)
     | .TB | .BT => (width, height)
   let spec : Option RegionSpec :=
     if idSets.isEmpty then none else some { sets := idSets, titles := titles }
   let start : Acc :=
     ⟨0, 0, 0, Array.replicate inp.boxes.length default,
       Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
       false, [], []⟩
   let mid ← (components g).foldlM
     (fun acc comp => layoutComponentR P [] spec inp o g acc comp measured) start
   let packed ← packAcc P o mid
   pure (P, lines, packed)

 /-- Bool mirror of `R_FallbackCaptionClearB8` on recomputed phases. -/
 private def rfbFallbackB (inp : Input) (idSets : List (String × List String))
     (o : Options) : Bool :=
   match rfbPhases inp idSets o with
   | .error _ => true
   | .ok (P, lines, packed) =>
     let boxes := sceneBoxesExpr P inp o packed
     let titles := sceneTitlesExpr P inp o lines packed
     (List.range inp.labels.length).all fun index =>
       match inp.labels[index]? with
       | none => true
       | some source =>
         match inp.boxes.findIdx?
             (fun box : ModelBox => box.id == source.owner && !box.exclusive) with
         | none => true
         | some ownerIndex =>
           if (titles.find? (fun t => t.1 == source.owner)).isSome then true
           else
             let l := ownedTextRect P (boxes.getD ownerIndex ⟨"", "", default, "", false⟩)
               (lines.getD ownerIndex [])
             boxes.all fun g => !(g.role == "group") ||
               decide (Disjoint g.rect l) || decide (g.rect.StrictInside l)

 #eval rfbFallbackB rfbFitInp rfbFitIdSets rfbOpts
 #eval rfbFallbackB rfbNestInp [] rfbOpts
 #eval rfbFallbackB rfbSelfInp [] rfbOpts
 #eval rfbFallbackB rfbFixedInp [] rfbOpts
 #eval rfbFallbackB rfbDupInp [] rfbOpts
 #eval rfbFallbackB rfbSelfParInp [] rfbOpts
 #eval modelWellFormed (inputModel rfbFitInp rfbOpts)
 #eval modelWellFormed (inputModel rfbDupInp rfbOpts)
 #eval modelWellFormed (inputModel rfbSelfParInp rfbOpts)

 /-! ## Replay helpers (prefixed copies of the `xfg_` lemmas in
 `ExactFallbackCaptionFactsProof.lean`, over `SceneExecutionR`). -/

 /-- `rfb_` copy of `xfg_sceneBoxes_eq`: the region scene boxes are the
 `sceneBoxesExpr` projection. -/
 private theorem rfb_sceneBoxes_eq {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res) :
     res.scene.boxes =
       sceneBoxesExpr execution.params inp o execution.packedAcc := by
   rw [execution.boxes_eq_mapR]
   rfl

 /-- `rfb_` copy of `xfg_box_index_origin`: the scene box at `index` comes
 from the input box at the same index. -/
 private theorem rfb_box_index_origin {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res) {index : Nat} {box : Box}
     (hbox : res.scene.boxes[index]? = some box) :
     ∃ source, inp.boxes[index]? = some source ∧
       box = Box.mk source.id source.role.id
         (shiftRect execution.params.canvasMargin execution.params.canvasMargin
           (orientRect o.direction execution.packedAcc.canvasH
             (execution.packedAcc.rects.getD index default)))
         source.parent source.exclusive := by
   rw [execution.boxes_eq_mapR] at hbox
   cases hs : inp.boxes[index]? with
   | none => simp [hs] at hbox
   | some source =>
     refine ⟨source, rfl, ?_⟩
     simpa [hs] using hbox.symm

 /-- `rfb_` copy of `xfg_scene_box_source`: every scene box comes from the
 input box at the same index, keeping id, parent, and role. -/
 private theorem rfb_scene_box_source {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     {b : Box} (hb : b ∈ res.scene.boxes) :
     ∃ (idx : Nat) (src : ModelBox), inp.boxes[idx]? = some src ∧
       b.id = src.id ∧ b.parent = src.parent ∧ b.role = src.role.id := by
   obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hb
   obtain ⟨src, hsrc, hboxeq⟩ := rfb_box_index_origin execution hidx
   refine ⟨idx, src, hsrc, ?_, ?_, ?_⟩ <;> rw [hboxeq]

 /-- `rfb_` copy of `xfg_go_succ_step` (`FallbackOwnerFrameProof.lean`): one
 unfolded step of the ancestor walk. -/
 private theorem rfb_go_succ_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
     (hb : d.box? s = some b) (hne : b.parent ≠ "") :
     LayoutDump.ancestors.go d (k + 1) s =
       b.parent :: LayoutDump.ancestors.go d k b.parent := by
   have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
   simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

 /-- `rfb_` copy of `xfg_go_none_step`: the ancestor walk from a missing id
 is empty. -/
 private theorem rfb_go_none_step {d : LayoutDump} {k : Nat} {s : String}
     (h : d.box? s = none) :
     LayoutDump.ancestors.go d (k + 1) s = [] := by
   have hfind : d.boxes.find? (fun b => b.id == s) = none := h
   simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

 /-- `rfb_` copy of `xfg_go_root_step`: the ancestor walk from a root box is
 empty. -/
 private theorem rfb_go_root_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
     (hb : d.box? s = some b) (hpar : b.parent = "") :
     LayoutDump.ancestors.go d (k + 1) s = [] := by
   have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
   simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

 /-- `rfb_` copy of `xfg_ancestors_mem_ne`: members of an ancestor walk are
 never the empty id. -/
 private theorem rfb_ancestors_mem_ne {d : LayoutDump} {x : String}
     {n : Nat} {s : String}
     (hmem : x ∈ LayoutDump.ancestors.go d n s) : x ≠ "" := by
   induction n generalizing s with
   | zero =>
       have e : LayoutDump.ancestors.go d 0 s = [] := rfl
       rw [e] at hmem
       cases hmem
   | succ n ih =>
       cases h : d.box? s with
       | none =>
           rw [rfb_go_none_step h] at hmem
           cases hmem
       | some b =>
           by_cases hpar : b.parent = ""
           · rw [rfb_go_root_step h hpar] at hmem
             cases hmem
           · rw [rfb_go_succ_step h hpar] at hmem
             rcases List.mem_cons.mp hmem with heq | hmem'
             · rw [heq]
               exact hpar
             · exact ih hmem'

 /-- `rfb_` copy of `xfg_ancestors_member_parent`: ancestor membership yields
 a scene box parented at the member id. -/
 private theorem rfb_ancestors_member_parent {d : LayoutDump} {x : String}
     {n : Nat} {s : String}
     (hmem : x ∈ LayoutDump.ancestors.go d n s) :
     ∃ c ∈ d.boxes, c.parent = x := by
   induction n generalizing s with
   | zero =>
       have e : LayoutDump.ancestors.go d 0 s = [] := rfl
       rw [e] at hmem
       cases hmem
   | succ n ih =>
       cases h : d.box? s with
       | none =>
           rw [rfb_go_none_step h] at hmem
           cases hmem
       | some b =>
           by_cases hpar : b.parent = ""
           · rw [rfb_go_root_step h hpar] at hmem
             cases hmem
           · rw [rfb_go_succ_step h hpar] at hmem
             rcases List.mem_cons.mp hmem with heq | hmem'
             · exact ⟨b, List.mem_of_find?_eq_some h, heq.symm⟩
             · exact ih hmem'

 /-- The `W` scene id uniqueness over region executions: from the scene/input
 id transport (`boxes_eq_mapR`, `zipIdx_map_comp`) and input uniqueness. -/
 private theorem rfb_sceneBoxesNodupW {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true) :
     (res.scene.boxes.map (·.id)).Nodup := by
   have hmap : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
     rw [execution.boxes_eq_mapR, List.map_map]
     exact zipIdx_map_comp (·.id) inp.boxes 0
   rw [hmap]
   exact Model.boxIds_nodup hwf

 /-- `W` no-descendants over region executions: a fallback owner never appears
 in any scene ancestor walk. Proved below by replaying
 `owner_not_in_ancestors_of_framed`. -/
 private def rfb_OwnerNoDescW (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true)
     (ownerIndex : Nat) (obox : ModelBox),
     inp.boxes[ownerIndex]? = some obox →
     (sceneTitlesExpr execution.params inp o execution.lines
         execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
     ∀ (g : Box), obox.id ∉ res.scene.layoutDump.ancestors g.id

 /-- The `W` no-descendants fact from the fallback-owner cases: replay of
 `X_fallbackOwnerNoDescW_holds` over `SceneExecutionR`. -/
 private theorem rfb_noDesc_holds (exactIds : List String)
     (idSets : List (String × List String))
     (hcases : R_FallbackOwnerCasesW exactIds idSets) :
     rfb_OwnerNoDescW exactIds idSets := by
   intro inp o res execution hwf hfp ownerIndex obox hobox hnone g hmem
   have hmemGo : obox.id ∈ LayoutDump.ancestors.go res.scene.layoutDump
       res.scene.layoutDump.boxes.length g.id := hmem
   have hneid : obox.id ≠ "" := rfb_ancestors_mem_ne hmemGo
   obtain ⟨c, hcMem, hcPar⟩ := rfb_ancestors_member_parent hmemGo
   obtain ⟨cIdx, cSrc, hsrc, -, hcpar, -⟩ := rfb_scene_box_source execution hcMem
   have hspe : cSrc.parent = obox.id := hcpar.symm.trans hcPar
   have hsrcMem : cSrc ∈ inp.boxes := List.mem_of_getElem? hsrc
   have hne : cSrc.parent ≠ "" := by rw [hspe]; exact hneid
   obtain ⟨par, hparMem, hparId, hparRole, hparNotFixed⟩ :=
     framedParents_parent hfp hsrcMem hne
   have hparIdOb : par.id = obox.id := hparId.trans hspe
   obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp hparMem
   have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
   have ha : (inp.boxes.map (·.id))[pIdx]? = some obox.id := by
     simp [List.getElem?_map, hpIdx, hparIdOb]
   have hb : (inp.boxes.map (·.id))[ownerIndex]? = some obox.id := by
     simp [List.getElem?_map, hobox]
   have hlookups : (inp.boxes.map (·.id))[pIdx]? =
       (inp.boxes.map (·.id))[ownerIndex]? := by rw [ha, hb]
   have hbound : pIdx < (inp.boxes.map (·.id)).length := by
     rw [List.length_map]
     exact (List.getElem?_eq_some_iff.mp hpIdx).1
   have hidxEq : pIdx = ownerIndex :=
     (List.Nodup.getElem?_inj hbound hids).mp hlookups
   have hparOb : par = obox := by
     have hsame : inp.boxes[pIdx]? = inp.boxes[ownerIndex]? := by rw [hidxEq]
     rw [hpIdx, hobox] at hsame
     exact Option.some.inj hsame
   have hfall := hcases execution hwf hobox hnone
   rcases hfall with hnode | hfixed
   · have hgr : obox.role = .group := hparOb ▸ hparRole
     rw [hnode] at hgr
     exact absurd hgr (by decide)
   · have hnf : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false := by
       rw [← hparIdOb]
       exact hparNotFixed
     rw [hfixed] at hnf
     exact absurd hnf (by decide)

 /-- R group-owner strict caption: under the fixed-size fit premise, the
 fallback caption of a group-role owner with no installed title lies strictly
 inside the owner frame. Copy of `X_FallbackGroupStrictCaption` over
 `SceneExecutionR`. -/
 private def rfb_GroupStrictCaption (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res),
     InputFixedFit inp o →
     ∀ (ownerIndex : Nat) (obox : ModelBox),
       inp.boxes[ownerIndex]? = some obox →
       (sceneTitlesExpr execution.params inp o execution.lines
           execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
       obox.exclusive = false →
       (∃ l ∈ inp.labels, l.owner = obox.id) →
       obox.role = .group →
       ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
         ownerIndex ⟨"", "", default, "", false⟩).rect.StrictInside
         (ownedTextRect execution.params
           ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
             ownerIndex ⟨"", "", default, "", false⟩)
           (execution.lines.getD ownerIndex []))

 /-- The region group-owner strict caption from the fixed-size output fit and
 the non-fixed title residual. Replay of `X_fallbackGroupStrictCaption_holds`. -/
 private theorem rfb_groupStrict_holds (exactIds : List String)
     (idSets : List (String × List String))
     (hfix : R_FixedOwnerFit exactIds idSets)
     (htitle : R_NonfixedGroupTitle exactIds idSets) :
     rfb_GroupStrictCaption exactIds idSets := by
   intro inp o res execution hfit ownerIndex obox hobox hnone hex hown hgroup
   have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
       = inp.boxes.length := by
     simp [sceneBoxesExpr]
   have hlt : ownerIndex < inp.boxes.length :=
     (List.getElem?_eq_some_iff.mp hobox).1
   have hi : ownerIndex <
       (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
     omega
   obtain ⟨obv, hobb⟩ : ∃ box : Box,
       (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
         some box := ⟨_, List.getElem?_eq_getElem hi⟩
   have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
       ownerIndex ⟨"", "", default, "", false⟩ = obv := by
     rw [List.getD_eq_getElem?_getD, hobb]
     rfl
   have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
     rw [rfb_sceneBoxes_eq execution]
     exact hobb
   obtain ⟨actual, hactual, hboxeq⟩ := rfb_box_index_origin execution hboxScene
   rw [hobox] at hactual
   have hact : actual = obox := (Option.some.inj hactual).symm
   have hroleEq : obv.role = obox.role.id := by rw [hboxeq, hact]
   have hgroupScene : obv.role = "group" := by
     simp only [hroleEq, hgroup, BoxRole.id]
   rw [hgetD]
   by_cases hany : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true
   · have hfit' := hfix execution hfit hboxScene hobox hany hex hown
     rw [hgroup] at hfit'
     simp only [FixedSizeFit] at hfit'
     obtain ⟨hgw, hgh⟩ := hfit'
     have hcp : 0 < execution.params.clusterPad :=
       checkedParams_clusterPad_pos execution.checked
     rw [ownedTextRect_group_eq hgroupScene]
     exact titleRect_strictInside_of_fit hcp hgw hgh
   · have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false :=
       Bool.eq_false_iff.mpr hany
     have hsome := htitle execution hobox hgroup hfalse
     have hnoneSome : ((sceneTitlesExpr execution.params inp o execution.lines
         execution.packedAcc).find? (fun title => title.1 == obox.id)).isSome = false := by
       rw [hnone]
       rfl
     rw [hsome] at hnoneSome
     exact absurd hnoneSome (by decide)

 /-- R owner-frame fact: every group scene box is disjoint from the owner
 frame, strictly contains it, or is the owner scene box itself. Copy of
 `X_FallbackOwnerFrameClearX` over `SceneExecutionR`. -/
 private def rfb_OwnerFrameClearXW (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true)
     (ownerIndex : Nat) (obox : ModelBox) (g : Box),
     inp.boxes[ownerIndex]? = some obox →
     (sceneTitlesExpr execution.params inp o execution.lines
         execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
     g ∈ res.scene.boxes → g.role = "group" →
     Disjoint g.rect
       ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
         ownerIndex ⟨"", "", default, "", false⟩).rect ∨
       g.rect.StrictInside
         ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
           ownerIndex ⟨"", "", default, "", false⟩).rect ∨
       g = (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
         ownerIndex ⟨"", "", default, "", false⟩

 /-- The `W` owner-frame fact from the C8a instance, ancestor strictness,
 no-descendants, and scene nodup. Replay of
 `X_fallbackOwnerFrameClearXW_holds` over `SceneExecutionR`. -/
private theorem rfb_ownerFrame_holds (exactIds : List String)
    (idSets : List (String × List String))
    (hdisj : R_OwnerFrameDisjoint exactIds idSets)
    (hastrict : R_AncestorFrameStrictW exactIds idSets)
    (hnodesc : rfb_OwnerNoDescW exactIds idSets) :
    rfb_OwnerFrameClearXW exactIds idSets := by
  intro inp o res execution hwf hfp ownerIndex obox g hobox hnone hgMem hgRole
  have hnodup := rfb_sceneBoxesNodupW execution hwf hfp
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨obv, hobb⟩ : ∃ box : Box,
       (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
         some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = obv := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
    rw [rfb_sceneBoxes_eq execution]
    exact hobb
  obtain ⟨actual, hactual, hboxeq⟩ := rfb_box_index_origin execution hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hobId : obv.id = obox.id := by rw [hboxeq, hact]
  have hobMem : obv ∈ res.scene.boxes := List.mem_of_getElem? hboxScene
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hgMem
  rw [hgetD]
  show Disjoint g.rect obv.rect ∨ g.rect.StrictInside obv.rect ∨ g = obv
  by_cases hjEq : j = ownerIndex
  · subst hjEq
    have hgo : g = obv :=
      Option.some.inj (hj.symm.trans hboxScene)
    exact Or.inr (Or.inr hgo)
  · by_cases hanc : g.id ∈ res.scene.layoutDump.ancestors obv.id
    · have hst := hastrict execution hwf hfp g obv hgMem hobMem hgRole hanc
      exact Or.inr (Or.inl hst)
    · by_cases hEqId : g.id = obox.id
      · have ha : (res.scene.boxes.map (·.id))[j]? = some obox.id := by
          simp [List.getElem?_map, hj, hEqId]
        have hb : (res.scene.boxes.map (·.id))[ownerIndex]? = some obox.id := by
          simp [List.getElem?_map, hboxScene, hobId]
        have hbound : j < (res.scene.boxes.map (·.id)).length := by
          rw [List.length_map]
          exact (List.getElem?_eq_some_iff.mp hj).1
        have heqIdx : j = ownerIndex :=
          (List.Nodup.getElem?_inj hbound hnodup).mp (ha.trans hb.symm)
        exact absurd heqIdx hjEq
      · have hancOb : g.id ∉ res.scene.layoutDump.ancestors obox.id := by
          rw [← hobId]
          exact hanc
        have hobAbsent := hnodesc execution hwf hfp ownerIndex obox hobox hnone g
        have hd := hdisj execution ownerIndex obox g hobox hnone hgMem hgRole
          hEqId hancOb hobAbsent
        rw [hgetD] at hd
        exact Or.inl hd

 /-- The `W` fallback-caption clearance from the six region premises.
 Replay of `X_fallbackCaptionClearBW_closed` over `SceneExecutionR`: scene
 nodup and no-descendants are discharged by the proved `W` theorems above. -/
 theorem R_fallbackCaptionClearB8W_closed (exactIds : List String)
     (idSets : List (String × List String))
     (hcontain : R_OwnerCaptionContainFallbackFit exactIds idSets)
     (hfix : R_FixedOwnerFit exactIds idSets)
     (htitle : R_NonfixedGroupTitle exactIds idSets)
     (hdisj : R_OwnerFrameDisjoint exactIds idSets)
     (hastrict : R_AncestorFrameStrictW exactIds idSets)
     (hcases : R_FallbackOwnerCasesW exactIds idSets) :
     R_FallbackCaptionClearBW exactIds idSets := by
  intro inp o res execution hwf hfp hfit source index ownerIndex g hsrc hfind
     hnone hgMem hgRole
  have hnodupW := rfb_sceneBoxesNodupW execution hwf hfp
  have hnodescW : rfb_OwnerNoDescW exactIds idSets :=
    rfb_noDesc_holds exactIds idSets hcases
  have hR2 : rfb_GroupStrictCaption exactIds idSets :=
    rfb_groupStrict_holds exactIds idSets hfix htitle
  have hR3W : rfb_OwnerFrameClearXW exactIds idSets :=
    rfb_ownerFrame_holds exactIds idSets hdisj hastrict hnodescW
  obtain ⟨hlt, hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  obtain ⟨obox, hobox⟩ : ∃ obox, inp.boxes[ownerIndex]? = some obox :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hge : inp.boxes[ownerIndex] = obox :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hobox)
  rw [hge] at hpred
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpred
  obtain ⟨hownId, hex⟩ := hpred
  have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [hownId]
    exact hnone
  have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
    ⟨source, List.mem_of_getElem? hsrc, hownId.symm⟩
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨obv, hobb⟩ : ∃ box : Box,
      (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = obv := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
    rw [rfb_sceneBoxes_eq execution]
    exact hobb
  obtain ⟨actual, hactual, hboxeq⟩ := rfb_box_index_origin execution hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hroleEq : obv.role = obox.role.id := by rw [hboxeq, hact]
  have hcontFull : obv.rect.Contained (ownedTextRect execution.params obv
      (execution.lines.getD ownerIndex [])) := by
    have h := hcontain execution hfit ownerIndex obox hobox hnone' hex hown
    rw [hgetD] at h
    exact h
  rw [hgetD]
  show Disjoint g.rect (ownedTextRect execution.params obv
      (execution.lines.getD ownerIndex [])) ∨
    g.rect.StrictInside (ownedTextRect execution.params obv
      (execution.lines.getD ownerIndex []))
  have hfr := hR3W execution hwf hfp ownerIndex obox g hobox hnone' hgMem hgRole
  rw [hgetD] at hfr
  rcases hfr with hdisj | hstrictfr | heq
  · exact Or.inl ((Disjoint.comm _ _).mpr
      (disjoint_of_sub_disjoint hcontFull ((Disjoint.comm _ _).mp hdisj)))
  · by_cases hgr : obox.role = .group
    · have hsc :=
        hR2 execution hfit ownerIndex obox hobox hnone' hex hown hgr
      rw [hgetD] at hsc
      have hcont2 : g.rect.Contained obv.rect := by
        unfold Rect.StrictInside at hstrictfr
        unfold Rect.Contained at ⊢
        omega
      exact Or.inr (strictInside_of_contained hsc hcont2)
    · have hgoal : g.rect.StrictInside (ownedTextRect execution.params obv
          (execution.lines.getD ownerIndex [])) := by
          unfold Rect.StrictInside at hstrictfr ⊢
          unfold Rect.Contained at hcontFull
          omega
      exact Or.inr hgoal
  · subst heq
    have hgr : obox.role = .group := by
      rw [hroleEq] at hgRole
      cases h : obox.role with
      | node =>
        rw [h] at hgRole
        simp only [BoxRole.id] at hgRole
        exact absurd hgRole (by decide)
      | group => rfl
    have hsc :=
      hR2 execution hfit ownerIndex obox hobox hnone' hex hown hgr
    rw [hgetD] at hsc
    exact Or.inr hsc

 /-- Bool mirror of `R_FixedOwnerFit` on recomputed phases. -/
 private def rfbFixB (inp : Input) (idSets : List (String × List String))
     (o : Options) : Bool :=
   match rfbPhases inp idSets o with
   | .error _ => true
   | .ok (P, lines, packed) =>
     let boxes := sceneBoxesExpr P inp o packed
     inp.fixedSizes.all fun entry =>
       match inp.boxes.findIdx? (fun box : ModelBox => box.id == entry.1) with
       | none => true
       | some i =>
         match inp.boxes[i]?, boxes[i]? with
         | some src, some box =>
           if src.exclusive then true
           else if !(inp.labels.any fun l => l.owner == src.id) then true
           else
             let ls := lines.getD i []
             match src.role with
             | .group => decide (2 * P.clusterPad ≤ box.rect.w) &&
               decide (P.clusterPad + (max 1 ls.length : Int) * P.lineH < box.rect.h)
             | .node => decide ((ls.length : Int) * P.lineH ≤ box.rect.h)
         | _, _ => false

 /-- Bool mirror of `R_NonfixedGroupTitle` on recomputed phases. -/
 private def rfbTitleB (inp : Input) (idSets : List (String × List String))
     (o : Options) : Bool :=
   match rfbPhases inp idSets o with
   | .error _ => true
   | .ok (P, lines, packed) =>
     let titles := sceneTitlesExpr P inp o lines packed
     inp.boxes.all fun obox =>
       if obox.role != .group then true
       else if inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) then true
       else ((titles.find? (fun title => title.1 == obox.id)).isSome)

 /-- Bool mirror of `R_FallbackOwnerCasesW` on recomputed phases. -/
 private def rfbCasesB (inp : Input) (idSets : List (String × List String))
     (o : Options) : Bool :=
   match rfbPhases inp idSets o with
   | .error _ => true
   | .ok (P, lines, packed) =>
     let titles := sceneTitlesExpr P inp o lines packed
     inp.boxes.all fun obox =>
       if (titles.find? (fun title => title.1 == obox.id)).isSome then true
       else (obox.role == .node) ||
         inp.fixedSizes.any (fun fixed => fixed.1 == obox.id)

 #eval rfbFixB rfbFitInp rfbFitIdSets rfbOpts
 #eval rfbFixB rfbFixedInp [] rfbOpts
 #eval rfbTitleB rfbFitInp rfbFitIdSets rfbOpts
 #eval rfbTitleB rfbNestInp [] rfbOpts
 #eval rfbTitleB rfbFixedInp [] rfbOpts
 #eval rfbCasesB rfbFitInp rfbFitIdSets rfbOpts
 #eval rfbCasesB rfbDupInp [] rfbOpts
 #eval rfbCasesB rfbSelfParInp [] rfbOpts

 /-- Wide fixed box owning a fallback label (fits its caption). -/
 private def rfbWideInp : Input :=
   { kind := "state"
     boxes := [{ id := "W", parent := "", exclusive := false }]
     routes := []
     texts := ["W"]
     edges := []
     fixedSizes := [("W", { w := 5000, h := 5000 })]
     labels := [{ id := "L2", owner := "W", text := "wide" }] }

 #eval rfbOk rfbWideInp []
 #eval rfbFallbackB rfbWideInp [] rfbOpts
 #eval rfbFixB rfbWideInp [] rfbOpts

 /-- Bool mirror of the `InputFixedFit` premise on fixed entries. -/
private def rfbFitPremiseB (P : Params) (_o : Options) (lines : List (List Measure.Line))
     (inp : Input) : Bool :=
   inp.fixedSizes.all fun entry =>
     match inp.boxes.findIdx? (fun box : ModelBox => box.id == entry.1) with
     | none => true
     | some i =>
       match inp.boxes[i]? with
       | none => false
       | some box =>
         if box.exclusive then true
         else if !(inp.labels.any fun l => l.owner == box.id) then true
         else
           let ls := lines.getD i []
           match box.role with
           | .group => decide (2 * P.clusterPad ≤ entry.2.w) &&
             decide (P.clusterPad + (max 1 ls.length : Int) * P.lineH < entry.2.h)
           | .node => decide ((ls.length : Int) * P.lineH ≤ entry.2.h)

 /-- Fit premise on recomputed lines for the fixed rows. -/
 private def rfbFitPremiseOn (inp : Input) (o : Options) : Bool :=
   match rfbPhases inp [] o with
   | .error _ => true
   | .ok (P, lines, _) => rfbFitPremiseB P o lines inp

 #eval rfbFitPremiseOn rfbFixedInp rfbOpts
 #eval rfbFitPremiseOn rfbWideInp rfbOpts

 /-! NOTE: the three-premise wrapper (`R_fallbackCaptionClearB8W_holds`
 from the three geometric twins alone) is withheld: its three structural
 premises (`R_FixedOwnerFit`, `R_NonfixedGroupTitle`,
 `R_FallbackOwnerCasesW`) still need the region part-sizing residual
 (`R_PartSizingR`) and the region title-existence chain, both open.
 The six-premise `R_fallbackCaptionClearB8W_closed` above stays proved.

 ## Structural twins: fixed-owner fit. -/

/-- The packing fold preserves the rect array size (copy of
`r8b_packFold_rects_size` in `RegionFlatC8b.lean`). -/
private theorem rfb_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Region packed rect array size (copy of `r8b_packedAcc_rects_sizeR` in
`RegionFlatC8b.lean`, via `SceneExecutionR.components_rects_sizeR`). -/
private theorem rfb_packedAcc_rects_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [rfb_packFold_rects_size]
  exact execution.components_rects_sizeR

 /-- Region packed rect existence from the input length. -/
 private theorem rfb_packed_rect_existsR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res) {i : Nat}
     (hi : i < inp.boxes.length) :
     ∃ rect, execution.packedAcc.rects[i]? = some rect := by
   have hsize : i < execution.packedAcc.rects.size := by
     rw [rfb_packedAcc_rects_sizeR execution]
     exact hi
   exact ⟨execution.packedAcc.rects[i],
    Array.getElem?_eq_some_iff.mpr ⟨hsize, rfl⟩⟩

 /-- Region title reservations keep border-0 nodes fixed: mirror of the
 `titleF` step for `titleReservationsR`. -/
 private theorem rfb_titleReservationsR_border0 (titles : List (Int × Int))
     (pad : Int) (p : Proper) {i : Nat} {nd : ProperNode}
     (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0) :
     (titleReservationsR titles pad p).nodes[i]? = some nd := by
   have hb128 : (nd.node.border == -2 || nd.node.border == 2) = false := by
     simp only [hb]
     decide
   have hlen : i < (p.nodes.map (fun node =>
       if node.node.border == -2 || node.node.border == 2 then
         { node with node := { node.node with w := 0, h := 0 } } else node)).length := by
     rw [List.length_map]
     exact (List.getElem?_eq_some_iff.mp hp).1
   simp only [titleReservationsR, List.getElem?_append_left hlen, List.getElem?_map,
     hp, Option.map_some]
   simp [hb128]
