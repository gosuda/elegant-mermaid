import Elegant.Layered.ExactStepFacts
import Elegant.Layered.FamilyC5B
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.ExactFlatC5Closed
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.InsetFit
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.Assembly
import Elegant.Layered.RecursiveFit
import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.ExpandChildC6StepFacts
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.MergedRouteIdsProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.RecursiveC78

import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExpandChildLabelFactsProof
set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Short step facts at the exact base

Discharges three `ExactSeams` step fields outright by replaying the plain
proofs over the exact pipeline `layoutX`:

* `stepC6Anchors_layoutX` (field `stepC6Anchors`),
* `stepC8aAncestry_layoutX` (field `stepC8aAncestry`),
* `stepC8aGeometry_layoutX` (field `stepC8aGeometry`).

`expandChild` is base independent; only the two recursive successes in
`ExpandChildCallContextB` mention the base.  The geometry fact closes with
no residual: the child inset comes from the `layoutRecursiveB_inset` lift
over the closed flat inset, and the frame reservation from `xExactFixedMin`
through the exact flat C5 ids.
-/

/-- The exact flat inset as a `FlatInsetB` fact: replay of the `flatInset`
lambda in `exactBaseSeams` (`UsecaseValidExact.lean`) through
`exactPartsBounded'` conjunct 1, which holds with no hypothesis. -/
private theorem ESS_flatInset (exactIds : List String) :
    FlatInsetB (layoutX exactIds) := by
  intro inp o res h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hacc := SceneExecutionX.packedAcc_bounded execution
    (exactPartsBounded' execution)
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc (by omega)

/-- Frame reservation of an executed exact `expandChild` call: the located
group frame dominates the `childFrameSize` for the inner title lines.
B-twin of `expandChild_frame_size_bounds`, with the flat C5 ids
(`flatC5B_layoutX_closed`) in place of the `layoutRecursive_ids` induction
and `xExactFixedMin` in place of the plain fixed-source minimum. -/
private theorem ESS_frame_size_bounds (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (frame : Box) (titleLines' : List Measure.Line)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hwrap' : ExpandChildTitleWrapped P inp o group titleLines') :
    (childFrameSize group.direction P.clusterPad
      (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w ∧
    (childFrameSize group.direction P.clusterPad
      (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
  obtain ⟨hP, hheightEq, hwrapCtx⟩ := hparams
  obtain ⟨metric, hmetric, hwrapEq⟩ := hwrapCtx
  obtain ⟨metric', hmetric', hwrapEq'⟩ := hwrap'
  have hmetricEq : metric' = metric := Except.ok.inj (hmetric'.symm.trans hmetric)
  subst hmetricEq
  have htlEq : titleLines' = titleLines := Except.ok.inj (hwrapEq'.symm.trans hwrapEq)
  subst titleLines'
  obtain ⟨hwf, hgroup, hpboxes, hchild, hparent, _hexpand'⟩ := hctxB
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P metric'
    titleLines child parent hwf _hframed hP hmetric hwrapEq hchild hparent
  have hparentC5 := layoutRecursiveB_c5_facts (flatC5B_layoutX_closed exactIds)
    (subInputWellFormedB_layoutX exactIds) fuel hsub.2.2.1 hsub.2.2.2 hparent
  have hparentOutputIds : parent.scene.boxes.map (·.id) =
      (parentSubInput inp group P titleLines child).boxes.map (·.id) :=
    hparentC5.1
  have hparentIds : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hboxIds
  have hparentCovered : RoutesCovered (parentSubInput inp group P titleLines child) := by
    change RoutesCovered
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id))
    exact selectInput_routesCovered inp _ ""
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hparentSourceId : group.id ∈
      (parentSubInput inp group P titleLines child).boxes.map (·.id) := by
    rw [← hparentOutputIds, ← hframeId]
    exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
  obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
  have hsourceBase : source ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := by
    rw [← hpboxes]
    exact hsource
  obtain ⟨original, horiginal, _, hsourceEq⟩ :=
    selectInput_box_source inp (fun box => !Compound.inside inp.boxes group.id box.id)
      "" source hsourceBase
  have hsourceOriginalId : source.id = original.id := by
    rw [hsourceEq]
    split <;> rfl
  have horiginalId : original.id = group.id := hsourceOriginalId.symm.trans hsourceId
  have horiginalLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds original horiginal
  have hgroupLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds
    group (List.mem_of_find?_eq_some hgroup)
  rw [horiginalId] at horiginalLookup
  have horiginalEq : original = group :=
    Option.some.inj (horiginalLookup.symm.trans hgroupLookup)
  have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
  let size := childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩
  have hfixed : (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size) := by
    change (inp.fixedSizes ++ [(group.id, size)]).find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size)
    simp [List.find?_append, hsourceId, hnone]
  obtain ⟨actual, hactual, _, hw, hh⟩ :=
    (xExactFixedMin exactIds) fuel _ _ _ _ _ hparentIds hparentCovered hparent
      hsource hfixed
  rw [hsourceId] at hactual
  have hactualEq : actual = frame := Option.some.inj (hactual.symm.trans hframe)
  subst actual
  have hw' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := by
    have hw'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := hw
    rw [← hheightEq] at hw''
    exact hw''
  have hh' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
    have hh'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := hh
    rw [← hheightEq] at hh''
    exact hh''
  exact ⟨hw', hh'⟩

/-- Strict content fit of an executed exact `expandChild` call: every rect
inside the child canvas shrunk by `P.canvasMargin` lands strictly inside the
group frame. B-twin of `expandChild_content_fit_strict`. -/
private theorem ESS_content_fit_strict (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ (r : Rect),
    (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained r →
    frame.rect.StrictInside (shiftRect dx dy r) := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap' r hr
  obtain ⟨hw, hh⟩ := ESS_frame_size_bounds exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams frame titleLines'
    hframe hwrap'
  obtain ⟨hP, hheightEq, _hwrapCtx⟩ := hparams
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  have htw : 0 ≤ titleLines'.foldl (fun width line => max width line.width) 0 := by
    suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
        0 ≤ ls.foldl (fun width line => max width line.width) acc by
      exact key titleLines' 0 (by omega)
    intro ls acc hac
    induction ls generalizing acc with
    | nil => simpa using hac
    | cons line ls ih =>
      simp only [List.foldl_cons]
      exact ih _ (Int.le_trans hac (Int.le_max_left _ _))
  have hth : 0 ≤ titleHeight := by
    rw [hheightEq]
    exact Int.mul_nonneg (by omega)
      (Int.le_of_lt (callParams_lineH_pos hP))
  have hS : frame.rect.StrictInside
      (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩) := by
    rw [hdx, hdy]
    exact childInsetContent_strict hpad htw hth hw hh
  have hshift : (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin,
      child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩).Contained (shiftRect dx dy r) :=
    (contained_shiftRect dx dy).mpr hr
  unfold Rect.StrictInside at hS ⊢
  unfold Rect.Contained at hshift
  omega

/-- Child boxes of an executed exact `expandChild` lie in the margin inset of
the child canvas. B-twin of `expandChild_child_boxes_inset`, via the
`layoutRecursiveB_inset` lift over the closed flat inset and fit. -/
private theorem ESS_child_boxes_insetB (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect := by
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, hparent, _hexpand'⟩ := hctxB
  obtain ⟨hP, _hheightEq, hwrapCtx⟩ := hparams
  obtain ⟨metric, hmetric, hwrapEq⟩ := hwrapCtx
  have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P metric
    titleLines child parent hwf hframed hP hmetric hwrapEq hchild hparent
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hinset := layoutRecursiveB_inset (layoutX exactIds)
    (ESS_flatInset exactIds) subInputWellFormedC2 (exactFitClosed exactIds)
    fuel _ _ _ hsub.1 hsub.2.1 hchild P hQchild
  exact hinset.2

/-- The `stepC8aGeometry` seam field holds for every exact `expandChild`
call: composition of the strict frame reservation and the child inset
through `stepC8aGeometry_holdsB`, with both base facts closed above. -/
theorem stepC8aGeometry_layoutX (exactIds : List String) :
    RecursiveStepFactsB (layoutX exactIds) ExpandChildC8aGeometry :=
  stepC8aGeometry_holdsB (layoutX exactIds)
    (ESS_content_fit_strict exactIds) (ESS_child_boxes_insetB exactIds)

/-!
## Short-step ancestor-walk toolkit

Prefixed copies of the private walk and list utilities from
`ExpandChildAncestryProof.lean` (the `go_*` steps, fuel monotonicity,
step-chain transport, box lookup, `removeFirst` nodup-length block,
empty-id facts, and filter lengths).  Proofs copy verbatim; only the names
carry the `ESS_` prefix.
-/

/-- One unfolded step of the ancestor walk. -/
private theorem ESS_go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty. -/
private theorem ESS_go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty. -/
private theorem ESS_go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- Fuel monotonicity of the ancestor walk. -/
private theorem ESS_ancestors_go_mono {d : LayoutDump} {k k' : Nat} (hle : k ≤ k')
    {s x : String} (hm : x ∈ LayoutDump.ancestors.go d k s) :
    x ∈ LayoutDump.ancestors.go d k' s := by
  induction k' generalizing k s x with
  | zero =>
    have hk : k = 0 := Nat.le_zero.mp hle
    subst hk
    cases hm
  | succ k' ih =>
    cases k with
    | zero => cases hm
    | succ k =>
      have hkk : k ≤ k' := Nat.le_of_succ_le_succ hle
      cases h : d.box? s with
      | none =>
        have e1 := ESS_go_none (d := d) (k := k) (s := s) h
        rw [e1] at hm
        cases hm
      | some b =>
        by_cases hp : b.parent = ""
        · have e1 := ESS_go_root (d := d) (k := k) (s := s) (b := b) h hp
          rw [e1] at hm
          cases hm
        · have e1 := ESS_go_succ (d := d) (k := k) (s := s) (b := b) h hp
          have e2 := ESS_go_succ (d := d) (k := k') (s := s) (b := b) h hp
          rw [e1] at hm
          rw [e2]
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons_of_mem _ (ih hkk hm')

/-- Every tail member of a step chain lies on the ancestor walk from its
head, with fuel one less than the chain length. -/
private theorem ESS_mem_of_stepChain {d : LayoutDump} (c : List String)
    (hchain : StepChain
      (fun s t => ∃ b, d.box? s = some b ∧ b.parent = t ∧ t ≠ "") c)
    (s x : String) (hhead : c.head? = some s) (htail : x ∈ c.tail) :
    x ∈ LayoutDump.ancestors.go d (c.length - 1) s := by
  induction hchain generalizing s x with
  | nil => simp at hhead
  | single a => simp at htail
  | cons hab htailChain ih =>
    rename_i a b rest
    have hs : a = s := by simpa using hhead
    subst hs
    have hlen : (a :: b :: rest).length - 1 = rest.length + 1 := by simp
    rw [hlen]
    obtain ⟨box, hbox, hpar, hne⟩ := hab
    have hne' : box.parent ≠ "" := by rw [hpar]; exact hne
    have hgo := ESS_go_succ (d := d) (k := rest.length) (s := a) (b := box) hbox hne'
    rw [hpar] at hgo
    rw [hgo]
    have htail' : x ∈ b :: rest := htail
    rcases List.mem_cons.mp htail' with rfl | hmem
    · exact List.mem_cons.mpr (Or.inl rfl)
    · have hmem' : x ∈ (b :: rest).tail := hmem
      have hhead' : (b :: rest).head? = some b := by simp
      have hmemgo := ih b x hhead' hmem'
      have hlen2 : (b :: rest).length - 1 = rest.length := by simp
      rw [hlen2] at hmemgo
      exact List.mem_cons_of_mem _ hmemgo

/-- Membership in the ancestor walk exhibits a step chain from the start to
the member, of length at most the fuel plus one. -/
private theorem ESS_go_chain_of_mem {d : LayoutDump} : ∀ (K : Nat) (s x : String),
    x ∈ LayoutDump.ancestors.go d K s →
    ∃ c, StepChain (fun s t => ∃ b, d.box? s = some b ∧ b.parent = t ∧ t ≠ "") c ∧
      c.head? = some s ∧ c.getLast? = some x ∧ c.length ≤ K + 1
  | 0, s, x, hx => by
    simp only [LayoutDump.ancestors.go] at hx
    cases hx
  | K + 1, s, x, hx => by
    cases h : d.box? s with
    | none =>
      have hfind : d.boxes.find? (fun b => b.id == s) = none := h
      simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind] at hx
      cases hx
    | some b =>
      have hfind : d.boxes.find? (fun b => b.id == s) = some b := h
      by_cases hpar : b.parent = ""
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar,
          ↓reduceIte] at hx
        cases hx
      · have hgo := ESS_go_succ (d := d) (k := K) (s := s) (b := b) h hpar
        rw [hgo] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · refine ⟨[s, b.parent],
            StepChain.cons ⟨b, h, rfl, hpar⟩ (StepChain.single _),
            by simp, by simp, ?_⟩
          simp only [List.length_cons, List.length_nil]
          omega
        · obtain ⟨c', hchain', hhead', hlast', hlen'⟩ := ESS_go_chain_of_mem K b.parent x hx'
          obtain ⟨p', rest', hcsplit⟩ : ∃ p' rest', c' = p' :: rest' := by
            cases c' with
            | nil => simp at hhead'
            | cons p' rest' => exact ⟨p', rest', rfl⟩
          subst hcsplit
          have hpeq : p' = b.parent := by simpa using hhead'
          subst hpeq
          refine ⟨s :: b.parent :: rest', StepChain.cons ⟨b, h, rfl, hpar⟩ hchain',
            by simp, ?_, ?_⟩
          · have hgg : ((s :: b.parent :: rest').getLast? =
              (b.parent :: rest').getLast?) := rfl
            rw [hgg]
            exact hlast'
          · simp only [List.length_cons] at hlen' ⊢
            omega

/-- Concatenating two step chains at their shared endpoint value. -/
private theorem ESS_stepChain_concat {R : String → String → Prop} :
    ∀ (l₁ l₂ : List String) (j : String),
    StepChain R l₁ → StepChain R l₂ → l₁.getLast? = some j → l₂.head? = some j →
    ∃ l, StepChain R l ∧ l.head? = l₁.head? ∧ l.getLast? = l₂.getLast? ∧
      l.length + 1 = l₁.length + l₂.length
  | [], l₂, j, _, hchain₂, hlast₁, _ => by
    simp at hlast₁
  | [a], l₂, j, _, hchain₂, hlast₁, hlast₂ => by
    have hj : a = j := by simpa using hlast₁
    subst hj
    cases l₂ with
    | nil => simp at hlast₂
    | cons b rest =>
      have hb : b = a := by simpa using hlast₂
      subst hb
      exact ⟨b :: rest, hchain₂, rfl, rfl, by simp; omega⟩
  | a :: b :: rest, l₂, j, hchain₁, hchain₂, hlast₁, hlast₂ => by
    cases hchain₁ with
    | cons hab htailChain =>
      have hlast₁' : (b :: rest).getLast? = some j := hlast₁
      obtain ⟨l', hl'chain, hl'head, hl'last, hl'len⟩ :=
        ESS_stepChain_concat (b :: rest) l₂ j htailChain hchain₂ hlast₁' hlast₂
      obtain ⟨b', rest'', hsplit⟩ : ∃ b' rest'', l' = b' :: rest'' := by
        cases l' with
        | nil => simp at hl'head
        | cons b' rest'' => exact ⟨b', rest'', rfl⟩
      subst hsplit
      have hb'eq : b = b' := by
        have h : b' = b := by simpa using hl'head
        exact h.symm
      subst hb'eq
      refine ⟨a :: b :: rest'', StepChain.cons hab hl'chain, rfl, ?_, ?_⟩
      · have hgg : ((a :: b :: rest'').getLast? = (b :: rest'').getLast?) := rfl
        rw [hgg]
        exact hl'last
      · simp only [List.length_cons] at hl'len ⊢
        omega

private theorem ESS_box_id_of_box_some {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : b.id = s := by
  simp only [LayoutDump.box?] at h
  have hpred := List.find?_some h
  have htrue : (b.id == s) = true := hpred
  exact beq_iff_eq.mp htrue

private theorem ESS_parent_chain_lift_of_trans
    {parent res : FamilyResult}
    (htransP : ∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
      res.scene.layoutDump.box? b.id = some b)
    {c : List String}
    (hchain : StepChain (fun s t => ∃ b,
      parent.scene.layoutDump.box? s = some b ∧ b.parent = t ∧ t ≠ "") c) :
    StepChain (fun s t => ∃ b,
      res.scene.layoutDump.box? s = some b ∧ b.parent = t ∧ t ≠ "") c := by
  induction hchain with
  | nil => exact StepChain.nil
  | single a => exact StepChain.single a
  | cons hab htail ih =>
    obtain ⟨bx, hb, hpar, hne⟩ := hab
    have hbid := ESS_box_id_of_box_some hb
    have hb' := hbid.symm ▸ hb
    have htrans := htransP bx hb'
    have htransA := hbid ▸ htrans
    exact StepChain.cons ⟨bx, htransA, hpar, hne⟩ ih

/-- Membership from a successful `getLast?` lookup. -/
private theorem ESS_mem_of_getLast? (l : List String) (x : String)
    (h : l.getLast? = some x) : x ∈ l := by
  cases hl : l with
  | nil => simp [hl] at h
  | cons a t =>
    cases ht : t with
    | nil =>
      have hax : a = x := by simpa [hl, ht] using h
      subst hax
      exact List.mem_cons.mpr (Or.inl rfl)
    | cons b t2 =>
      have hT : (a :: b :: t2).getLast? = some x := by
        rw [← ht, ← hl]
        exact h
      have h' : (b :: t2).getLast? = some x := hT
      exact List.mem_cons.mpr (Or.inr (ESS_mem_of_getLast? _ _ h'))

/-- A step chain whose ends differ has length at least two. -/
private theorem ESS_chain_length_ge_two {c : List String} {s x : String}
    (hhead : c.head? = some s) (hlast : c.getLast? = some x) (hne : s ≠ x) :
    2 ≤ c.length := by
  cases hc : c with
  | nil => simp [hc] at hhead
  | cons a t =>
    cases ht : t with
    | nil =>
      have ha : a = s := by simpa [hc] using hhead
      have hax : a = x := by simpa [hc, ht] using hlast
      exact absurd (ha.symm.trans hax) hne
    | cons b t2 =>
      simp only [List.length_cons]
      omega

/-- A list whose head lookup succeeds is nonempty. -/
private theorem ESS_length_ge_one_of_head? {l : List String} {s : String}
    (h : l.head? = some s) : 1 ≤ l.length := by
  cases hl : l with
  | nil => simp [hl] at h
  | cons a t =>
    simp only [List.length_cons]
    omega

/-- The last element of a length-two-or-more list lies in its tail. -/
private theorem ESS_last_mem_tail {l : List String} {x : String}
    (hlast : l.getLast? = some x) (h2 : 2 ≤ l.length) : x ∈ l.tail := by
  cases hl : l with
  | nil => simp [hl] at hlast
  | cons a t =>
    show x ∈ t
    have hlastT : (a :: t).getLast? = some x := hl ▸ hlast
    cases ht : t with
    | nil => simp [hl, ht] at h2
    | cons b t2 =>
      have hlastB : (a :: b :: t2).getLast? = some x := ht ▸ hlastT
      have hlast'' : (b :: t2).getLast? = some x := hlastB
      exact ESS_mem_of_getLast? _ _ hlast''

/-- The last link of a step chain whose ends differ ends at the last element. -/
private theorem ESS_stepChain_last_link {R : String → String → Prop}
    {c : List String} {s x : String}
    (hchain : StepChain R c) (hhead : c.head? = some s)
    (hlast : c.getLast? = some x) (hne : s ≠ x) :
    ∃ y, R y x ∧ y ∈ c := by
  induction hchain generalizing s x with
  | nil => simp at hhead
  | single a =>
    have hs : a = s := by simpa using hhead
    have hx : a = x := by simpa using hlast
    exact absurd (hs.symm.trans hx) hne
  | cons hab htail ih =>
    rename_i a b rest
    have hlast' : (b :: rest).getLast? = some x := hlast
    by_cases hbx : b = x
    · exact ⟨a, hbx ▸ hab, List.mem_cons.mpr (Or.inl rfl)⟩
    · obtain ⟨y, hry, hym⟩ := ih (by simp) hlast' hbx
      exact ⟨y, hry, List.mem_cons.mpr (Or.inr hym)⟩

/-- A member of a box-id list resolves through `box?`, exposing the box. -/
private theorem ESS_box_of_mem_ids {l : List Box} {s : String}
    (hmem : s ∈ l.map (·.id)) :
    ∃ b, b ∈ l ∧ l.find? (fun b => b.id == s) = some b ∧ b.id = s := by
  match hfind : l.find? (fun b => b.id == s) with
  | none =>
    exfalso
    obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hmem
    have hfalse := List.find?_eq_none.mp hfind b hb
    simp [hbid] at hfalse
  | some b =>
    refine ⟨b, List.mem_of_find?_eq_some hfind, hfind, ?_⟩
    have hpred := List.find?_some hfind
    simpa using hpred

/-- With nodup ids, `find?` at a member box returns that box. -/
private theorem ESS_find?_of_mem_nodup {l : List Box} {b : Box}
    (hnd : (l.map (·.id)).Nodup) (hmem : b ∈ l) :
    l.find? (fun b' => b'.id == b.id) = some b := by
  match hfind : l.find? (fun b' => b'.id == b.id) with
  | none =>
    exfalso
    have hfalse := List.find?_eq_none.mp hfind b hmem
    simp at hfalse
  | some b' =>
    have hb'mem := List.mem_of_find?_eq_some hfind
    have hid : b'.id = b.id := by
      have hpred := List.find?_some hfind
      simpa using hpred
    have heq : b' = b := expandChild_nodup_map_inj (·.id) hnd hb'mem hmem hid
    rw [heq] at hfind
    exact hfind

/-- Remove the first occurrence of an id. -/
private def ESS_removeFirst (a : String) : List String → List String
  | [] => []
  | b :: rest => if b = a then rest else b :: ESS_removeFirst a rest

private theorem ESS_removeFirst_mem : ∀ (l : List String) (a x : String),
    x ∈ ESS_removeFirst a l → x ∈ l
  | [], _, _, h => by cases h
  | b :: rest, a, x, h => by
    simp only [ESS_removeFirst] at h
    by_cases heq : b = a
    · simp only [heq, ↓reduceIte] at h
      exact List.mem_cons.mpr (Or.inr h)
    · simp only [heq, ↓reduceIte] at h
      rcases List.mem_cons.mp h with rfl | hmem
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ESS_removeFirst_mem rest a x hmem))

private theorem ESS_removeFirst_mem_of_ne : ∀ (l : List String) (a x : String),
    x ≠ a → x ∈ l → x ∈ ESS_removeFirst a l
  | [], _, _, _, h => by cases h
  | b :: rest, a, x, hne, hmem => by
    simp only [ESS_removeFirst]
    by_cases heq : b = a
    · subst heq
      simp only [↓reduceIte]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact absurd rfl hne
      · exact hmem'
    · simp only [heq, ↓reduceIte]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ESS_removeFirst_mem_of_ne rest a x hne hmem'))

private theorem ESS_removeFirst_nodup : ∀ (l : List String) (a : String),
    l.Nodup → (ESS_removeFirst a l).Nodup
  | [], _, _ => List.nodup_nil
  | b :: rest, a, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [ESS_removeFirst]
    by_cases heq : b = a
    · subst heq
      simp only [↓reduceIte]
      exact hnd.2
    · simp only [heq, ↓reduceIte]
      rw [List.nodup_cons]
      refine ⟨?_, ESS_removeFirst_nodup rest a hnd.2⟩
      intro hmem
      exact hnd.1 (ESS_removeFirst_mem rest a b hmem)

private theorem ESS_removeFirst_length : ∀ (l : List String) (a : String),
    a ∈ l → (ESS_removeFirst a l).length + 1 = l.length
  | b :: rest, a, hmem => by
    simp only [ESS_removeFirst]
    by_cases heq : b = a
    · subst heq
      simp only [↓reduceIte, List.length_cons]
    · simp only [heq, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact absurd rfl heq
      · have ih := ESS_removeFirst_length rest a hmem'
        omega

/-- A nodup list covering another nodup list is at least as long. -/
private theorem ESS_nodup_length_le_string : ∀ (l₁ l₂ : List String),
    l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₂.Nodup → l₁.length ≤ l₂.length
  | [], _, _, _, _ => Nat.zero_le _
  | a :: rest, l₂, hnd1, hsub, hnd2 => by
    rw [List.nodup_cons] at hnd1
    have ha : a ∈ l₂ := hsub a (List.mem_cons.mpr (Or.inl rfl))
    have h1 : rest.length ≤ (ESS_removeFirst a l₂).length := by
      apply ESS_nodup_length_le_string rest (ESS_removeFirst a l₂) hnd1.2 _ (ESS_removeFirst_nodup l₂ a hnd2)
      intro x hx
      have hx2 := hsub x (List.mem_cons.mpr (Or.inr hx))
      have hxa : x ≠ a := fun heq => hnd1.1 (heq ▸ hx)
      exact ESS_removeFirst_mem_of_ne l₂ a x hxa hx2
    have h2 : (ESS_removeFirst a l₂).length + 1 = l₂.length :=
      ESS_removeFirst_length l₂ a ha
    simp only [List.length_cons]
    omega

/-- Membership in a list splits it around the member. -/
private theorem ESS_mem_split : ∀ (l : List String) (a : String), a ∈ l →
    ∃ pre suf, l = pre ++ a :: suf
  | b :: rest, a, hmem => by
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact ⟨[], rest, rfl⟩
    · obtain ⟨pre, suf, hsplit⟩ := ESS_mem_split rest a hmem'
      exact ⟨b :: pre, suf, by simp [hsplit]⟩

/-- A non-nodup list repeats some element with everything between. -/
private theorem ESS_nodup_split_repeat : ∀ (l : List String), ¬ l.Nodup →
    ∃ pre x mid suf, l = pre ++ x :: mid ++ x :: suf
  | [], h => absurd List.nodup_nil h
  | a :: rest, h => by
    rw [List.nodup_cons] at h
    have hcases : a ∈ rest ∨ ¬ rest.Nodup := by
      by_cases ha : a ∈ rest
      · exact Or.inl ha
      · exact Or.inr (fun hnd => h ⟨ha, hnd⟩)
    rcases hcases with hmem | hrest
    · obtain ⟨pre, suf, hsplit⟩ := ESS_mem_split rest a hmem
      exact ⟨[], a, pre, suf, by simp [hsplit]⟩
    · obtain ⟨pre, x, mid, suf, hsplit⟩ := ESS_nodup_split_repeat rest hrest
      exact ⟨a :: pre, x, mid, suf, by simp [hsplit]⟩

/-- Membership in a list has an index. -/
private theorem ESS_mem_index : ∀ (l : List String) (a : String), a ∈ l →
    ∃ n, n < l.length ∧ l[n]? = some a
  | [], _, h => by cases h
  | b :: rest, a, h => by
    rcases List.mem_cons.mp h with rfl | hmem
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨n, hlt, hget⟩ := ESS_mem_index rest a hmem
      exact ⟨n + 1, by simpa using Nat.succ_lt_succ hlt, by simpa using hget⟩

/-- The index of the `""` walk result never appears. -/
private theorem ESS_empty_not_mem_ancestors_go {d : LayoutDump} (k : Nat) (s : String) :
    "" ∉ LayoutDump.ancestors.go d k s := by
  revert s
  induction k with
  | zero =>
    intro s hmem
    cases hmem
  | succ k ih =>
    intro s hmem
    simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hmem
    match h : d.boxes.find? (fun b => b.id == s) with
    | none =>
      simp only [h] at hmem
      cases hmem
    | some b =>
      simp only [h] at hmem
      by_cases hp : b.parent = ""
      · simp only [hp, ↓reduceIte] at hmem
        cases hmem
      · simp only [hp, ↓reduceIte, List.mem_cons] at hmem
        have hne : ("" : String) ≠ b.parent := Ne.symm hp
        have hmem' : "" ∈ LayoutDump.ancestors.go d k b.parent := by
          rcases hmem with hcontra | hrest
          · exact absurd hcontra hne
          · exact hrest
        exact ih _ hmem'

private theorem ESS_empty_not_mem_ancestors {d : LayoutDump} (s : String) :
    "" ∉ d.ancestors s := by
  unfold LayoutDump.ancestors
  exact ESS_empty_not_mem_ancestors_go d.boxes.length s

/-- The index of the `""`-id box never occurs in a `Compound.ancestors`
walk. -/
private theorem ESS_compound_ancestors_ne_gidx {boxes : List ModelBox}
    {gidx : Nat} (hg : boxes.findIdx? (fun b => b.id == "") = some gidx)
    (n : Nat) (id : String) :
    gidx ∉ Compound.ancestors boxes n id := by
  revert id
  induction n with
  | zero =>
    intro id hmem
    simp only [Compound.ancestors] at hmem
    exact absurd hmem (by simp)
  | succ n ih =>
    intro id hmem
    by_cases hid : id = ""
    · subst hid
      have h2 : Compound.ancestors boxes (n + 1) "" = [] :=
        Compound.ancestors.eq_2 _ _
      rw [h2] at hmem
      cases hmem
    · have h3 : Compound.ancestors boxes (n + 1) id =
          match boxes.findIdx? (fun box => box.id == id) with
          | none => []
          | some index =>
            match boxes[index]? with
            | none => []
            | some box => Compound.ancestors boxes n box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes id n hid
      rw [h3] at hmem
      match hf : boxes.findIdx? (fun box => box.id == id) with
      | none =>
        simp only [hf] at hmem
        exact absurd hmem (by simp)
      | some j =>
        simp only [hf] at hmem
        match hb : boxes[j]? with
        | none =>
          simp only [hb] at hmem
          exact absurd hmem (by simp)
        | some bj =>
          simp only [hb, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · exact ih _ hmem
          · obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            obtain ⟨_, hgid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hg
            subst hmem
            have hjj : boxes[gidx].id = id := beq_iff_eq.mp hjid
            have hgj : boxes[gidx].id = "" := beq_iff_eq.mp hgid
            rw [hgj] at hjj
            exact hid hjj.symm

/-- No box is inside a group whose id is `""`. -/
private theorem ESS_inside_empty_id {boxes : List ModelBox} (x : String) :
    Compound.inside boxes "" x = false := by
  unfold Compound.inside
  match hfind : boxes.find? (fun box => box.id == x) with
  | none =>
    simp only [hfind]
  | some box =>
    simp only [hfind]
    match hgidx : boxes.findIdx? (fun box => box.id == "") with
    | none =>
      simp only [hgidx]
    | some gidx =>
      simp only [hgidx]
      have hnot : gidx ∉ Compound.ancestors boxes boxes.length box.parent :=
        ESS_compound_ancestors_ne_gidx hgidx _ _
      cases hc : (Compound.path boxes box).contains gidx with
      | false => rfl
      | true =>
        simp only [List.contains_iff_mem] at hc
        exact absurd hc hnot

/-- Merging two filtered halves cannot lengthen the merged box list. -/
private theorem ESS_filter_not_length_sum {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !(p x))).length = l.length := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    by_cases h : p b = true
    · have h1 : ((b :: rest).filter p) = b :: rest.filter p := by simp [h]
      have h2 : ((b :: rest).filter (fun x => !(p x))) =
          rest.filter (fun x => !(p x)) := by simp [h]
      rw [h1, h2]
      simp only [List.length_cons]
      omega
    · have hpb : p b = false := by cases hb : p b <;> simp_all
      have h1 : ((b :: rest).filter p) = rest.filter p := by simp [hpb]
      have h2 : ((b :: rest).filter (fun x => !(p x))) =
          b :: rest.filter (fun x => !(p x)) := by simp [hpb]
      rw [h1, h2]
      simp only [List.length_cons]
      omega

private theorem ESS_filterMap_length_of_all_some {α β : Type} (l : List α)
    (f : α → Option β) (h : ∀ x ∈ l, ∃ y, f x = some y) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨y, hy⟩ := h b (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ x ∈ rest, ∃ y, f x = some y := fun x hx =>
      h x (List.mem_cons.mpr (Or.inr hx))
    have ih' := ih hrest
    simp only [List.filterMap_cons] at ⊢
    rw [hy]
    simp only [List.length_cons, ih']

private theorem ESS_filterMap_map_id_eq {α β : Type} (l : List α)
    (f : α → Option β) (key : β → String) (idOf : α → String)
    (h : ∀ x ∈ l, ∃ y, f x = some y ∧ key y = idOf x) :
    (l.filterMap f).map key = l.map idOf := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨y, hy, hkey⟩ := h b (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ x ∈ rest, ∃ y, f x = some y ∧ key y = idOf x := fun x hx =>
      h x (List.mem_cons.mpr (Or.inr hx))
    have ih' := ih hrest
    simp only [List.filterMap_cons, hy, List.map_cons]
    rw [hkey, ih']
/-!
## Short-step model parent walk

Prefixed copies of the private `rootChain` machinery from
`ExpandChildAncestryProof.lean`: the model-level walk toward the expanded
group and its termination, link, and last-link properties.
-/

private def ESS_rootChain (boxes : List ModelBox) (groupId : String) : Nat → String → Option (List ModelBox)
  | 0, _ => none
  | n + 1, id =>
    match boxes.findIdx? (fun b => b.id == id) with
    | none => none
    | some i =>
      match boxes[i]? with
      | none => none
      | some b =>
        if b.parent == groupId then some [b]
        else match ESS_rootChain boxes groupId n b.parent with
          | none => none
          | some pre => some (b :: pre)

/-- Unfolding equation for `ESS_rootChain` at positive fuel. -/
private theorem ESS_rootChain_succ {boxes : List ModelBox} {groupId : String} {n : Nat} {id : String} :
    ESS_rootChain boxes groupId (n + 1) id =
      match boxes.findIdx? (fun b => b.id == id) with
      | none => none
      | some i =>
        match boxes[i]? with
        | none => none
        | some b =>
          if b.parent == groupId then some [b]
          else match ESS_rootChain boxes groupId n b.parent with
            | none => none
            | some pre => some (b :: pre) := by
  rfl

/-- A `Bool` disequality testifies inequality. -/
private theorem ESS_ne_of_beq_false {a b : String} (h : (a == b) = false) : a ≠ b := by
  intro heq
  rw [heq, beq_self_eq_true] at h
  exact Bool.noConfusion h

/-- A successful `ESS_rootChain` run returns a nonempty list. -/
private theorem ESS_rootChain_ne_nil {boxes : List ModelBox} {groupId : String} {n : Nat} {s : String}
    {pre : List ModelBox} (h : ESS_rootChain boxes groupId n s = some pre) : pre ≠ [] := by
  induction n generalizing s pre with
  | zero => simp only [ESS_rootChain] at h; cases h
  | succ n ih =>
    rw [ESS_rootChain_succ] at h
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at h; cases h
    | some i =>
      simp only [hf] at h
      cases hg : boxes[i]? with
      | none => simp only [hg] at h; cases h
      | some b =>
        simp only [hg] at h
        by_cases hc : b.parent == groupId
        · simp only [hc] at h
          obtain rfl := Option.some.inj h
          exact by simp
        · simp only [hc] at h
          cases hr : ESS_rootChain boxes groupId n b.parent with
          | none => simp only [hr] at h; cases h
          | some pre' =>
            simp only [hr] at h
            obtain rfl := Option.some.inj h
            exact by simp

/-- The head of a successful `ESS_rootChain` run is the box with the start id. -/
private theorem ESS_rootChain_head {boxes : List ModelBox} {groupId : String} {n : Nat} {s : String}
    {pre : List ModelBox} (h : ESS_rootChain boxes groupId n s = some pre) :
    ∃ b₀ rest, pre = b₀ :: rest ∧ b₀.id = s := by
  induction n generalizing s pre with
  | zero => simp only [ESS_rootChain] at h; cases h
  | succ n _ =>
    rw [ESS_rootChain_succ] at h
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at h; cases h
    | some i =>
      simp only [hf] at h
      cases hg : boxes[i]? with
      | none => simp only [hg] at h; cases h
      | some b =>
        simp only [hg] at h
        have hid : b.id = s := by
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have hget : boxes[i]? = some boxes[i] := List.getElem?_eq_getElem hlt
          have hb : b = boxes[i] := (Option.some.inj (hget.symm.trans hg)).symm
          have hbeq : (boxes[i].id == s) = true := hmatch
          rw [hb]
          exact beq_iff_eq.mp hbeq
        by_cases hc : b.parent == groupId
        · simp only [hc] at h
          obtain rfl := Option.some.inj h
          exact ⟨b, [], rfl, hid⟩
        · simp only [hc] at h
          cases hr : ESS_rootChain boxes groupId n b.parent with
          | none => simp only [hr] at h; cases h
          | some pre' =>
            simp only [hr] at h
            obtain rfl := Option.some.inj h
            exact ⟨b, pre', rfl, hid⟩

/-- Mapped ids keep nodup when the source boxes have unique ids. -/
private theorem ESS_nodup_map_id {boxes : List ModelBox} {l : List ModelBox}
    (hnodup : (boxes.map (·.id)).Nodup)
    (hmem : ∀ b ∈ l, b ∈ boxes) (hnd : l.Nodup) : (l.map (·.id)).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun b hb => hmem b (List.mem_cons.mpr (Or.inr hb))) (List.nodup_cons.mp hnd).2⟩
    intro hmemA
    obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hmemA
    have hab : a = b :=
      expandChild_nodup_map_inj (·.id) hnodup (hmem _ (List.mem_cons.mpr (Or.inl rfl)))
        (hmem _ (List.mem_cons.mpr (Or.inr hb))) hbid.symm
    exact (List.nodup_cons.mp hnd).1 (hab ▸ hb)

/-- A `Bool` disequality hypothesis yields the corresponding inequality. -/
private theorem ESS_ne_of_nbeq_true {a b : String} (h : ¬((a == b) = true)) : a ≠ b := by
  intro heq
  rw [heq, beq_self_eq_true] at h
  exact absurd rfl h

/-- Head injectivity for cons. -/
private theorem ESS_cons_head_eq {α : Type} {a₁ a₂ : α} {l₁ l₂ : List α} (h : a₁ :: l₁ = a₂ :: l₂) :
    a₁ = a₂ := by
  have h1 := congrArg List.head? h
  simp only [List.head?_cons] at h1
  exact Option.some.inj h1

/-- Tail injectivity for cons. -/
private theorem ESS_cons_tail_eq {α : Type} {a₁ a₂ : α} {l₁ l₂ : List α} (h : a₁ :: l₁ = a₂ :: l₂) :
    l₁ = l₂ := by
  have h1 := congrArg List.tail h
  simp only [List.tail_cons] at h1
  exact h1

/-- The walk toward the group never gets stuck when the model walk
terminates. -/
private theorem ESS_rootChain_some {boxes : List ModelBox} {gid : String}
    (hterm : ∀ b ∈ boxes, ∀ n, boxes.length ≤ n + 1 → chainTerm boxes n b.parent = true)
    (hnodup : (boxes.map (·.id)).Nodup)
    {n : Nat} {s : String}
    (hct : chainTerm boxes n s = true) (hne : s ≠ "")
    (hev : ∀ b ∈ boxes, b.id = s → Compound.inside boxes gid b.id = true) :
    ∃ pre, ESS_rootChain boxes gid n s = some pre := by
  induction n generalizing s with
  | zero =>
    rw [chainTerm.eq_2 boxes s hne] at hct
    simp at hct
  | succ n ih =>
    rw [chainTerm.eq_3 boxes s n hne] at hct
    rw [ESS_rootChain_succ]
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at hct; simp at hct
    | some i =>
      simp only [hf] at hct
      cases hg : boxes[i]? with
      | none => simp only [hg] at hct; simp at hct
      | some b =>
        simp only [hg] at hct
        have hbid : b.id = s := by
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have hget : boxes[i]? = some (boxes.get ⟨i, hlt⟩) := List.getElem?_eq_getElem hlt
          have hb : b = boxes.get ⟨i, hlt⟩ := (Option.some.inj (hget.symm.trans hg)).symm
          have hbeq : ((boxes.get ⟨i, hlt⟩).id == s) = true := hmatch
          rw [hb]
          exact beq_iff_eq.mp hbeq
        have hbmem : b ∈ boxes := getElem?_mem' hg
        have hinside : Compound.inside boxes gid b.id = true := hev b hbmem hbid
        have hneB : b.parent ≠ "" := inside_parent_ne_empty hnodup hinside hbmem rfl
        by_cases hc : b.parent == gid
        · exact ⟨[b], by simp [hg, hc]⟩
        · have hev' : ∀ bb ∈ boxes, bb.id = b.parent → Compound.inside boxes gid bb.id = true := by
            intro bb hbbmem hbbid
            rcases inside_parent_step hnodup hterm hbmem hbbmem hbbid hinside with hcon | hpg
            · exact absurd hcon (ESS_ne_of_nbeq_true hc)
            · exact hpg
          obtain ⟨pre, hpre⟩ := ih (s := b.parent) hct hneB hev'
          exact ⟨b :: pre, by simp [hg, hc, hpre]⟩

/-- Every successful `ESS_rootChain` run reaches the group and links by
parent pointers. -/
private theorem ESS_rootChain_props {boxes : List ModelBox} {gid : String}
    (hterm : ∀ b ∈ boxes, ∀ n, boxes.length ≤ n + 1 → chainTerm boxes n b.parent = true)
    (hnodup : (boxes.map (·.id)).Nodup)
    {n : Nat} {s : String} {pre : List ModelBox}
    (h : ESS_rootChain boxes gid n s = some pre) (hne : s ≠ "")
    (hev : ∀ b ∈ boxes, b.id = s → Compound.inside boxes gid b.id = true) :
    (chainWalk boxes n s = pre ++ chainWalk boxes (n - pre.length) gid) ∧
    (∀ b ∈ pre, b ∈ boxes ∧ Compound.inside boxes gid b.id = true) ∧
    (∀ x y xs ys, pre = xs ++ x :: y :: ys → y.id = x.parent) ∧
    (∀ x ∈ pre, ((x.parent == gid) = true) → pre.getLast? = some x) ∧
    (∃ last, pre.getLast? = some last ∧ ((last.parent == gid) = true)) ∧
    pre ≠ [] := by
  induction n generalizing s pre with
  | zero =>
    simp only [ESS_rootChain] at h
    cases h
  | succ n ih =>
    rw [ESS_rootChain_succ] at h
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at h; cases h
    | some i =>
      simp only [hf] at h
      cases hg : boxes[i]? with
      | none => simp only [hg] at h; cases h
      | some b =>
        simp only [hg] at h
        have hbid : b.id = s := by
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have hget : boxes[i]? = some (boxes.get ⟨i, hlt⟩) := List.getElem?_eq_getElem hlt
          have hb : b = boxes.get ⟨i, hlt⟩ := (Option.some.inj (hget.symm.trans hg)).symm
          have hbeq : ((boxes.get ⟨i, hlt⟩).id == s) = true := hmatch
          rw [hb]
          exact beq_iff_eq.mp hbeq
        have hbmem : b ∈ boxes := getElem?_mem' hg
        have hinside : Compound.inside boxes gid b.id = true := hev b hbmem hbid
        have hneB : b.parent ≠ "" := inside_parent_ne_empty hnodup hinside hbmem rfl
        have hwalk : chainWalk boxes (n + 1) s = b :: chainWalk boxes n b.parent := by
          rw [chainWalk_succ hne n]
          simp only [hf, hg]
        by_cases hc : b.parent == gid
        · simp only [hc] at h
          obtain rfl := Option.some.inj h
          have hbeq : b.parent = gid := beq_iff_eq.mp hc
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hwalk, hbeq]; simp
          · intro bb hbb
            rw [List.mem_singleton.mp hbb]
            exact ⟨hbmem, hinside⟩
          · intro x y xs ys hsplit
            have hlen := congrArg List.length hsplit
            simp only [List.length_cons, List.length_nil, List.length_append] at hlen
            omega
          · intro x hx _
            simp [List.mem_singleton.mp hx]
          · exact ⟨b, rfl, hc⟩
          · exact by simp
        · have hev' : ∀ bb ∈ boxes, bb.id = b.parent → Compound.inside boxes gid bb.id = true := by
            intro bb hbbmem hbbid
            rcases inside_parent_step hnodup hterm hbmem hbbmem hbbid hinside with hcon | hpg
            · exact absurd hcon (ESS_ne_of_nbeq_true hc)
            · exact hpg
          simp only [hc] at h
          cases hr : ESS_rootChain boxes gid n b.parent with
          | none => simp only [hr] at h; cases h
          | some pre' =>
            simp only [hr] at h
            obtain rfl := Option.some.inj h
            obtain ⟨ihS, ihM, ihL, ihN, ihE, ihNe⟩ :=
              ih (s := b.parent) (pre := pre') hr hneB hev'
            have hfu : n + 1 - ((b :: pre').length) = n - pre'.length := by
              simp only [List.length_cons]; omega
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hwalk, ihS, hfu, List.cons_append]
            · intro bb hbb
              rw [List.mem_cons] at hbb
              rcases hbb with rfl | hmem'
              · exact ⟨hbmem, hinside⟩
              · exact ihM _ hmem'
            · intro x y xs ys hsplit
              have hsplit' : b :: pre' = xs ++ x :: y :: ys := hsplit
              cases xs with
              | nil =>
                have hsplit0 : b :: pre' = x :: y :: ys := by simpa using hsplit'
                have hx : b = x := ESS_cons_head_eq hsplit0
                have hpre' : pre' = y :: ys := ESS_cons_tail_eq hsplit0
                obtain rfl := hx
                have hsync' : chainWalk boxes n b.parent =
                    y :: (ys ++ chainWalk boxes (n - pre'.length) gid) := by
                  rw [hpre'] at ihS ⊢
                  rw [List.cons_append] at ihS
                  exact ihS
                exact chainWalk_head_id hsync'
              | cons x0 xs' =>
                have hsplit' : b :: pre' = x0 :: (xs' ++ x :: y :: ys) := by simpa using hsplit'
                have hpre' : pre' = xs' ++ x :: y :: ys := ESS_cons_tail_eq hsplit'
                exact ihL x y xs' ys hpre'
            · intro x hxmem hxpar
              rw [List.mem_cons] at hxmem
              rcases hxmem with hxb | hxmem'
              · have hF : (b.parent == gid) = false := Bool.eq_false_iff.mpr hc
                rw [← hxb] at hF
                rw [hF] at hxpar
                simp at hxpar
              · have htail : pre'.getLast? = some x := ihN x hxmem' hxpar
                cases hpre' : pre' with
                | nil => exact absurd hpre' ihNe
                | cons y ys =>
                  rw [hpre'] at htail
                  rw [List.getLast?_cons_cons]
                  exact htail
            · obtain ⟨last, hlast, hpar⟩ := ihE
              refine ⟨last, ?_, hpar⟩
              cases hpre' : pre' with
              | nil => exact absurd hpre' ihNe
              | cons y ys =>
                rw [hpre'] at hlast
                rw [List.getLast?_cons_cons]
                exact hlast
            · exact List.cons_ne_nil _ _

/-- A list of ids with a parent link after every element forms a step chain. -/
private theorem ESS_chain_of_links {R : String → String → Prop} {l : List String} {z : String}
    (h : ∀ x y xs ys, l ++ [z] = xs ++ x :: y :: ys → R x y) :
    StepChain R (l ++ [z]) := by
  induction l with
  | nil => exact StepChain.single z
  | cons a rest ih =>
    cases rest with
    | nil => exact StepChain.cons (h a z [] [] (by simp)) (StepChain.single z)
    | cons b rest' =>
      refine StepChain.cons (h a b [] (rest' ++ [z]) (by simp)) (ih ?_)
      intro x y xs ys hxy
      exact h x y (a :: xs) ys (by simpa using congrArg (fun t => a :: t) hxy)

/-- The index of a member box under nodup ids, with its lookup. -/
private theorem ESS_findIdx_of_mem_box {boxes : List ModelBox} {b : ModelBox}
    (hnd : (boxes.map (·.id)).Nodup) (hb : b ∈ boxes) :
    ∃ i, boxes.findIdx? (fun x => x.id == b.id) = some i ∧ boxes[i]? = some b := by
  obtain ⟨i, hget⟩ := mem_getElem? hb
  obtain ⟨hi, hbox⟩ := List.getElem?_eq_some_iff.mp hget
  have hfin : boxes.findIdx? (fun x => x.id == b.id) = some i := by
    refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hi, ?_, ?_⟩
    · rw [hbox, beq_self_eq_true]
    · intro j hj hsame
      have hjid : boxes[j].id = boxes[i].id :=
        (beq_iff_eq.mp hsame).trans (by rw [hbox])
      have hmap : (boxes.map (·.id))[j]'(by simpa using Nat.lt_trans hj hi) =
          (boxes.map (·.id))[i]'(by simpa using hi) := by
        simpa using hjid
      have hji : j = i := (hnd.getElem_inj).mp hmap
      omega
  exact ⟨i, hfin, hget⟩

/-- Recursion: a parent walk whose adjacent links and last link hold yields the
merged step chain from its first id to the group. -/
private theorem ESS_merged_chain_rec {R : String → String → Prop} {gid : String} :
    ∀ (pre : List ModelBox),
      (∀ x y xs ys, pre = xs ++ x :: y :: ys → R x.id y.id) →
      (∀ l, pre.getLast? = some l → R l.id gid) →
      StepChain R ((pre.map (·.id)) ++ [gid]) := by
  intro pre
  induction pre with
  | nil => intro _ _; exact StepChain.single gid
  | cons p rest ih =>
    intro hstep hlast
    cases rest with
    | nil => exact StepChain.cons (hlast p (by simp)) (StepChain.single gid)
    | cons q rest' =>
      have hpq : R p.id q.id := hstep p q [] rest' rfl
      have htailStep : ∀ x y xs ys, (q :: rest') = xs ++ x :: y :: ys → R x.id y.id := by
        intro x y xs ys h
        exact hstep x y (p :: xs) ys (by simpa using congrArg (fun t => p :: t) h)
      have htailLast : ∀ l, (q :: rest').getLast? = some l → R l.id gid := by
        intro l h
        exact hlast l h
      exact StepChain.cons hpq (ih htailStep htailLast)
/-!
## Short-step exact id and selection facts

Prefixed copies of the private `XB_` foundation from `ExactStepFacts.lean`:
the exact successor split, leaf id fact, `B`-recursion id preservation,
child/parent scene id selection, disjointness, merge bounds, box-parent
mirror, route-endpoint mirror, and box-lookup transport.
-/

/-- Successor split for `layoutRecursiveB` at the exact base. -/
private theorem ESS_succ (exactIds : List String) {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (h : layoutRecursiveB (layoutX exactIds) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      layoutX exactIds inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (layoutX exactIds) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
          group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursiveB (layoutX exactIds) fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with hflat |
    ⟨group, P, _metric, child, _titleLines, parent, hg, _, _, hc, _, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩

/-- Exact leaf id fact: `layoutX` builds its scene with the same `sceneOf`
call as `layout`, with one extra bind for the `exactGraph` step. -/
private theorem ESS_layout_ids {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf, List.map_map]
    exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

/-- Exact `B`-recursion id fact: scene ids of a successful exact recursive
layout are the sub-input ids. -/
private theorem ESS_ids (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    RoutesCovered inp → layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero => intro inp o res _ h; exact ESS_layout_ids h
  | succ fuel ih =>
    intro inp o res hc h
    rcases ESS_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, hexp⟩
    · exact ESS_layout_ids hlayout
    · have hgi := List.find?_some hg
      simp only [Bool.and_eq_true] at hgi
      have hin := independent_inside hgi.1
      have ih1 := ih _ _ _
        (selectInput_routesCovered inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
      have ih2 := ih
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } o parent
        (selectInput_routesCovered inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "") hparent
      have idsC := selectInput_box_ids inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      have idsP := selectInput_box_ids inp
        (fun box => !Compound.inside inp.boxes group.id box.id) ""
      refine expandChild_ids hexp ?_ ?_
      · intro bx hbx
        by_cases hi : Compound.inside inp.boxes group.id bx.id = true
        · have hm : bx.id ∈ child.scene.boxes.map (·.id) := by
            rw [ih1.1, idsC]
            exact mem_filter_ids inp _ bx hbx hi
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hm : bx.id ∈ parent.scene.boxes.map (·.id) := by
            rw [ih2.1]
            show bx.id ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)
            rw [idsP]
            exact mem_filter_ids inp _ bx hbx (by simpa using hi)
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩
      · intro r hr
        obtain ⟨⟨bf, hbf, ef⟩, ⟨bt, hbt, et⟩⟩ := hc r hr
        have heq := hin r hr
        by_cases hi : Compound.inside inp.boxes group.id r.fromId = true
        · have hit : Compound.inside inp.boxes group.id r.toId = true := by
            rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsC]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; exact hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; exact hit)
          have hm : r.id ∈ child.scene.routes.map (·.id) := by
            rw [ih1.2]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hit : ¬ Compound.inside inp.boxes group.id r.toId = true := by
            rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsP]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; simpa using hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; simpa using hit)
          have hm : r.id ∈ parent.scene.routes.map (·.id) := by
            rw [ih2.2]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩

/-- The child/parent scene id lists of one exact expansion, as the two
disjoint halves of the input ids. -/
private theorem ESS_selected_ids (exactIds : List String)
    {fuel : Nat} {inp : Input} {o : Options} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent) :
    child.scene.boxes.map (·.id) =
      (inp.boxes.filter (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) ∧
    parent.scene.boxes.map (·.id) =
      (inp.boxes.filter (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) ∧
    ((inp.boxes.filter (fun box => Compound.inside inp.boxes group.id box.id)).map
      (·.id)).Nodup ∧
    ((inp.boxes.filter (fun box => !Compound.inside inp.boxes group.id box.id)).map
      (·.id)).Nodup ∧
    ∀ id : String,
      id ∈ (inp.boxes.filter (fun box => Compound.inside inp.boxes group.id box.id)).map
        (·.id) →
      id ∈ (inp.boxes.filter (fun box => !Compound.inside inp.boxes group.id box.id)).map
        (·.id) → False := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hchildCov : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hparentCov : RoutesCovered (parentSubInput inp group P titleLines child) :=
    selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hchildIds := ESS_ids exactIds fuel _ _ _ hchildCov hchild
  have hparentIds := ESS_ids exactIds fuel _ _ _ hparentCov hparent
  refine ⟨?_, ?_, expandChild_nodup_filter_map _ _ hnodup,
    expandChild_nodup_filter_map _ _ hnodup, ?_⟩
  · rw [hchildIds.1]
    show (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map (·.id) = _
    rw [selectInput_box_ids]
  · rw [hparentIds.1]
    show (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id) = _
    rw [selectInput_box_ids]
  · intro id hidC hidP
    obtain ⟨m1, hmemC1, hid1⟩ := List.mem_map.mp hidC
    obtain ⟨m2, hmemC2, hid2⟩ := List.mem_map.mp hidP
    obtain ⟨_hm1, hin1⟩ := List.mem_filter.mp hmemC1
    obtain ⟨_hm2, hin2⟩ := List.mem_filter.mp hmemC2
    have heq : m1 = m2 := expandChild_nodup_map_inj (·.id) hnodup
      (List.mem_filter.mp hmemC1).1 (List.mem_filter.mp hmemC2).1 (hid1.trans hid2.symm)
    rw [heq] at hin1
    exact absurd hin2 (fun hc => by
      have hbad : ¬ ((!Compound.inside inp.boxes group.id m2.id) = true) := by
        rw [hin1]; simp
      exact hbad hc)

/-- Scene ids of the two exact sub-layouts are disjoint. -/
private theorem ESS_disjoint (exactIds : List String)
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hchild : layoutRecursiveB (layoutX exactIds) fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.boxes.map (·.id), id ∉ parent.scene.boxes.map (·.id) := by
  have hc := ESS_ids exactIds fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := ESS_ids exactIds fuel _ _ _ hparentCoverage hparent
  have hcIds := hc.1
  have hpIds := hp.1
  change parent.scene.boxes.map (·.id) =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
      (·.id) at hpIds
  rw [selectInput_box_ids] at hcIds hpIds
  intro id hidChild hidParent
  rw [hcIds] at hidChild
  rw [hpIds] at hidParent
  obtain ⟨childBox, hchildBox, hchildId⟩ := List.mem_map.mp hidChild
  obtain ⟨parentBox, hparentBox, hparentId⟩ := List.mem_map.mp hidParent
  have hinside := (List.mem_filter.mp hchildBox).2
  have houtside := (List.mem_filter.mp hparentBox).2
  have heqId : childBox.id = parentBox.id := hchildId.trans hparentId.symm
  rw [heqId] at hinside
  simp only [hinside, Bool.not_true, Bool.false_eq_true] at houtside
/-- The offset-independent structural facts of one exact `expandChild` call:
the two scene-size bounds and the child/group id isolation. -/
private theorem ESS_merge_bounds (exactIds : List String)
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    child.scene.boxes.length ≤ res.scene.boxes.length ∧
    parent.scene.boxes.length ≤ res.scene.boxes.length ∧
    (∀ (frame : Box), parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hchildCov : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hparentCov : RoutesCovered (parentSubInput inp group P titleLines child) :=
    selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hchildIds := ESS_ids exactIds fuel _ _ _ hchildCov hchild
  have hparentIds := ESS_ids exactIds fuel _ _ _ hparentCov hparent
  have hdisjoint := ESS_disjoint exactIds hchild hparent
  have hbox : ∀ b ∈ inp.boxes, ∃ x ∈ child.scene.boxes ++ parent.scene.boxes, x.id = b.id := by
    intro b hb
    by_cases hi : Compound.inside inp.boxes group.id b.id = true
    · obtain ⟨cb, _hcbmem, hcbid, _⟩ := selectInput_box_exists inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id hb hi
      have hcid : child.scene.boxes.map (·.id) =
          (inp.boxes.filter
            (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
        have hsel : (childSubInput inp group).boxes.map (·.id) =
            (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
          show (selectInput inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
              (·.id) =
            (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id)
          rw [selectInput_box_ids]
        rw [hchildIds.1, hsel]
      have hmem : b.id ∈ child.scene.boxes.map (·.id) := by
        rw [hcid]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hi⟩, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
      exact ⟨x, List.mem_append_left _ hx, hxid⟩
    · have hninside : (!Compound.inside inp.boxes group.id b.id) = true := by
        rw [Bool.not_eq_true']; exact Bool.of_not_eq_true hi
      obtain ⟨pb, _hpbmem, hpbid, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hb hninside
      have hpid : parent.scene.boxes.map (·.id) =
          (inp.boxes.filter
            (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
        have hboxes : (parentSubInput inp group P titleLines child).boxes =
            (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
        rw [hparentIds.1, hboxes, selectInput_box_ids]
      have hmem : b.id ∈ parent.scene.boxes.map (·.id) := by
        rw [hpid]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hninside⟩, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
      exact ⟨x, List.mem_append_right _ hx, hxid⟩
  have hroute : ∀ r ∈ inp.routes,
      ∃ x ∈ child.scene.routes ++ parent.scene.routes, x.id = r.id := by
    intro r hr
    obtain ⟨⟨bf, hbf, hbfid⟩, ⟨bt, hbt, hbtid⟩⟩ := hcovered r hr
    have hIndep : Compound.independent inp.boxes inp.routes group = true := by
      have hfind := List.find?_some hgroup
      simp only [Bool.and_eq_true] at hfind
      exact hfind.1
    have hsame := independent_inside hIndep r hr
    by_cases hi : Compound.inside inp.boxes group.id r.fromId = true
    · have hti : Compound.inside inp.boxes group.id r.toId = true := by
        rw [← hsame]; exact hi
      obtain ⟨bf', hbf'mem, hbf'id, _⟩ := selectInput_box_exists inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id hbf
        (by rw [hbfid]; exact hi)
      obtain ⟨bt', hbt'mem, hbt'id, _⟩ := selectInput_box_exists inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id hbt
        (by rw [hbtid]; exact hti)
      have hmem : r ∈ (childSubInput inp group).routes := by
        exact (selectInput_route_mem inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id r).mpr
          ⟨hr, by
            rw [List.any_eq_true]
            exact ⟨bf', hbf'mem, by simp [hbf'id, hbfid]⟩,
          by
            rw [List.any_eq_true]
            exact ⟨bt', hbt'mem, by simp [hbt'id, hbtid]⟩⟩
      have hcr : child.scene.routes.map (·.id) =
          (childSubInput inp group).routes.map (·.id) := hchildIds.2
      have hmid : r.id ∈ child.scene.routes.map (·.id) := by
        rw [hcr]
        exact List.mem_map.mpr ⟨r, hmem, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmid
      exact ⟨x, List.mem_append_left _ hx, hxid⟩
    · have hfi : Compound.inside inp.boxes group.id r.fromId = false :=
        Bool.of_not_eq_true hi
      have hft : Compound.inside inp.boxes group.id r.toId = false := by
        have := hsame
        rw [hfi] at this
        exact this.symm
      obtain ⟨bf', hbf'mem, hbf'id, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hbf
        (by rw [hbfid]; rw [Bool.not_eq_true']; exact hfi)
      obtain ⟨bt', hbt'mem, hbt'id, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hbt
        (by rw [hbtid]; rw [Bool.not_eq_true']; exact hft)
      have hmem : r ∈ (parentSubInput inp group P titleLines child).routes := by
        have hsel := (selectInput_route_mem inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" r).mpr
          ⟨hr, by
            rw [List.any_eq_true]
            exact ⟨bf', hbf'mem, by simp [hbf'id, hbfid]⟩,
          by
            rw [List.any_eq_true]
            exact ⟨bt', hbt'mem, by simp [hbt'id, hbtid]⟩⟩
        have hroutes : (parentSubInput inp group P titleLines child).routes =
            (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := rfl
        rwa [hroutes]
      have hpr : parent.scene.routes.map (·.id) =
          (parentSubInput inp group P titleLines child).routes.map (·.id) := hparentIds.2
      have hmid : r.id ∈ parent.scene.routes.map (·.id) := by
        rw [hpr]
        exact List.mem_map.mpr ⟨r, hmem, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmid
      exact ⟨x, List.mem_append_right _ hx, hxid⟩
  obtain ⟨hboxIds, hroutesIds⟩ := expandChild_ids hexpand hbox hroute
  have hresLen : res.scene.boxes.length = inp.boxes.length := by
    have h := congrArg List.length hboxIds
    simp only [List.length_map] at h
    exact h
  have hchildLen : child.scene.boxes.length = (childSubInput inp group).boxes.length := by
    have h := congrArg List.length hchildIds.1
    simpa using h
  have hparentLen : parent.scene.boxes.length =
      (parentSubInput inp group P titleLines child).boxes.length := by
    have h := congrArg List.length hparentIds.1
    simpa using h
  have hsubC : (childSubInput inp group).boxes.length ≤ inp.boxes.length := by
    show (((inp.boxes.zipIdx 0).filter
      fun q => Compound.inside inp.boxes group.id q.1.id).map
        fun q => if q.1.parent == group.id then { q.1 with parent := "" } else q.1).length ≤
      inp.boxes.length
    simp only [List.length_map]
    have h := List.length_filter_le
      (fun q => Compound.inside inp.boxes group.id q.1.id) (inp.boxes.zipIdx 0)
    rw [List.length_zipIdx] at h
    exact h
  have hsubP : (parentSubInput inp group P titleLines child).boxes.length ≤
      inp.boxes.length := by
    have hboxes : (parentSubInput inp group P titleLines child).boxes =
        (selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
    rw [hboxes]
    show (((inp.boxes.zipIdx 0).filter
      fun q => (!Compound.inside inp.boxes group.id q.1.id)).map
        fun q => if q.1.parent == "" then { q.1 with parent := "" } else q.1).length ≤
      inp.boxes.length
    simp only [List.length_map]
    have h := List.length_filter_le
      (fun q => !Compound.inside inp.boxes group.id q.1.id) (inp.boxes.zipIdx 0)
    rw [List.length_zipIdx] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hchildLen, hresLen]; exact Nat.le_trans hsubC (Nat.le_refl _)
  · rw [hparentLen, hresLen]; exact Nat.le_trans hsubP (Nat.le_refl _)
  · intro frame hframe cb hcb hEq
    have hcbId : cb.id ∈ child.scene.boxes.map (·.id) := List.mem_map.mpr ⟨cb, hcb, rfl⟩
    have hframeMem : frame ∈ parent.scene.boxes := List.mem_of_find?_eq_some hframe
    have hfid : frame.id = group.id := by simpa using List.find?_some hframe
    have hparentId : group.id ∈ parent.scene.boxes.map (·.id) :=
      List.mem_map.mpr ⟨frame, hframeMem, hfid⟩
    exact hdisjoint group.id (hEq ▸ hcbId) hparentId

/-- Exact leaf box-parent mirror fact. -/
private theorem ESS_layout_box_parent {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf]
    intro cb hcb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
    exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Exact `B`-recursion box-parent mirror fact. -/
private theorem ESS_box_parent (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact ESS_layout_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases ESS_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact ESS_layout_box_parent hlayout
    · have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
          ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
        intro keep root
        rw [selectInput_box_ids]
        exact nodup_filter_map keep (·.id) inp.boxes hnodup
      have hchildNodup : ((selectInput inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
            (·.id)).Nodup := hselNodup _ _
      have hparentNodup : (({ selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } : Input).boxes.map
            (·.id)).Nodup := by
        show ((selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
            (·.id)).Nodup
        rw [selectInput_box_ids]
        exact nodup_filter_map _ _ _ hnodup
      have hchildParent := ih _ _ _ hchildNodup hchild
      have hparentParent := ih _ _ _ hparentNodup hparent
      obtain ⟨_frame, _metric', _titleLines', _lines, dx, dy, _hframe, _hmetric',
        _htitle', _hlines', _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
      intro cb hcb
      rw [hboxes] at hcb
      obtain ⟨_model, _hmodelmem, hfind⟩ := List.mem_filterMap.mp hcb
      have hcbItems : cb ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hcbItems with hbc | hbp
      · obtain ⟨cbb, hcbbmem, hEmbed⟩ := List.mem_map.mp hbc
        obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hchildParent cbb hcbbmem
        obtain ⟨m, hmmem, hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
        have hne : m.parent ≠ "" := by
          have hkeep' : Compound.inside inp.boxes group.id m.id = true := hkeep
          exact inside_parent_ne_empty hnodup hkeep' hmmem rfl
        refine ⟨m, hmmem, ?_, ?_⟩
        · have hcid : cbb.id = cb.id := by
            have h := congrArg (fun b : Box => b.id) hEmbed
            simpa [embedBox] using h
          exact hmsbid.symm.trans (hsbid.trans hcid)
        · have hcpar : cb.parent = (if cbb.parent == "" then group.id else cbb.parent) := by
            have h := congrArg (fun b : Box => b.parent) hEmbed
            simpa [embedBox] using h.symm
          rw [hsbpar, hmsbpar] at hcpar
          exact hcpar.trans (embed_parent_eq hne)
      · obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hparentParent cb hbp
        obtain ⟨m, _hmmem, _hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, _hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · have hsp : sb.parent = m.parent := by
            rw [hmsbpar]
            exact selectInput_parent_root m.parent
          exact hsbpar.trans hsp

/-- Exact leaf route-endpoint mirror. -/
private theorem ESS_layout_mirror (exactIds : List String) {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : layoutX exactIds inp o = .ok res) :
    (∀ rt ∈ res.scene.routes,
      rt.fromId ∈ res.scene.boxes.map (·.id) ∧ rt.toId ∈ res.scene.boxes.map (·.id)) ∧
    (∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner) := by
  have hcov : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hids := ESS_layout_ids h
  unfold layoutX at h
  dsimp only at h
  obtain ⟨P, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨lines, _, h⟩ := bind_ok h
  obtain ⟨measured, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have hres := Except.ok.inj h
    have hsc : res.scene = sceneOf P inp o lines acc measured :=
      (congrArg FamilyResult.scene hres).symm
    constructor
    · intro rt hrt
      rw [hsc] at hrt
      obtain ⟨k, hkget⟩ := List.mem_iff_getElem?.mp hrt
      obtain ⟨hk, _hget⟩ := List.getElem?_eq_some_iff.mp hkget
      rw [sceneOf_routes_length] at hk
      have hrec := sceneOf_routes_getElem? P inp o lines acc measured k hk
      have hrtEq : rt = ⟨(inp.routes[k]).id, (inp.routes[k]).fromId,
          (inp.routes[k]).toId, (inp.routes[k]).orthogonal,
          (acc.routes.getD k []).map (fun p =>
            shiftPoint P.canvasMargin P.canvasMargin
              (orientPoint o.direction acc.canvasH p))⟩ :=
        Option.some.inj (hkget.symm.trans hrec)
      have hfrom : rt.fromId = (inp.routes[k]).fromId := congrArg Route.fromId hrtEq
      have hto : rt.toId = (inp.routes[k]).toId := congrArg Route.toId hrtEq
      have hkmem : inp.routes[k] ∈ inp.routes := List.getElem_mem hk
      obtain ⟨hfromCov, htoCov⟩ := hcov _ hkmem
      obtain ⟨bf, hbf, hbfid⟩ := hfromCov
      obtain ⟨bt, hbt, hbtid⟩ := htoCov
      constructor
      · rw [hfrom]
        have hbid : (inp.routes[k]).fromId ∈ inp.boxes.map (·.id) :=
          List.mem_map.mpr ⟨bf, hbf, hbfid⟩
        rwa [hids.1]
      · rw [hto]
        have hbid : (inp.routes[k]).toId ∈ inp.boxes.map (·.id) :=
          List.mem_map.mpr ⟨bt, hbt, hbtid⟩
        rwa [hids.1]
    · intro sl hsl
      rw [hsc] at hsl
      exact sceneOf_label_mem P inp o lines acc measured sl hsl

/-- Exact `B`-recursion endpoint mirror. -/
private theorem ESS_mirror_endpoints (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
    ∀ rt ∈ res.scene.routes,
      rt.fromId ∈ res.scene.boxes.map (·.id) ∧ rt.toId ∈ res.scene.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf _hframed h
    exact (ESS_layout_mirror exactIds hwf h).1
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨hn, hlayout⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, hexpand⟩
    · exact (ESS_layout_mirror exactIds hwf hlayout).1
    · have hchildB : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
          (childSubOptions o group) = .ok child := hc
      have hparentB : layoutRecursiveB (layoutX exactIds) fuel
          (parentSubInput inp group P titleLines child) o = .ok parent := hp
      have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P metric titleLines
        child parent hwf hframed hP hm ht hchildB hparentB
      have ihC := ih _ _ _ hsub.1 hsub.2.1 hchildB
      have ihP := ih _ _ _ hsub.2.2.1 hsub.2.2.2 hparentB
      have hcovC : RoutesCovered (childSubInput inp group) :=
        selectInput_routesCovered inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
      have hcovP : RoutesCovered (parentSubInput inp group P titleLines child) :=
        selectInput_routesCovered inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have hchildIds := ESS_ids exactIds fuel _ _ _ hcovC hchildB
      have hparentIds := ESS_ids exactIds fuel _ _ _ hcovP hparentB
      have hboxPart : ∀ b ∈ inp.boxes,
          b.id ∈ child.scene.boxes.map (·.id) ++ parent.scene.boxes.map (·.id) := by
        intro b hb
        by_cases hi : Compound.inside inp.boxes group.id b.id = true
        · have hmem : b.id ∈ (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) :=
            (mem_selected_box_ids inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id b.id).mpr
              ⟨b, hb, hi, rfl⟩
          have hcid : child.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hchildIds.1]
            show (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
                (·.id) = _
            rw [selectInput_box_ids]
          rw [← hcid] at hmem
          exact List.mem_append_left _ hmem
        · have hn : (!Compound.inside inp.boxes group.id b.id) = true := by
            simp [hi]
          have hmem : b.id ∈ (inp.boxes.filter
              (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) :=
            (mem_selected_box_ids inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "" b.id).mpr
              ⟨b, hb, hn, rfl⟩
          have hpid : parent.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hparentIds.1]
            show (parentSubInput inp group P titleLines child).boxes.map (·.id) = _
            show (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
                (·.id) = _
            rw [selectInput_box_ids]
          rw [← hpid] at hmem
          exact List.mem_append_right _ hmem
      have hboxIds : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
        obtain ⟨frameS, metricS, tlS, _linesS, dxS, dyS, hframeS, hmetricS, htitleS,
          _hlinesS, hdxS, hdyS, _hcanvasS, hboxesS⟩ := expandChild_sources hexpand
        rw [hboxesS]
        refine filterMap_find_ids (fun b : Box => b.id) (inp.boxes.map (·.id))
          (child.scene.boxes.map (embedBox group.id dxS dyS) ++ parent.scene.boxes)
          ?_ inp.boxes (fun b : ModelBox => b.id) rfl
        intro id hid
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hid
        have hbp := hboxPart b hb
        rcases List.mem_append.mp hbp with hcl | hpr
        · obtain ⟨cb, hcb, hcbid⟩ := List.mem_map.mp hcl
          refine ⟨embedBox group.id dxS dyS cb, ?_, ?_⟩
          · exact List.mem_append_left _
              (List.mem_map.mpr ⟨cb, hcb, rfl⟩)
          · exact hcbid
        · obtain ⟨pb, hpb, hpbid⟩ := List.mem_map.mp hpr
          exact ⟨pb, List.mem_append_right _ hpb, hpbid⟩
      · intro rt hrt
        obtain ⟨frameS, metricS, tlS, _linesS, dxS, dyS, hframeS, hmetricS, htitleS,
          _hlinesS, hdxS, hdyS, _hcanvasS, _hboxesS⟩ := expandChild_sources hexpand
        have hroutes := expandChild_routes_eq hexpand frameS metricS tlS dxS dyS
          hframeS hmetricS htitleS hdxS hdyS
        rw [hroutes] at hrt
        obtain ⟨model, hmMem, hfind⟩ := List.mem_filterMap.mp hrt
        have hrtMem : rt ∈ (child.scene.routes.map (fun route : Route =>
            { route with points := route.points.map (shiftPoint dxS dyS) })) ++
          parent.scene.routes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hrtMem with hcl | hpr
        · obtain ⟨cr, hcr, hrtEq⟩ := List.mem_map.mp hcl
          have hfrom : rt.fromId = cr.fromId := by rw [← hrtEq]
          have hto : rt.toId = cr.toId := by rw [← hrtEq]
          obtain ⟨ihCfrom, ihCto⟩ := ihC cr hcr
          have hcid : child.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hchildIds.1]
            show (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
                (·.id) = _
            rw [selectInput_box_ids]
          have hsubC : ∀ x ∈ child.scene.boxes.map (·.id),
              x ∈ inp.boxes.map (·.id) := by
            intro x hx
            rw [hcid] at hx
            exact (List.Sublist.map (fun box : ModelBox => box.id)
              (List.filter_sublist (l := inp.boxes))).subset hx
          constructor
          · rw [hfrom, hboxIds]
            exact hsubC _ ihCfrom
          · rw [hto, hboxIds]
            exact hsubC _ ihCto
        · obtain ⟨ihPfrom, ihPto⟩ := ihP rt hpr
          have hpid : parent.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hparentIds.1]
            show (parentSubInput inp group P titleLines child).boxes.map (·.id) = _
            show (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
                (·.id) = _
            rw [selectInput_box_ids]
          have hsubP : ∀ x ∈ parent.scene.boxes.map (·.id),
              x ∈ inp.boxes.map (·.id) := by
            intro x hx
            rw [hpid] at hx
            exact (List.Sublist.map (fun box : ModelBox => box.id)
              (List.filter_sublist (l := inp.boxes))).subset hx
          constructor
          · rw [hboxIds]
            exact hsubP _ ihPfrom
          · rw [hboxIds]
            exact hsubP _ ihPto

/-- The merged scene resolves every child box to its embedded image and every
parent box to itself, at the exact base. -/
private theorem ESS_boxLookup_transport (exactIds : List String)
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin ∧
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin ∧
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        res.scene.layoutDump.box? b.id = some b) := by
  obtain ⟨frame, _metric, tl, _lines, dx, dy, hframe, _hmetric, _htitle,
    _hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ :=
    ESS_selected_ids exactIds hwf hchild hparent
  refine ⟨frame, tl, dx, dy, hframe, hdx, hdy, ?_, ?_⟩
  · intro b hb
    have hbMem : b ∈ child.scene.boxes := List.mem_of_find?_eq_some hb
    have hidC : b.id ∈ (inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hcid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidC
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hchildFirst : ∀ (cb : Box), cb ∈ child.scene.boxes → cb.id = b.id → cb = b := by
      intro cb hcbmem hcbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hcid]; exact hnC) hcbmem hbMem hcbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some (embedBox group.id dx dy b)
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := embedBox group.id dx dy b) (s := b.id)
      ⟨m, hmin, ?_⟩ rfl ?_
    · have hcf : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = some (embedBox group.id dx dy b) := by
        rw [List.find?_map]
        have hinside : (child.scene.boxes.find?
            ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy)) = some b := by
          have hpred : ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy) =
              (fun cb => cb.id == b.id) := by
            funext cb
            simp only [Function.comp_apply, embedBox]
            rw [hmid]
          rw [hpred]
          exact hb
        rw [hinside]
        rfl
      rw [List.find?_append]
      rw [hcf]
      rfl
    · intro m' hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        rw [hchildFirst cb hcb hcbkey]
      · exfalso
        exact hdisj z.id
          (by rw [hzid, ← hcid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
          (by rw [← hpid]; exact List.mem_map.mpr ⟨z, hzp, rfl⟩)
  · intro b hb
    have hbMem : b ∈ parent.scene.boxes := List.mem_of_find?_eq_some hb
    have hidP : b.id ∈ (inp.boxes.filter
        (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hpid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidP
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hparentFirst : ∀ (pb : Box), pb ∈ parent.scene.boxes → pb.id = b.id → pb = b := by
      intro pb hpmem hpbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hpid]; exact hnP) hpmem hbMem hpbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some b
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := b) (s := b.id) ⟨m, hmin, ?_⟩ rfl ?_
    · have hcfNone : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = none := by
        rw [List.find?_eq_none]
        intro cb hcb hp
        obtain ⟨cd, hcd, hcdrfl⟩ := List.mem_map.mp hcb
        subst hcdrfl
        have hkey : (embedBox group.id dx dy cd).id = m.id := beq_iff_eq.mp hp
        rw [show (embedBox group.id dx dy cd).id = cd.id from rfl] at hkey
        exact hdisj cd.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cd, hcd, rfl⟩)
          (by rw [hkey]; exact List.mem_map.mpr ⟨m, hmf, rfl⟩)
      have hcfP : parent.scene.boxes.find? (fun box => box.id == m.id) = some b := by
        show parent.scene.layoutDump.box? m.id = some b
        rw [hmid]
        exact hb
      rw [List.find?_append, hcfNone, hcfP]
      rfl
    · intro m' hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        exfalso
        exact hdisj cb.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cb, hcb, rfl⟩)
          (by rw [hcbkey, ← hpid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
      · rw [hparentFirst z hzp hzid]
/-!
## Short-step ancestry replay

Prefixed `B`-twins of the ancestry chain from
`ExpandChildAncestryProof.lean`: merged length, empty-group child, merged
box transport, model-box last-link utilities, the group-anchored walk
fact, the executed root chain, merged anchors, and the anchor assemblers.
-/

private theorem ESS_merged_length_sum
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} (exactIds : List String)
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    child.scene.boxes.length + parent.scene.boxes.length ≤
      res.scene.boxes.length := by
  obtain ⟨hcid, hpid, _hnC, _hnP, _hdisj⟩ :=
    ESS_selected_ids exactIds hwf hchild hparent
  obtain ⟨_frame, _metric, _tl, _lines, dx, dy, _hframe, _hmetric, _htitle,
    _hlines, _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  have hmem : ∀ m ∈ inp.boxes, ∃ b,
      (((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == m.id)) = some b ∧
      b.id = m.id := by
    intro m hm
    by_cases hinside : Compound.inside inp.boxes group.id m.id = true
    · have hflt : m ∈ inp.boxes.filter
          (fun box => Compound.inside inp.boxes group.id box.id) :=
        List.mem_filter.mpr ⟨hm, hinside⟩
      have hid : m.id ∈ child.scene.boxes.map (·.id) := by
        rw [hcid]
        exact List.mem_map.mpr ⟨m, hflt, rfl⟩
      obtain ⟨cb, hcb, hcbid⟩ := List.mem_map.mp hid
      have hmemE : (embedBox group.id dx dy cb) ∈
          (child.scene.boxes.map (embedBox group.id dx dy)) :=
        List.mem_map.mpr ⟨cb, hcb, rfl⟩
      have hmemU : (embedBox group.id dx dy cb) ∈
          ((child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes) :=
        List.mem_append_left _ hmemE
      have hkey : (embedBox group.id dx dy cb).id = m.id := hcbid
      have hmemId : m.id ∈ (((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes).map (·.id)) :=
        List.mem_map.mpr ⟨_, hmemU, hkey⟩
      obtain ⟨b, _hbmem, hbfind, hbid⟩ :=
        ESS_box_of_mem_ids (l := ((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes)) hmemId
      exact ⟨b, hbfind, hbid⟩
    · have hnot : ((!Compound.inside inp.boxes group.id m.id) = true) := by
        rw [Bool.not_eq_true']
        exact Bool.of_not_eq_true hinside
      have hflt : m ∈ inp.boxes.filter
          (fun box => !Compound.inside inp.boxes group.id box.id) :=
        List.mem_filter.mpr ⟨hm, hnot⟩
      have hid : m.id ∈ parent.scene.boxes.map (·.id) := by
        rw [hpid]
        exact List.mem_map.mpr ⟨m, hflt, rfl⟩
      obtain ⟨pb, hpb, hpbid⟩ := List.mem_map.mp hid
      have hmemU : pb ∈ ((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes) :=
        List.mem_append_right _ hpb
      have hmemId : m.id ∈ (((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes).map (·.id)) :=
        List.mem_map.mpr ⟨pb, hmemU, hpbid⟩
      obtain ⟨b, _hbmem, hbfind, hbid⟩ :=
        ESS_box_of_mem_ids (l := ((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes)) hmemId
      exact ⟨b, hbfind, hbid⟩
  have hlenM : res.scene.boxes.length = inp.boxes.length := by
    have h1 := ESS_filterMap_length_of_all_some inp.boxes _ (fun x hx =>
      let ⟨b, hb, _⟩ := hmem x hx; ⟨b, hb⟩)
    have heq : res.scene.boxes =
        inp.boxes.filterMap (fun model =>
          ((child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes).find? (fun box => box.id == model.id)) :=
      hboxes
    rw [heq]
    exact h1
  have hlenC : child.scene.boxes.length =
      (inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id)).length := by
    have h := congrArg List.length hcid
    simpa using h
  have hlenP : parent.scene.boxes.length =
      (inp.boxes.filter
        (fun box => !Compound.inside inp.boxes group.id box.id)).length := by
    have h := congrArg List.length hpid
    simpa using h
  have hsum := ESS_filter_not_length_sum inp.boxes
    (fun box => Compound.inside inp.boxes group.id box.id)
  rw [hlenC, hlenP, hlenM, hsum]
  exact Nat.le_refl _

/-- With an empty group id the exact child scene is empty. -/
private theorem ESS_child_empty_of_empty_group (exactIds : List String)
    {inp : Input} {o : Options}
    {group : ModelBox} {P : Params} {fuel : Nat}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child : FamilyResult} {res : FamilyResult}
    (hgid : group.id = "")
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res) :
    child.scene.boxes = [] := by
  obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctxB
  have hcid := (ESS_selected_ids exactIds hwf hchild hparent).1
  have hmap : child.scene.boxes.map (·.id) = [] := by
    rw [hcid]
    have hnil : inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id) = [] := by
      have hall : ∀ m ∈ inp.boxes,
          Compound.inside inp.boxes group.id m.id = false := by
        intro m _
        rw [hgid]
        exact ESS_inside_empty_id m.id
      have key : ∀ (l : List ModelBox),
          (∀ m ∈ l, Compound.inside inp.boxes group.id m.id = false) →
          l.filter (fun box => Compound.inside inp.boxes group.id box.id) = [] := by
        intro l hl
        induction l with
        | nil => rfl
        | cons b rest ih =>
          have hb := hl b (List.mem_cons.mpr (Or.inl rfl))
          simp only [List.filter_cons, hb]
          exact ih (fun m hm => hl m (List.mem_cons.mpr (Or.inr hm)))
      exact key _ hall
    rw [hnil, List.map_nil]
  match hcb : child.scene.boxes with
  | [] => rfl
  | _ :: _ => simp [hcb] at hmap

/-- The merged-dump image of an inside model box, with its merged parent. -/
private theorem ESS_merged_box_of_inside (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    {p : ModelBox} (hpmem : p ∈ inp.boxes)
    (hinside : Compound.inside inp.boxes group.id p.id = true) :
    ∃ bx, res.scene.layoutDump.box? p.id = some bx ∧
      bx.parent = (if p.parent == group.id then group.id else p.parent) := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  obtain ⟨hcid, _hpid, hnC, _hnP, _hdisj⟩ := ESS_selected_ids exactIds hwf hchild hparent
  obtain ⟨_frame, _tl, dx, dy, _hf, _hdx, _hdy, htransC, _htp⟩ :=
    ESS_boxLookup_transport exactIds hwf hchild hparent hexpand
  have hppar : p.parent ≠ "" := inside_parent_ne_empty hnodup hinside hpmem rfl
  have hmemIds : p.id ∈ child.scene.boxes.map (·.id) := by
    rw [hcid]
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hpmem, hinside⟩, rfl⟩
  obtain ⟨bx0, hbx0mem, hbx0id⟩ := List.mem_map.mp hmemIds
  have hndChild : (child.scene.boxes.map (·.id)).Nodup := by
    rw [hcid]
    exact hnC
  have hfind : child.scene.boxes.find? (fun b => b.id == p.id) = some bx0 := by
    rw [← hbx0id]
    exact ESS_find?_of_mem_nodup hndChild hbx0mem
  have hchildNodup : ((childSubInput inp group).boxes.map (·.id)).Nodup := by
    show ((selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
      group.id).boxes.map (·.id)).Nodup
    rw [selectInput_box_ids]
    exact nodup_filter_map _ _ _ hnodup
  obtain ⟨sb, hsbmem, _hsbid, hsbpar⟩ :=
    ESS_box_parent exactIds fuel (childSubInput inp group)
      (childSubOptions o group) child hchildNodup hchild bx0 hbx0mem
  obtain ⟨m, hmmem, _hkeep, hmsid, hmspar⟩ :=
    selectInput_box_spec inp (fun box => Compound.inside inp.boxes group.id box.id)
      group.id hsbmem
  have hmeq : m = p := by
    refine eq_of_mem_id hnodup hmmem hpmem ?_
    rw [← hmsid, ← hbx0id]
    exact _hsbid
  have hparval : bx0.parent = (if p.parent == group.id then "" else p.parent) := by
    rw [hsbpar, hmspar, hmeq]
  have hcb : child.scene.layoutDump.box? bx0.id = some bx0 := by
    rw [hbx0id]
    exact hfind
  have htrans := htransC bx0 hcb
  refine ⟨embedBox group.id dx dy bx0, ?_, ?_⟩
  · rw [← hbx0id]
    exact htrans
  · have hparentE : (embedBox group.id dx dy bx0).parent =
        (if bx0.parent == "" then group.id else bx0.parent) := rfl
    rw [hparentE, hparval]
    by_cases hp : (p.parent == group.id) = true
    · simp [hp]
    · have hpf : (p.parent == group.id) = false := by
        cases h : (p.parent == group.id)
        · rfl
        · exact absurd h hp
      have hne : (p.parent == "") = false := by
        cases h : (p.parent == "")
        · rfl
        · exact absurd (beq_iff_eq.mp h) hppar
      simp [hpf, hne]

private theorem ESS_mem_box_of_getLast? (l : List ModelBox) (x : ModelBox)
    (h : l.getLast? = some x) : x ∈ l := by
  cases hl : l with
  | nil => simp [hl] at h
  | cons a t =>
    cases ht : t with
    | nil =>
      have hax : a = x := by simpa [hl, ht] using h
      subst hax
      exact List.mem_cons.mpr (Or.inl rfl)
    | cons b t2 =>
      have hT : (a :: b :: t2).getLast? = some x := by
        rw [← ht, ← hl]
        exact h
      have h' : (b :: t2).getLast? = some x := hT
      exact List.mem_cons.mpr (Or.inr (ESS_mem_box_of_getLast? _ _ h'))

private theorem ESS_getLast_append_cons {α : Type} (xs : List α) (x y : α) (ys : List α) :
    (xs ++ x :: y :: ys).getLast? = (y :: ys).getLast? := by
  induction xs with
  | nil =>
    have hnil : (([] : List α) ++ x :: y :: ys) = (x :: y :: ys) := rfl
    rw [hnil]
    exact List.getLast?_cons_cons
  | cons x₀ xs ih =>
    have hne : xs ++ x :: y :: ys ≠ [] :=
      List.ne_nil_of_mem (List.mem_append_right _
        (List.mem_cons.mpr (Or.inl rfl)))
    rw [List.cons_append, List.getLast?_cons_of_ne_nil hne, ih]

/-- Every box on a group-anchored parent walk has a nonempty id. -/
private theorem ESS_chain_all_ids_ne_empty {boxes : List ModelBox} {gid : String}
    (hnodup : (boxes.map (·.id)).Nodup) :
    ∀ (pre : List ModelBox) (s : String), s ≠ "" →
    (∀ b ∈ pre, b ∈ boxes ∧ Compound.inside boxes gid b.id = true) →
    (∀ x y xs ys, pre = xs ++ x :: y :: ys → y.id = x.parent) →
    (∀ b₀ rest, pre = b₀ :: rest → b₀.id = s) →
    ∀ b ∈ pre, b.id ≠ "" := by
  intro pre
  induction pre with
  | nil =>
    intro s _hsNe _hMem _hLink _hHead b hb
    cases hb
  | cons b₀ rest ih =>
    intro s hsNe hMem hLink hHead b hb
    have hb0id : b₀.id = s := hHead b₀ rest rfl
    rcases List.mem_cons.mp hb with rfl | hmemRest
    · rw [hb0id]
      exact hsNe
    · cases rest with
      | nil => cases hmemRest
      | cons b₁ rest' =>
        have hb1eq : b₁.id = b₀.parent := hLink b₀ b₁ [] rest' rfl
        have hb0mem : b₀ ∈ boxes := (hMem b₀ (List.mem_cons.mpr (Or.inl rfl))).1
        have hb0in : Compound.inside boxes gid b₀.id = true :=
          (hMem b₀ (List.mem_cons.mpr (Or.inl rfl))).2
        have hparNe : b₀.parent ≠ "" :=
          inside_parent_ne_empty hnodup hb0in hb0mem rfl
        have hb1ne : b₁.id ≠ "" := by
          rw [hb1eq]
          exact hparNe
        have hMemT : ∀ c ∈ b₁ :: rest',
            c ∈ boxes ∧ Compound.inside boxes gid c.id = true := by
          intro c hc
          exact hMem c (List.mem_cons.mpr (Or.inr hc))
        have hLinkT : ∀ x y xs ys, (b₁ :: rest') = xs ++ x :: y :: ys →
            y.id = x.parent := by
          intro x y xs ys h
          exact hLink x y (b₀ :: xs) ys (by simpa using congrArg (fun t => b₀ :: t) h)
        have hHeadT : ∀ c₀ r, (b₁ :: rest') = c₀ :: r → c₀.id = b₁.id := by
          intro c₀ r h
          have heq : b₁ = c₀ := ESS_cons_head_eq h
          rw [← heq]
        exact ih b₁.id hb1ne hMemT hLinkT hHeadT b hmemRest
/-- The executed merge walks every embedded child box to the group frame. -/
private theorem ESS_childRootChain (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildChildRootChain group child res := by
  by_cases hgNe : group.id = ""
  · have hempty : child.scene.boxes = [] :=
      ESS_child_empty_of_empty_group exactIds hgNe hctxB
    intro cb hcb
    rw [hempty] at hcb
    cases hcb
  · obtain ⟨hwf, _hgroup, _hpboxes, hchild, hparent, _hexpand'⟩ := hctxB
    have hf : InputFacts inp := inputFacts_of_wellFormed hwf
    have hnodup : (inp.boxes.map (·.id)).Nodup := hf.nodup
    obtain ⟨hcid, _hpid, hnC, _hnP, _hdisj⟩ :=
      ESS_selected_ids exactIds hwf hchild hparent
    have hChildNodup : (child.scene.boxes.map (·.id)).Nodup := by
      rw [hcid]
      exact hnC
    intro cb hcb
    have hcbId : cb.id ∈ child.scene.boxes.map (·.id) :=
      List.mem_map.mpr ⟨cb, hcb, rfl⟩
    rw [hcid] at hcbId
    obtain ⟨m, hmFilt, hmId⟩ := List.mem_map.mp hcbId
    obtain ⟨hmMem, hmInside⟩ := List.mem_filter.mp hmFilt
    have hmParNe : m.parent ≠ "" :=
      inside_parent_ne_empty hnodup hmInside hmMem rfl
    by_cases hpar : (m.parent == group.id) = true
    · have hbeq : m.parent = group.id := beq_iff_eq.mp hpar
      obtain ⟨bx, hbx, hbxpar⟩ :=
        ESS_merged_box_of_inside exactIds hwf hchild hparent hexpand hmMem hmInside
      have hparEqG : bx.parent = group.id := by
        simpa [hpar] using hbxpar
      have hgNe' : group.id ≠ "" := by
        rw [← hbeq]
        exact hmParNe
      refine ⟨[m.id, group.id],
        StepChain.cons ⟨bx, hbx, hparEqG, hgNe'⟩ (StepChain.single group.id),
        ?_, ?_, ?_⟩
      · simp only [List.head?_cons, hmId]
      · simp
      · have hlenC : 1 ≤ child.scene.boxes.length := by
          have hne : child.scene.boxes ≠ [] := List.ne_nil_of_mem hcb
          have hpos : 0 < child.scene.boxes.length := List.length_pos_iff.mpr hne
          omega
        simp only [List.length_cons, List.length_nil]
        omega
    · have hparF : (m.parent == group.id) = false := by
        cases h : (m.parent == group.id) with
        | false => rfl
        | true => exact absurd h hpar
      have hneMP : m.parent ≠ group.id := ESS_ne_of_beq_false hparF
      have hneP : m.parent ≠ "" := hmParNe
      have hev : ∀ b ∈ inp.boxes, b.id = m.parent →
          Compound.inside inp.boxes group.id b.id = true := by
        intro bb hbbmem hbbid
        rcases inside_parent_step hnodup hf.term hmMem hbbmem hbbid hmInside with
          hcon | hpg
        · exact absurd hcon hneMP
        · exact hpg
      have hNlen : inp.boxes.length ≤ inp.boxes.length + 1 := by omega
      have hctMP : chainTerm inp.boxes inp.boxes.length m.parent = true :=
        hf.term m hmMem inp.boxes.length hNlen
      obtain ⟨pre, hPre⟩ := ESS_rootChain_some hf.term hnodup hctMP hneP hev
      obtain ⟨hAlign, hMem, hLink, hLastGroup, hLastEx, _hNe⟩ :=
        ESS_rootChain_props hf.term hnodup hPre hneP hev
      rcases chainWalk_of_chainTerm inp.boxes.length m.parent hctMP with
        hContra | ⟨w, hwWalk, hwLast⟩
      · exact absurd hContra hneP
      · have hwNodup : w.Nodup :=
          chainWalk_nodup inp.boxes.length m.parent w hwWalk hwLast
        have hweq : pre ++
            chainWalk inp.boxes (inp.boxes.length - pre.length) group.id = w :=
          hAlign.symm.trans hwWalk
        rw [← hweq] at hwNodup
        have hPreNodup : pre.Nodup := (List.nodup_append.mp hwNodup).1
        obtain ⟨b₀, restPre, hPreEq, hB0id⟩ := ESS_rootChain_head hPre
        have hmNotPre : m ∉ pre := by
          by_cases hmEmpty : m.id = ""
          · intro hmPre
            have hHead : ∀ c₀ r, pre = c₀ :: r → c₀.id = m.parent := by
              intro c₀ r h
              have h2 : b₀ :: restPre = c₀ :: r := hPreEq.symm.trans h
              have heq : b₀ = c₀ := ESS_cons_head_eq h2
              rw [← heq]
              exact hB0id
            have hall := ESS_chain_all_ids_ne_empty hnodup pre m.parent hneP
              hMem hLink hHead
            have hcon := hall m hmPre
            rw [hmEmpty] at hcon
            exact hcon rfl
          · have hMne : m.id ≠ "" := hmEmpty
            obtain ⟨iM, hfinM, hgetM⟩ := ESS_findIdx_of_mem_box hnodup hmMem
            have hctM : chainTerm inp.boxes (inp.boxes.length + 1) m.id = true := by
              rw [chainTerm.eq_3 inp.boxes m.id inp.boxes.length hMne]
              simp only [hfinM, hgetM]
              exact hctMP
            rcases chainWalk_of_chainTerm (inp.boxes.length + 1) m.id hctM with
              hC | ⟨w2, hw2, hg2⟩
            · exact absurd hC hMne
            · have hw2Nodup :=
                chainWalk_nodup (inp.boxes.length + 1) m.id w2 hw2 hg2
              have hsucc : chainWalk inp.boxes (inp.boxes.length + 1) m.id =
                  m :: w := by
                rw [chainWalk_succ hMne inp.boxes.length]
                simp only [hfinM, hgetM, hwWalk]
              have hweq2 : w2 = m :: w := hw2.symm.trans hsucc
              rw [hweq2] at hw2Nodup
              have hmNotW : m ∉ w := (List.nodup_cons.mp hw2Nodup).1
              intro hmPre
              have hmemW : m ∈ w := by
                rw [← hweq]
                exact List.mem_append_left _ hmPre
              exact hmNotW hmemW
        have hConsNodup : (m :: pre).Nodup :=
          List.nodup_cons.mpr ⟨hmNotPre, hPreNodup⟩
        have hMemCons : ∀ b ∈ m :: pre, b ∈ inp.boxes := by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | h
          · exact hmMem
          · exact (hMem b h).1
        have hMapNodup : ((m :: pre).map (·.id)).Nodup :=
          ESS_nodup_map_id hnodup hMemCons hConsNodup
        have hSub : ∀ x ∈ (m :: pre).map (·.id),
            x ∈ child.scene.boxes.map (·.id) := by
          intro x hx
          obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hx
          have hbBoxes : b ∈ inp.boxes := hMemCons b hb
          have hbIn : Compound.inside inp.boxes group.id b.id = true := by
            rcases List.mem_cons.mp hb with rfl | hpre
            · exact hmInside
            · exact (hMem b hpre).2
          have hmemF : b.id ∈ (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map
              (·.id) :=
            List.mem_map.mpr
              ⟨b, List.mem_filter.mpr ⟨hbBoxes, hbIn⟩, rfl⟩
          rw [← hcid] at hmemF
          rwa [hbid] at hmemF
        have hLe := ESS_nodup_length_le_string ((m :: pre).map (·.id))
          (child.scene.boxes.map (·.id)) hMapNodup hSub hChildNodup
        have hlenPre : pre.length + 1 ≤ child.scene.boxes.length := by
          simpa using hLe
        have hStepPre : ∀ x y xs ys, pre = xs ++ x :: y :: ys →
            (∃ b, res.scene.layoutDump.box? x.id = some b ∧
              b.parent = y.id ∧ y.id ≠ "") := by
          intro x y xs ys hSplit
          have hyx : y.id = x.parent := hLink x y xs ys hSplit
          have hxMem : x ∈ pre := by
            rw [hSplit]
            exact List.mem_append_right _
              (List.mem_cons.mpr (Or.inl rfl))
          have hxBoxes : x ∈ inp.boxes := (hMem x hxMem).1
          have hxIn : Compound.inside inp.boxes group.id x.id = true :=
            (hMem x hxMem).2
          have hxParNe : x.parent ≠ "" :=
            inside_parent_ne_empty hnodup hxIn hxBoxes rfl
          have hNotG : (x.parent == group.id) = false := by
            cases h : (x.parent == group.id) with
            | false => rfl
            | true =>
              exfalso
              have hLastX : pre.getLast? = some x := hLastGroup x hxMem h
              have hEqLast := ESS_getLast_append_cons xs x y ys
              rw [← hSplit] at hEqLast
              have hTailLast : (y :: ys).getLast? = some x :=
                hEqLast.symm.trans hLastX
              have hmemTail : x ∈ y :: ys := ESS_mem_box_of_getLast? _ _ hTailLast
              have hmemHead : x ∈ xs ++ [x] :=
                List.mem_append_right _ (List.mem_singleton.mpr rfl)
              have hPreEq2 : pre = (xs ++ [x]) ++ (y :: ys) := by
                rw [hSplit]
                simp
              rw [hPreEq2] at hPreNodup
              have hDisj := (List.nodup_append.mp hPreNodup).2.2
              exact (hDisj x hmemHead x hmemTail) rfl
          obtain ⟨bx, hbx, hbxpar⟩ :=
            ESS_merged_box_of_inside exactIds hwf hchild hparent hexpand hxBoxes hxIn
          have hparEq : bx.parent = y.id := by
            have h1 : bx.parent = x.parent := by
              simpa [hNotG] using hbxpar
            rw [h1, hyx]
          have hyNe : y.id ≠ "" := by
            rw [hyx]
            exact hxParNe
          exact ⟨bx, hbx, hparEq, hyNe⟩
        have hLastPre : ∀ l, pre.getLast? = some l →
            (∃ b, res.scene.layoutDump.box? l.id = some b ∧
              b.parent = group.id ∧ group.id ≠ "") := by
          intro l hl
          obtain ⟨last, hlast, hparLast⟩ := hLastEx
          have hll : last = l := Option.some.inj (hlast.symm.trans hl)
          subst hll
          have hlastMem : last ∈ pre := ESS_mem_box_of_getLast? pre last hlast
          have hlastBoxes : last ∈ inp.boxes := (hMem last hlastMem).1
          have hlastIn : Compound.inside inp.boxes group.id last.id = true :=
            (hMem last hlastMem).2
          have hlastParNe : last.parent ≠ "" :=
            inside_parent_ne_empty hnodup hlastIn hlastBoxes rfl
          have hbeq : last.parent = group.id := beq_iff_eq.mp hparLast
          have hgNe2 : group.id ≠ "" := by
            rw [← hbeq]
            exact hlastParNe
          obtain ⟨bx, hbx, hbxpar⟩ :=
            ESS_merged_box_of_inside exactIds hwf hchild hparent hexpand hlastBoxes hlastIn
          have hparEq : bx.parent = group.id := by
            simpa [hparLast] using hbxpar
          exact ⟨bx, hbx, hparEq, hgNe2⟩
        have hFirst : ∃ b, res.scene.layoutDump.box? m.id = some b ∧
            b.parent = b₀.id ∧ b₀.id ≠ "" := by
          obtain ⟨bx, hbx, hbxpar⟩ :=
            ESS_merged_box_of_inside exactIds hwf hchild hparent hexpand hmMem hmInside
          have hparEq : bx.parent = b₀.id := by
            have h1 : bx.parent = m.parent := by
              simpa [hparF] using hbxpar
            rw [h1, hB0id]
          have hb0Ne : b₀.id ≠ "" := by
            rw [hB0id]
            exact hneP
          exact ⟨bx, hbx, hparEq, hb0Ne⟩
        have hTail : StepChain
            (fun s t => ∃ b, res.scene.layoutDump.box? s = some b ∧
              b.parent = t ∧ t ≠ "")
            (pre.map (·.id) ++ [group.id]) :=
          ESS_merged_chain_rec
            (R := fun s t => ∃ b, res.scene.layoutDump.box? s = some b ∧
              b.parent = t ∧ t ≠ "")
            pre hStepPre hLastPre
        subst hPreEq
        refine ⟨m.id :: ((((b₀ :: restPre).map (·.id))) ++ [group.id]),
          StepChain.cons hFirst hTail, ?_, ?_, ?_⟩
        · simp only [List.head?_cons, hmId]
        · have hneTail : ((((b₀ :: restPre).map (·.id))) ++ [group.id]) ≠ [] :=
            List.ne_nil_of_mem (List.mem_append_right _
              (List.mem_singleton.mpr rfl))
          rw [List.getLast?_cons_of_ne_nil hneTail]
          exact List.getLast?_eq_some_iff.mpr
            ⟨((b₀ :: restPre).map (·.id)), rfl⟩
        · simp only [List.length_cons, List.length_append, List.length_map,
            List.length_nil] at hlenPre ⊢
          omega

/-- Every embedded child box reaches the group in the merged dump. -/
private theorem ESS_child_ancestors_group (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ∀ cb ∈ child.scene.boxes, group.id ∈ res.scene.layoutDump.ancestors cb.id := by
  obtain ⟨hwf, hgroup, _, hchild, hparent, _⟩ := hctxB
  obtain ⟨hleC, _, _hne⟩ :=
    ESS_merge_bounds exactIds hwf hgroup hchild hparent hexpand
  obtain ⟨frame, _tl, _dx, _dy, hframe, _hdx, _hdy, _htransC, _htransP⟩ :=
    ESS_boxLookup_transport exactIds hwf hchild hparent hexpand
  intro cb hcb
  obtain ⟨c, hchain, hhead, hlast, hclen⟩ := hroot cb hcb
  have hcbne : cb.id ≠ group.id := _hne frame hframe cb hcb
  have htail : group.id ∈ c.tail :=
    ESS_last_mem_tail hlast (ESS_chain_length_ge_two hhead hlast hcbne)
  have hmem := ESS_mem_of_stepChain c hchain cb.id group.id hhead htail
  have hle : c.length - 1 ≤ res.scene.layoutDump.boxes.length := by
    have hM : res.scene.layoutDump.boxes.length = res.scene.boxes.length := rfl
    omega
  exact ESS_ancestors_go_mono hle hmem

/-- Every scope anchor of the expanded group lies on the merged ancestor
chain of every embedded child box. -/
private theorem ESS_merged_anchors_of_child (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ∀ cb ∈ child.scene.boxes,
      ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
        x ∈ res.scene.layoutDump.ancestors cb.id := by
  have hwf := hctxB.1
  have hgroup := hctxB.2.1
  have hchild := hctxB.2.2.2.1
  have hparent := hctxB.2.2.2.2.1
  obtain ⟨frame, _, _, _, hframe, _, _, _, htransP⟩ :=
    ESS_boxLookup_transport exactIds hwf hchild hparent hexpand
  obtain ⟨_, _, hne⟩ :=
    ESS_merge_bounds exactIds hwf hgroup hchild hparent hexpand
  have hsum := ESS_merged_length_sum exactIds hwf hchild hparent hexpand
  have hPdump : parent.scene.layoutDump.boxes.length = parent.scene.boxes.length := rfl
  intro cb hcb x hx
  have h1 := ESS_child_ancestors_group exactIds hexpand hframed hctxB hparams hroot cb hcb
  rcases List.mem_cons.mp hx with h | hxP
  · rw [h]
    exact h1
  · have hxgo : x ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        parent.scene.layoutDump.boxes.length group.id := hxP
    obtain ⟨c₂, hchain₂, hhead₂, hlast₂, hlen₂⟩ := ESS_go_chain_of_mem _ _ _ hxgo
    have hchain₂M := ESS_parent_chain_lift_of_trans htransP hchain₂
    obtain ⟨c₁, hchain₁, hhead₁, hlast₁, hlen₁⟩ := hroot cb hcb
    have hcbne : cb.id ≠ group.id := hne frame hframe cb hcb
    obtain ⟨c, hchain, hhead, hlast, hclen⟩ :=
      ESS_stepChain_concat c₁ c₂ group.id hchain₁ hchain₂M hlast₁ hhead₂
    have hheadX : c.head? = some cb.id := hhead₁ ▸ hhead
    have hlastX : c.getLast? = some x := hlast₂ ▸ hlast
    have htail : x ∈ c.tail :=
      ESS_last_mem_tail hlastX (by
        have hc₁2 := ESS_chain_length_ge_two hhead₁ hlast₁ hcbne
        have hc₂1 := ESS_length_ge_one_of_head? hhead₂
        omega)
    have hmem := ESS_mem_of_stepChain c hchain cb.id x hheadX htail
    have hcb : c.length + 1 ≤
        child.scene.boxes.length + parent.scene.boxes.length + 2 := by
      omega
    have hle : c.length - 1 ≤ res.scene.layoutDump.boxes.length := by
      have hM : res.scene.layoutDump.boxes.length = res.scene.boxes.length := rfl
      omega
    exact ESS_ancestors_go_mono hle hmem

/-- The child-scene route endpoints name child-scene boxes, at the exact base. -/
private theorem ESS_child_route_endpoints (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7RouteEndpoints child := by
  obtain ⟨hwf, _hfind, _hpboxes, hchild, hparent, _⟩ := hctxB
  obtain ⟨frameS, metricS, _tlS, _lS, _dxS, _dyS, _hframeS, hmetricS, htitleS,
    _hlS, _hdxS, _hdyS, _hcS, _hbS⟩ := expandChild_sources hexpand
  obtain ⟨hP, _ht, hwrapE⟩ := hparams
  obtain ⟨metricW, hMW, hTW⟩ := hwrapE
  have hmet : metricS = metricW := Except.ok.inj (hmetricS.symm.trans hMW)
  subst hmet
  have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P metricS titleLines
    child parent hwf hframed hP hmetricS hTW hchild hparent
  exact ESS_mirror_endpoints exactIds fuel _ _ _ hsub.1 hsub.2.1 hchild
private theorem ESS_c6_anchors (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ExpandChildC6Anchors group parent child res := by
  have h2 := ESS_merged_anchors_of_child exactIds hexpand hframed hctxB hparams hroot
  have hend := ESS_child_route_endpoints exactIds hexpand hframed hctxB hparams
  intro rt hrt x hx
  obtain ⟨hmF, _hmT⟩ := hend rt hrt
  obtain ⟨cbf, hmemf, heq⟩ := List.mem_map.mp hmF
  have hmem := h2 cbf hmemf x hx
  rw [heq] at hmem
  exact Or.inl hmem


/-- The expanded group is isolated from the other parent boxes. -/
private theorem ESS_group_isolated (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
    group.id ∉ parent.scene.layoutDump.ancestors pb.id := by
  obtain ⟨hwf, hgroup, hpboxes, _, hparent, _⟩ := hctxB
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hgsel : group ∈ inp.boxes := List.mem_of_find?_eq_some hgroup
  have hpnodup : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hnodup
  intro pb hpb hne
  by_cases hg : group.id = ""
  · rw [hg]
    exact ESS_empty_not_mem_ancestors pb.id
  · intro hmem
    have hxgo : group.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        parent.scene.layoutDump.boxes.length pb.id := hmem
    obtain ⟨c₂, hchain₂, hhead₂, hlast₂, _hlen₂⟩ := ESS_go_chain_of_mem _ _ _ hxgo
    obtain ⟨y, hry, hym⟩ := ESS_stepChain_last_link hchain₂ hhead₂ hlast₂ hne
    obtain ⟨bb, hbbhit, hbbpar, _hbbne⟩ := hry
    have hbbmem : bb ∈ parent.scene.boxes :=
      List.mem_of_find?_eq_some hbbhit
    obtain ⟨sb, hsbmem, _hsbid, hsbpar⟩ :=
      ESS_box_parent exactIds fuel _ _ _ hpnodup hparent bb hbbmem
    rw [hpboxes] at hsbmem
    obtain ⟨m, hmmem, hkeep, _, hmsbpar⟩ :=
      selectInput_box_spec inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
    have hsbpar' : sb.parent = group.id := by
      rw [← hsbpar]
      exact hbbpar
    have hmpar : m.parent = group.id := by
      rw [hmsbpar] at hsbpar'
      by_cases he : m.parent = ""
      · rw [he] at hsbpar' ⊢
        simpa using hsbpar'
      · have hcond : (m.parent == "") = false := by
          cases hbe : (m.parent == "") with
          | true => exact absurd (beq_iff_eq.mp hbe) he
          | false => rfl
        simpa [hcond] using hsbpar'
    have hmne : m.parent ≠ "" := by
      rw [hmpar]
      exact hg
    have hin : Compound.inside inp.boxes group.id m.id = true :=
      inside_of_parent hnodup hgsel hmmem hmpar.symm hmne
    simp [hin] at hkeep

/-- Both C8a ancestry conjuncts for one exact `expandChild` call. -/
private theorem ESS_c8a_ancestry (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ExpandChildC8aAncestry group parent child res := by
  refine ⟨?_, ESS_group_isolated exactIds hexpand hframed hctxB hparams⟩
  intro cb hcb x hx
  exact ESS_merged_anchors_of_child exactIds hexpand hframed hctxB hparams hroot cb hcb x hx

/-- The C6 scope anchors with only the executed-call premises, at the exact base. -/
private theorem ESS_c6_anchors' (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC6Anchors group parent child res :=
  ESS_c6_anchors exactIds hexpand hframed hctxB hparams
    (ESS_childRootChain exactIds hexpand hframed hctxB hparams)

/-- The C8a ancestry conjuncts with only the executed-call premises, at the exact base. -/
private theorem ESS_c8a_ancestry' (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC8aAncestry group parent child res :=
  ESS_c8a_ancestry exactIds hexpand hframed hctxB hparams
    (ESS_childRootChain exactIds hexpand hframed hctxB hparams)
/-- The `stepC6Anchors` seam field holds for every exact `expandChild` call. -/
theorem stepC6Anchors_layoutX (exactIds : List String) :
    RecursiveStepFactsB (layoutX exactIds)
      (fun _ _ _ group _ parent child res =>
        ExpandChildC6Anchors group parent child res) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact ESS_c6_anchors' exactIds hexpand hframed hctxB hparams

/-- The `stepC8aAncestry` seam field holds for every exact `expandChild`
call. -/
theorem stepC8aAncestry_layoutX (exactIds : List String) :
    RecursiveStepFactsB (layoutX exactIds)
      (fun _ _ _ group _ parent child res =>
        ExpandChildC8aAncestry group parent child res) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact ESS_c8a_ancestry' exactIds hexpand hframed hctxB hparams

end PipelineImpl
end Layered
end Elegant
