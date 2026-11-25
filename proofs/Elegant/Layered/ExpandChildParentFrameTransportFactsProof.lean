import Elegant.Layered.Pipeline
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.MergedAncestorsProof
import Elegant.Layered.ExpandChildLabelFactsProof
import Elegant.Layered.ExpandChildParentFramePlacementProof
import Elegant.Layered.RecursiveC6
import Elegant.Layered.BoxRouteIdsDisjoint

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant.Layered.PipelineImpl

 /-!
 # Transport facts for the parent-frame placement residuals.

 Target defs live in `ExpandChildParentFramePlacementProof.lean`.
 Probe evidence is in `proofs/wip/Probe/PfpTransportFactsTProbe.lean`.
 -/

/-- Witness parameters: zero margins so the child scene lands unshifted. -/
private def tptP : Params :=
  { nodePadX := 0, nodePadY := 0, nodeBorder := 0, lineH := 0,
    nodeMinW := 0, nodeMinH := 0, portGap := 0, nodeGap := 0,
    rankGap := 0, slot := 0, cornerRadius := 0, clusterPad := 0,
    clusterBorderW := 0, wrapWidth := 0, canvasMargin := 0 }

private def tptO : Options := {}

private def tptInner : ModelBox := { id := "I", role := .group, parent := "" }
private def tptG : ModelBox := { id := "G", role := .group, parent := "" }

private def tptBoxG : Box :=
  { id := "G", role := "group", rect := ⟨0, 0, 100, 100⟩, parent := "", exclusive := false }
private def tptBoxX : Box :=
  { id := "X", role := "node", rect := ⟨0, 0, 5, 5⟩, parent := "", exclusive := true }
private def tptBoxY : Box :=
  { id := "Y", role := "group", rect := ⟨0, 0, 5, 5⟩, parent := "", exclusive := false }
private def tptBoxI : Box :=
  { id := "I", role := "group", rect := ⟨0, 0, 50, 50⟩, parent := "", exclusive := false }

private def tptLab : Rect := ⟨10, 10, 10, 10⟩

private def tptCl1 : SceneLabel := { id := "L1", owner := "X", rect := tptLab, lines := [], text := "" }
private def tptCl2 : SceneLabel := { id := "L2", owner := "R2", rect := tptLab, lines := [], text := "" }
private def tptCl3 : SceneLabel := { id := "L3", owner := "Y", rect := tptLab, lines := [], text := "" }

private def tptSceneP : Scene :=
  { kind := "flowchart", profile := .vector, options := {}, canvas := ⟨200, 200⟩,
    boxes := [tptBoxG, tptBoxX, tptBoxY, tptBoxI],
    routes := [{ id := "R2", fromId := "X", toId := "X", orthogonal := true, points := [] }],
    labels := [], items := [] }

private def tptSceneC : Scene :=
  { kind := "flowchart", profile := .vector, options := {}, canvas := ⟨200, 200⟩,
    boxes := [],
    routes := [{ id := "R2", fromId := "X", toId := "X", orthogonal := true, points := [] }],
    labels := [tptCl1, tptCl2, tptCl3], items := [] }

private def tptParent : FamilyResult := { scene := tptSceneP, budgetExhausted := false, itemArea := 0 }
private def tptChild : FamilyResult := { scene := tptSceneC, budgetExhausted := false, itemArea := 0 }

private def tptInp : Input :=
  { kind := "flowchart",
    boxes := [{ id := "G", role := .group, parent := "" },
      { id := "X", role := .node, parent := "" },
      { id := "Y", role := .group, parent := "" },
      { id := "I", role := .group, parent := "" }],
    routes := [{ id := "R2", fromId := "X", toId := "X" }],
    texts := ["", "", "", ""], edges := [],
    labels := [{ id := "L1", owner := "X", text := "" },
      { id := "L2", owner := "R2", text := "" },
      { id := "L3", owner := "Y", text := "" }] }

private def tptR2 : Route :=
  { id := "R2", fromId := "X", toId := "X", orthogonal := true, points := [] }

/-- The witness labels sit strictly inside the `G` frame. -/
private theorem tpt_strict : Rect.StrictInside tptBoxG.rect tptLab := by
  decide

/-- The witness call succeeds with the displayed merged scene; ancestor
walks from the kept boxes are empty. Single kernel evaluation. -/
private theorem tpt_all : ∃ res,
    expandChild tptP tptInp tptO tptInner 0 tptParent tptChild = .ok res ∧
    res.scene.boxes = [tptBoxG, tptBoxX, tptBoxY, tptBoxI] ∧
    res.scene.labels = [tptCl1, tptCl2, tptCl3] ∧
    res.scene.routes = [tptR2] ∧
    res.scene.layoutDump.ancestors "X" = [] ∧
    res.scene.layoutDump.ancestors "Y" = [] := ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pfpBoxLabelTransport_false : ¬ PfpBoxLabelTransport := by
  intro h
  obtain ⟨res, hexpand, hboxes, hlabels, hroutes, hancX, hancY⟩ := tpt_all
  have hne : tptInner.id ≠ tptG.id := by decide
  have hframe : res.scene.boxes.find? (fun box => box.id == tptG.id) = some tptBoxG := by
    rw [hboxes]
    rfl
  have hmem : tptCl1 ∈ res.scene.labels := by
    rw [hlabels]
    simp
  have hown : tptCl1.owner ≠ tptG.id := by decide
  have hex : ∃ b ∈ res.scene.boxes, b.id = tptCl1.owner ∧ b.role ≠ "group" :=
    ⟨tptBoxX, by rw [hboxes]; simp, rfl, by decide⟩
  have hnd : tptG.id ∉ res.scene.layoutDump.ancestors tptCl1.owner := by
    show tptG.id ∉ res.scene.layoutDump.ancestors "X"
    rw [hancX]
    simp
  have hbad := h tptP tptInp tptO tptInner tptG 0 tptParent tptChild res hexpand hne
    (fun frame hframe pl hpl hown hex => by
      have : pl ∈ ([] : List SceneLabel) := hpl
      simp at this)
    (fun frame hframe => by
      have hempty : tptChild.scene.boxes.find? (fun box => box.id == tptG.id) =
        (none : Option Box) := rfl
      rw [hempty] at hframe
      simp at hframe)
    tptBoxG hframe tptCl1 hmem hown hex hnd
  exact absurd tpt_strict hbad

theorem pfpRouteLabelTransport_false : ¬ PfpRouteLabelTransport := by
  intro h
  obtain ⟨res, hexpand, hboxes, hlabels, hroutes, hancX, hancY⟩ := tpt_all
  have hne : tptInner.id ≠ tptG.id := by decide
  have hframe : res.scene.boxes.find? (fun box => box.id == tptG.id) = some tptBoxG := by
    rw [hboxes]
    rfl
  have hmem : tptCl2 ∈ res.scene.labels := by
    rw [hlabels]
    simp
  have hown : tptCl2.owner ≠ tptG.id := by decide
  have hnoBox : ∀ b ∈ res.scene.boxes, b.id ≠ tptCl2.owner := by
    intro b hb
    rw [hboxes] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  have hroute : ∀ r ∈ res.scene.routes, r.id = tptCl2.owner →
      (tptG.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
        tptG.id ∉ res.scene.layoutDump.ancestors r.toId) := by
    intro r hr hid
    rw [hroutes] at hr
    simp only [List.mem_singleton] at hr
    subst hr
    left
    show tptG.id ∉ res.scene.layoutDump.ancestors "X"
    rw [hancX]
    simp
  have hbad := h tptP tptInp tptO tptInner tptG 0 tptParent tptChild res hexpand hne
    (fun frame hframe pl hpl hown hnb hr => by
      have : pl ∈ ([] : List SceneLabel) := hpl
      simp at this)
    (fun frame hframe => by
      have hempty : tptChild.scene.boxes.find? (fun box => box.id == tptG.id) =
        (none : Option Box) := rfl
      rw [hempty] at hframe
      simp at hframe)
    tptBoxG hframe tptCl2 hmem hown hnoBox hroute
  exact absurd tpt_strict hbad

theorem pfpTitleLabelTransport_false : ¬ PfpTitleLabelTransport := by
  intro h
  obtain ⟨res, hexpand, hboxes, hlabels, hroutes, hancX, hancY⟩ := tpt_all
  have hne : tptInner.id ≠ tptG.id := by decide
  have hframe : res.scene.boxes.find? (fun box => box.id == tptG.id) = some tptBoxG := by
    rw [hboxes]
    rfl
  have hmem : tptCl3 ∈ res.scene.labels := by
    rw [hlabels]
    simp
  have hown : tptCl3.owner ≠ tptG.id := by decide
  have hex : ∃ b ∈ res.scene.boxes, b.id = tptCl3.owner ∧ b.role = "group" :=
    ⟨tptBoxY, by rw [hboxes]; simp, rfl, rfl⟩
  have hnd : tptG.id ∉ res.scene.layoutDump.ancestors tptCl3.owner := by
    show tptG.id ∉ res.scene.layoutDump.ancestors "Y"
    rw [hancY]
    simp
  have hbad := h tptP tptInp tptO tptInner tptG 0 tptParent tptChild res hexpand hne
    (fun frame hframe pl hpl hown hexg hndg => by
      have : pl ∈ ([] : List SceneLabel) := hpl
      simp at this)
    (fun frame hframe => by
      have hempty : tptChild.scene.boxes.find? (fun box => box.id == tptG.id) =
        (none : Option Box) := rfl
      rw [hempty] at hframe
      simp at hframe)
    tptBoxG hframe tptCl3 hmem hown hex hnd
  exact absurd tpt_strict hbad

/-- Box-class executed-call transport: the box fragment is preserved by an
`expandChild` call the recursion actually makes (context + params + framed),
for result labels on the same side of the split as `G` (inside parity).
Strictly narrower than `PfpBoxLabelTransport` by the call-context
restriction and the same-side premise; cross-side pairs need the open
geometric clearance seams. -/
def PfpBoxLabelTransportCtx : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    framedParents inp = true →
    BoxRouteIdsDisjoint inp →
    ExpandChildCallContext fuel P inp o inner titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o inner titleLines titleHeight →
    inner.id ≠ G.id →
    (∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ G.id →
        (∃ b ∈ parent.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
        (G.id ∉ parent.scene.layoutDump.ancestors pl.owner) →
        ¬ frame.rect.StrictInside pl.rect) →
    (∀ (frame : Box),
      child.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ child.scene.labels, pl.owner ≠ G.id →
        (∃ b ∈ child.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
        (G.id ∉ child.scene.layoutDump.ancestors pl.owner) →
        ¬ frame.rect.StrictInside pl.rect) →
    ∀ (frame : Box),
      res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
        pl.owner ≠ inner.id →
        (Compound.inside inp.boxes inner.id pl.owner =
          Compound.inside inp.boxes inner.id G.id) →
        (∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
        (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
        ¬ frame.rect.StrictInside pl.rect

/-- Route-class executed-call transport: the route fragment is preserved by
an `expandChild` call the recursion actually makes, for result labels on
the same side of the split as `G` (inside parity). Strictly narrower than
`PfpRouteLabelTransport` by the call-context restriction and the same-side
premise; cross-side pairs need the open geometric clearance seams. -/
def PfpRouteLabelTransportCtx : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    framedParents inp = true →
    BoxRouteIdsDisjoint inp →
    ExpandChildCallContext fuel P inp o inner titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o inner titleLines titleHeight →
    inner.id ≠ G.id →
    (∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ G.id →
        (∀ b ∈ parent.scene.boxes, b.id ≠ pl.owner) →
        (∀ r ∈ parent.scene.routes, r.id = pl.owner →
          (G.id ∉ parent.scene.layoutDump.ancestors r.fromId ∨
            G.id ∉ parent.scene.layoutDump.ancestors r.toId)) →
        ¬ frame.rect.StrictInside pl.rect) →
    (∀ (frame : Box),
      child.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ child.scene.labels, pl.owner ≠ G.id →
        (∀ b ∈ child.scene.boxes, b.id ≠ pl.owner) →
        (∀ r ∈ child.scene.routes, r.id = pl.owner →
          (G.id ∉ child.scene.layoutDump.ancestors r.fromId ∨
            G.id ∉ child.scene.layoutDump.ancestors r.toId)) →
        ¬ frame.rect.StrictInside pl.rect) →
    ∀ (frame : Box),
      res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
        pl.owner ≠ inner.id →
        (∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) →
        (∀ r ∈ res.scene.routes, r.id = pl.owner →
          (Compound.inside inp.boxes inner.id r.fromId =
            Compound.inside inp.boxes inner.id G.id) →
          (Compound.inside inp.boxes inner.id r.toId =
            Compound.inside inp.boxes inner.id G.id) →
          (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
            G.id ∉ res.scene.layoutDump.ancestors r.toId)) →
        ¬ frame.rect.StrictInside pl.rect

/-- Title-class executed-call transport: the title fragment is preserved by
an `expandChild` call the recursion actually makes, for result labels on
the same side of the split as `G` (inside parity). Strictly narrower than
`PfpTitleLabelTransport` by the call-context restriction and the same-side
premise. OPEN residual: the group-caption case needs the title-rect
containment geometry (caption rect inside its frame cannot strictly contain
a foreign frame), which is an open geometric seam. -/
def PfpTitleLabelTransportCtx : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    framedParents inp = true →
    BoxRouteIdsDisjoint inp →
    ExpandChildCallContext fuel P inp o inner titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o inner titleLines titleHeight →
    (∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ G.id →
        (∃ b ∈ parent.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
        (G.id ∉ parent.scene.layoutDump.ancestors pl.owner) →
        ¬ frame.rect.StrictInside pl.rect) →
    (∀ (frame : Box),
      child.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ child.scene.labels, pl.owner ≠ G.id →
        (∃ b ∈ child.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
        (G.id ∉ child.scene.layoutDump.ancestors pl.owner) →
        ¬ frame.rect.StrictInside pl.rect) →
    ∀ (frame : Box),
      res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
        pl.owner ≠ inner.id →
        (Compound.inside inp.boxes inner.id pl.owner =
          Compound.inside inp.boxes inner.id G.id) →
        (∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
        (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
        ¬ frame.rect.StrictInside pl.rect

/-- Shifting both rects by the same offset preserves strict containment. -/
private theorem pfpCtx_shift_strictInside (o i : Rect) (dx dy : Int) :
    (shiftRect dx dy o).StrictInside (shiftRect dx dy i) ↔ o.StrictInside i := by
  simp only [Rect.StrictInside, shiftRect]
  omega

/-- Prefixed copy of `sceneOf_label_mem`: every `sceneOf` label comes from
the input label at the same position, keeping id and owner. -/
private theorem pfpCtx_sceneOf_label_mem (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel) :
    ∀ sl ∈ (sceneOf P inp o lines acc measured).labels,
      ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  simp only [sceneOf]
  intro sl hsl
  obtain ⟨q, hq, hmem⟩ := List.mem_filterMap.mp hsl
  obtain ⟨q1, q2⟩ := q
  have key : sl.id = q1.id ∧ sl.owner = q1.owner := by
    dsimp only at hmem
    split at hmem
    · simp at hmem
    · split at hmem
      · next label hfind =>
        have hid : sl.id = q1.id :=
          (congrArg (fun s => s.toLabel.id) (Option.some.inj hmem)).symm
        have hown : sl.owner = q1.owner :=
          (congrArg (fun s => s.toLabel.owner) (Option.some.inj hmem)).symm
        exact ⟨hid, hown⟩
      · next hfind =>
        split at hmem
        · simp at hmem
        · next idx hidx =>
          have hid : sl.id = q1.id :=
            (congrArg (fun s => s.toLabel.id) (Option.some.inj hmem)).symm
          have hown : sl.owner = q1.owner :=
            (congrArg (fun s => s.toLabel.owner) (Option.some.inj hmem)).symm
          exact ⟨hid, hown⟩
  exact ⟨q1, List.fst_mem_of_mem_zipIdx hq, key.1.symm, key.2.symm⟩

/-- Prefixed copy of `layout_label_mem`: flat layouts keep label ids/owners. -/
private theorem pfpCtx_layout_label_mem {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  unfold layout at h
  dsimp only at h
  obtain ⟨P, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨lines, _, h⟩ := bind_ok h
  obtain ⟨measured, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have heq := Except.ok.inj h
    subst heq
    intro sl hsl
    exact pfpCtx_sceneOf_label_mem P inp o lines acc measured sl hsl

/-- Prefixed copy of `expandChild_label_mem`: merged labels keep id/owner
from a child- or parent-scene label. -/
private theorem pfpCtx_expandChild_label_mem
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res) :
    ∀ rl ∈ res.scene.labels,
      ∃ s ∈ child.scene.labels ++ parent.scene.labels,
        rl.id = s.id ∧ rl.owner = s.owner := by
  obtain ⟨frame₀, metric₀, tl₀, _, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _,
    hdx₀, hdy₀, _, _⟩ := expandChild_sources h
  have hwrap : ExpandChildTitleWrapped P inp o group tl₀ := ⟨metric₀, hmetric₀, htitle₀⟩
  have hlabels :=
    expandChild_labels_eq_wrapped h frame₀ tl₀ dx₀ dy₀ hframe₀ hdx₀ hdy₀ hwrap
  intro rl hrl
  rw [hlabels] at hrl
  obtain ⟨model, _, hdo⟩ := List.mem_filterMap.mp hrl
  cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
      { label with rect := shiftRect dx₀ dy₀ label.rect }) ++
      parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) with
  | none => rw [hfind] at hdo; simp at hdo
  | some label =>
    rw [hfind, Option.bind_some] at hdo
    have hif := Option.some.inj hdo
    by_cases hcond : (model.owner == group.id) = true
    · rw [hcond] at hif
      simp only [reduceIte] at hif
      have hid : rl.id = label.id := by rw [← hif]
      have hown : rl.owner = label.owner := by rw [← hif]
      have hmem2 := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hmem2 with hcl | hpl
      · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
        have e1 : label.id = cl.id := by rw [← hclEq]
        have e2 : label.owner = cl.owner := by rw [← hclEq]
        exact ⟨cl, List.mem_append_left _ hclmem, hid.trans e1, hown.trans e2⟩
      · exact ⟨label, List.mem_append_right _ hpl, hid, hown⟩
    · have hcondF : (model.owner == group.id) = false := by
        cases hb : (model.owner == group.id) with
        | false => rfl
        | true => exact absurd hb hcond
      rw [hcondF] at hif
      simp only [Bool.false_eq_true, reduceIte] at hif
      have hid : rl.id = label.id := by rw [← hif]
      have hown : rl.owner = label.owner := by rw [← hif]
      have hmem2 := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hmem2 with hcl | hpl
      · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
        have e1 : label.id = cl.id := by rw [← hclEq]
        have e2 : label.owner = cl.owner := by rw [← hclEq]
        exact ⟨cl, List.mem_append_left _ hclmem, hid.trans e1, hown.trans e2⟩
      · exact ⟨label, List.mem_append_right _ hpl, hid, hown⟩

/-- Prefixed copy of `layoutRecursive_label_mem`: recursive layouts keep
label ids/owners from the input. -/
private theorem pfpCtx_layoutRecursive_label_mem :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res →
      ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h sl hsl
    exact pfpCtx_layout_label_mem h sl hsl
  | succ fuel ih =>
    intro inp o res h sl hsl
    rcases layoutRecursive_succ h with ⟨_, hlayout⟩ |
      ⟨group, _, _, _, child, parent, _, _, _, hchild, hparent, hexpand⟩
    · exact pfpCtx_layout_label_mem hlayout sl hsl
    · obtain ⟨s, hsmem, hsId, hsOwn⟩ := pfpCtx_expandChild_label_mem hexpand sl hsl
      rcases List.mem_append.mp hsmem with hsc | hsp
      · obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := ih _ _ _ hchild s hsc
        have hsub := selectInput_labels_sublist inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
        exact ⟨mc, hsub.subset hmcmem, hmcId.trans hsId.symm, hmcOwn.trans hsOwn.symm⟩
      · obtain ⟨mp, hmpmem, hmpId, hmpOwn⟩ := ih _ _ _ hparent s hsp
        have hsub := selectInput_labels_sublist inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
        exact ⟨mp, hsub.subset hmpmem, hmpId.trans hsId.symm, hmpOwn.trans hsOwn.symm⟩







/-- Parent sub-input boxes lie outside the split group. -/
private theorem pfpCtx_parentBoxOutside {P : Params} {inp : Input} {inner : ModelBox}
    {titleLines : List Measure.Line} {child : FamilyResult} {b : ModelBox}
    (hmem : b ∈ (parentSubInput inp inner P titleLines child).boxes) :
    Compound.inside inp.boxes inner.id b.id = false := by
  simp only [parentSubInput, selectInput] at hmem
  obtain ⟨q, hqmem, hqeq⟩ := List.mem_map.mp hmem
  have hkeep : (fun box : ModelBox => !Compound.inside inp.boxes inner.id box.id) q.1 = true := (List.mem_filter.mp hqmem).2
  have hfalse : Compound.inside inp.boxes inner.id q.1.id = false := by simpa using hkeep
  have hid : b.id = q.1.id := by rw [← hqeq]; split <;> rfl
  rw [hid]; exact hfalse

/-- Child sub-input boxes lie inside the split group. -/
private theorem pfpCtx_childBoxInside {inp : Input} {inner : ModelBox} {b : ModelBox}
    (hmem : b ∈ (childSubInput inp inner).boxes) :
    Compound.inside inp.boxes inner.id b.id = true := by
  simp only [childSubInput, selectInput] at hmem
  obtain ⟨q, hqmem, hqeq⟩ := List.mem_map.mp hmem
  have hkeep : (fun box : ModelBox => Compound.inside inp.boxes inner.id box.id) q.1 = true := (List.mem_filter.mp hqmem).2
  have htrue : Compound.inside inp.boxes inner.id q.1.id = true := hkeep
  have hid : b.id = q.1.id := by rw [← hqeq]; split <;> rfl
  rw [hid]; exact htrue


/-- Inside-true box-owned labels never come from the parent scene. -/
private theorem pfpCtx_box_noParent {fuel : Nat} {o : Options} {P : Params} {inp : Input} {inner : ModelBox} {titleLines : List Measure.Line} {child : FamilyResult} {parent : FamilyResult} (hparent : layoutRecursive fuel (parentSubInput inp inner P titleLines child) o = .ok parent) (hdisjI : BoxRouteIdsDisjoint inp) {label : SceneLabel} (hpm : label ∈ parent.scene.labels) {ownerBox : ModelBox} (hmO : ownerBox ∈ inp.boxes) (hownId : ownerBox.id = label.owner) (hsideO : Compound.inside inp.boxes inner.id label.owner = true) : False := by
  obtain ⟨mp, hmpmem, _, hmpOwn⟩ := pfpCtx_layoutRecursive_label_mem fuel _ _ _ hparent label hpm
  have hflt : mp ∈ inp.labels.filter (fun l => (parentSubInput inp inner P titleLines child).boxes.any (fun b => b.id == l.owner) || (parentSubInput inp inner P titleLines child).routes.any (fun r => r.id == l.owner)) := by simpa [parentSubInput, selectInput] using hmpmem
  rw [List.mem_filter] at hflt
  cases hbox : (parentSubInput inp inner P titleLines child).boxes.any (fun b => b.id == mp.owner) with
  | true =>
    obtain ⟨b, hbmem, hbid⟩ := List.any_eq_true.mp hbox
    have hbeq : b.id = mp.owner := beq_iff_eq.mp hbid
    have hboxmem : b ∈ (parentSubInput inp inner P titleLines child).boxes := hbmem
    have hsideF : Compound.inside inp.boxes inner.id b.id = false := pfpCtx_parentBoxOutside hboxmem
    rw [hbeq, hmpOwn] at hsideF
    rw [hsideO] at hsideF
    simp at hsideF
  | false =>
    have hpred : ((parentSubInput inp inner P titleLines child).boxes.any (fun b => b.id == mp.owner) || (parentSubInput inp inner P titleLines child).routes.any (fun r => r.id == mp.owner)) = true := hflt.2
    rw [hbox] at hpred
    simp only [Bool.false_or] at hpred
    obtain ⟨r, hrmem, hrid⟩ := List.any_eq_true.mp hpred
    have hreq : r.id = mp.owner := beq_iff_eq.mp hrid
    have hrInp : r ∈ inp.routes := (selectInput_routes_sublist inp _ _).subset (by simpa [parentSubInput] using hrmem)
    have hownBox : label.owner ∈ inp.boxes.map (·.id) := List.mem_map.mpr ⟨ownerBox, hmO, hownId⟩
    have hownRoute : label.owner ∈ inp.routes.map (·.id) := by rw [← hmpOwn, ← hreq]; exact List.mem_map.mpr ⟨r, hrInp, rfl⟩
    have hdis := hdisjI _ hownBox
    simp [hownRoute] at hdis

/-- Inside-false box-owned labels never come from the child scene. -/
private theorem pfpCtx_box_noChild {fuel : Nat} {o : Options} {inp : Input} {inner : ModelBox} {child : FamilyResult} (hchild : layoutRecursive fuel (childSubInput inp inner) (childSubOptions o inner) = .ok child) (hdisjI : BoxRouteIdsDisjoint inp) {label : SceneLabel} (hcl : label ∈ child.scene.labels) {ownerBox : ModelBox} (hmO : ownerBox ∈ inp.boxes) (hownId : ownerBox.id = label.owner) (hsideO : Compound.inside inp.boxes inner.id label.owner = false) : False := by
  obtain ⟨mc, hmcmen, _, hmcOwn⟩ := pfpCtx_layoutRecursive_label_mem fuel _ _ _ hchild label hcl
  have hflt : mc ∈ inp.labels.filter (fun l => (childSubInput inp inner).boxes.any (fun b => b.id == l.owner) || (childSubInput inp inner).routes.any (fun r => r.id == l.owner)) := by simpa [childSubInput, selectInput] using hmcmen
  rw [List.mem_filter] at hflt
  obtain ⟨_, hpred⟩ := hflt
  rw [Bool.or_eq_true] at hpred
  rcases hpred with hbox | hroute
  · obtain ⟨b, hbmem, hbid⟩ := List.any_eq_true.mp hbox
    have hbeq : b.id = mc.owner := beq_iff_eq.mp hbid
    have hboxmem : b ∈ (childSubInput inp inner).boxes := hbmem
    have hsideT : Compound.inside inp.boxes inner.id b.id = true := pfpCtx_childBoxInside hboxmem
    rw [hbeq, hmcOwn] at hsideT
    rw [hsideO] at hsideT
    simp at hsideT
  · obtain ⟨r, hrmem, hrid⟩ := List.any_eq_true.mp hroute
    have hreq : r.id = mc.owner := beq_iff_eq.mp hrid
    have hrInp : r ∈ inp.routes := (selectInput_routes_sublist inp _ _).subset (by simpa [childSubInput] using hrmem)
    have hownBox : label.owner ∈ inp.boxes.map (·.id) := List.mem_map.mpr ⟨ownerBox, hmO, hownId⟩
    have hownRoute : label.owner ∈ inp.routes.map (·.id) := by rw [← hmcOwn, ← hreq]; exact List.mem_map.mpr ⟨r, hrInp, rfl⟩
    have hdis := hdisjI _ hownBox
    simp [hownRoute] at hdis

end Elegant.Layered.PipelineImpl
