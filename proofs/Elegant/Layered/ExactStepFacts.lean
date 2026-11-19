import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.ExactPipeline
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveFit
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Pipeline
import Elegant.Layered.RecursiveC78
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.MergedRouteIdsProof
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.SelectInputWellFormed
import Elegant.Layered.MergedAncestorsProof
import Elegant.Layered.RecursiveC7

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Recursion-step facts at the exact base

The `BaseSeams` step fields (`FamilyAssemblyB.lean`) are statements about one
`expandChild` call whose parent and child results come from
`layoutRecursiveB base`.  The plain step seams (`LayeredSeams` fields
`stepC6Geometry`, `stepC6Anchors`, `stepC7Geometry`, `stepC8aGeometry`,
`stepC8bGeometry`, `stepC8aAncestry`) are stated over the plain call context
`ExpandChildCallContext` (which mentions `layoutRecursive`), so they cannot
be applied to an exact call.  This module defines the base-parametric
restatement `RecursiveStepFactsB base`, shows it coincides with the plain
form at `base := layout`, and discharges the `stepC6` seam at
`base := layoutX exactIds` from its two B-form hypotheses.

Base-dependence classification of the plain C6 step pipeline:

* `expandChild` itself, `expandChild_sources`, `expandChild_ids`,
  `expandChild_nodup_map_inj`, `expandChild_nodup_filter_map`,
  `expandChild_find?_filterMap_eq_some`, and all `selectInput` id/filter
  lemmas are base-independent and reused unchanged.
* `layoutRecursive_ids` needs one B-induction (`XB_ids`), from the exact
  leaf id fact (`XB_layout_ids`, the `layout_ids` proof with one extra bind
  for the `exactGraph` step) through the exact successor split (`XB_succ`,
  the `X_B_succ` argument of `ExactSubInputStepC2`).
* `expandChild_selected_ids`, `recursive_selected_box_ids_disjoint`, and
  `expandChild_merge_bounds` copy verbatim with the B-induction swapped in;
  their covering, nodup, and route-membership arguments never inspect the
  base.  The C6 assembler copies verbatim with those two swaps.
-/

/-- The per-expansion step fact at an arbitrary base: the same statement as
`RecursiveStepFacts`, over `ExpandChildCallContextB base`. -/
abbrev RecursiveStepFactsB
    (base : Input → Options → Except LayoutError FamilyResult)
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res

/-- At `base := layout` the B-form is the plain form, by
`expandChildCallContext_iff`. -/
theorem recursiveStepFactsB_layout_iff
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) :
    RecursiveStepFactsB layout Step ↔ RecursiveStepFacts Step := by
  unfold RecursiveStepFactsB RecursiveStepFacts
  constructor
  · intro h fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hctx hparams
    exact h fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      ((expandChildCallContext_iff fuel P inp o group titleLines titleHeight parent child
        res).mp hctx)
      hparams
  · intro h fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hctxB hparams
    exact h fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      ((expandChildCallContext_iff fuel P inp o group titleLines titleHeight parent child
        res).mpr hctxB)
      hparams

/-- Successor split for `layoutRecursiveB` at the exact base, in the shape of
`layoutRecursive_succ`: the concrete appended tables are generalized to
`∃ a b c` so the induction proofs below copy the plain ones verbatim. -/
private theorem XB_succ (exactIds : List String) {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (h : layoutRecursiveB (layoutX exactIds) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      layoutX exactIds inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (layoutX exactIds) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
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
call as `layout`, so the proof is `layout_ids` with one extra bind for the
`exactGraph` step. -/
private theorem XB_layout_ids {exactIds : List String} {inp : Input} {o : Options}
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
layout are the sub-input ids.  Copies `layoutRecursive_ids` with `XB_succ`
and the exact leaf fact. -/
private theorem XB_ids (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    RoutesCovered inp → layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero => intro inp o res _ h; exact XB_layout_ids h
  | succ fuel ih =>
    intro inp o res hc h
    rcases XB_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, hexp⟩
    · exact XB_layout_ids hlayout
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
disjoint halves of the input ids.  Copies `expandChild_selected_ids` with
`XB_ids`. -/
private theorem XB_selected_ids (exactIds : List String)
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
  have hchildIds := XB_ids exactIds fuel _ _ _ hchildCov hchild
  have hparentIds := XB_ids exactIds fuel _ _ _ hparentCov hparent
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

/-- Scene ids of the two exact sub-layouts are disjoint.  Copies
`recursive_selected_box_ids_disjoint` with `XB_ids`. -/
private theorem XB_disjoint (exactIds : List String)
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
  have hc := XB_ids exactIds fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := XB_ids exactIds fuel _ _ _ hparentCoverage hparent
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
the two scene-size bounds and the child/group id isolation.  Copies
`expandChild_merge_bounds` with `XB_ids` and `XB_disjoint`. -/
private theorem XB_merge_bounds (exactIds : List String)
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
  have hchildIds := XB_ids exactIds fuel _ _ _ hchildCov hchild
  have hparentIds := XB_ids exactIds fuel _ _ _ hparentCov hparent
  have hdisjoint := XB_disjoint exactIds hchild hparent
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

/-- The C6 step of one exact `expandChild` call, from the B-geometry and
B-anchor remainders.  Copies `expandChild_c6_step_of_geometry` with the
B-selected-ids and B-merge-bounds swaps. -/
private theorem XB_c6_step_of_geometry (exactIds : List String)
    (hgeoC6 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Geometry P inp o group titleHeight parent child res)
    (hanchorC6 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Anchors group parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  have hanch := hanchorC6 fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hgeo := hgeoC6 fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctx
  intro frame metric tl _lines dx dy hframe hmetric htitle _hlines hdx hdy
  have hwrap : ExpandChildTitleWrapped P inp o group tl := ⟨metric, hmetric, htitle⟩
  obtain ⟨frame₀, metric₀, tl₀, _lines₀, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _hlines₀,
    hdx₀, hdy₀, _hcanvas, hboxes⟩ := expandChild_sources hexpand'
  have hff : frame₀ = frame := Option.some.inj (hframe₀.symm.trans hframe)
  rw [hff] at hdx₀ hdy₀
  have hmetricEq : metric = metric₀ := Except.ok.inj (hmetric.symm.trans hmetric₀)
  rw [hmetricEq] at htitle
  have htl : tl = tl₀ := Except.ok.inj (htitle.symm.trans htitle₀)
  rw [← htl] at hdx₀ hdy₀
  have hdxEq : dx = dx₀ := by omega
  have hdyEq : dy = dy₀ := by omega
  rw [← hdxEq, ← hdyEq] at hboxes
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ := XB_selected_ids exactIds hwf hchild hparent
  have hb := XB_merge_bounds exactIds hwf hgroup hchild hparent hexpand'
  obtain ⟨hg1, hg2⟩ := hgeo frame tl dx dy hframe hdx hdy hwrap
  refine ⟨?_, ?_, hb.1, hb.2.1, hg1, hg2, hanch⟩
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
    · intro m' _hm' z hz hzid
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
    · intro m' _hm' z hz hzid
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

/-- The `stepC6` seam of `BaseSeams` at `base := layoutX exactIds`: every
`expandChild` call the exact recursion performs satisfies `ExpandChildC6Step`.
The binders match `FamilyAssemblyB.lean` `stepC6` lines 85-94.  Discharged
from the B-form geometry and anchor hypotheses; the residual plain proofs to
redo at the exact base are `expandChild_c6_geometry` (pure rectangle glue,
no flat `layout` facts) and `expandChild_c6_anchors` (via
`expandChild_merged_anchors_of_child` and `expandChild_child_route_endpoints`,
which use the flat `layout_ids` through `layoutRecursive_ids` and
`layoutRecursive_scene_mirror`). -/
theorem stepC6_layoutX (exactIds : List String)
    (hgeoC6B : RecursiveStepFactsB (layoutX exactIds) ExpandChildC6Geometry)
    (hanchC6B : RecursiveStepFactsB (layoutX exactIds)
      (fun _ _ _ group _ parent child res => ExpandChildC6Anchors group parent child res)) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams
  exact XB_c6_step_of_geometry exactIds hgeoC6B hanchC6B fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
/-- Exact leaf mirror fact (box-parent copy): every exact scene box carries
the id and parent pointer of a source input box.  Copy of the private
`X_layout_box_parent` in `ExactSubInputStepC2.lean`. -/
private theorem XB_layout_box_parent {exactIds : List String} {inp : Input} {o : Options}
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

/-- Exact `B`-recursion mirror fact: every scene box of a successful exact
recursive layout carries the id and parent pointer of a source input box.
Copy of the private `X_rec_box_parent` in `ExactSubInputStepC2.lean`. -/
private theorem XB_box_parent (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact XB_layout_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases XB_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact XB_layout_box_parent hlayout
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

/-- Exact leaf role fact: every exact scene box carries the role of a source
input box.  Same `sceneOf` unfolding as `XB_layout_box_parent`; the role
rides in the second tuple component. -/
private theorem XB_layout_role {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.role = sb.role.id := by
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

/-- Role transport through `selectInput`: kept boxes keep their role (only
the parent pointer is rewritten). -/
private theorem XB_selectInput_box_role (inp : Input) (keep : ModelBox → Bool) (root : String)
    {b : ModelBox} (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧ b.role = m.role := by
  unfold selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  exact ⟨q.1, List.fst_mem_of_mem_zipIdx hqzip, hkq, by rw [← hbq]; split <;> rfl,
    by rw [← hbq]; split <;> rfl⟩

/-- Exact `B`-recursion role mirror: every scene box of a successful exact
recursive layout carries the role of a source input box.  Same induction as
`XB_box_parent` without the parent-pointer reasoning; `embedBox` preserves
roles. -/
private theorem XB_role_mirror (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ bb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = bb.id ∧ bb.role = sb.role.id := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact XB_layout_role h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases XB_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact XB_layout_role hlayout
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
      have hchildRole := ih _ _ _ hchildNodup hchild
      have hparentRole := ih _ _ _ hparentNodup hparent
      obtain ⟨_frame, _metric', _titleLines', _lines, dx, dy, _hframe, _hmetric',
        _htitle', _hlines', _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
      intro bb hbb
      rw [hboxes] at hbb
      obtain ⟨_model, _hmodelmem, hfind⟩ := List.mem_filterMap.mp hbb
      have hbbItems : bb ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hbbItems with hbc | hbp
      · obtain ⟨cbb, hcbbmem, hEmbed⟩ := List.mem_map.mp hbc
        obtain ⟨sb, hsbmem, hsbid, hsrole⟩ := hchildRole cbb hcbbmem
        obtain ⟨m, hmmem, _hkeep, hmsbid, hmsbrole⟩ := XB_selectInput_box_role inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
        refine ⟨m, hmmem, ?_, ?_⟩
        · have hcid : cbb.id = bb.id := by
            have h := congrArg (fun b : Box => b.id) hEmbed
            simpa [embedBox] using h
          exact hmsbid.symm.trans (hsbid.trans hcid)
        · have hcrole : cbb.role = bb.role := by
            have h := congrArg (fun b : Box => b.role) hEmbed
            simpa [embedBox] using h
          rw [← hcrole, hsrole, hmsbrole]
      · obtain ⟨sb, hsbmem, hsbid, hsrole⟩ := hparentRole bb hbp
        obtain ⟨m, hmmem, _hkeep, hmsbid, hmsbrole⟩ := XB_selectInput_box_role inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · rw [hsrole, hmsbrole]

/-- The shared core of one exact `expandChild` call: box-lookup transports,
scene-size bounds, the frame's `"group"` role, and child/group id isolation.
Copies `expandChild_core_wrapped` with the B-swaps; the frame role comes
from the exact role mirror and the source chain instead of the flat
fixed-source fact. -/
private theorem XB_core_wrapped (exactIds : List String)
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
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some b) ∧
      child.scene.boxes.length ≤ res.scene.boxes.length ∧
      parent.scene.boxes.length ≤ res.scene.boxes.length ∧
      frame.role = "group" ∧
      (∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  obtain ⟨frame₀, metric₀, tl₀, _lines₀, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _hlines₀,
    hdx₀, hdy₀, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  have hff : frame₀ = frame := Option.some.inj (hframe₀.symm.trans hframe)
  rw [hff] at hdx₀ hdy₀
  obtain ⟨metricW, hmetricW, hwrapW⟩ := hwrap
  have hmetricEq : metricW = metric₀ := Except.ok.inj (hmetricW.symm.trans hmetric₀)
  rw [hmetricEq] at hwrapW
  have htl : tl = tl₀ := Except.ok.inj (hwrapW.symm.trans htitle₀)
  rw [← htl] at hdx₀ hdy₀
  have hdxEq : dx = dx₀ := by omega
  have hdyEq : dy = dy₀ := by omega
  rw [← hdxEq, ← hdyEq] at hboxes
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ :=
    XB_selected_ids exactIds hwf hchild hparent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact (XB_merge_bounds exactIds hwf hgroup hchild hparent hexpand).1
  · exact (XB_merge_bounds exactIds hwf hgroup hchild hparent hexpand).2.1
  · -- the frame's role, from the exact role mirror and the source chain
    have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
    have hparentNodup : ((parentSubInput inp group P titleLines child).boxes.map (·.id)).Nodup := by
      show ((selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)).Nodup
      rw [selectInput_box_ids]
      exact List.Nodup.sublist ((List.filter_sublist).map _) hids
    obtain ⟨source, hsource, hsbid, hsrole⟩ := XB_role_mirror exactIds fuel _ _ _
      hparentNodup hparent frame (List.mem_of_find?_eq_some hframe)
    have hsourceId : source.id = group.id := hsbid.trans hframeId
    have hsourceBase : source ∈ (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := hsource
    obtain ⟨original, horiginal, _hkeep, hsourceEq⟩ :=
      selectInput_box_source inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" source hsourceBase
    have horiginalId : original.id = group.id := by
      have h1 : original.id = source.id := by
        rw [hsourceEq]
        split <;> rfl
      exact h1.trans hsourceId
    have horiginalEq : original = group :=
      expandChild_nodup_map_inj (·.id) hids horiginal
        (List.mem_of_find?_eq_some hgroup) horiginalId
    have hsourceRole : source.role = group.role := by
      rw [hsourceEq]
      split <;> simp only [horiginalEq]
    have hgroupRole : group.role = .group := by
      have hs := List.find?_some hgroup
      simp only [Bool.and_eq_true] at hs
      have hi := hs.1
      unfold Compound.independent at hi
      simp only [Bool.and_eq_true] at hi
      exact beq_iff_eq.mp hi.1.1
    rw [hsrole, hsourceRole, hgroupRole]
    rfl
  · exact (XB_merge_bounds exactIds hwf hgroup hchild hparent hexpand).2.2 frame hframe

/-- The C8a structure of one exact `expandChild` call: the shared core plus
the split-out ancestry residual.  Copies `expandChild_c8a_structure_wrapped`. -/
private theorem XB_c8a_structure_wrapped (exactIds : List String)
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
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hanc : ExpandChildC8aAncestry group parent child res) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some b) ∧
      child.scene.boxes.length ≤ res.scene.boxes.length ∧
      parent.scene.boxes.length ≤ res.scene.boxes.length ∧
      frame.role = "group" ∧
      (∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) ∧
      ExpandChildC8aAncestry group parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hcore := XB_core_wrapped exactIds hwf hgroup hchild hparent hexpand
    frame tl dx dy hframe hdx hdy hwrap
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
    hcore.2.2.2.2.2, hanc⟩

/-- The `hstructC8a` B-premise: the C8a structure of every exact
`expandChild` call, discharged from the wrapped core and the ancestry
hypothesis.  Copies `expandChild_c8a_structure`. -/
private theorem XB_c8a_structure (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (hanc : ExpandChildC8aAncestry group parent child res) :
    ExpandChildC8aStructure P inp o group titleHeight parent child res := by
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctxB
  exact XB_c8a_structure_wrapped exactIds hwf hgroup hchild hparent hexpand' hanc

/-- The C8a step assembler at the exact base: every exact `expandChild` call
satisfying the B-geometry and B-structure satisfies `ExpandChildC8aStep`.
Copies `expandChild_c8a_step_of_geometry` (its proof never inspects the
context). -/
private theorem XB_c8a_step_of_geometry (exactIds : List String)
    (hgeoC8a : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res)
    (hstructC8a : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStructure P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    hstructC8a fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨s1, s2, s3, s4, s5, s6,
    hgeoC8a fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap,
    s7, s8⟩

/-- The `stepC8a` seam of `BaseSeams` at `base := layoutX exactIds`: every
`expandChild` call the exact recursion performs satisfies `ExpandChildC8aStep`.
The binders match `FamilyAssemblyB.lean` `stepC8a` lines 105-114. -/
theorem stepC8a_layoutX (exactIds : List String)
    (hgeoC8aB : RecursiveStepFactsB (layoutX exactIds) ExpandChildC8aGeometry)
    (hancC8aB : RecursiveStepFactsB (layoutX exactIds)
      (fun _ _ _ group _ parent child res => ExpandChildC8aAncestry group parent child res)) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams
  exact XB_c8a_step_of_geometry exactIds hgeoC8aB
    (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hctxB hparams =>
      XB_c8a_structure exactIds fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctxB
        (hancC8aB fuel P inp o group titleLines titleHeight parent child res hexpand hframed
          hctxB hparams))
    fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctxB hparams



/-- Exact leaf label fact: every exact scene label comes from an input label
with the same id and owner.  `layoutX` feeds the same `sceneOf` call as
`layout`, so the proof is `layout_label_mem` with one extra bind for the
`exactGraph` step, closed by the public `sceneOf_label_mem`. -/
private theorem XB_layout_label_mem {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨P, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨lines, _, h⟩ := bind_ok h
  obtain ⟨measured, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have heq := Except.ok.inj h
    subst heq
    intro sl hsl
    exact sceneOf_label_mem P inp o lines acc measured sl hsl

/-- A successful exact `expandChild` labels every merged label from a
child- or parent-scene label, keeping id and owner.  Copies the private
`expandChild_label_mem` (base-independent: only `expandChild_sources` and
the label-list equation). -/
private theorem XB_expandChild_label_mem {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int} {parent child res : FamilyResult}
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

/-- Labels of a successful exact recursive layout come from input labels
with the same id and owner.  Copies `layoutRecursive_label_mem` with
`XB_succ` and the exact leaf/expansion facts. -/
private theorem XB_label_mem (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h sl hsl
    exact XB_layout_label_mem h sl hsl
  | succ fuel ih =>
    intro inp o res h sl hsl
    rcases XB_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _, _, _, child, parent, _, _, _, hchild, hparent, hexpand⟩
    · exact XB_layout_label_mem hlayout sl hsl
    · obtain ⟨s, hsmem, hsId, hsOwn⟩ := XB_expandChild_label_mem hexpand sl hsl
      rcases List.mem_append.mp hsmem with hsc | hsp
      · obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := ih _ _ _ hchild s hsc
        have hsub := selectInput_labels_sublist inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
        exact ⟨mc, hsub.subset hmcmem, hmcId.trans hsId.symm, hmcOwn.trans hsOwn.symm⟩
      · obtain ⟨mp, hmpmem, hmpId, hmpOwn⟩ := ih _ _ _ hparent s hsp
        have hsub := selectInput_labels_sublist inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
        exact ⟨mp, hsub.subset hmpmem, hmpId.trans hsId.symm, hmpOwn.trans hsOwn.symm⟩

/-- The label-owner invariant of one exact `expandChild` call: labels of
both exact recursive sub-scenes carry the owner of the input label with the
same id.  Copies `expandChild_label_owners` with `XB_label_mem`. -/
private theorem XB_label_owners (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildLabelOwners inp parent child := by
  obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctxB
  have hnodup : (inp.labels.map (·.id)).Nodup := labelIds_nodup hwf
  have hmemC := XB_label_mem exactIds _ _ _ _ hchild
  have hmemP := XB_label_mem exactIds _ _ _ _ hparent
  have hsubC := selectInput_labels_sublist inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hsubP := selectInput_labels_sublist inp
    (fun box => !Compound.inside inp.boxes group.id box.id) ""
  constructor
  · intro cl hcl m hm heq
    obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := hmemC cl hcl
    have hmcIn : mc ∈ inp.labels := hsubC.subset hmcmem
    have heq' : m.id = mc.id := heq.trans hmcId.symm
    have hmmc : m = mc := expandChild_nodup_map_inj (·.id) hnodup hm hmcIn heq'
    rw [hmmc]
    exact hmcOwn
  · intro pl hpl m hm heq
    obtain ⟨mp, hmpmem, hmpId, hmpOwn⟩ := hmemP pl hpl
    have hmpIn : mp ∈ inp.labels := hsubP.subset hmpmem
    have heq' : m.id = mp.id := heq.trans hmpId.symm
    have hmmp : m = mp := expandChild_nodup_map_inj (·.id) hnodup hm hmpIn heq'
    rw [hmmp]
    exact hmpOwn

/-- The `hstructC8b` B-premise: the C8b structure of every exact
`expandChild` call, from the label classification under the label-owner
invariant.  The wrapped lemma is base-independent, so the plain one is
reused directly. -/
private theorem XB_c8b_structure (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (howners : ExpandChildLabelOwners inp parent child) :
    ExpandChildC8bStructure P inp o group titleHeight parent child res := by
  obtain ⟨_hwf, _hgroup, _hpboxes, _hchild, _hparent, hexpand'⟩ := hctxB
  exact expandChild_c8b_structure_wrapped hexpand' howners

/-- The C8b step assembler at the exact base.  Copies
`expandChild_c8b_step_of_geometry` (its proof never inspects the context). -/
private theorem XB_c8b_step_of_geometry (exactIds : List String)
    (hgeoC8b : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bGeometry P inp o group titleHeight parent child res)
    (hstructC8b : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStructure P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨g1, g2, g3, g4⟩ :=
    hgeoC8b fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨hstructC8b fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap, g1, g2, g3, g4⟩

/-- The `stepC8b` seam of `BaseSeams` at `base := layoutX exactIds`: every
`expandChild` call the exact recursion performs satisfies `ExpandChildC8bStep`.
The binders match `FamilyAssemblyB.lean` `stepC8b` lines 115-124. -/
theorem stepC8b_layoutX (exactIds : List String)
    (hgeoC8bB : RecursiveStepFactsB (layoutX exactIds) ExpandChildC8bGeometry) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      InputFixedFit inp o →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    _hfix hctxB hparams
  exact XB_c8b_step_of_geometry exactIds hgeoC8bB
    (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hctxB hparams =>
      XB_c8b_structure exactIds fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctxB
        (XB_label_owners exactIds fuel P inp o group titleLines titleHeight parent child
          res hexpand hframed hctxB hparams))
    fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctxB hparams



/-- Exact flat scene mirror: every exact scene route's endpoints name scene
boxes, and every exact scene label comes from an input label.  Copies the
private `layout_scene_mirror`, closed by the public `sceneOf_label_mem`. -/
private theorem XB_layout_mirror (exactIds : List String) {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : layoutX exactIds inp o = .ok res) :
    (∀ rt ∈ res.scene.routes,
      rt.fromId ∈ res.scene.boxes.map (·.id) ∧ rt.toId ∈ res.scene.boxes.map (·.id)) ∧
    (∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner) := by
  have hcov : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hids := XB_layout_ids h
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

/-- Exact `B`-recursion endpoint mirror: every scene route's endpoints name
scene boxes.  Copies the endpoint half of `layoutRecursive_scene_mirror`. -/
private theorem XB_mirror_endpoints (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
    ∀ rt ∈ res.scene.routes,
      rt.fromId ∈ res.scene.boxes.map (·.id) ∧ rt.toId ∈ res.scene.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf _hframed h
    exact (XB_layout_mirror exactIds hwf h).1
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨hn, hlayout⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, hexpand⟩
    · exact (XB_layout_mirror exactIds hwf hlayout).1
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
      have hchildIds := XB_ids exactIds fuel _ _ _ hcovC hchildB
      have hparentIds := XB_ids exactIds fuel _ _ _ hcovP hparentB
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
parent box to itself, at the exact base.  Copies
`expandChild_boxLookup_transport` with `XB_selected_ids`. -/
private theorem XB_boxLookup_transport (exactIds : List String)
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
    XB_selected_ids exactIds hwf hchild hparent
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

/-- One unfolded step of the ancestor walk.  Copy of the private `go_succ`. -/
private theorem XB_go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty.  Copy of `go_none`. -/
private theorem XB_go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty.  Copy of `go_root`. -/
private theorem XB_go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- A `box?` hit names its own id.  Copy of `box_id_of_box_some`. -/
private theorem XB_box_id_of_box_some {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : b.id = s := by
  simp only [LayoutDump.box?] at h
  have hpred := List.find?_some h
  have htrue : (b.id == s) = true := hpred
  exact beq_iff_eq.mp htrue

/-- Parent walks reproduce link for link in the merged dump.  Copy of the
private `parent_go_prefix`. -/
private theorem XB_parent_go_prefix {dP dM : LayoutDump}
    (htrans : ∀ b : Box, dP.box? b.id = some b → dM.box? b.id = some b)
    (k : Nat) : ∀ (m : Nat) (s : String), k ≤ m →
    ∃ suf, LayoutDump.ancestors.go dM m s =
      LayoutDump.ancestors.go dP k s ++ suf := by
  induction k with
  | zero =>
    intro m s _
    refine ⟨LayoutDump.ancestors.go dM m s, ?_⟩
    have h0 : LayoutDump.ancestors.go dP 0 s = [] := by
      simp only [LayoutDump.ancestors.go]
    rw [h0, List.nil_append]
  | succ k ih =>
    intro m s hle
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases hP : dP.box? s with
    | none =>
      refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
      have h0 : LayoutDump.ancestors.go dP (k + 1) s = [] := XB_go_none hP
      rw [h0, List.nil_append]
    | some b =>
      by_cases hpar : b.parent = ""
      · refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
        have h0 : LayoutDump.ancestors.go dP (k + 1) s = [] := XB_go_root hP hpar
        rw [h0, List.nil_append]
      · have hbid : b.id = s := XB_box_id_of_box_some hP
        have hMs : dM.box? s = some b := by
          have h2 := htrans b (by rw [hbid]; exact hP)
          rwa [hbid] at h2
        have eP : LayoutDump.ancestors.go dP (k + 1) s =
            b.parent :: LayoutDump.ancestors.go dP k b.parent :=
          XB_go_succ hP hpar
        have eM : LayoutDump.ancestors.go dM (m' + 1) s =
            b.parent :: LayoutDump.ancestors.go dM m' b.parent :=
          XB_go_succ hMs hpar
        have hle' : k ≤ m' := by omega
        obtain ⟨suf, hsuf⟩ := ih m' b.parent hle'
        refine ⟨suf, ?_⟩
        rw [eM, eP, hsuf, List.cons_append]

/-- Child walks reproduce link for link in the merged dump until the child
root.  Copy of the private `child_go_prefix`. -/
private theorem XB_child_go_prefix {dC dM : LayoutDump} (groupId : String)
    (dx dy : Int)
    (htrans : ∀ b : Box, dC.box? b.id = some b →
      dM.box? b.id = some (embedBox groupId dx dy b))
    (k : Nat) : ∀ (m : Nat) (s : String), k ≤ m →
    ∃ suf, LayoutDump.ancestors.go dM m s =
      LayoutDump.ancestors.go dC k s ++ suf := by
  induction k with
  | zero =>
    intro m s _
    refine ⟨LayoutDump.ancestors.go dM m s, ?_⟩
    have h0 : LayoutDump.ancestors.go dC 0 s = [] := by
      simp only [LayoutDump.ancestors.go]
    rw [h0, List.nil_append]
  | succ k ih =>
    intro m s hle
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases hC : dC.box? s with
    | none =>
      refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
      have h0 : LayoutDump.ancestors.go dC (k + 1) s = [] := XB_go_none hC
      rw [h0, List.nil_append]
    | some b =>
      by_cases hpar : b.parent = ""
      · refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
        have h0 : LayoutDump.ancestors.go dC (k + 1) s = [] := XB_go_root hC hpar
        rw [h0, List.nil_append]
      · have hbid : b.id = s := XB_box_id_of_box_some hC
        have hMb : dM.box? s = some (embedBox groupId dx dy b) := by
          have h2 := htrans b (by rw [hbid]; exact hC)
          rwa [hbid] at h2
        have hcond : (b.parent == "") = false := by
          cases hc : (b.parent == "") with
          | true => exact absurd (beq_iff_eq.mp hc) hpar
          | false => rfl
        have hparE : (embedBox groupId dx dy b).parent = b.parent := by
          simp [embedBox, hcond]
        have hneE : (embedBox groupId dx dy b).parent ≠ "" := by
          rw [hparE]; exact hpar
        have eC : LayoutDump.ancestors.go dC (k + 1) s =
            b.parent :: LayoutDump.ancestors.go dC k b.parent :=
          XB_go_succ hC hpar
        have eM : LayoutDump.ancestors.go dM (m' + 1) s =
            (embedBox groupId dx dy b).parent ::
              LayoutDump.ancestors.go dM m' (embedBox groupId dx dy b).parent :=
          XB_go_succ hMb hneE
        have hle' : k ≤ m' := by omega
        obtain ⟨suf, hsuf⟩ := ih m' b.parent hle'
        refine ⟨suf, ?_⟩
        rw [eM, eC, hparE, hsuf, List.cons_append]

/-- Ancestor chains of both exact sub-dumps are contained in the merged
dump's chain for the same id.  Copies `expandChild_ancestor_mono`. -/
private theorem XB_ancestor_mono (exactIds : List String)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {fuel : Nat} {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7AncestorMono parent child res := by
  obtain ⟨hwf, hgroup, _hboxes, hchild, hparent, _hexpand2⟩ := hctxB
  obtain ⟨_frame, _tl, dx, dy, _hframe, _hdx, _hdy, htransC, htransP⟩ :=
    XB_boxLookup_transport exactIds hwf hchild hparent hexpand
  obtain ⟨hleC, hleP, _hne⟩ :=
    XB_merge_bounds exactIds hwf hgroup hchild hparent hexpand
  have hleP' : (parent.scene.layoutDump).boxes.length ≤
      (res.scene.layoutDump).boxes.length := hleP
  have hleC' : (child.scene.layoutDump).boxes.length ≤
      (res.scene.layoutDump).boxes.length := hleC
  constructor
  · intro id x hx
    have hx' : x ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        (parent.scene.layoutDump).boxes.length id := hx
    obtain ⟨suf, hsuf⟩ := XB_parent_go_prefix htransP _ _ id hleP'
    show x ∈ LayoutDump.ancestors.go res.scene.layoutDump
      (res.scene.layoutDump).boxes.length id
    rw [hsuf]
    exact List.mem_append.mpr (Or.inl hx')
  · intro id x hx
    have hx' : x ∈ LayoutDump.ancestors.go child.scene.layoutDump
        (child.scene.layoutDump).boxes.length id := hx
    obtain ⟨suf, hsuf⟩ := XB_child_go_prefix group.id dx dy htransC _ _ id hleC'
    show x ∈ LayoutDump.ancestors.go res.scene.layoutDump
      (res.scene.layoutDump).boxes.length id
    rw [hsuf]
    exact List.mem_append.mpr (Or.inl hx')

/-- Exact scene route ids of the two sub-layouts are disjoint.  Copies
`recursive_selected_route_ids_disjoint_of_route_ids_nodup`. -/
private theorem XB_routedisjoint_of (exactIds : List String)
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hrouteIds : (inp.routes.map (·.id)).Nodup)
    (hchild : layoutRecursiveB (layoutX exactIds) fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.routes.map (·.id), id ∉ parent.scene.routes.map (·.id) := by
  have hc := XB_ids exactIds fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := XB_ids exactIds fuel _ _ _ hparentCoverage hparent
  have hpRoutes := hp.2
  change parent.scene.routes.map (·.id) =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).routes.map
      (·.id) at hpRoutes
  intro id hchildId hparentId
  rw [hc.2] at hchildId
  rw [hpRoutes] at hparentId
  obtain ⟨childRoute, hchildRoute, hchildRouteId⟩ := List.mem_map.mp hchildId
  obtain ⟨parentRoute, hparentRoute, hparentRouteId⟩ := List.mem_map.mp hparentId
  have hcMem := (selectInput_route_mem inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id childRoute).mp hchildRoute
  have hpMem := (selectInput_route_mem inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" parentRoute).mp hparentRoute
  have hnodup : (inp.routes.map (·.id)).Nodup := hrouteIds
  have hsame : childRoute = parentRoute :=
    expandChild_nodup_map_inj (·.id) hnodup hcMem.1 hpMem.1
      (hchildRouteId.trans hparentRouteId.symm)
  have hcCovered := selectInput_routesCovered inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id childRoute hchildRoute
  have hpCovered := selectInput_routesCovered inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" parentRoute hparentRoute
  obtain ⟨childBox, hchildBox, hchildBoxId⟩ := hcCovered.1
  obtain ⟨parentBox, hparentBox, hparentBoxId⟩ := hpCovered.1
  have hcBoxId : childRoute.fromId ∈ child.scene.boxes.map (·.id) := by
    rw [hc.1]
    exact List.mem_map.mpr ⟨childBox, hchildBox, hchildBoxId⟩
  have hpBoxId : childRoute.fromId ∈ parent.scene.boxes.map (·.id) := by
    rw [hp.1]
    change childRoute.fromId ∈
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).boxes.map (·.id)
    rw [hsame]
    exact List.mem_map.mpr ⟨parentBox, hparentBox, hparentBoxId⟩
  exact XB_disjoint exactIds hchild hparent childRoute.fromId hcBoxId hpBoxId

/-- Exact wrapper: route ids of the two sub-layouts are disjoint. -/
private theorem XB_routedisjoint (exactIds : List String)
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (layoutX exactIds) fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.routes.map (·.id), id ∉ parent.scene.routes.map (·.id) :=
  XB_routedisjoint_of exactIds (Model.routeIds_nodup hwf) hchild hparent

/-- The child-scene route endpoints name child-scene boxes, at the exact
base.  Copies `expandChild_child_route_endpoints`. -/
private theorem XB_child_route_endpoints (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
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
  exact XB_mirror_endpoints exactIds fuel _ _ _ hsub.1 hsub.2.1 hchild



/-- Rewriting under an option `or`.  Copy of the private `option_map_or`. -/
private theorem XB_option_map_or {α β : Type} (o₁ o₂ : Option α) (g : α → β) :
    (o₁.or o₂).map g = (o₁.map g).or (o₂.map g) := by
  cases o₁ <;> cases o₂ <;> rfl

/-- Input box ids cover sub-input box ids.  Copy of the private
`selectInput_box_ids_subset`. -/
private theorem XB_selectInput_box_ids_subset (inp : Input) (keep : ModelBox → Bool)
    (root : String) :
    ∀ x ∈ (selectInput inp keep root).boxes.map (·.id), x ∈ inp.boxes.map (·.id) := by
  intro x hx
  rw [selectInput_box_ids] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨b, (List.mem_filter.mp hb).1, rfl⟩

/-- A kept label's owner resolves in the kept boxes or routes.  Copy of the
private `selectInput_label_owner_mem`. -/
private theorem XB_selectInput_label_owner_mem (inp : Input) (keep : ModelBox → Bool)
    (root : String) (l : ModelLabel)
    (hl : l ∈ (selectInput inp keep root).labels) :
    l.owner ∈ (selectInput inp keep root).boxes.map (·.id) ∨
      l.owner ∈ (selectInput inp keep root).routes.map (·.id) := by
  unfold selectInput at hl
  obtain ⟨_, hflt⟩ := List.mem_filter.mp hl
  have hcases := Bool.or_eq_true_iff.mp hflt
  rcases hcases with hbox | hroute
  · rw [List.any_eq_true] at hbox
    obtain ⟨b, hb, he⟩ := hbox
    left
    apply List.mem_map.mpr
    refine ⟨b, ?_, ?_⟩
    · exact hb
    · exact beq_iff_eq.mp he
  · rw [List.any_eq_true] at hroute
    obtain ⟨rt, hrt, he⟩ := hroute
    right
    apply List.mem_map.mpr
    refine ⟨rt.1, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨rt, hrt, rfl⟩
    · exact beq_iff_eq.mp he

/-- A successful exact `expandChild` labels every merged label from an input
label.  Copy of the private `expandChild_label_model_mem` (base-independent:
only `expandChild_sources` and the label-list equation). -/
private theorem XB_label_model_mem {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res)
    (howners : ExpandChildLabelOwners inp parent child) :
    ∀ rl ∈ res.scene.layoutDump.labels,
      ∃ model ∈ inp.labels, rl.id = model.id ∧ rl.owner = model.owner := by
  obtain ⟨frame₀, metric₀, tl₀, _, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _,
    hdx₀, hdy₀, _, _⟩ := expandChild_sources h
  have hwrap : ExpandChildTitleWrapped P inp o group tl₀ := ⟨metric₀, hmetric₀, htitle₀⟩
  have hlabels :=
    expandChild_labels_eq_wrapped h frame₀ tl₀ dx₀ dy₀ hframe₀ hdx₀ hdy₀ hwrap
  intro rl hrl
  have hrls : rl ∈ res.scene.labels.map (·.toLabel) := hrl
  obtain ⟨sl, hsl, hto⟩ := List.mem_map.mp hrls
  subst hto
  rw [hlabels] at hsl
  obtain ⟨model, hmmem, hdo⟩ := List.mem_filterMap.mp hsl
  cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
      { label with rect := shiftRect dx₀ dy₀ label.rect }) ++
      parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) with
  | none => rw [hfind] at hdo; simp at hdo
  | some label =>
    rw [hfind, Option.bind_some] at hdo
    have hif := Option.some.inj hdo
    have hmem2 := List.mem_of_find?_eq_some hfind
    have hlid : label.id = model.id := by simpa using List.find?_some hfind
    have hlown : label.owner = model.owner := by
      rcases List.mem_append.mp hmem2 with hcl | hpl
      · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
        have e2 : label.owner = cl.owner := by rw [← hclEq]
        have hmid : model.id = cl.id := hlid.symm.trans (by rw [← hclEq])
        exact e2.trans (howners.1 cl hclmem model hmmem hmid).symm
      · exact (howners.2 label hpl model hmmem hlid.symm).symm
    by_cases hcond : (model.owner == group.id) = true
    · rw [hcond] at hif
      simp only [reduceIte] at hif
      exact ⟨model, hmmem, by rw [← hif]; exact hlid, by rw [← hif]; exact hlown⟩
    · have hcondF : (model.owner == group.id) = false := by
        cases hb : (model.owner == group.id) with
        | true => exact absurd hb hcond
        | false => rfl
      rw [hcondF] at hif
      simp only [Bool.false_eq_true, reduceIte] at hif
      exact ⟨model, hmmem, by rw [← hif]; exact hlid, by rw [← hif]; exact hlown⟩

/-- Merged route-lookup agreement at the exact base.  Copies
`expandChild_route_agreement`. -/
private theorem XB_route_agreement (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7RouteAgreement parent child res := by
  obtain ⟨hwf, _hfind, _hpboxes, hchild, hparent, _⟩ := hctxB
  obtain ⟨frameS, metricS, tlS, _lS, dxS, dyS, hframeS, hmetricS, htitleS,
    _hlS, hdxS, hdyS, _hcS, _hbS⟩ := expandChild_sources hexpand
  have hroutes := expandChild_routes_eq hexpand frameS metricS tlS dxS dyS
    hframeS hmetricS htitleS hdxS hdyS
  have hrouteNodup : (inp.routes.map (·.id)).Nodup := Model.routeIds_nodup hwf
  have hcovC : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp _ _
  have hcovP : RoutesCovered (parentSubInput inp group P titleLines child) := by
    show RoutesCovered (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "")
    exact selectInput_routesCovered inp _ _
  have hchildIds := XB_ids exactIds fuel _ _ _ hcovC hchild
  have hparentIds := XB_ids exactIds fuel _ _ _ hcovP hparent
  have hdisjRoutes : ∀ id ∈ child.scene.routes.map (·.id),
      id ∉ parent.scene.routes.map (·.id) :=
    XB_routedisjoint exactIds hwf hchild hparent
  intro owner
  change (res.scene.routes.find? (fun r : Route => r.id == owner)).map
      (fun r => (r.fromId, r.toId)) =
    (((child.scene.routes.find? (fun r : Route => r.id == owner)).map
      (fun r => (r.fromId, r.toId))).orElse (fun _ =>
      ((parent.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r => (r.fromId, r.toId)))))
  rw [hroutes]
  have hmerged : (inp.routes.filterMap (fun model =>
      ((child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun route : Route => route.id == model.id))).find?
      (fun r : Route => r.id == owner) =
      ((child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun r : Route => r.id == owner) := by
    cases hSP : ((child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun r : Route => r.id == owner) with
    | none =>
      apply List.find?_eq_none.mpr
      intro rt hrt htest
      obtain ⟨model, hmMem, hfind⟩ := List.mem_filterMap.mp hrt
      have hrtId : rt.id = model.id := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hfind).1
      have hro : rt.id = owner := beq_iff_eq.mp htest
      have hmo : model.id = owner := hrtId.symm.trans hro
      have hg : ((child.scene.routes.map (fun route : Route =>
            { route with points := route.points.map (shiftPoint dxS dyS) })) ++
          parent.scene.routes).find? (fun route : Route => route.id == model.id) = none := by
        rw [hmo]; exact hSP
      rw [hg] at hfind
      cases hfind
    | some r =>
      have hrId : r.id = owner := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hSP).1
      have hrMem : r ∈ (child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes := List.mem_of_find?_eq_some hSP
      obtain ⟨m₀, hm₀mem, hm₀id⟩ : ∃ m₀ ∈ inp.routes, m₀.id = owner := by
        rcases List.mem_append.mp hrMem with hrS | hrP
        · obtain ⟨cr, hcr, hrEq⟩ := List.mem_map.mp hrS
          have hcrid : cr.id = owner := by
            have e := congrArg (fun x : Route => x.id) hrEq
            exact e.trans hrId
          have hownMem : owner ∈ child.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨cr, hcr, hcrid⟩
          rw [hchildIds.2] at hownMem
          obtain ⟨mC, hmCsub, hmCid⟩ := List.mem_map.mp hownMem
          exact ⟨mC, (selectInput_route_mem inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id mC).mp
            hmCsub |>.1, hmCid⟩
        · have hownMem : owner ∈ parent.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨r, hrP, hrId⟩
          rw [hparentIds.2] at hownMem
          obtain ⟨mP, hmPsub, hmPid⟩ := List.mem_map.mp hownMem
          have hmPsel : mP ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes :=
            hmPsub
          exact ⟨mP, (selectInput_route_mem inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" mP).mp
            hmPsel |>.1, hmPid⟩
      have hg₀ : ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
          parent.scene.routes).find? (fun route : Route => route.id == m₀.id) = some r := by
        rw [hm₀id]; exact hSP
      have hrRes : r ∈ res.scene.routes := by
        rw [hroutes]
        exact List.mem_filterMap.mpr ⟨m₀, hm₀mem, hg₀⟩
      cases hf : res.scene.routes.find? (fun r' : Route => r'.id == owner) with
      | none =>
        have hp : (fun r' : Route => r'.id == owner) r = true := beq_iff_eq.mpr hrId
        exact absurd hp ((List.find?_eq_none.mp hf) r hrRes)
      | some b =>
        have hbmem : b ∈ res.scene.routes := List.mem_of_find?_eq_some hf
        have hbp : b.id = owner := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hf).1
        rw [hroutes] at hbmem
        obtain ⟨m', hm'mem, hg'm⟩ := List.mem_filterMap.mp hbmem
        have hbm'id : b.id = m'.id := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hg'm).1
        have hm'id : m'.id = owner := hbm'id.symm.trans hbp
        have hm'eq : m' = m₀ := expandChild_nodup_map_inj (·.id) hrouteNodup
          hm'mem hm₀mem (hm'id.trans hm₀id.symm)
        have hg'm' : ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
            parent.scene.routes).find? (fun route : Route => route.id == m'.id) = some b := hg'm
        have hgg : ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
            parent.scene.routes).find? (fun route : Route => route.id == m'.id) =
            ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
            parent.scene.routes).find? (fun route : Route => route.id == m₀.id) := by rw [hm'eq]
        rw [hg'm', hg₀] at hgg
        have hbr : b = r := Option.some.inj hgg
        rw [hroutes] at hf
        rw [hbr] at hf
        exact hf
  rw [hmerged]
  have hSmap : ((child.scene.routes.map (fun route : Route =>
        { route with points := route.points.map (shiftPoint dxS dyS) })).find?
        (fun r : Route => r.id == owner)).map (fun r : Route => (r.fromId, r.toId)) =
      (child.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId)) := by
    rw [List.find?_map, Option.map_map]
    rfl
  have hPmap : (parent.scene.routes.find? (fun r : Route => r.id == owner)).map
      (fun r : Route => (r.fromId, r.toId)) =
      (parent.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId)) := rfl
  have hkey : (((child.scene.routes.map (fun route : Route =>
        { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId)) =
      ((child.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId))).orElse (fun _ =>
        ((parent.scene.routes.find? (fun r : Route => r.id == owner)).map
          (fun r : Route => (r.fromId, r.toId)))) := by
    rw [List.find?_append, XB_option_map_or, hSmap, hPmap, Option.orElse_eq_or]
  exact hkey

/-- Owner separation at the exact base: no label owner of one sub-scene
names a route of the other, and neither sub-scene routes on the group id.
Copies `expandChild_owner_separation`, with the recursive mirror replaced by
`XB_label_mem` (only its label half is used). -/
private theorem XB_owner_separation (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hdisjoint : BoxRouteIdsDisjoint inp) :
    ExpandChildC7OwnerSeparation group parent child := by
  obtain ⟨hwf, hfind, _hpboxes, hchild, hparent, _⟩ := hctxB
  have hcovC : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp _ _
  have hcovP : RoutesCovered (parentSubInput inp group P titleLines child) := by
    show RoutesCovered (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "")
    exact selectInput_routesCovered inp _ _
  have hchildIds := XB_ids exactIds fuel _ _ _ hcovC hchild
  have hparentIds := XB_ids exactIds fuel _ _ _ hcovP hparent
  have hdisjRoutes : ∀ id ∈ child.scene.routes.map (·.id),
      id ∉ parent.scene.routes.map (·.id) :=
    XB_routedisjoint exactIds hwf hchild hparent
  have hgroup : group ∈ inp.boxes := List.mem_of_find?_eq_some hfind
  have hgroupBox : group.id ∈ inp.boxes.map (·.id) :=
    List.mem_map.mpr ⟨group, hgroup, rfl⟩
  have hchildRouteInp : ∀ id ∈ child.scene.routes.map (·.id),
      id ∈ inp.routes.map (·.id) := by
    intro id hid
    rw [hchildIds.2] at hid
    change id ∈ (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).routes.map (·.id) at hid
    exact (selectInput_routes_ids_sublist inp _ _).subset hid
  have hparentRouteInp : ∀ id ∈ parent.scene.routes.map (·.id),
      id ∈ inp.routes.map (·.id) := by
    intro id hid
    rw [hparentIds.2] at hid
    change id ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").routes.map (·.id) at hid
    exact (selectInput_routes_ids_sublist inp _ _).subset hid
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cl hcl
    show (parent.scene.routes.find? (fun r => r.id == cl.owner)) = none
    obtain ⟨m, hmlab, _hmid, hmown⟩ := XB_label_mem exactIds _ _ _ _ hchild cl hcl
    change m ∈ (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).labels at hmlab
    have hown := XB_selectInput_label_owner_mem inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id m hmlab
    cases h : (parent.scene.routes.find? (fun r => r.id == cl.owner)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ parent.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = cl.owner :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have heq : rt.id = m.owner := hrtid.trans hmown.symm
      rcases hown with hboxown | hrouteown
      · have hboxIn : m.owner ∈ inp.boxes.map (·.id) :=
          XB_selectInput_box_ids_subset inp _ _ _ hboxown
        have hrouteIn : m.owner ∈ inp.routes.map (·.id) :=
          heq ▸ hparentRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
        exact False.elim (hdisjoint m.owner hboxIn hrouteIn)
      · have hcown : m.owner ∈ child.scene.routes.map (·.id) :=
          hchildIds.2.symm ▸ hrouteown
        have hpown : m.owner ∈ parent.scene.routes.map (·.id) := by
          have hpm : cl.owner ∈ parent.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨rt, hrtmem, hrtid⟩
          rwa [← hmown] at hpm
        exact False.elim (hdisjRoutes m.owner hcown hpown)
  · intro pl hpl
    show (child.scene.routes.find? (fun r => r.id == pl.owner)) = none
    obtain ⟨m, hmlab, _hmid, hmown⟩ := XB_label_mem exactIds _ _ _ _ hparent pl hpl
    change m ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").labels at hmlab
    have hown := XB_selectInput_label_owner_mem inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "" m hmlab
    cases h : (child.scene.routes.find? (fun r => r.id == pl.owner)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ child.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = pl.owner :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have heq : rt.id = m.owner := hrtid.trans hmown.symm
      rcases hown with hboxown | hrouteown
      · have hboxIn : m.owner ∈ inp.boxes.map (·.id) :=
          XB_selectInput_box_ids_subset inp _ _ _ hboxown
        have hrouteIn : m.owner ∈ inp.routes.map (·.id) :=
          heq ▸ hchildRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
        exact False.elim (hdisjoint m.owner hboxIn hrouteIn)
      · have hpown : m.owner ∈ parent.scene.routes.map (·.id) :=
          hparentIds.2.symm ▸ hrouteown
        have hcown : m.owner ∈ child.scene.routes.map (·.id) := by
          have hcm : pl.owner ∈ child.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨rt, hrtmem, hrtid⟩
          rwa [← hmown] at hcm
        exact False.elim (hdisjRoutes m.owner hcown hpown)
  · show (child.scene.routes.find? (fun r : Route => r.id == group.id)) = none
    cases h : (child.scene.routes.find? (fun r : Route => r.id == group.id)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ child.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = group.id :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have hrouteIn : group.id ∈ inp.routes.map (·.id) :=
        hrtid ▸ hchildRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
      exact False.elim (hdisjoint group.id hgroupBox hrouteIn)
  · show (parent.scene.routes.find? (fun r : Route => r.id == group.id)) = none
    cases h : (parent.scene.routes.find? (fun r : Route => r.id == group.id)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ parent.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = group.id :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have hrouteIn : group.id ∈ inp.routes.map (·.id) :=
        hrtid ▸ hparentRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
      exact False.elim (hdisjoint group.id hgroupBox hrouteIn)

/-- The label-scope invariant of one exact `expandChild` call: owner scopes
transport from both exact sub-scenes into the merged dump, and the group
scope anchors every group-owned or child-sourced merged label.  Copies
`expandChild_c7_label_scopes` with the exact sub-proofs. -/
private theorem XB_scopes (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child result : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok result)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child result)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hmono : ExpandChildC7AncestorMono parent child result)
    (hagree : ExpandChildC7RouteAgreement parent child result)
    (hsep : ExpandChildC7OwnerSeparation group parent child)
    (hanc : ExpandChildC8aAncestry group parent child result)
    (hendpoints : ExpandChildC7RouteEndpoints child) :
    ExpandChildC7LabelScopes P group parent child result := by
  obtain howners := XB_label_owners exactIds fuel P inp o group titleLines titleHeight
    parent child result hexpand hframed hctxB hparams
  obtain ⟨_, _, _, hchild, _, _⟩ := hctxB
  have hcovC : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hidsC := XB_ids exactIds _ _ _ _ hcovC hchild
  refine ⟨?_, ?_, ?_⟩
  · intro cl hcl rl hrl heq x hx
    obtain ⟨model, hmmem, hmid, hmown⟩ := XB_label_model_mem hexpand howners rl hrl
    have hmid' : model.id = cl.id := hmid.symm.trans heq
    have hmo : model.owner = cl.owner := howners.1 cl hcl model hmmem hmid'
    have hro : rl.owner = cl.owner := hmown.trans hmo
    cases hcf : child.scene.layoutDump.routes.find? (fun r => r.id == cl.owner) with
    | some r =>
      have hcscope : child.scene.layoutDump.labelOwnerAnc cl.toLabel =
          child.scene.layoutDump.ancestors r.fromId ++
            child.scene.layoutDump.ancestors r.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hcf]
      have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hro, hcf]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.1 cl hcl]
      have hrm' : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hagree rl.owner, hcm, hpm]
      obtain ⟨r', hr', hef, het⟩ : ∃ r',
          result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = some r' ∧
          r'.fromId = r.fromId ∧ r'.toId = r.toId := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rw [hr'] at hrm'; simp at hrm'
        | some r' =>
          have h2 := hrm'
          simp [hr'] at h2
          exact ⟨r', rfl, h2.1, h2.2⟩
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          result.scene.layoutDump.ancestors r'.fromId ++
            result.scene.layoutDump.ancestors r'.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hr']
      rw [hcscope] at hx
      rw [hrscope] at ⊢
      rw [hef, het] at ⊢
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hmono.2 _ _ h)
      · exact List.mem_append_right _ (hmono.2 _ _ h)
    | none =>
      have hcscope : child.scene.layoutDump.labelOwnerAnc cl.toLabel =
          cl.owner :: child.scene.layoutDump.ancestors cl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hcf]
      have hcm0 : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hcf]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.1 cl hcl]
      have hrm0 : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hagree rl.owner, hcm0, hpm]
      have hrnone : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rfl
        | some r' => rw [hr'] at hrm0; simp at hrm0
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hrnone]
      rw [hcscope] at hx
      rw [hrscope] at ⊢
      rw [hro] at ⊢
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hmono.2 _ _ h))
  · intro pl hpl rl hrl heq x hx
    obtain ⟨model, hmmem, hmid, hmown⟩ := XB_label_model_mem hexpand howners rl hrl
    have hmid' : model.id = pl.id := hmid.symm.trans heq
    have hmo : model.owner = pl.owner := howners.2 pl hpl model hmmem hmid'
    have hro : rl.owner = pl.owner := hmown.trans hmo
    cases hpf : parent.scene.layoutDump.routes.find? (fun r => r.id == pl.owner) with
    | some r =>
      have hpscope : parent.scene.layoutDump.labelOwnerAnc pl.toLabel =
          parent.scene.layoutDump.ancestors r.fromId ++
            parent.scene.layoutDump.ancestors r.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hpf]
      have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.2.1 pl hpl]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hro, hpf]
      have hrm' : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hagree rl.owner, hcm, hpm]
      obtain ⟨r', hr', hef, het⟩ : ∃ r',
          result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = some r' ∧
          r'.fromId = r.fromId ∧ r'.toId = r.toId := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rw [hr'] at hrm'; simp at hrm'
        | some r' =>
          have h2 := hrm'
          simp [hr'] at h2
          exact ⟨r', rfl, h2.1, h2.2⟩
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          result.scene.layoutDump.ancestors r'.fromId ++
            result.scene.layoutDump.ancestors r'.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hr']
      rw [hpscope] at hx
      rw [hrscope] at ⊢
      rw [hef, het] at ⊢
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hmono.1 _ _ h)
      · exact List.mem_append_right _ (hmono.1 _ _ h)
    | none =>
      have hpscope : parent.scene.layoutDump.labelOwnerAnc pl.toLabel =
          pl.owner :: parent.scene.layoutDump.ancestors pl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hpf]
      have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.2.1 pl hpl]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hpf]
      have hrm0 : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hagree rl.owner, hcm, hpm]
      have hrnone : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rfl
        | some r' => rw [hr'] at hrm0; simp at hrm0
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hrnone]
      rw [hpscope] at hx
      rw [hrscope] at ⊢
      rw [hro] at ⊢
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hmono.1 _ _ h))
  · intro rl hrl hsrc x hx
    rcases hsrc with hcap | hchildsrc
    · have hcmG : (child.scene.layoutDump.routes.find? (fun r => r.id == group.id)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hsep.2.2.1]
      have hpmG : (parent.scene.layoutDump.routes.find? (fun r => r.id == group.id)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hsep.2.2.2]
      have hrmG : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hcap, hagree group.id, hcmG, hpmG]
      have hresG : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rfl
        | some r' => rw [hr'] at hrmG; simp at hrmG
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hresG]
      rw [hrscope, hcap] at ⊢
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hmono.1 _ _ h))
    · obtain ⟨cl, hcl, _hid, hown⟩ := hchildsrc
      cases hcf : child.scene.layoutDump.routes.find? (fun r => r.id == cl.owner) with
      | some r =>
        have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hown, hsep.1 cl hcl]
        have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
          simp [hown, hcf]
        have hrm' : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
          simp [hagree rl.owner, hcm, hpm]
        obtain ⟨r', hr', hef, het⟩ : ∃ r',
            result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = some r' ∧
            r'.fromId = r.fromId ∧ r'.toId = r.toId := by
          cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
          | none => rw [hr'] at hrm'; simp at hrm'
          | some r' =>
            have h2 := hrm'
            simp [hr'] at h2
            exact ⟨r', rfl, h2.1, h2.2⟩
        have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
            result.scene.layoutDump.ancestors r'.fromId ++
              result.scene.layoutDump.ancestors r'.toId := by
          unfold LayoutDump.labelOwnerAnc
          rw [hr']
        have hrmem : r ∈ child.scene.routes := List.mem_of_find?_eq_some hcf
        obtain ⟨hfbox, _⟩ := hendpoints r hrmem
        obtain ⟨ob, hob, hobid⟩ := List.mem_map.mp hfbox
        have hchain := hanc.1 ob hob x hx
        rw [hobid] at hchain
        rw [hrscope, hef, het] at ⊢
        exact List.mem_append_left _ hchain
      | none =>
        have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hown, hsep.1 cl hcl]
        have hcm0 : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hown, hcf]
        have hrm0 : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hagree rl.owner, hcm0, hpm]
        have hrnone : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
          cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
          | none => rfl
          | some r' => rw [hr'] at hrm0; simp at hrm0
        have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
            rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
          unfold LayoutDump.labelOwnerAnc
          rw [hrnone]
        obtain ⟨mc, hmcmem, _, hmcOwn⟩ :=
          XB_label_mem exactIds _ _ _ _ hchild cl hcl
        have hmcsub : mc ∈ (selectInput inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id).labels := hmcmem
        have hvalid := selectInput_label_owner inp _ _ mc hmcsub
        have hmo : mc.owner = cl.owner := hmcOwn
        rcases hvalid with hbox | hroute
        · have h1' : mc.owner ∈ (childSubInput inp group).boxes.map (·.id) := hbox
          rw [← hidsC.1] at h1'
          obtain ⟨ob, hob, hobid⟩ := List.mem_map.mp h1'
          have e : ob.id = rl.owner := hobid.trans (hmo.trans hown.symm)
          have hchain := hanc.1 ob hob x hx
          rw [e] at hchain
          rw [hrscope] at ⊢
          exact List.mem_cons.mpr (Or.inr hchain)
        · have h1' : mc.owner ∈ (childSubInput inp group).routes.map (·.id) := hroute
          rw [← hidsC.2] at h1'
          obtain ⟨r, hr, hrid⟩ := List.mem_map.mp h1'
          have hne : child.scene.layoutDump.routes.find? (fun r => r.id == cl.owner) ≠ none := by
            intro hnone
            have hff := List.find?_eq_none.mp hnone r hr
            rw [hrid, hmo] at hff
            simp at hff
          exact absurd hcf hne



/-- C7 label scopes from disjointness at the exact base.  Copies
`expandChild_c7_label_scopes_of_disjoint`. -/
private theorem XB_scopes_of_disjoint (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hdisjoint : BoxRouteIdsDisjoint inp)
    (hanc : ExpandChildC8aAncestry group parent child res) :
    ExpandChildC7LabelScopes P group parent child res :=
  XB_scopes exactIds fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
    (XB_ancestor_mono exactIds hexpand hframed hctxB hparams)
    (XB_route_agreement exactIds hexpand hframed hctxB hparams)
    (XB_owner_separation exactIds hexpand hframed hctxB hparams hdisjoint)
    hanc
    (XB_child_route_endpoints exactIds hexpand hframed hctxB hparams)

/-- The restricted C7 structure of one exact `expandChild` call.  Copies
`expandChild_c7_structure_wrapped`. -/
private theorem XB_c7wrapped (exactIds : List String)
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
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (howners : ExpandChildLabelOwners inp parent child)
    (hscopes : ExpandChildC7LabelScopes P group parent child res) :
    ExpandChildC7StructureRestricted P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hcore := XB_core_wrapped exactIds hwf hgroup hchild hparent hexpand
    frame tl dx dy hframe hdx hdy hwrap
  have hcl := (expandChild_label_classes_wrapped hexpand howners frame tl dx dy hframe
    hdx hdy hwrap).2
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcl,
    hscopes.1, hscopes.2.1, hscopes.2.2⟩

/-- The `hstructC7` B-premise: the restricted C7 structure of every exact
`expandChild` call.  Copies `expandChild_c7_structure`. -/
private theorem XB_c7structure (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines
      titleHeight parent child res)
    (howners : ExpandChildLabelOwners inp parent child)
    (hscopes : ExpandChildC7LabelScopes P group parent child res) :
    ExpandChildC7StructureRestricted P inp o group titleHeight parent child res := by
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctxB
  exact XB_c7wrapped exactIds hwf hgroup hchild hparent hexpand' howners hscopes

/-- The `stepC7` seam of `BaseSeams` at `base := layoutX exactIds`: every
`expandChild` call the exact recursion performs satisfies `ExpandChildC7Step`.
The binders match `FamilyAssemblyB.lean` `stepC7` lines 95-104, including the
`BoxRouteIdsDisjoint` premise.  Assembled inline like `baseSeams_of_layered`. -/
theorem stepC7_layoutX (exactIds : List String)
    (hgeoC7B : RecursiveStepFactsB (layoutX exactIds) ExpandChildC7Geometry)
    (hancC8aB : RecursiveStepFactsB (layoutX exactIds)
      (fun _ _ _ group _ parent child res => ExpandChildC8aAncestry group parent child res)) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true → BoxRouteIdsDisjoint inp →
      InputFixedFit inp o →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hdisjoint _hfix hctxB hparams
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    XB_c7structure exactIds fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB
      (XB_label_owners exactIds fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctxB hparams)
      (XB_scopes_of_disjoint exactIds fuel P inp o group titleLines titleHeight parent child
        res hexpand hframed hctxB hparams hdisjoint
        (hancC8aB fuel P inp o group titleLines titleHeight parent child res hexpand hframed
          hctxB hparams))
      frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨g1, g2, g3, g4⟩ :=
    hgeoC7B fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, g1, g2, g3, g4⟩

end Elegant.Layered.PipelineImpl
