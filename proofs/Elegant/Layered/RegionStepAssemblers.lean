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
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.RegionSubInputStepC2
import Elegant.Layered.RegionPipeline
import Elegant.Layered.RegionFoundation

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Region recursion-step assemblers (packet P11)

Region twins of the recursive step theorems of the exact base, for the
reindexing base `fun sub o' => layoutRIds exactIds (reindexRegionSets
idSets sub) sub o'`: `stepC6_layoutRIds`, `stepC7_layoutRIds`,
`stepC8aAncestry_layoutRIds`, `stepC8a_layoutRIds`, `stepC8b_layoutRIds`.
Twins: `Layered/ExactStepFacts.lean`, `Layered/ExactStepShortFacts.lean`;
the binders match the `stepC6`, `stepC7`, `stepC8a`, `stepC8b` fields of
`BaseSeams` (`FamilyAssemblyB.lean:52-135`) instantiated at the region base,
as the terms at `Kinds/UsecaseValidExact.lean:270-274` do for the exact base.

The exact proofs use the id lemma (`XB_layout_ids`; region twin
`RB_layout_ids`), `expandChild` source and id lemmas, and `selectInput`
lemmas that do not depend on the base: those are reused and only what
mentions `layoutX` is replayed. Geometry premises are taken open exactly
as the exact twins take them (the `RecursiveStepFactsB` shape at the
region base, written out: this file does not import `ExactStepFacts`,
whose `RecursiveStepFactsB` abbrev would otherwise be reused verbatim).

Three narrow residuals stay open (each a single public def over executed
calls, strictly narrower than its target; see the probe evidence below):
`R_StepC7ScopesB` (the C7 label scopes feeding `stepC7`), and
`R_StepC8aMergedAnchorsB` / `R_StepC8aGroupIsolatedB` (the two ancestry
conjuncts feeding `stepC8aAncestry`). The ancestry root-chain and C7
scope-ingredient proofs would replay hundreds of lines of already-true
exact-base walk machinery; the residuals name exactly the per-call facts
the assemblers consume.
-/

/-- The reindexing base of packet P11. -/
private abbrev RSA_rbBase (exactIds : List String) (idSets : List (String × List String)) :
    Input → Options → Except LayoutError FamilyResult :=
  fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'

/-- Residual: the C7 label scopes of every region `expandChild` call.
Strictly narrower than `stepC7` (scopes are three of the eight structure
conjuncts; geometry is not included). -/
def R_StepC7ScopesB (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7LabelScopes P group parent child res

/-- Residual: the merged-anchors conjunct of the region C8a ancestry.
Strictly narrower than `stepC8aAncestry` (first of two conjuncts). -/
def R_StepC8aMergedAnchorsB (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ cb ∈ child.scene.boxes,
      ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
        x ∈ res.scene.layoutDump.ancestors cb.id

/-- Residual: the group-isolation conjunct of the region C8a ancestry.
Strictly narrower than `stepC8aAncestry` (second of two conjuncts). -/
def R_StepC8aGroupIsolatedB (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildGroupIsolated group parent

/-- Two-region probe input (same shape as `rapProbeInp`). -/
private def RSA_probeInp : Input :=
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
    labels := [] }

/-- Resolved region sets of the probe. -/
private def RSA_probeIdSets : List (String × List String) :=
  [("G1", ["A", "B"]), ("G2", ["C", "D"])]

/-- The region recursion succeeds on the two-region probe. Every group
there is crossed by a route, so the run stays flat and the residuals hold
vacuously over it. -/
private def RSA_probeRecOk : Bool :=
  match layoutRecursiveB (RSA_rbBase [] RSA_probeIdSets) 11 RSA_probeInp
    { profile := .vector, direction := .TB } with
  | .ok _ => true
  | .error _ => false

/-- Nested probe: `G` contains `R1`/`B`, regions nest inside `R1`; `G`
carries a direction and no route crosses it, so it is independent and the
recursion performs a genuine `expandChild`. -/
private def RSA_probeNestedInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false, direction := "TB" },
      { id := "R1", role := .group, parent := "G", exclusive := false },
      { id := "B", role := .group, parent := "G", exclusive := false },
      { id := "A", role := .group, parent := "R1", exclusive := false },
      { id := "C", role := .group, parent := "R1", exclusive := false },
      { id := "a1", parent := "A", exclusive := false },
      { id := "c1", parent := "C", exclusive := false },
      { id := "b1", parent := "B", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "b1" },
      { id := "eBack", fromId := "c1", toId := "a1" }]
    texts := ["G", "R1", "B", "A", "C", "a1", "c1", "b1"]
    edges := [.plain, .plain]
    labels := [] }

/-- Nested region sets of the nested probe. -/
private def RSA_probeNestedIdSets : List (String × List String) :=
  [("G", ["R1", "B"]), ("R1", ["A", "C"])]

/-- The region recursion succeeds on the nested probe, through expansion. -/
private def RSA_probeNestedRecOk : Bool :=
  match layoutRecursiveB (RSA_rbBase [] RSA_probeNestedIdSets) 9 RSA_probeNestedInp
    { profile := .vector, direction := .TB } with
  | .ok _ => true
  | .error _ => false

/-- The nested probe offers an independent group, so the recursion performs
at least one `expandChild` on the way to success. -/
private def RSA_probeHasGroup : Bool :=
  (RSA_probeNestedInp.boxes.find? (fun box => Compound.independent RSA_probeNestedInp.boxes
    RSA_probeNestedInp.routes box &&
    !RSA_probeNestedInp.fixedSizes.any (fun fixed => fixed.1 == box.id))).isSome

#eval RSA_probeRecOk

#eval RSA_probeNestedRecOk

#eval RSA_probeHasGroup

/-- Successor split for `layoutRecursiveB` at the reindexing base, in the
shape of `layoutRecursive_succ`: the concrete appended tables are
generalized to `∃ a b c` so the induction proofs copy the plain ones
verbatim. Twin of `XB_succ`. -/
private theorem RSA_succ (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRecursiveB (RSA_rbBase exactIds idSets) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      RSA_rbBase exactIds idSets inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursiveB_succ_sources (RSA_rbBase exactIds idSets) h with hflat |
    ⟨group, P, _metric, child, _titleLines, parent, hg, _, _, hc, _, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩

/-- Region `B`-recursion id fact: scene ids of a successful region recursive
layout are the sub-input ids. Copies `XB_ids` with `RSA_succ` and the
region leaf fact `RB_layout_ids` (which holds for every `idSets`, hence also
for the reindexed sets of the base). -/
private theorem RSA_ids (exactIds : List String) (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    RoutesCovered inp → layoutRecursiveB (RSA_rbBase exactIds idSets) fuel inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero => intro inp o res _ h; exact RB_layout_ids h
  | succ fuel ih =>
    intro inp o res hc h
    rcases RSA_succ exactIds idSets h with ⟨_, hlayout⟩ |
      ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, hexp⟩
    · exact RB_layout_ids hlayout
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
/-- The child/parent scene id lists of one region expansion, as the two
disjoint halves of the input ids. Copies `XB_selected_ids` with `RSA_ids`. -/
private theorem RSA_selected (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
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
  have hchildIds := RSA_ids exactIds idSets fuel _ _ _ hchildCov hchild
  have hparentIds := RSA_ids exactIds idSets fuel _ _ _ hparentCov hparent
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

/-- Scene ids of the two region sub-layouts are disjoint. Copies
`XB_disjoint` with `RSA_ids`. -/
private theorem RSA_disjoint (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hchild : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.boxes.map (·.id), id ∉ parent.scene.boxes.map (·.id) := by
  have hc := RSA_ids exactIds idSets fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := RSA_ids exactIds idSets fuel _ _ _ hparentCoverage hparent
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

/-- The offset-independent structural facts of one region `expandChild`
call: the two scene-size bounds and the child/group id isolation. Copies
`XB_merge_bounds` with `RSA_ids` and `RSA_disjoint`. -/
private theorem RSA_bounds (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
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
  have hchildIds := RSA_ids exactIds idSets fuel _ _ _ hchildCov hchild
  have hparentIds := RSA_ids exactIds idSets fuel _ _ _ hparentCov hparent
  have hdisjoint := RSA_disjoint exactIds idSets hchild hparent
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
        have hsame' := hsame
        rw [hfi] at hsame'
        exact hsame'.symm
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

/-- The merged scene resolves every child box to its embedded image and
every parent box to itself, at the offsets the region `expandChild`
actually used. Factored twin of `expandChild_boxLookup_transport` (whose
proof only needs the selected ids): serves the C6/C8a assemblers and the
C8a structure below. -/
private theorem RSA_transports (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
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
      ExpandChildTitleWrapped P inp o group tl ∧
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        res.scene.layoutDump.box? b.id = some b) := by
  obtain ⟨frame, metric₀, tl, _lines, dx, dy, hframe, hmetric₀, htitle₀,
    _hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ :=
    RSA_selected exactIds idSets hwf hchild hparent
  refine ⟨frame, tl, dx, dy, hframe, hdx, hdy, ⟨metric₀, hmetric₀, htitle₀⟩, ?_, ?_⟩
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

/-- The `stepC6` seam of `BaseSeams` at the reindexing base: every
`expandChild` call the region recursion performs satisfies
`ExpandChildC6Step`. The binders match `FamilyAssemblyB.lean` `stepC6`.
Discharged from the open B-form geometry and anchor hypotheses, exactly as
`stepC6_layoutX`; the residual plain proof is `RSA_transports` plus the
id partition. -/
theorem stepC6_layoutRIds (exactIds : List String) (idSets : List (String × List String))
    (hgeoC6B : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Geometry P inp o group titleHeight parent child res)
    (hanchC6B : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Anchors group parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams
  have hanch := hanchC6B fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  have hgeo := hgeoC6B fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctxB
  obtain ⟨frame₁, tl₁, dx₁, dy₁, hframe₁, hdx₁, hdy₁, hwrap₁, htransC, htransP⟩ :=
    RSA_transports exactIds idSets hwf hchild hparent hexpand'
  intro frame metric tl _lines dx dy hframe hmetric htitle _hlines hdx hdy
  have hwrap : ExpandChildTitleWrapped P inp o group tl := ⟨metric, hmetric, htitle⟩
  have hff : frame₁ = frame := Option.some.inj (hframe₁.symm.trans hframe)
  obtain ⟨metric₁, hmetric₁, htitle₁⟩ := hwrap₁
  have hmetricEq : metric = metric₁ := Except.ok.inj (hmetric.symm.trans hmetric₁)
  rw [hmetricEq] at htitle
  have htl : tl = tl₁ := Except.ok.inj (htitle.symm.trans htitle₁)
  have hdxEq : dx = dx₁ := by rw [hdx, hdx₁, hff, htl]
  have hdyEq : dy = dy₁ := by rw [hdy, hdy₁, hff, htl]
  rw [← hdxEq, ← hdyEq] at htransC
  have hb := RSA_bounds exactIds idSets hwf hgroup hchild hparent hexpand'
  obtain ⟨hg1, hg2⟩ := hgeo frame tl dx dy hframe hdx hdy hwrap
  refine ⟨?_, ?_, hb.1, hb.2.1, hg1, hg2, hanch⟩
  · intro b hbmem
    have hcb : child.scene.layoutDump.box? b.id = some b := hbmem
    exact htransC b hcb
  · intro b hbmem
    have hpb : parent.scene.layoutDump.box? b.id = some b := hbmem
    exact htransP b hpb

/-- Region leaf label fact: every region scene label comes from an input
label with the same id and owner. Twin of `XB_layout_label_mem`, via the
`SceneExecutionR` record instead of peeling binds. -/
private theorem RSA_layout_label_mem {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  intro sl hsl
  rw [execution.scene_eq] at hsl
  exact sceneOf_label_mem _ _ _ _ _ _ sl hsl

/-- A successful region `expandChild` labels every merged label from a
child- or parent-scene label, keeping id and owner. Base-independent copy
of `XB_expandChild_label_mem`. -/
private theorem RSA_xl_label_mem {P : Params} {inp : Input} {o : Options}
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

/-- Labels of a successful region recursive layout come from input labels
with the same id and owner. Copies `XB_label_mem` with `RSA_succ` and the
region leaf fact. -/
private theorem RSA_label_mem (exactIds : List String) (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursiveB (RSA_rbBase exactIds idSets) fuel inp o = .ok res →
      ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h sl hsl
    exact RSA_layout_label_mem h sl hsl
  | succ fuel ih =>
    intro inp o res h sl hsl
    rcases RSA_succ exactIds idSets h with ⟨_, hlayout⟩ |
      ⟨group, _, _, _, child, parent, _, _, _, hchild, hparent, hexpand⟩
    · exact RSA_layout_label_mem hlayout sl hsl
    · obtain ⟨s, hsmem, hsId, hsOwn⟩ := RSA_xl_label_mem hexpand sl hsl
      rcases List.mem_append.mp hsmem with hsc | hsp
      · obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := ih _ _ _ hchild s hsc
        have hsub := selectInput_labels_sublist inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
        exact ⟨mc, hsub.subset hmcmem, hmcId.trans hsId.symm, hmcOwn.trans hsOwn.symm⟩
      · obtain ⟨mp, hmpmem, hmpId, hmpOwn⟩ := ih _ _ _ hparent s hsp
        have hsub := selectInput_labels_sublist inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
        exact ⟨mp, hsub.subset hmpmem, hmpId.trans hsId.symm, hmpOwn.trans hsOwn.symm⟩

/-- The label-owner invariant of one region `expandChild` call: labels of
both region recursive sub-scenes carry the owner of the input label with
the same id. Copies `XB_label_owners` with `RSA_label_mem`. -/
private theorem RSA_label_owners (exactIds : List String) (idSets : List (String × List String))
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildLabelOwners inp parent child := by
  obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctxB
  have hnodup : (inp.labels.map (·.id)).Nodup := labelIds_nodup hwf
  have hmemC := RSA_label_mem exactIds idSets _ _ _ _ hchild
  have hmemP := RSA_label_mem exactIds idSets _ _ _ _ hparent
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

/-- The `stepC8b` seam of `BaseSeams` at the reindexing base: every
`expandChild` call the region recursion performs satisfies
`ExpandChildC8bStep`. The binders match `FamilyAssemblyB.lean` `stepC8b`.
Discharged from the open B-form geometry hypothesis, exactly as
`stepC8b_layoutX`; the structure comes from the label classification under
the label-owner invariant. -/
theorem stepC8b_layoutRIds (exactIds : List String) (idSets : List (String × List String))
    (hgeoC8bB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bGeometry P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams
  have howners : ExpandChildLabelOwners inp parent child :=
    RSA_label_owners exactIds idSets fuel P inp o group titleLines titleHeight parent child
      res hexpand hframed hctxB hparams
  have hstruct : ExpandChildC8bStructure P inp o group titleHeight parent child res := by
    obtain ⟨_, _, _, _, _, hexpand'⟩ := hctxB
    exact expandChild_c8b_structure_wrapped hexpand' howners
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨g1, g2, g3, g4⟩ :=
    hgeoC8bB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨hstruct frame tl dx dy hframe hdx hdy hwrap, g1, g2, g3, g4⟩

/-- Region leaf role fact: every region scene box carries the role of a
source input box. Twin of `XB_layout_role`, via the `SceneExecutionR`
record. -/
private theorem RSA_layout_role {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.role = sb.role.id := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  rw [execution.scene_eq]
  simp only [sceneOf]
  intro cb hcb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
  exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Role transport through `selectInput`: kept boxes keep their role (only
the parent pointer is rewritten). Base-independent copy of
`XB_selectInput_box_role`. -/
private theorem RSA_sel_role (inp : Input) (keep : ModelBox → Bool) (root : String)
    {b : ModelBox} (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧ b.role = m.role := by
  unfold selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  exact ⟨q.1, List.fst_mem_of_mem_zipIdx hqzip, hkq, by rw [← hbq]; split <;> rfl,
    by rw [← hbq]; split <;> rfl⟩

/-- Region `B`-recursion role mirror: every scene box of a successful region
recursive layout carries the role of a source input box. Twin of
`XB_role_mirror`. -/
private theorem RSA_role_mirror (exactIds : List String) (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (RSA_rbBase exactIds idSets) fuel inp o = .ok res →
      ∀ bb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = bb.id ∧ bb.role = sb.role.id := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact RSA_layout_role h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases RSA_succ exactIds idSets h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact RSA_layout_role hlayout
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
        obtain ⟨m, hmmem, _hkeep, hmsbid, hmsbrole⟩ := RSA_sel_role inp
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
        obtain ⟨m, hmmem, _hkeep, hmsbid, hmsbrole⟩ := RSA_sel_role inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · rw [hsrole, hmsbrole]

/-- The shared core of one region `expandChild` call: box-lookup transports,
scene-size bounds, the frame's `"group"` role, and child/group id isolation.
Twin of `XB_core_wrapped`, factored over `RSA_transports`, `RSA_bounds`,
and `RSA_role_mirror`. -/
private theorem RSA_core (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (RSA_rbBase exactIds idSets) fuel
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
  obtain ⟨frame₁, tl₁, dx₁, dy₁, hframe₁, hdx₁, hdy₁, hwrap₁, htransC, htransP⟩ :=
    RSA_transports exactIds idSets hwf hchild hparent hexpand
  have hff : frame₁ = frame := Option.some.inj (hframe₁.symm.trans hframe)
  obtain ⟨metric₁, hmetric₁, htitle₁⟩ := hwrap₁
  obtain ⟨metricW, hmetricW, hwrapW⟩ := hwrap
  have hmetricEq : metricW = metric₁ := Except.ok.inj (hmetricW.symm.trans hmetric₁)
  have htl : tl = tl₁ := by
    have h := hwrapW
    rw [hmetricEq] at h
    exact Except.ok.inj (h.symm.trans htitle₁)
  have hdxEq : dx = dx₁ := by rw [hdx, hdx₁, hff, htl]
  have hdyEq : dy = dy₁ := by rw [hdy, hdy₁, hff, htl]
  rw [← hdxEq, ← hdyEq] at htransC
  have hb := RSA_bounds exactIds idSets hwf hgroup hchild hparent hexpand
  refine ⟨htransC, htransP, hb.1, hb.2.1, ?_, hb.2.2 frame hframe⟩
  · have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
    have hparentNodup : ((parentSubInput inp group P titleLines child).boxes.map
        (·.id)).Nodup := by
      show ((selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)).Nodup
      rw [selectInput_box_ids]
      exact List.Nodup.sublist ((List.filter_sublist).map _) hids
    obtain ⟨source, hsource, hsbid, hsrole⟩ := RSA_role_mirror exactIds idSets fuel _ _ _
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

/-- The `stepC8a` seam of `BaseSeams` at the reindexing base: every
`expandChild` call the region recursion performs satisfies
`ExpandChildC8aStep`. The binders match `FamilyAssemblyB.lean` `stepC8a`.
Discharged from the open B-form geometry and ancestry hypotheses, exactly
as `stepC8a_layoutX`; the structure is the shared core plus the ancestry. -/
theorem stepC8a_layoutRIds (exactIds : List String) (idSets : List (String × List String))
    (hgeoC8aB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res)
    (hancC8aB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aAncestry group parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams
  have hstruct : ExpandChildC8aStructure P inp o group titleHeight parent child res := by
    have hanc : ExpandChildC8aAncestry group parent child res :=
      hancC8aB fuel P inp o group titleLines titleHeight parent child res hexpand hframed
        hctxB hparams
    obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctxB
    intro frame tl dx dy hframe hdx hdy hwrap
    have hcore := RSA_core exactIds idSets hwf hgroup hchild hparent hexpand'
      frame tl dx dy hframe hdx hdy hwrap
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
      hcore.2.2.2.2.2, hanc⟩
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    hstruct frame tl dx dy hframe hdx hdy hwrap
  exact ⟨s1, s2, s3, s4, s5, s6,
    hgeoC8aB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams frame tl dx dy hframe hdx hdy hwrap,
    s7, s8⟩

/-- The `stepC7` seam of `BaseSeams` at the reindexing base: every
`expandChild` call the region recursion performs satisfies
`ExpandChildC7Step`. The binders match `FamilyAssemblyB.lean` `stepC7`,
including the `BoxRouteIdsDisjoint` premise (whose contribution, like the
ancestry's, is folded into the scopes residual below). Discharged from the
open B-form geometry hypothesis plus the narrow scopes residual. -/
theorem stepC7_layoutRIds (exactIds : List String) (idSets : List (String × List String))
    (hgeoC7B : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Geometry P inp o group titleHeight parent child res)
    (hscopesB : R_StepC7ScopesB exactIds idSets) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true → BoxRouteIdsDisjoint inp →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    _hdisjoint hctxB hparams
  have hctxB' := hctxB
  have howners : ExpandChildLabelOwners inp parent child :=
    RSA_label_owners exactIds idSets fuel P inp o group titleLines titleHeight parent child
      res hexpand hframed hctxB hparams
  have hscopes : ExpandChildC7LabelScopes P group parent child res :=
    hscopesB fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hctxB hparams
  have hstruct : ExpandChildC7StructureRestricted P inp o group titleHeight parent child
      res := by
    obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctxB
    intro frame tl dx dy hframe hdx hdy hwrap
    have hcore := RSA_core exactIds idSets hwf hgroup hchild hparent hexpand'
      frame tl dx dy hframe hdx hdy hwrap
    have hcl := (expandChild_label_classes_wrapped hexpand' howners frame tl dx dy hframe
      hdx hdy hwrap).2
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcl,
      hscopes.1, hscopes.2.1, hscopes.2.2⟩
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    hstruct frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨g1, g2, g3, g4⟩ :=
    hgeoC7B fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB' hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, g1, g2, g3, g4⟩

/-- The `stepC8aAncestry` seam field at the reindexing base: every region
`expandChild` call satisfies the two ancestry conjuncts. Assembled from the
two narrow residuals (merged anchors and group isolation), which are
strictly narrower than the target; the exact twin `stepC8aAncestry_layoutX`
closes both outright. -/
theorem stepC8aAncestry_layoutRIds (exactIds : List String) (idSets : List (String × List String))
    (hmergedB : R_StepC8aMergedAnchorsB exactIds idSets)
    (hisoB : R_StepC8aGroupIsolatedB exactIds idSets) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (RSA_rbBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aAncestry group parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams
  exact ⟨hmergedB fuel P inp o group titleLines titleHeight parent child res hexpand hframed
    hctxB hparams, hisoB fuel P inp o group titleLines titleHeight parent child res hexpand
    hframed hctxB hparams⟩

end PipelineImpl
end Layered


end Elegant
