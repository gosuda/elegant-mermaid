import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionPipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Region sub-input well-formedness and the C2 step (packet P10)

Region twins of `subInputWellFormedB_layoutX` (`ExactSubInputStepC2.lean:65-68`)
and `stepC2_layoutX` (`:419-424`) for the reindexing base
`fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'`.
The exact proofs use only the leaf id fact plus the `B`-recursion lifts, so the
region proofs do not depend on `idSets`: `sceneOf` copies box ids/routes/parents
verbatim and never looks at the spec.

Truth probes (executed below by `#eval`):
* `rbProbeIdsOk` is `true`: on the two-region probe, box and route id lists of a
  successful `layoutRIds` run equal the input lists.
* `rbProbeLabelsKept` is `["lx"]`: the dangling label `ld` (owner `ZZZ` names no
  box) is dropped by `sceneOf`, so unconditional label-id preservation is FALSE.
  The proved `RB_layout_ids` therefore covers boxes and routes only, exactly like
  its `XB_layout_ids` twin; no label conclusion is stated.
* `rbProbeNestedOk` is `true`: same id check on a nested-region witness with a
  backward route (`eBack` runs against declaration order).
-/

/-- Two-region probe input (same shape as `rapProbeInp`). -/
private def rbProbeInp : Input :=
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

/-- Resolved region sets of the probe, as `graphRegions` would produce. -/
private def rbProbeIdSets : List (String × List String) :=
  [("G1", ["A", "B"]), ("G2", ["C", "D"])]

/-- Id preservation on the two-region probe. -/
private def rbProbeIdsOk : Bool :=
  match layoutRIds [] rbProbeIdSets rbProbeInp { profile := .vector, direction := .TB } with
  | .ok res =>
    res.scene.boxes.map (·.id) == rbProbeInp.boxes.map (·.id) &&
    res.scene.routes.map (·.id) == rbProbeInp.routes.map (·.id)
  | .error _ => false

#eval rbProbeIdsOk

/-- The probe with one owned and one dangling label. -/
private def rbProbeInpLabels : Input :=
  { rbProbeInp with labels := [{ id := "lx", owner := "a1", text := "hi" },
    { id := "ld", owner := "ZZZ", text := "dangling" }] }

/-- Scene label ids on the label probe: the dangling label is dropped. -/
private def rbProbeLabelsKept : List String :=
  match layoutRIds [] rbProbeIdSets rbProbeInpLabels { profile := .vector, direction := .TB } with
  | .ok res => res.scene.labels.map (·.id)
  | .error _ => ["<error>"]

/-- Nested-region probe: `R1` sits inside `G` and regions nest inside `R1`;
`eBack` runs against declaration order. -/
private def rbProbeNestedInp : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
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
private def rbProbeNestedIdSets : List (String × List String) :=
  [("G", ["R1", "B"]), ("R1", ["A", "C"])]

/-- Id preservation on the nested-region probe. -/
private def rbProbeNestedOk : Bool :=
  match layoutRIds [] rbProbeNestedIdSets rbProbeNestedInp
    { profile := .vector, direction := .TB } with
  | .ok res =>
    res.scene.boxes.map (·.id) == rbProbeNestedInp.boxes.map (·.id) &&
    res.scene.routes.map (·.id) == rbProbeNestedInp.routes.map (·.id)
  | .error _ => false

#eval rbProbeNestedOk

#eval rbProbeLabelsKept
/-- Region leaf id fact, twin of `XB_layout_ids`: a successful `layoutRIds`
run keeps the input box and route id lists, for every `idSets`. The proof goes
through the `SceneExecutionR` record (`layoutRIds_sceneExecution`) instead of
peeling binds: `sceneOf` builds both lists from the input by `zipIdx.map`. -/
theorem RB_layout_ids {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  rw [execution.scene_eq]
  simp only [sceneOf, List.map_map]
  exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

/-- Region leaf mirror fact, twin of `X_layout_box_parent`: every region scene
box carries the id and parent pointer of a source input box. -/
private theorem RB_layout_box_parent {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  rw [execution.scene_eq]
  simp only [sceneOf]
  intro cb hcb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
  exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩
/-- The reindexing base of packet P10. -/
private abbrev rbBase (exactIds : List String) (idSets : List (String × List String)) :
    Input → Options → Except LayoutError FamilyResult :=
  fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'

/-- Successor split for `layoutRecursiveB` at the reindexing base, in the shape
of `layoutRecursive_succ`: the concrete appended tables are generalized to
`∃ a b c` so the induction proofs below copy the plain ones verbatim. -/
private theorem RB_B_succ (exactIds : List String) (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRecursiveB (rbBase exactIds idSets) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      rbBase exactIds idSets inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (rbBase exactIds idSets) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursiveB (rbBase exactIds idSets) fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursiveB_succ_sources (rbBase exactIds idSets) h with hflat |
    ⟨group, P, _metric, child, _titleLines, parent, hg, _, _, hc, _, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩
/-- Region `B`-recursion mirror fact: every scene box of a successful region
recursive layout carries the id and parent pointer of a source input box. -/
private theorem RB_rec_box_parent (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (rbBase exactIds idSets) fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact RB_layout_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases RB_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact RB_layout_box_parent hlayout
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


/-- Region `B`-recursion coverage: every nonempty parent pointer of a result
scene box names an input box id of the laid-out input. -/
private theorem RB_rec_parent_in_ids (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (rbBase exactIds idSets) fuel inp o = .ok res →
      ∀ p ∈ res.scene.boxes, p.parent ≠ "" → p.parent ∈ inp.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h p hp hne
      obtain ⟨sb, hsb, _, hsbpar⟩ := RB_layout_box_parent h p hp
      rw [hsbpar] at hne ⊢
      rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
      · exact absurd h0 hne
      · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  | succ fuel ih =>
      intro inp o res hf h p hp hne
      rcases RB_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · obtain ⟨sb, hsb, _, hsbpar⟩ := RB_layout_box_parent hlayout p hp
        rw [hsbpar] at hne ⊢
        rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
        · exact absurd h0 hne
        · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      · obtain ⟨_, _metric, _titleLines, _lines, dx, dy, _hframe, _, _, _, _, _, _,
          hboxes⟩ := expandChild_sources hexpand
        rw [hboxes] at hp
        obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hp
        have hfound : p ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hfound with hcb | hpb
        · obtain ⟨cb, hcbmem, hE⟩ := List.mem_map.mp hcb
          have hproj : p.parent = (if cb.parent == "" then group.id else cb.parent) := by
            have hpar := congrArg (fun bx : Box => bx.parent) hE
            simpa [embedBox] using hpar.symm
          by_cases hcb0 : cb.parent = ""
          · rw [hproj]
            split
            · exact List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some hg, rfl⟩
            · rename_i hcond
              exact absurd (beq_iff_eq.mpr hcb0) hcond
          · rw [hproj]
            split
            · rename_i hcond
              exact absurd (beq_iff_eq.mp hcond) hcb0
            · have hchildFacts := selectInput_facts_inside inp group hf
              have hci := ih _ _ _ hchildFacts hchild cb hcbmem hcb0
              exact selectInput_ids_subset inp
                (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
        · have hparentFacts : InputFacts { selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) with
              fixedSizes := a, fixedChildren := b, fixedAreas := c } :=
            inputFacts_congr
              (rfl : (selectInput inp
                (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes =
                  { selectInput inp
                    (fun box => !Compound.inside inp.boxes group.id box.id) with
                    fixedSizes := a, fixedChildren := b, fixedAreas := c }.boxes)
              (selectInput_facts_outside inp group hf)
          have hpIn := ih _ _ _ hparentFacts hparent p hpb hne
          exact selectInput_ids_subset inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" hpIn

/-- Region flat parent closure, from the two leaf facts. -/
private theorem RB_layout_parent_closed {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (hf : InputFacts inp)
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    SceneParentClosed res.scene := by
  intro bb hbb
  obtain ⟨hidsB, _⟩ := RB_layout_ids h
  obtain ⟨sb, hsb, _, hsbpar⟩ := RB_layout_box_parent h bb hbb
  rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
  · rw [hsbpar]; exact Or.inl h0
  · have hqidIn : q.id ∈ res.scene.boxes.map (·.id) := by
      rw [hidsB]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨bb', hbb', hbb'id⟩ := List.mem_map.mp hqidIn
    rw [hsbpar]
    exact Or.inr ⟨bb', hbb', hbb'id.trans hqid⟩

/-- Region `B`-recursion parent closure: every nonempty parent pointer of a
result scene stays inside that scene. -/
private theorem RB_rec_parent_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (rbBase exactIds idSets) fuel inp o = .ok res →
      SceneParentClosed res.scene := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h
      exact RB_layout_parent_closed hf h
  | succ fuel ih =>
      intro inp o res hf h
      rcases RB_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · exact RB_layout_parent_closed hf hlayout
      · have hchildFacts := selectInput_facts_inside inp group hf
        have hparentFacts : InputFacts { selectInput inp
            (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } :=
          inputFacts_congr
            (rfl : (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes =
                { selectInput inp
                  (fun box => !Compound.inside inp.boxes group.id box.id) with
                  fixedSizes := a, fixedChildren := b, fixedAreas := c }.boxes)
            (selectInput_facts_outside inp group hf)
        have hcc := ih _ _ _ hchildFacts hchild
        have hpc := ih _ _ _ hparentFacts hparent
        have hcoverC : ∀ q ∈ child.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hci := RB_rec_parent_in_ids exactIds idSets fuel _ _ _ hchildFacts hchild q hq hne
          exact selectInput_ids_subset inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
        have hcoverP : ∀ q ∈ parent.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hpi := RB_rec_parent_in_ids exactIds idSets fuel _ _ _ hparentFacts hparent q hq hne
          exact selectInput_ids_subset inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" hpi
        have hgroupRes : ∃ q ∈ res.scene.boxes, q.id = group.id := by
          obtain ⟨frame, _, _, _, dx, dy, hframe, _, _, _, _, _, _, hboxes⟩ :=
            expandChild_sources hexpand
          have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
          cases hF : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
              parent.scene.boxes).find? (fun box => box.id == group.id) with
          | none =>
              have hnone := List.find?_eq_none.mp hF frame
                (List.mem_append_right _ (List.mem_of_find?_eq_some hframe))
              rw [hframeId] at hnone
              simp at hnone
          | some f =>
              refine ⟨f, ?_, ?_⟩
              · rw [hboxes]
                exact filterMap_mem_of_find (fun m : ModelBox => m.id) inp.boxes
                  (fun bx : Box => bx.id) _ group (List.mem_of_find?_eq_some hg) f hF
              · simpa using List.find?_some hF
        exact expandChild_parent_closed hpc hcc hcoverC hcoverP hgroupRes hexpand

/-- Parent closure of a successful region recursive layout from well-formedness
of the original input model alone. -/
private theorem RB_rec_parent_closed_wellFormed (exactIds : List String)
    (idSets : List (String × List String))
    {inp : Input} {o : Options} (hwf : WellFormed (inputModel inp o)) :
    ∀ (fuel : Nat) (res : FamilyResult),
      layoutRecursiveB (rbBase exactIds idSets) fuel inp o = .ok res →
        SceneParentClosed res.scene := by
  intro fuel res h
  exact RB_rec_parent_closed exactIds idSets fuel inp o res (inputFacts_of_wellFormed hwf) h

/-- Discharge of `ExpandChildC2Step` for an `expandChild` call the region
`B`-recursion performs: the `B`-context supplies well-formedness, the group
witness, the parent-input box list, and the two recursive successes. -/
private theorem RB_c2_step_of_recursion (exactIds : List String)
    (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {group : ModelBox} {P : Params} {child parent : FamilyResult}
    {titleHeight : Int} {pInput : Input}
    (hwf : WellFormed (inputModel inp o))
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hclosed : SceneParentClosed parent.scene ∧ SceneParentClosed child.scene)
    (hgroup : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hpboxes : pInput.boxes = (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes)
    (hchild : layoutRecursiveB (rbBase exactIds idSets) fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child)
    (hparent : layoutRecursiveB (rbBase exactIds idSets) fuel pInput o = .ok parent)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ExpandChildC2Step P inp o group titleHeight parent child res := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
      ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
    intro keep root
    rw [selectInput_box_ids]
    exact nodup_filter_map keep (·.id) inp.boxes hnodup
  have hchildParent := RB_rec_box_parent exactIds idSets _ _ _ _ (hselNodup _ _) hchild
  have hparentParent := RB_rec_box_parent exactIds idSets _ _ _ _
    (by rw [hpboxes]; exact hselNodup _ _) hparent
  refine ⟨⟨hnodup, List.mem_of_find?_eq_some hgroup, hids⟩, hclosed.1, hclosed.2, ?_, ?_⟩
  · intro cb hcb
    obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hchildParent cb hcb
    obtain ⟨m, hmmem, hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
    refine ⟨m, hmmem, ?_, ?_, ?_⟩
    · exact hkeep
    · exact hmsbid.symm.trans hsbid
    · exact hsbpar.trans hmsbpar
  · intro pb hpb
    obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hparentParent pb hpb
    rw [hpboxes] at hsbmem
    obtain ⟨m, hmmem, hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
    refine ⟨m, hmmem, ?_, ?_, ?_⟩
    · exact hkeep
    · exact hmsbid.symm.trans hsbid
    · have hsp : sb.parent = m.parent := by
        rw [hmsbpar]
        exact selectInput_parent_root m.parent
      exact hsbpar.trans hsp

/-- The `subInputB` seam of `BaseSeams` at the reindexing base. The plain proof
never looks at the recursive successes, so no base facts are needed. -/
theorem subInputWellFormedB_layoutRIds (exactIds : List String)
    (idSets : List (String × List String)) :
    SubInputWellFormedB
      (fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o') :=
  subInputWellFormedB_of _



/-- The `stepC2` seam of `BaseSeams` at the reindexing base: every `expandChild`
call the region recursion performs satisfies `ExpandChildC2Step`. The binders
match `FamilyAssemblyB.lean` `stepC2` with
`base := fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'`. -/
theorem stepC2_layoutRIds (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      ExpandChildCallContextB
        (fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o')
        fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC2Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res _hexpand
    hids hctx _hparams
  obtain ⟨hwf, hgroup, hpboxes, hchild, hparent, _hexpand2⟩ := hctx
  obtain ⟨hchildWf, hparentWf⟩ := subInputWellFormedC2 inp o group hwf
  have hclosed : SceneParentClosed parent.scene ∧ SceneParentClosed child.scene :=
    ⟨RB_rec_parent_closed_wellFormed exactIds idSets (hparentWf _ _ _) fuel parent hparent,
     RB_rec_parent_closed_wellFormed exactIds idSets hchildWf fuel child hchild⟩
  exact RB_c2_step_of_recursion exactIds idSets (hwf := hwf) (hids := hids)
    (hclosed := hclosed) (hgroup := hgroup) (hpboxes := hpboxes)
    (hchild := hchild) (hparent := hparent) _hexpand

end PipelineImpl
end Layered
end Elegant
