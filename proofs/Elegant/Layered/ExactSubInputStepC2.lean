import Elegant.Layered.ExactPipeline
import Elegant.Layered.FamilyC5B
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.RecursiveC2
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveFit
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SelectFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Sub-input well-formedness and the C2 step for the exact pipeline

Base-dependence classification (plain proof in `SubInputWellFormedFacts.lean`,
C2 chain in `ExpandChildC2Facts.lean` / `RecursiveC1C3.lean`):

* `subInputWellFormed` ignores every hypothesis that mentions `layoutRecursive`
  (fuel and both recursive successes are discarded); its conclusions follow
  from `WellFormed`, `framedParents`, and `selectInput` preservation alone.
  Hence `subInputWellFormedB_of` is generic in `base` with no base facts.
* `ExpandChildC2Step` is base-independent (it mentions only the input and the
  two scenes). Its discharge needs two exact-run facts: the leaf mirror fact
  (`X_layout_box_parent`, from `sceneOf`, which `layoutX` shares with `layout`)
  and the leaf id fact (`X_layout_ids`), plus the `B`-recursion lifts built
  from them (`X_rec_box_parent`, `X_rec_parent_in_ids`, `X_rec_parent_closed`).
  Everything else (`expandChild_parent_closed`, `expandChild_sources`,
  `selectInput_*`, `subInputWellFormedC2`, `framedParents_*`,
  `keepInside_close` / `keepOutside_close`) is reused unchanged.
-/

/-- The sub-input seam at an arbitrary base: the plain proof never looks at
the recursive successes, so no base facts are needed. -/
theorem subInputWellFormedB_of
    (base : Input → Options → Except LayoutError FamilyResult) :
    SubInputWellFormedB base := by
  intro _fuel inp o group _P _metric _titleLines child _parent hwf hframed
    _hP _hm _hwrap _hchild _hparent
  refine ⟨selectInput_wellFormed inp o
      (fun box => Compound.inside inp.boxes group.id box.id) group.id hwf
      (fun c hc hkept => keepInside_close (group := group.id)
        (inputFacts_of_wellFormed hwf) hc hkept)
      (childSubOptions o group),
    framedParents_selectInput_inside inp o group hwf hframed, ?_, ?_⟩
  · exact inputModel_wellFormed_fixed_congr
        (p := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "") _ _ _
      (selectInput_wellFormed inp o
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hwf
        (fun c hc hkept => keepOutside_close (group := group.id)
          (inputFacts_of_wellFormed hwf) hc hkept) o)
  · exact framedParents_selectInput_outside_append inp o group hwf hframed
      _ child.scene child.itemArea

/-- The sub-input seam at the exact base. -/
theorem subInputWellFormedB_layoutX (exactIds : List String) :
    SubInputWellFormedB (layoutX exactIds) :=
  subInputWellFormedB_of (layoutX exactIds)

/-- Exact leaf id fact: `layoutX` builds its scene with the same `sceneOf`
call as `layout`, so the proof is `layout_ids` with one extra bind for the
`exactGraph` step and one for the `straightenAcc` step. -/
private theorem X_layout_ids {exactIds : List String} {inp : Input} {o : Options}
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
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf, List.map_map]
    exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

/-- Exact leaf mirror fact: every exact scene box carries the id and parent
pointer of a source input box. -/
private theorem X_layout_box_parent {exactIds : List String} {inp : Input} {o : Options}
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
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf]
    intro cb hcb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
    exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Exact flat parent closure, from the two leaf facts above. -/
private theorem X_layout_parent_closed {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hf : InputFacts inp) (h : layoutX exactIds inp o = .ok res) :
    SceneParentClosed res.scene := by
  intro bb hbb
  obtain ⟨hidsB, _⟩ := X_layout_ids h
  obtain ⟨sb, hsb, _, hsbpar⟩ := X_layout_box_parent h bb hbb
  rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
  · rw [hsbpar]; exact Or.inl h0
  · have hqidIn : q.id ∈ res.scene.boxes.map (·.id) := by
      rw [hidsB]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨bb', hbb', hbb'id⟩ := List.mem_map.mp hqidIn
    rw [hsbpar]
    exact Or.inr ⟨bb', hbb', hbb'id.trans hqid⟩

/-- Successor split for `layoutRecursiveB` at the exact base, in the shape of
`layoutRecursive_succ`: the concrete appended tables are generalized to
`∃ a b c` so the induction proofs below copy the plain ones verbatim. -/
private theorem X_B_succ (exactIds : List String) {fuel : Nat} {inp : Input} {o : Options}
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

/-- Exact `B`-recursion mirror fact: every scene box of a successful exact
recursive layout carries the id and parent pointer of a source input box. -/
private theorem X_rec_box_parent (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact X_layout_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact X_layout_box_parent hlayout
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

/-- Exact `B`-recursion coverage: every nonempty parent pointer of a result
scene box names an input box id of the laid-out input. -/
private theorem X_rec_parent_in_ids (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ p ∈ res.scene.boxes, p.parent ≠ "" → p.parent ∈ inp.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h p hp hne
      obtain ⟨sb, hsb, _, hsbpar⟩ := X_layout_box_parent h p hp
      rw [hsbpar] at hne ⊢
      rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
      · exact absurd h0 hne
      · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  | succ fuel ih =>
      intro inp o res hf h p hp hne
      rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · obtain ⟨sb, hsb, _, hsbpar⟩ := X_layout_box_parent hlayout p hp
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
              have hcov := ih _ _ _ hchildFacts hchild cb hcbmem hcb0
              exact selectInput_ids_subset inp
                (fun box => Compound.inside inp.boxes group.id box.id) group.id hcov
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

/-- Exact `B`-recursion parent closure: every nonempty parent pointer of a
result scene stays inside that scene. -/
private theorem X_rec_parent_closed (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      SceneParentClosed res.scene := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h
      exact X_layout_parent_closed hf h
  | succ fuel ih =>
      intro inp o res hf h
      rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · exact X_layout_parent_closed hf hlayout
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
          have hci := X_rec_parent_in_ids exactIds fuel _ _ _ hchildFacts hchild q hq hne
          exact selectInput_ids_subset inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
        have hcoverP : ∀ q ∈ parent.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hpi := X_rec_parent_in_ids exactIds fuel _ _ _ hparentFacts hparent q hq hne
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

/-- Parent closure of a successful exact recursive layout from well-formedness
of the original input model alone. -/
private theorem X_rec_parent_closed_wellFormed (exactIds : List String)
    {inp : Input} {o : Options} (hwf : WellFormed (inputModel inp o)) :
    ∀ (fuel : Nat) (res : FamilyResult),
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
        SceneParentClosed res.scene := by
  intro fuel res h
  exact X_rec_parent_closed exactIds fuel inp o res (inputFacts_of_wellFormed hwf) h

/-- Discharge of `ExpandChildC2Step` for an `expandChild` call the exact
`B`-recursion performs: the `B`-context supplies well-formedness, the group
witness, the parent-input box list, and the two recursive successes. -/
private theorem X_c2_step_of_recursion (exactIds : List String)
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
    (hchild : layoutRecursiveB (layoutX exactIds) fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel pInput o = .ok parent)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ExpandChildC2Step P inp o group titleHeight parent child res := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
      ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
    intro keep root
    rw [selectInput_box_ids]
    exact nodup_filter_map keep (·.id) inp.boxes hnodup
  have hchildParent := X_rec_box_parent exactIds _ _ _ _ (hselNodup _ _) hchild
  have hparentParent := X_rec_box_parent exactIds _ _ _ _
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

/-- The `stepC2` seam of `BaseSeams` at `base := layoutX exactIds`: every
`expandChild` call the exact recursion performs satisfies `ExpandChildC2Step`.
The binders match `FamilyAssemblyB.lean` `stepC2` lines 75-84, whose file is
not imported here. -/
theorem stepC2_layoutX (exactIds : List String) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC2Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res _hexpand
    hids hctx _hparams
  obtain ⟨hwf, hgroup, hpboxes, hchild, hparent, _hexpand2⟩ := hctx
  obtain ⟨hchildWf, hparentWf⟩ := subInputWellFormedC2 inp o group hwf
  have hclosed : SceneParentClosed parent.scene ∧ SceneParentClosed child.scene :=
    ⟨X_rec_parent_closed_wellFormed exactIds (hparentWf _ _ _) fuel parent hparent,
     X_rec_parent_closed_wellFormed exactIds hchildWf fuel child hchild⟩
  exact X_c2_step_of_recursion exactIds (hwf := hwf) (hids := hids)
    (hclosed := hclosed) (hgroup := hgroup) (hpboxes := hpboxes)
    (hchild := hchild) (hparent := hparent) _hexpand

end PipelineImpl
end Layered
end Elegant
