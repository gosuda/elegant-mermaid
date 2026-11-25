import Elegant.Layered.RegionForwardChildCutover
import Elegant.Layered.RegionC8aSelectedGroupPairs
import Elegant.Layered.RegionTitleCaptionFit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- An active chosen part with a genuine installed title and a target in a separated
allocation branch. Plain targets include source groups demoted to fixed boxes. -/
def R8b_ActiveForeignCaption {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (i pos : Nat) : Prop :=
  ∃ (s : RegionSpec) (owner target : Node), selected.spec = some s ∧
    selected.cg.nodes[i]? = some owner ∧ owner.border = -2 ∧
    selected.cg.nodes[pos]? = some target ∧ target.clusterPath.contains owner.decl = false ∧
    (target.border = 0 ∨ (target.border = -2 ∧ owner.decl ≠ target.decl ∧
      owner.clusterPath.contains target.decl = false))

private theorem activeForeignCaption_rawClear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hpart : part ∈ execution.componentsAcc.parts)
    {i pos key : Nat} {src : ModelBox} {raw : Rect}
    (hkey : part.1[pos]? = some key) (hsrc : inp.boxes[key]? = some src)
    (htitle : (i, raw) ∈ componentTitles execution.params selected.cg selected.run)
    (hforeign : R8b_ActiveForeignCaption selected i pos)
    (width height : Int) (hwidth : width ≤ raw.w) :
    Disjoint (frameRect execution.params selected.cg selected.run pos)
      { raw with w := width, h := height } := by
  obtain ⟨s, owner, target, hs, ho, htop, ht, hforeign, hkind⟩ := hforeign
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem hpart
  have hrun := selected.run_eq
  rw [hs] at hrun
  have hresolved : newComponentRegions selected.spec execution.params inp
      (componentCandidateR selected.spec execution.graph part.1 selected.candidate) =
        .ok selected.regions := by
    rw [selected.effective_eq]
    exact componentTrialR_selected_regions _ selected.regions_eq
  rw [hs] at hresolved
  obtain ⟨rm, hrm⟩ : ∃ rm, selected.regions = some rm := by
    cases h : selected.regions with
    | none =>
      have he := selected.effective_eq
      rw [hs, h] at he
      simp at he
    | some rm => exact ⟨rm, rfl⟩
  rw [hrm] at hresolved
  rcases hkind with hp | ⟨htop', hne, hreverse⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
      componentRunR_active_allocation_stages hrun hresolved
    have hnodes := rankEquivalentR_nodes_eq hrank
    have ho' := ho
    have ht' := ht
    rw [hnodes] at ho' ht'
    obtain ⟨hOwnerKey, _, _, hOwnerSource⟩ := active_candidate_top_source execution hcomp ho' htop
    have htdecl := active_candidate_plain_decl execution hcomp ht' hp hkey hsrc
    obtain ⟨_, _, _, _, hbounds, hgap⟩ := active_group_plain_slot_geometry execution hwf hfp
      hcomp hrun hresolved ho ht htop hp hOwnerKey (by rwa [htdecl]) hOwnerSource
      (by rwa [htdecl]) hforeign
    obtain ⟨hlo, hhi⟩ := hbounds raw htitle
    apply rect_disjoint_of_x
    dsimp only
    rcases hgap with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · exact active_foreign_group_title_disjoint execution hwf hcomp hrun hresolved ho ht htop
      htop' hne hforeign hreverse htitle width height hwidth

theorem r8b_activeForeignCaption_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hpart : part ∈ execution.componentsAcc.parts)
    {i pos key : Nat} {src : ModelBox} {stored frame : Rect}
    (hmem : (i, stored) ∈ part.2.titles) (hkey : part.1[pos]? = some key)
    (hsrc : inp.boxes[key]? = some src) (hframe : part.2.rects[pos]? = some frame)
    (hforeign : R8b_ActiveForeignCaption selected i pos) :
    let size := titleCaptionSize execution.params o (execution.lines.getD (part.1.getD i 0) [])
    Disjoint frame { stored with w := size.w, h := size.h } := by
  let bounds := placeBoundsX execution.params selected.cg selected.run execution.measured selected.loops
  let dx := 0 - bounds.minX
  let dy := -bounds.minY
  let size := titleCaptionSize execution.params o (execution.lines.getD (part.1.getD i 0) [])
  have hfit := R_exactTitleCaptionFitB8_holds exactIds idSets execution hpart hmem
  have hwidth : size.w ≤ stored.w := hfit.2.2.1
  have hmem' := hmem
  rw [selected.part_eq] at hmem'
  change (i, stored) ∈ (componentTitles execution.params selected.cg selected.run).map
    (fun q => (q.1, shiftRect dx dy q.2)) at hmem'
  obtain ⟨⟨j, raw⟩, hraw, he⟩ := List.mem_map.mp hmem'
  obtain ⟨he, hstored⟩ := Prod.mk.inj he
  change j = i at he
  subst j
  have hrawWidth : size.w ≤ raw.w := by
    rw [← hstored] at hwidth
    exact hwidth
  have hframe' := hframe
  rw [selected.part_eq] at hframe'
  change (((List.range selected.cg.nodes.length).map
    (frameRect execution.params selected.cg selected.run)).map (shiftRect dx dy))[pos]? =
      some frame at hframe'
  have hpos : pos < selected.cg.nodes.length := by
    simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp hframe').1
  simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some, Option.some.injEq] at hframe'
  have hclear := activeForeignCaption_rawClear selected hwf hfp hpart hkey hsrc hraw hforeign
    size.w size.h hrawWidth
  change Disjoint frame { stored with w := size.w, h := size.h }
  rw [← hframe', ← hstored]
  exact disjoint_shiftRect hclear

/-- Keeps exactly the prior route remainder, and leaves only captions outside
an executed active foreign allocation branch. Nested/self/inactive pairs still
retain their disjoint-or-strictly-inside contract. -/
def R_ExecutedPartFrameCoresB8ForeignCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ part ∈ execution.componentsAcc.parts,
      (∀ (selected : R8b_ChosenPart execution part)
        (index : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (index, stored) ∈ part.2.labels → part.1[pos]? = some key →
        inp.boxes[key]? = some src → src.role = .group → part.2.rects[pos]? = some frame →
        ¬ R8b_EmittedOuterReversedAt selected index stored pos →
        ¬ R8b_EmittedReservedChildAt selected index pos →
        ¬ R8b_EmittedDemotedReversedAt selected index stored pos src →
        ¬ R8b_EmittedSelectedLoopFrameAt selected index pos →
        ¬ R8b_EmittedForwardChildAt selected index pos →
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      (∀ (selected : R8b_ChosenPart execution part)
        (i : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (i, stored) ∈ part.2.titles → part.1[pos]? = some key →
        inp.boxes[key]? = some src → src.role = .group → part.2.rects[pos]? = some frame →
        ¬ R8b_ActiveForeignCaption selected i pos →
        let size := titleCaptionSize execution.params o (execution.lines.getD (part.1.getD i 0) [])
        Disjoint frame { stored with w := size.w, h := size.h } ∨
          frame.StrictInside { stored with w := size.w, h := size.h })

theorem R_loopForwardChildRemainder_iff_foreignCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8LoopForwardChildRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8ForeignCaptionRemainder exactIds idSets := by
  classical
  constructor
  · intro h inp o res execution hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h execution hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro _ i stored pos key src frame hm hk hs hg hf _
    exact hcaption i stored pos key src frame hm hk hs hg hf
  · intro h inp o res execution hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h execution hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    obtain ⟨selected⟩ := r8b_chosenPart execution hpart
    intro i stored pos key src frame hm hk hs hg hf
    by_cases hx : R8b_ActiveForeignCaption selected i pos
    · exact Or.inl (r8b_activeForeignCaption_disjoint selected hwf hfp hpart hm hk hs hf hx)
    · exact hcaption selected i stored pos key src frame hm hk hs hg hf hx

theorem flatC8bB_layoutRIds_foreignCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8ForeignCaptionRemainder exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (layoutRIds exactIds idSets) :=
  flatC8bB_layoutRIds_loopForwardChildRemainder exactIds idSets
    ((R_loopForwardChildRemainder_iff_foreignCaptionRemainder exactIds idSets).mpr hcores)
    hfallW hres hcap

end Elegant.Layered.PipelineImpl
