import Elegant.Layered.RegionC7ActiveCaptionCutover
import Elegant.Layered.RegionC8aGroupPlain
import Elegant.Layered.ForeignNonGroupSpansProof

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- The installed caption uses the selected title's origin but substitutes the
measured dimensions from the same declaration. Its raw cross-axis interval is
therefore contained in the executed title slot, before any scene orientation. -/
theorem r7Caption_installed_active_foreign_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hforeign : pair.targetNode.clusterPath.contains pair.topNode.decl = false) :
    R7_OverlapRowsXGap l.rect b.rect := by
  obtain ⟨rs, hrs, heff⟩ := pair.effective_eq
  have hresolve := componentTrialR_selected_regions pair.candidate hrs
  change newComponentRegions (r7Eff idSets o execution.params execution.lines rs)
    execution.params inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph pair.part.1 pair.candidate) = .ok rs at hresolve
  rw [← heff, hs] at hresolve
  have hsome : ∃ rm, rs = some rm := by
    cases rs with
    | none => rw [hs] at heff; simp [r7Eff] at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hresolve
  have hrun := pair.run_eq
  rw [hs] at hrun
  have hpart := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem hpart
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hresolve
  have hnodes := rankEquivalentR_nodes_eq hrank
  have htop := pair.top_eq
  have htarget := pair.target_eq
  rw [hnodes] at htop htarget
  obtain ⟨htopKey, _, owner, howner⟩ :=
    active_candidate_top_source execution hcomp htop pair.top_border
  have hdecl := active_candidate_plain_decl execution hcomp htarget pair.target_plain
    pair.target_pos pair.target_source
  have htargetKey : pair.part.1[pair.targetPos]? = some pair.targetNode.decl := by
    rw [hdecl]
    exact pair.target_pos
  have htargetSource : inp.boxes[pair.targetNode.decl]? = some pair.targetSource := by
    rw [hdecl]
    exact pair.target_source
  obtain ⟨_, _, _, _, htitle, hgap⟩ := active_group_plain_slot_geometry execution hwf hfp hcomp
    hrun hresolve pair.top_eq pair.target_eq pair.top_border pair.target_plain htopKey htargetKey
    (groupSource := owner) howner htargetSource hforeign
  obtain ⟨hleft, hright⟩ := htitle pair.raw.2 pair.top_mem
  let bounds := placeBoundsX execution.params pair.cg pair.run execution.measured pair.loops
  let stored := (pair.raw.1, shiftRect (0 - bounds.minX) (-bounds.minY) pair.raw.2)
  have hstored : stored ∈ pair.part.2.titles := by
    rw [pair.part_eq]
    change stored ∈ (componentTitles execution.params pair.cg pair.run).map
      (fun q => (q.1, shiftRect (0 - bounds.minX) (-bounds.minY) q.2))
    exact List.mem_map.mpr ⟨pair.raw, pair.top_mem, rfl⟩
  let size := titleCaptionSize execution.params o (execution.lines.getD oi [])
  have hsize : size.w ≤ pair.raw.2.w := by
    have hfit := R_exactTitleCaptionFitB8_holds exactIds idSets execution hpart hstored
    have hindex : pair.part.1.getD pair.raw.1 0 = oi := by
      simp only [List.getD_eq_getElem?_getD, pair.owner_pos, Option.getD_some]
    change 0 ≤ (titleCaptionSize execution.params o
      (execution.lines.getD (pair.part.1.getD pair.raw.1 0) [])).w ∧
      0 ≤ (titleCaptionSize execution.params o
        (execution.lines.getD (pair.part.1.getD pair.raw.1 0) [])).h ∧
      (titleCaptionSize execution.params o
        (execution.lines.getD (pair.part.1.getD pair.raw.1 0) [])).w ≤ pair.raw.2.w ∧
      (titleCaptionSize execution.params o
        (execution.lines.getD (pair.part.1.getD pair.raw.1 0) [])).h ≤ pair.raw.2.h at hfit
    rw [hindex] at hfit
    exact hfit.2.2.1
  let rawCaption : Rect := { pair.raw.2 with w := size.w, h := size.h }
  have hclear : Disjoint rawCaption
      (frameRect execution.params pair.cg pair.run pair.targetPos) := by
    apply rect_disjoint_of_x
    change pair.raw.2.x + size.w ≤ (frameRect execution.params pair.cg pair.run pair.targetPos).x ∨
      (frameRect execution.params pair.cg pair.run pair.targetPos).x +
        (frameRect execution.params pair.cg pair.run pair.targetPos).w ≤ pair.raw.2.x
    rcases hgap with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Int.le_trans h hleft)
  have hlabel : l.rect = r7SelectedTransport execution pair.shelf pair.cg pair.run pair.loops
      rawCaption := pair.label_rect
  have hscene : Disjoint l.rect b.rect := by
    rw [hlabel, pair.box_rect]
    unfold r7SelectedTransport
    exact disjoint_sceneTransport (not_meetsInterior_shiftRect hclear)
  change ¬ l.rect.meetsInterior b.rect at hscene
  unfold R7_OverlapRowsXGap Rect.meetsInterior at *
  intro hrows hlw hbw
  omega

/-- Closes only the caption projection of the selected C7 seam. -/
theorem r7Caption_activeEqualRank_holds {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    R7_SelectedCaptionActiveEqualRankResidual execution := by
  intro l b _ _ _ _ _ _ _ _ _ _ _ hrows hlw hbw hcase
  obtain ⟨_, _, _, pair, spec, hs, hforeign, _⟩ := hcase
  exact r7Caption_installed_active_foreign_clear hwf hfp pair (spec := spec) hs hforeign
    hrows hlw hbw

end Elegant.Layered.PipelineImpl
