import Elegant.Layered.RegionFallbackAncestorActiveGroup
import Elegant.Layered.RegionFallbackAncestorActiveLeaf
import Elegant.Layered.RegionFallbackAncestorInactive
import Elegant.Layered.RegionFallbackFitProof

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

theorem R_selectedDirectFrameStrict_closed (exactIds : List String)
    (idSets : List (String × List String)) : R_SelectedDirectFrameStrict exactIds idSets := by
  intro inp o res e hwf hfp part candidate spec' cg run _ _ _ hcomp hselected hrun _ _
    memberIndex key parentKey parentIndex member hkey hkeyLen hmember child hchild
    parent hparent href hne hparentIndex
  obtain ⟨regions, hregions, hspec⟩ := hselected
  have hresolved : newComponentRegions spec' e.params inp
      (componentCandidateR spec' e.graph part.1 candidate) = .ok regions := by
    rw [hspec]
    exact componentTrialR_selected_regions candidate hregions
  cases regions with
  | none =>
    exact regionSelectedInactiveFrameStrict e hwf hfp hcomp ⟨none, hregions, hspec⟩
      hrun hresolved hkey hparentIndex hchild hparent href hne
  | some rm =>
    cases spec' with
    | none =>
      have himpossible : (none : Option ComponentRegions) = some rm := Except.ok.inj hresolved
      cases himpossible
    | some s =>
      rcases active_candidate_source_border e hcomp hmember hkey hkeyLen with hgroup | hplain
      · obtain ⟨p, hp, hpid, hrole, hfixed⟩ :=
          framedParents_parent hfp (List.mem_of_getElem? hchild) hne
        have he := eq_of_mem_id (Model.boxIds_nodup hwf) hp
          (List.mem_of_getElem? hparent) (hpid.trans href)
        subst p
        have heffective : (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
            else box)[parentKey]? = some parent := by
          simp only [List.getElem?_map, hparent, Option.map_some, hfixed, Bool.false_eq_true,
            ↓reduceIte]
        have hlen : parentKey < e.lines.length := by
          rw [boxLines_length e.lines_eq]
          exact (List.getElem?_eq_some_iff.mp hparent).1
        obtain ⟨raw, _, hraw, _, hrawBorder, _, hrawDecl, _, _, _, _, _⟩ :=
          measuredGraph_paired_markers e.graph0_eq hlen heffective hrole
        obtain ⟨top, htop, htopBorder, _, htopDecl⟩ := exactGraph_node_key e.graph_eq hraw
        have htopCandidate := component_node_lookupR (spec := some s) (cand := candidate)
          hparentIndex htop
        obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
          componentRunR_active_allocation_stages hrun hresolved
        have hnodes := rankEquivalentR_nodes_eq hrank
        have htopRun : cg.nodes[parentIndex]? = some top := by
          rw [hnodes]
          exact htopCandidate
        have hmemberRun : cg.nodes[memberIndex]? = some member := by
          rw [hnodes]
          exact hmember
        have hparentDecl : top.decl = parentKey := htopDecl.trans hrawDecl
        have hmemberKey := (active_candidate_top_source e hcomp hmember hgroup).1
        have hchildDecl : member.decl = key := Option.some.inj (hmemberKey.symm.trans hkey)
        have hparentSource : inp.boxes[top.decl]? = some parent := by rwa [hparentDecl]
        have hchildSource : inp.boxes[member.decl]? = some child := by rwa [hchildDecl]
        exact regionActiveDirectGroupFrame_strict e hwf hfp hcomp hrun hresolved
          htopRun (htopBorder.trans hrawBorder) hmemberRun hgroup hparentSource hchildSource href hne
      · exact regionActiveSelectedDirectLeaf_strict e hwf hfp hcomp hrun hresolved
          hparentIndex hkey hmember hplain hparent hchild href hne

theorem R_ancestorFrameStrictW_closed (exactIds : List String)
    (idSets : List (String × List String)) : R_AncestorFrameStrictW exactIds idSets :=
  R_ancestorFrameStrictW_of_selected exactIds idSets (R_selectedDirectFrameStrict_closed exactIds idSets)

theorem R_fallbackCaptionClearB8W_selected_closed (exactIds : List String)
    (idSets : List (String × List String)) : R_FallbackCaptionClearBW exactIds idSets :=
  R_fallbackCaptionClearB8W_holds exactIds idSets (R_ancestorFrameStrictW_closed exactIds idSets)

end Elegant.Layered.PipelineImpl

