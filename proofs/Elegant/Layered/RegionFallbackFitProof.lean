import Elegant.Layered.RegionFixedBoxDominance
import Elegant.Layered.PlainNodeSizingFacts
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.RegionC8aGroupPlainCutover

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem captionFit_nonfixed_exact_node {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {g₀ g : Graph}
    (hg : exactGraph P exactIds inp o measured g₀ = .ok g)
    {i : Nat} {source : ModelBox} (hsource : inp.boxes[i]? = some source)
    (hfixed : inp.fixedSizes.any (fun row => row.1 == source.id) = false)
    {node : Node} (hnode : g₀.nodes[i]? = some node) (hdecl : node.decl = i) :
    g.nodes[i]? = some node := by
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, hresult⟩ := bind_ok hg
  have hgnodes : g.nodes = nodes :=
    (congrArg Graph.nodes (Except.ok.inj hresult)).symm
  obtain ⟨out, hstep, hout⟩ := (mapM_getElem? _ _ _ hnodes).2 i node hnode
  have hbox : inp.boxes[node.decl]? = some source := by rwa [hdecl]
  rw [hbox] at hstep
  dsimp only at hstep
  split at hstep
  · simp only [pure, Except.pure] at hstep
    rw [← hgnodes, (Except.ok.inj hstep).symm] at hout
    exact hout
  · have hmissing : inp.fixedSizes.find? (fun row => row.1 == source.id) = none :=
      List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
    simp only [hmissing, throw, throwThe, MonadExceptOf.throw] at hstep
    cases hstep


private theorem captionFit_ordinary_height {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {i : Nat} {source : ModelBox} (hsource : inp.boxes[i]? = some source)
    (hrole : source.role = .node)
    (hfixed : inp.fixedSizes.any (fun row => row.1 == source.id) = false) :
    ((execution.lines.getD i []).length : Int) * execution.params.lineH ≤
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD i default)).h := by
  have hi := (List.getElem?_eq_some_iff.mp hsource).1
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  obtain ⟨_, hlookup⟩ := mapM_getElem? _ _ _ hlines
  obtain ⟨ls, _, hline⟩ := hlookup i (source, i)
    (by simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add])
  obtain ⟨node, hnode₀, hdecl, hborder⟩ := measuredGraph_node_border_zero
    execution.checked execution.graph0_eq hline hsource hrole hfixed
  obtain ⟨sized, hsized, _, hw, hh⟩ := measuredGraph_node_text_fit
    execution.checked execution.graph0_eq hline hsource hrole hfixed
  have hsame : sized = node := Option.some.inj (hsized.symm.trans hnode₀)
  subst sized
  have hnode := captionFit_nonfixed_exact_node execution.graph_eq hsource hfixed hnode₀ hdecl
  obtain ⟨part, pos, k, _, hpart, hpos⟩ := key_part_positionR execution hi
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  have hk : k < packed.boxes.length := by
    rw [Pack.pack_count hpacked, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hpart).1
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some (part, packed.boxes[k]) :=
    List.getElem?_zip_eq_some.mpr ⟨hpart, List.getElem?_eq_getElem hk⟩
  have hindex : i < execution.componentsAcc.rects.size := by
    rwa [execution.components_rects_sizeR]
  obtain ⟨index, cg, run, _, _, spec, hrun, _, _, hrect⟩ :=
    actual_components_packed_frame_sourceR (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected hpos hindex default
  have hcand : (componentCandidateR spec execution.graph part.1 index).nodes =
      part.1.map (fun key => execution.graph.nodes.getD key default) := by
    cases spec with
    | none => exact componentCandidate_nodes _ _ _
    | some _ => rfl
  have hlocal : (componentCandidateR spec execution.graph part.1 index).nodes[pos]? = some node := by
    rw [hcand]
    simp only [List.getElem?_map, hpos, Option.map_some, List.getD_eq_getElem?_getD, hnode,
      Option.getD_some]
  obtain ⟨hwframe, hhframe⟩ := regionRunFrameDims hrun hlocal hborder
  dsimp only at hrect
  rw [List.getD_eq_getElem?_getD, hline, Option.getD_some, hrect]
  have hrawWidth := Int.le_trans hw hwframe
  have hrawHeight := Int.le_trans hh hhframe
  cases hd : o.direction <;>
    simp only [hd, orientRect, shiftRect] at hrawWidth hrawHeight ⊢ <;>
    first | exact hrawHeight | exact hrawWidth

private theorem captionFit_node_contained {P : Params} {box : Box}
    {ls : List Measure.Line} (hrole : box.role = "node")
    (hfit : (ls.length : Int) * P.lineH ≤ box.rect.h) :
    box.rect.Contained (ownedTextRect P box ls) := by
  unfold ownedTextRect
  rw [ite_eq_right (by simp [hrole] : ¬((box.role == "group") = true))]
  have hdiff : 0 ≤ box.rect.h - (ls.length : Int) * P.lineH := by omega
  have hdiv : Int.fdiv (box.rect.h - (ls.length : Int) * P.lineH) 2 =
      (box.rect.h - (ls.length : Int) * P.lineH) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  dsimp only
  rw [hdiv]
  unfold Rect.Contained
  dsimp only
  have hhalf := Int.ediv_le_self 2 hdiff
  have hhalf_nonneg := Int.ediv_nonneg hdiff (by decide : 0 ≤ (2 : Int))
  exact ⟨Int.le_refl _, Int.le_refl _, by omega, by omega⟩

theorem R_ownerCaptionContainFallbackFit_holds (exactIds : List String)
    (idSets : List (String × List String)) : R_OwnerCaptionContainFallbackFit exactIds idSets := by
  intro inp o res execution hfit i source hsource hnone hex hown
  let box : Box := ⟨source.id, source.role.id,
    shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH (execution.packedAcc.rects.getD i default)),
    source.parent, source.exclusive⟩
  have hbox : (sceneBoxesExpr execution.params inp o execution.packedAcc)[i]? = some box := by
    simp only [sceneBoxesExpr, List.getElem?_map, List.getElem?_zipIdx, hsource,
      Option.map_some, Nat.zero_add, box]
  have hscene : res.scene.boxes[i]? = some box := by
    rw [execution.boxes_eq_mapR]
    exact hbox
  have hget : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      i ⟨"", "", default, "", false⟩ = box := by
    rw [List.getD_eq_getElem?_getD, hbox, Option.getD_some]
  dsimp only
  rw [hget]
  have hrole : box.role = source.role.id := rfl
  by_cases hany : inp.fixedSizes.any (fun row => row.1 == source.id) = true
  · have hf := R_fixedOwnerFit_of_dominates exactIds idSets
      (R_fixedBoxDominates_holds exactIds idSets) execution hfit hscene hsource hany hex hown
    by_cases hg : source.role = .group
    · rw [hg] at hf
      simp only [FixedSizeFit] at hf
      have hgroup : box.role = "group" := by simp only [hrole, hg, BoxRole.id]
      rw [ownedTextRect_group_eq hgroup]
      exact titleRect_contained (checkedParams_sizing_nonneg execution.checked).2.1
        hf.1 (Int.le_of_lt hf.2)
    · have hn : source.role = .node := by
        cases hr : source.role with
        | node => rfl
        | group => exact False.elim (hg hr)
      rw [hn] at hf
      simp only [FixedSizeFit] at hf
      have hnode : box.role = "node" := by simp only [hrole, hn, BoxRole.id]
      exact captionFit_node_contained hnode hf
  · have hfixed := Bool.eq_false_iff.mpr hany
    have hn : source.role = .node := by
      cases hr : source.role with
      | node => rfl
      | group =>
        have hsome := R_nonfixedGroupTitle_holds exactIds idSets execution hsource hr hfixed
        rw [hnone] at hsome
        cases hsome
    have hnode : box.role = "node" := by simp only [hrole, hn, BoxRole.id]
    exact captionFit_node_contained hnode (captionFit_ordinary_height execution hsource hn hfixed)

theorem R_ownerFrameDisjointW_holds (exactIds : List String)
    (idSets : List (String × List String)) : R_OwnerFrameDisjointW exactIds idSets := by
  intro inp o res execution hwf hfp ownerIndex obox g hobox _hnone hgMem hgRole
    hne hganc hobanc
  have hC8a := r8a_c8a_of_selectedClearance execution hwf hfp
    ((r8a_selectedClearance_iff_afterGroups execution hwf hfp).mpr
      (r8a_selectedAfterGroupsClearance_holds execution hwf hfp))
  let ownerBox : Box := ⟨obox.id, obox.role.id,
    shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD ownerIndex default)),
    obox.parent, obox.exclusive⟩
  have hbox : (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
      some ownerBox := by
    simp only [sceneBoxesExpr, List.getElem?_map, List.getElem?_zipIdx, hobox,
      Option.map_some, Nat.zero_add, ownerBox]
  have hscene : res.scene.boxes[ownerIndex]? = some ownerBox := by
    rw [execution.boxes_eq_mapR]
    exact hbox
  have hobMem : ownerBox ∈ res.scene.layoutDump.boxes := by
    simpa only [Scene.layoutDump] using List.mem_of_getElem? hscene
  have hgDump : g ∈ res.scene.layoutDump.boxes := by
    simpa only [Scene.layoutDump] using hgMem
  rw [List.getD_eq_getElem?_getD, hbox, Option.getD_some]
  exact hC8a g hgDump hgRole ownerBox hobMem (fun heq => hne heq.symm) hganc hobanc

theorem R_fallbackCaptionClearB8W_holds (exactIds : List String)
    (idSets : List (String × List String))
    (hastrict : R_AncestorFrameStrictW exactIds idSets) :
    R_FallbackCaptionClearBW exactIds idSets := by
  exact R_fallbackCaptionClearB8W_closed exactIds idSets
    (R_ownerCaptionContainFallbackFit_holds exactIds idSets)
    (R_fixedOwnerFit_of_dominates exactIds idSets
      (R_fixedBoxDominates_holds exactIds idSets))
    (R_nonfixedGroupTitle_holds exactIds idSets)
    (R_ownerFrameDisjointW_holds exactIds idSets) hastrict
    (R_fallbackOwnerCasesW_holds exactIds idSets
      (R_nonfixedGroupTitle_holds exactIds idSets))

end Elegant.Layered.PipelineImpl
