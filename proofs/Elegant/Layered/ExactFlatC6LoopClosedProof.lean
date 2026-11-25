import Elegant.Layered.ExactFlatC6LoopScopeProof
import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.ExactGroupOverlapClosedProof
import Elegant.Layered.ExactPlainRightNonPlainProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem exactLoopEnvelopeMiss_closed (exactIds : List String) :
    X_LoopEnvelopeMiss exactIds := by
  have hGroupOverlap : XLEM_GroupOverlapMiss exactIds :=
    fun inp o res execution hwf hfp => XLEM_groupOverlapMiss_holdsW exactIds
      (inp := inp) (o := o) (res := res) execution hwf hfp
  have hRight := xlem_plainRightNonPlain_holds exactIds
  have hMarker := XLEG_groupMarkerOrderX_of_leaves exactIds
    (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
    (xleg_loopMarkerSpanX_holds exactIds)
  exact glue_loopEnvelopeMiss exactIds (XLEM_plainReserve_holds exactIds)
    (XLEM_groupOtherRank_holds exactIds hGroupOverlap) (XLEM_leftNonPlain_holds exactIds)
    (XLEM_plainRightMiss_holds exactIds hRight) hMarker
    (glue_loopEnvOtherOwner exactIds hGroupOverlap hRight hMarker)

private theorem loopCandidateSlotPos {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) :
    0 < (componentCandidate execution.graph comp candidate).slot := by
  have hc : (componentCandidate execution.graph comp candidate).slot = execution.graph.slot := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hg := execution.graph_eq
  unfold exactGraph at hg
  obtain ⟨_, _, hg⟩ := bind_ok hg
  have hs : execution.graph.slot = execution.graph0.slot := by rw [← Except.ok.inj hg]
  obtain ⟨_, _, _, _, _, _, hslot, hprep, _⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph0_eq
  have hslot0 : execution.graph0.slot = execution.params.slot := by rw [hprep]; exact hslot
  have hvalid := (checkedParams_valid execution.checked).2.2.1
  rw [hc, hs, hslot0]
  omega

set_option maxHeartbeats 1200000 in
/-- Exact self-loop clearance for the flat C6 assembler. The old footprint can be
shorter than an exact loop's bend stack, so the same-part proof uses the full
reservation. Distinct packed shelves are axis-separated even at zero extent. -/
theorem X6_loopCaseW_holds (exactIds : List String)
    (_hpos : X6_ShelfPositiveW exactIds) (hbord : X6_BorderZeroRealW exactIds) :
    X6_LoopCaseW exactIds := by
  intro inp o res execution _hfix hwf hfp _hclear _hbridge _hsep r b _hr hb hex _hscope
    key hrAtKey hkeyLen packed c q candidate run loops i edge area hpacked hselected hrun
    hloops hpart hedge hdecl loop hfound
  by_cases hpositive : 0 < b.rect.w ∧ 0 < b.rect.h
  case neg =>
    exact Polyline.not_hits_of_zero (by omega)
  case pos =>
    let cg := componentCandidate execution.graph q.1.1 candidate
    let bounds := placeBoundsX execution.params cg run execution.measured loops
    have hndCg : (cg.edges.map Edge.decl).Nodup :=
      componentCandidate_decls_nodup execution.graph q.1.1 candidate
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
    have hnd : (q.1.2.routes.map (·.1)).Nodup := by
      rw [hpart]
      unfold placeComponentExact
      dsimp only
      rw [List.map_map]
      change (cg.edges.zipIdx.map (fun p => p.1.decl)).Nodup
      rw [zipIdx_map_comp (fun e : Edge => e.decl)]
      exact hndCg
    have hlocal : q.1.2.routes[i]? = some (edge.decl,
        loop.2.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))) := by
      rw [hpart]
      dsimp only [cg, bounds]
      unfold placeComponentExact placeBoundsX
      dsimp only
      simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some, hfound,
        Option.getD_some]
    have hrAt : res.scene.routes[edge.decl]? = some r := by rwa [hdecl]
    have hdeclLen : edge.decl < inp.routes.length := by rwa [hdecl]
    have hmodel : inp.routes[edge.decl]? = some inp.routes[edge.decl] :=
      List.getElem?_eq_getElem hdeclLen
    obtain ⟨boxKey, hbAt⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨source, hsource, _, _, hsourceExclusive, hboxRect⟩ := sceneBox_source_rectX execution hbAt
    have hboxKeyLen := (List.getElem?_eq_some_iff.mp hsource).1
    obtain ⟨targetPart, pos, targetShelf, _, htargetPart, hpos⟩ :=
      key_part_positionX execution hboxKeyLen
    by_cases hsame : targetShelf = c
    case neg =>
      exact execution.chosenRoute_misses_other_part hpacked hselected hlocal hnd
        hmodel hrAt (Ne.symm hsame) htargetPart hpos hbAt
    case pos =>
      subst targetShelf
      have hpartEq : targetPart = q.1 := Option.some.inj
        (htargetPart.symm.trans (zip_getElem?_left hselected))
      subst targetPart
      have hsourceBox := execution.source_box_lookup_of_box_ids_nodupX (Model.boxIds_nodup hwf) hsource
      have htargetBox := X_DumpLookup_holds exactIds execution hwf packed hpacked hselected
        hpart hpos hsource
      have hbrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
              (frameRect execution.params cg run pos))) :=
        hboxRect.trans (congrArg Box.rect (Option.some.inj (hsourceBox.symm.trans htargetBox)))
      have hslot := loopCandidateSlotPos execution q.1.1 candidate
      obtain ⟨owner, _, origin, horigin, horiginDecl, htail, hhead, hw, hh, hpoints⟩ :=
        componentLoops_entry_in_footprintExt hloops hslot (List.mem_of_find?_eq_some hfound)
      have hloopDecl : loop.1 = edge.decl := by
        simpa only [beq_iff_eq] using List.find?_some hfound
      have horiginEq : origin = edge := nodup_map_eq_of_mem hndCg
        (List.mem_filter.mp horigin).1 (List.mem_of_getElem? hedge) (horiginDecl.symm.trans hloopDecl)
      subst origin
      have hself : edge.tail = edge.head := htail.trans hhead.symm
      rw [← htail] at hw hh hpoints
      have hmiss : ¬ Polyline.hitsRect loop.2.points (frameRect execution.params cg run pos) := by
        by_cases howner : pos = edge.tail
        · rw [howner]
          have hsep : RectAxisSeparated (loopFootprintExt cg run execution.measured edge.tail)
              (frameRect execution.params cg run edge.tail) :=
            Or.inr (Or.inl (Int.le_refl _))
          exact Polyline.not_hits_of_allMiss
            (allSegsMiss_of_pointIn_of_separated hsep _ hpoints)
        · obtain ⟨hparts, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
          have hcomp : q.1.1 ∈ components execution.graph := by
            rw [← hparts]
            exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
          have hgraphKey := sceneExecutionX_graph_len execution hboxKeyLen
          have htargetNode : cg.nodes[pos]? = some execution.graph.nodes[boxKey] :=
            component_node_lookupX hpos (List.getElem?_eq_getElem hgraphKey)
          have hreal := X_componentRun_source_isReal hrun htargetNode
          have hborder : (cg.nodes.getD pos default).border = 0 :=
            hbord execution hwf hfp candidate run packed hpacked hselected hpart hcomp hrun
              hreal hb hex hpositive.1 hpositive.2 (by rw [shiftRect_pack_normalize]; exact hbrect)
          have hsourceEx := hsourceExclusive.symm.trans hex
          obtain ⟨hcovered, _, htailScope, hheadScope⟩ :=
            x6_loopSep_nonSelf_scopeB_holds exactIds inp o res execution hwf hfp q.1.1 candidate
              run edge.tail pos i edge hcomp hborder hrun (Ne.symm howner) hedge rfl hself.symm
              boxKey source hpos hsource hsourceEx
          rw [plain_frame_eq_boxRect execution.params cg run pos hcovered (by omega)]
          exact polyline_in_box_misses_disjoint hw hh hpoints
            (exactLoopEnvelopeMiss_closed exactIds inp o res execution hwf hfp q.1.1 candidate run
              (candidateOrder candidate) cg i edge pos hcomp rfl hrun hedge hself hcovered hreal
              htailScope hheadScope)
      have hrScene := X_chosen_part_route_from_points execution packed hpacked hselected hlocal hnd hmodel
      have hrPoints := congrArg Route.points (Option.some.inj (hrAt.symm.trans hrScene))
      rw [hrPoints, hbrect]
      exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY

end Elegant.Layered.PipelineImpl
