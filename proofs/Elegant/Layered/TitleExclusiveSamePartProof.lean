import Elegant.Layered.CaptionSamePartProof
import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.CaptionSelfSidesProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.PartCaptionRunClearProof
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.BottomSeamsRank
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.StrictMemberFrameProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Same-part title clearance against exclusive boxes

`TitleExclusiveSamePart` (`CaptionResidualsProof.lean`) at the run level:
within one executed component run, the stored title caption of a group
misses the frame rectangle of every exclusive plain node of the same run.
Two cases on the plain node `w` and the caption's group `G`, following the
split of `captionLocalClear_executed`:

* (a) `w` is a member of `G` (its cluster path contains `G`'s declaration,
  covering members of descendant groups transitively): the caption sits
  above its members (`titleSamePart_memberClear` below, the `hne`-free
  form of `captionPlainMemberClear_proved`).
* (b/c) `w` is outside `G` (its cluster path does not contain `G`'s
  declaration, covering both unrelated boxes and plain members of an
  ancestor group of `G`, whose own path likewise avoids `G`): the caption
  lies strictly inside `G`'s own frame (`captionSelfClear_executed` with
  executed self-sides strictness) and a plain node off the group is clear
  of that frame (`plain_frame_disjoint`, which needs only the one-sided
  path fact). Containment transports the frame disjointness to the
  caption.

Only `ForeignBorderChainXAligned` is assumed: it feeds
`sideMarkerSpanAligned'`; the bracket and plain-order seams are the proved
`bracketMarkersAtRank'` and `plainClearOfSideMarker'`. The probe
`proofs/wip/Probe/TitleSamePartRunClearProbe.lean` checks this exact
`Disjoint` conclusion on executed runs (titled group with an exclusive
member; titled group beside an exclusive plain box outside it; nested
titled groups with an exclusive box in the outer group; sibling
wide-titled groups; both profiles) with zero violations. -/

/-- Copy of the private `CaptionLocalClearProof.run_rank_eq_coordinate_copy`
(itself from `StrictMemberFrameProof.run_rank_eq_coordinate`): executed
proper rank equals coordinate rank. -/
private theorem titleSamePart_run_rank_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

/-- Copy of the private `PartCaptionRunClearProof.strictInside_contained`:
strict inside implies containment. -/
private theorem titleSamePart_inside_contained {o i : Rect}
    (h : o.StrictInside i) : o.Contained i := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Member case: a plain member sits on a rank strictly below the top
marker's rank (`ranked_compound_member_interval`), so its frame top lies at
or below the next band top, which `rankAxis_band_top_strict` puts strictly
below the caption bottom (`captionInTopBand_executed`). This is
`captionPlainMemberClear_proved` without the unused declaration-inequality
hypothesis (the proof never uses it), so no box-role fact is needed. -/
private theorem titleSamePart_memberClear {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {i : Nat} {stored0 : Rect} {tNode : Node}
    (hmem : (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2)
    {pos : Nat} {fNode : Node} {g0 : Rect}
    (hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode)
    (hplain : fNode.border = 0)
    (hpath : fNode.clusterPath.contains tNode.decl = true)
    (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos = g0) :
    Disjoint g0 (transportCaption execution.params o execution.lines comp i stored0) := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  obtain ⟨rr, labeled, hrr, hc, hk, hranks, hrecords, hshape⟩ :=
    rankSource_of_componentRun execution.graph_eq hcomp hrun
  obtain ⟨bottom, hbottom⟩ :=
    componentRun_cg_bottom_find execution.graph_eq hlines hcomp hnode hborder
  have hinterv := ranked_compound_member_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hborder hbottom
    (List.mk_mem_zipIdx_iff_getElem?.mpr hfn) hplain hpath
  have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hmemberLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hfn).1
  have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
    have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hindexLt
    rw [hc] at h2
    exact h2
  have eMember : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
    have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hmemberLt
    rw [hc] at h2
    exact h2
  have rEqT := titleSamePart_run_rank_eq hrun i
  have rEqM := titleSamePart_run_rank_eq hrun pos
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, hyseq, _⟩ :=
    componentRun_spec hrun
  have hindexLen : i < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun i hindexLt
  have hmemberLen : pos < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun pos hmemberLt
  have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
  obtain ⟨ltM, hlyM, _, hnnM⟩ := hcov pos hmemberLen
  rw [rEqT] at hlyT hnnT
  rw [rEqM] at hlyM hnnM
  have hltTM : (rk run.coordinateProper.rank i).toNat <
      (rk run.coordinateProper.rank pos).toNat := by
    have h1 := eTop
    have h2 := eMember
    have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks pos := hinterv.1
    have h4 := hnnT
    have h5 := hnnM
    omega
  have hbandTM := rankAxis_band_top_strict hry _ _ _ _ hltTM hlyT hlyM
  have hMemBandLo := (fbs_run_node_band hrun pos hmemberLen).1
  rw [rEqM] at hMemBandLo
  have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
    simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
  have hcap := (captionInTopBand_executed execution hcomp hrun hmem hnode hborder).2
  have hmemberGet : (componentCandidate execution.graph comp candidate).nodes.getD pos default = fNode := by
    simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
  have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos =
      nodeRect (componentCandidate execution.graph comp candidate) run pos := by
    unfold frameRect
    simp only []
    rw [hmemberGet, hplain]
    rfl
  have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
      run.ys.getD pos 0 := rfl
  rw [← hframe, hfr]
  unfold Disjoint
  intro hcon
  obtain ⟨-, hy⟩ := hcon
  rw [hltTget] at hcap
  omega

/-- The run-level title band from `ForeignBorderChainXAligned`: within one
executed run, the stored title caption of a group is disjoint from the
frame of every exclusive plain node. Members go through the rank-band
argument; non-members go through caption self-containment plus the plain
foreign-span separation. -/
theorem runTitleBandFirst_holds (hx : ForeignBorderChainXAligned)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    RunTitleBandClear inp o res := by
  intro execution comp hcomp candidate run ord hrun v nd hnode hborder
    raw hraw hrawEq w nodeW _k _fBox hwnode hwborder _hcompW _hbox _hex
  have hmem' : (v, raw.2) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run := by
    have heq : (v, raw.2) = raw := by rw [← hrawEq]
    rw [heq]
    exact hraw
  have hcapEq : transportCaption execution.params o execution.lines comp v raw.2 =
      { raw.2 with
        w := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).w
        h := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).h } := by
    unfold transportCaption transportCapSize
    rw [hrawEq]
  by_cases hpath : nodeW.clusterPath.contains nd.decl = true
  · have hdisj := titleSamePart_memberClear execution hcomp hrun hmem'
      hnode hborder hwnode hwborder hpath rfl
    rw [hcapEq] at hdisj
    exact hdisj
  · have hpathW : nodeW.clusterPath.contains nd.decl = false := by
      cases h : nodeW.clusterPath.contains nd.decl with
      | true => exact absurd h hpath
      | false => rfl
    have hside := captionSelfSidesStrict_executed execution hwf hfp hcomp hrun
    have hself := captionSelfClear_executed execution hcomp hrun hmem'
      hnode hborder hside
    have hlines : execution.lines.length = inp.boxes.length :=
      boxLines_length execution.lines_eq
    have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
    have hdisjFW := plain_frame_disjoint execution.graph_eq hlines hwf hfp
      hcomp hrun bracketMarkersAtRank' plainClearOfSideMarker' halign
      hnode hwnode hborder hwborder hpathW
    have hcont := titleSamePart_inside_contained hself
    have hfin := disjoint_of_sub_disjoint hcont hdisjFW
    rw [hcapEq] at hfin
    exact (Disjoint.comm _ _).mp hfin

/-- Same-part title clearance for an executed family result: from
`WellFormed`, framed parents, and the one open span seam. -/
theorem titleExclusiveSamePart_holds (hx : ForeignBorderChainXAligned) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    TitleExclusiveSamePart inp o res := by
  intro inp o res hwf hfp
  exact titleExclusiveSamePart
    (titleSamePartBand_of_runBand (runTitleBandFirst_holds hx hwf hfp) hwf)

end Elegant.Layered.PipelineImpl
