import Elegant.Layered.LoopFootprintGroupHullProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.MemberInFrame
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ChildFrameStrictRankProof
import Elegant.Layered.CgShape
import Elegant.Layered.LoopExtentReservationProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Loop-hull cover facts for executed runs

Closes the two remaining cover residuals consumed as the seam fields
`loopHullRightCover` and `loopHullRightNeighborCover` (same quantification as
`LayeredSeams`; `FamilyAssembly` is not imported):

* R1 (`loopHullRightCover_holds`): every ancestor group hull's right edge
  strictly covers the loop footprint's right edge.
* R3 (`loopHullRightNeighborCover_holds`): a foreign hull right of the loop
  owner's frame stays right of the footprint (the `y`-overlap premise is
  carried but the `x` conclusion needs no `y` fact).

Truth (all executed, 0 violations; `wip/Probe/LoopHullCoverTProbe.lean`, nine
adversarial inputs × five candidates: minimal/wide loop labels, wide right
sibling, foreign titled group in another rank, three siblings, fixed 0 and
negative owners, group-owner loops, same-rank foreign member):
* R1 margin (hull.right − fp.right) is ≈ 1535 constant on the direct parent
  (gap − ext), consistent with right-border-marker padding over the loop lane.
* R3 holds with margins 5000+ wherever `Fleft ∧ yOvl` holds; no
  `Fleft ∧ ¬R3` instance exists with or without `yOvl`.

Route: R1-A frame right-strictness via the ancestor strictness walk
(`component_member_strictInside'` + `walkStrictFrom`); R1-B/R3-B extent-vs-gap
from the ordering/coordinate reservation (right marker copies the top's
`loopExtent` at `Order.lean:175`, `CoordsImpl.nodeW = w + 2 * loopExtent`,
`coordSep`; `proxyWidths`/`routeProper` carry it to frames). Same-cluster
right markers share one `x` via `sideMarkerSpanAligned' hx`
(see `loopRectTopForeignReal_holds`).

Status: R1-A is discharged below (`lh_R1A_holds`, frame-only walk, no
footprints); R1-B (`R1ExtentFitGap`, now in `LoopExtentReservationProof`) is
discharged for plain owners via the shared core
(`loopRes_plainExtentGap_holds`, bracket + reservation + right-marker width);
non-plain owners stay as the single residual `LoopResGroupHullRight` below.
R3-B (`R3ExtentFitGap`, also in the core file) stays as the residual with its
exact open goal stated below. `hx : ForeignBorderChainXAligned` joins a
statement when its discharge needs alignment. -/

/-- Sub-lemma R1-A (ancestor frame right strictness): the loop owner's frame
right edge is strictly left of every ancestor group hull's right edge.
Discharged below as `lh_R1A_holds` via the frame-only strictness walk. -/
def R1FrameRightStrict (P : Params) (cg : Graph) (run : Run) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → np.decl ∈ nt.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w <
        (frameRect P cg run pos).x + (frameRect P cg run pos).w

/-- R1-A discharged: ancestor frame right strictness via the frame-only
strictness walk. Plain owners use `component_member_strictInside'` directly
(any ancestor); group owners chain the direct-parent frame strictness
(`component_child_frame_strictInside'`) with `walkStrictFrom`. No footprint
facts and no `hright` are used. -/
private theorem lh_R1A_holds {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    R1FrameRightStrict execution.params
      (componentCandidate execution.graph comp candidate) run := by
  intro t nt hnt het pos np hnp hgrp hne hmem
  obtain ⟨e', hmemE, htail, hhead⟩ := het
  obtain ⟨key_t, hkeyt, hkeytLt, hntG⟩ :=
    lh_loopOwnerKey execution hcomp hnt hmemE htail hhead
  have htb : nt.border = 0 ∨ nt.border = -2 :=
    component_node_border_plain_or_group execution hkeytLt hntG
  have hboxT : inp.boxes[key_t]? = some (inp.boxes[key_t]) :=
    List.getElem?_eq_getElem hkeytLt
  obtain ⟨childBox, hchildBox⟩ : ∃ b, inp.boxes[key_t]? = some b := ⟨_, hboxT⟩
  have hposLen : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnp).1
  have hcgLen : (componentCandidate execution.graph comp candidate).nodes.length =
      comp.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hposComp : pos < comp.length := hcgLen ▸ hposLen
  obtain ⟨key_p, hpkey⟩ : ∃ k, comp[pos]? = some k :=
    ⟨_, List.getElem?_eq_getElem hposComp⟩
  have hglen : key_p < execution.graph.nodes.length :=
    lh_compMemLt hcomp (List.mem_of_getElem? hpkey)
  have hgg : execution.graph.nodes[key_p]? = some np :=
    candLookup_graph hnp hpkey hglen
  obtain ⟨box_p, hbox_p, _hdecl_p, _hpath_p⟩ :=
    execution.group_node_path_source hgg hgrp
  have hlenP : key_p < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hbox_p).1
  have hinside : nt.clusterPath.contains np.decl = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hmem
  have hSI : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).StrictInside
      (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run t) := by
    rcases htb with h0 | h2
    · exact execution.component_member_strictInside' hwf hcomp hrun hnp hgrp
        hnt h0 hinside
    · have hdeclNe : np.decl ≠ nt.decl :=
        candDecl_ne_of_idx_ne execution hcomp hnt hkeyt hkeytLt hnp hpkey hlenP
          hne
      have hpareNe : childBox.parent ≠ "" :=
        walkParentNe execution hcomp hnt hkeyt hchildBox h2 hnp hpkey hlenP hmem hne
      obtain ⟨parentKey, parentBox, parentIdx, top, hparentBox, hparentRef,
          hparentIdx, htopCg, htopBorder, _htopDeclEq⟩ :=
        setupParentLink execution hwf hframed hcomp hkeytLt
          (List.mem_of_getElem? hkeyt) hchildBox hpareNe
      have hcl := walkClStep (parentBox := parentBox) execution hwf hnt hkeyt
        hchildBox h2 htopCg hparentIdx hparentBox hparentRef hpareNe htopBorder
      have htopG : execution.graph.nodes[parentKey]? = some top :=
        candLookup_graph htopCg hparentIdx
          (lh_compMemLt hcomp (List.mem_of_getElem? hparentIdx))
      obtain ⟨_box_top, _hbox_top, _hdecl_top, hpath_top⟩ :=
        execution.group_node_path_source htopG htopBorder
      have htopMemSelf : top.decl ∈ top.clusterPath := by
        rw [hpath_top, _hdecl_top]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      have hinsideTop : nt.clusterPath.contains top.decl = true := by
        have hmemTop0 : top.decl ∈ nt.clusterPath := by
          rw [hcl]
          exact List.mem_append_left _ htopMemSelf
        rw [List.contains_eq_mem, decide_eq_true_eq]
        exact hmemTop0
      have hlenPk : parentKey < inp.boxes.length :=
        (List.getElem?_eq_some_iff.mp hparentBox).1
      have htopLe := childTopRankLe_executed execution hwf hframed hcomp hrun
        hnt h2
      have hbotLe := childBottomRankLe_executed execution hwf hframed hcomp
        hrun hnt h2
      have htopDeclEq : top.decl = parentKey :=
        candNode_decl_eq_key execution htopCg hparentIdx hlenPk
      have hntDeclEq : nt.decl = key_t :=
        candNode_decl_eq_key execution hnt hkeyt hkeytLt
      have hparentBox' : inp.boxes[top.decl]? = some parentBox := by
        rw [htopDeclEq]; exact hparentBox
      rw [← hntDeclEq] at hchildBox
      have hstepFrame : (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run
          parentIdx).StrictInside
          (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run t) :=
        execution.component_child_frame_strictInside' hwf hcomp hrun htopCg
          htopBorder hnt h2 hparentBox' hchildBox hparentRef hpareNe htopLe hbotLe
      by_cases hpp : parentIdx = pos
      · subst hpp
        exact hstepFrame
      · have hmemTop : np.decl ∈ top.clusterPath := by
          rw [hcl] at hmem
          rcases List.mem_append.mp hmem with hL | hR
          · exact hL
          · have hEq : np.decl = nt.decl := List.mem_singleton.mp hR
            exact absurd hEq hdeclNe
        have hchain := walkStrictFrom execution hwf hframed hcomp hrun hnp
          hpkey hlenP htopCg htopBorder hparentIdx hlenPk hparentBox hmemTop
          (Ne.symm hpp)
        exact Rect.StrictInside.trans' hchain hstepFrame
  exact hSI.2.1

/-- Single residual for non-plain loop owners: the ancestor-hull right cover
conclusion restricted to owners whose border is not plain. Strictly narrower
than `LoopHullRightCover` (one extra border premise, same conclusion).
Probe: `LoopHullCoverTProbe` group-owner inputs (`grpLoopWide`, `grpLoopMin`:
R1 holds with the same ≈ 1535 margins via the top's right marker). Open:
derive it from `LoopResTopReservation` (top footprint vs marker-positioned
node) plus the ancestor marker achiever used in `loopRes_plainExtentGap_holds`,
closing the marker-marker ordering case in the owner's layer. -/
def LoopResGroupHullRight (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    nt.border ≠ 0 →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → np.decl ∈ nt.clusterPath →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w <
        (frameRect P cg run pos).x + (frameRect P cg run pos).w

/-- Executed ancestor-hull right cover: plain owners via the shared core
(`loopRes_plainExtentGap_holds` + `lh_R1A_holds`), non-plain owners via the
single residual `LoopResGroupHullRight`. -/
theorem loopHullRightCover_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hGrp : LoopResGroupHullRight execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hA := lh_R1A_holds execution hwf hframed hcomp hrun
  intro t nt hnt het pos np hnp hgrp hne hmem
  by_cases ht0 : nt.border = 0
  · have hstrict := hA t nt hnt het pos np hnp hgrp hne hmem
    have hfit := loopRes_plainExtentGap_holds execution hwf hframed hcomp hrun
      hnt ht0 hnp hgrp hne hmem
    have hfx : (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x =
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run t).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run t).w := rfl
    rw [hfx]
    omega
  · exact hGrp t nt hnt het ht0 pos np hnp hgrp hne hmem
 /-! `R3ExtentFitGap` now lives in `LoopExtentReservationProof` (shared core). -/

/-- Executed foreign-hull right-neighbor cover, modulo the named sub-lemma.
Exact open goal (`R3ExtentFitGap`): for a loop owner `t` (any border) with a
self-loop and a foreign group hull `pos` with `frame(t).right ≤ hull.left`,
show `fp(t).right ≤ hull.left`. What closes from the core today: the plain
owner's same-layer reservation (`loopRes_sameLayer_holds`) bounds the extent
by every same-layer right gap. What remains open: (1) the hull's left edge is
the minimum over its border markers, and the minimum-achieving marker must be
located in the owner's layer right of the owner — for a foreign hull there is
no member bracket forcing this position (markers of the foreign hull flank
its own members, and cross-rank `x` is otherwise unconstrained); the
`Fleft` premise plus `SideMarkerSpanAligned` span sharing is the only grip,
and the between-markers case needs positive marker width to rule out;
(2) group-top owners need `LoopResMarkerCopy` + `LoopResTopReservation`
(marker copy and marker-layer reservation), themselves open. Probe:
`LoopHullCoverTProbe` (R3 margins 5000+ wherever `Fleft ∧ yOvl`; no
`Fleft ∧ ¬R3` instance with or without `yOvl`) and `BeyondTopSliverTProbe`
(48 firings for the top-vs-sliver shape). -/
theorem loopHullRightNeighborCover_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hB : R3ExtentFitGap execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    LoopHullRightNeighborCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have _hwf := hwf
  have _hframed := hframed
  have _hcomp := hcomp
  have _hrun := hrun
  intro t nt hnt het pos np hnp hgrp hne hne2 hni1 hni2 hFL _hyOvl
  exact hB t nt hnt het pos np hnp hgrp hne hne2 hni1 hni2 hFL

end Elegant.Layered.PipelineImpl
