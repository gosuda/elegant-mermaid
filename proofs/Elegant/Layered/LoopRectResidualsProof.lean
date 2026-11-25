import Elegant.Layered.LoopRectRealClosed
import Elegant.Layered.PartSeparation
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.PartFrameWitnessProof
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Loop-rectangle top-foreign and title-copy residuals, closed

The last two premises of `loopRectTopReal_holds` and `loopRectTitleReal_holds`
(`LoopRectRealClosed.lean`). Truth was probed on executed layouts
(`proofs/wip/Probe/LoopRectResidualsProbe.lean`, 16 layouts: plain baseline,
zero and large fixed boxes, group tops with self-loops, nested groups with
titles, same-part outside plains, empty groups, zero-fixed outside plains,
both directions): no plain frame ever equals a group-top frame, outside
plains are disjoint from tops, every beyond-range real frame is shelf
contained, and every beyond-range real frame is disjoint from plains.

* Top-foreign: run-level disjointness (`plain_frame_disjoint` with the proved
bracket/order seams and the accepted alignment seam `hx`, the same residual
every recent clearance theorem carries) plus executed group-top positivity
(`top_frame_pos`, closed). No shelf argument is needed because both frames
live in one run.
* Title-copy: two sliver residuals about beyond-range real frames
(`hfit`: shifted within placement bounds; `hsep`: disjoint from plain
candidate frames), each strictly narrower than the goal (pure run geometry,
no shelves, transport, parts, or exclusive boxes) and probe-tested. The rest
is closed transport/bounds work mirroring `part_rects_within_shelf`.
-/

/-- Local copy of the private `ForeignFrameClearance.placeComponent_width`:
a placed component width is its placement-bounds span. -/
private theorem lrrPlaceWidth (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).width =
      (placeBounds P cg run labels loops).right -
        (placeBounds P cg run labels loops).minX := rfl

/-- Local copy of the private `ForeignFrameClearance.placeComponent_height`. -/
private theorem lrrPlaceHeight (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).height =
      (placeBounds P cg run labels loops).bottom -
        (placeBounds P cg run labels loops).minY := rfl

/-- Top-foreign residual, closed modulo the accepted alignment seam: a
same-part plain run node outside the group whose frame equals the group-top
frame is impossible. Disjointness comes from `plain_frame_disjoint`;
positivity comes from the closed `top_frame_pos` transported along the frame
equation. The exclusive-box hypotheses are carried only for residual shape. -/
theorem loopRectTopForeignReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) :
    LoopRectTopForeignReal inp o res := by
  intro execution candidate run _packed _hpack _c q _hselected _area _loops _hpart hcomp hrun _v _b _hreal _hbmem _hexcl _hrect _node hnode hb _w _key _member _hw _hbord0 hnodeW hbW hcon hframe
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hdis := plain_frame_disjoint execution.graph_eq hlines hwf hfp hcomp hrun
    bracketMarkersAtRank' plainClearOfSideMarker' halign hnode hnodeW hb hbW hcon
  have hpos := top_frame_pos execution hcomp hrun hnode hb
  have hposW : 0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run _w).w ∧
      0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run _w).h := by
    rw [hframe]
    exact hpos
  have hdisW : Disjoint (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run _w)
      (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run _w) := by
    rw [← hframe] at hdis
    exact hdis
  exact loopRect_frameNe_of_disjoint hdisW rfl hposW.1 hposW.2

/-- Title-copy residual, closed modulo two sliver facts about beyond-range
real frames: placement-bounds fit (`hfit`) and plain-frame disjointness
(`hsep`). Both are single-stage run-geometry facts, strictly narrower than
the goal, and probe-tested. The proof lifts them through the frame equation,
the part/shelf transport, and the pack/part dimension identities. -/
theorem loopRectTitleCopyReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (hfit : ∀ (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
      (loops : List (Nat × LoopPlacement)) (v : Nat) (nd : ProperNode),
      cg.nodes.length ≤ v → run.proper.nodes[v]? = some nd → nd.dummy = false →
      0 < (nodeRect cg run v).w → 0 < (nodeRect cg run v).h →
      (placeBounds P cg run labels loops).minX ≤ (nodeRect cg run v).x ∧
      (nodeRect cg run v).x + (nodeRect cg run v).w ≤
        (placeBounds P cg run labels loops).right ∧
      (placeBounds P cg run labels loops).minY ≤ (nodeRect cg run v).y ∧
      (nodeRect cg run v).y + (nodeRect cg run v).h ≤
        (placeBounds P cg run labels loops).bottom)
    (hsep : ∀ (cg : Graph) (run : Run) (v w : Nat) (nd : ProperNode) (member : Node),
      cg.nodes.length ≤ v → run.proper.nodes[v]? = some nd → nd.dummy = false →
      0 < (nodeRect cg run v).w → 0 < (nodeRect cg run v).h →
      cg.nodes[w]? = some member → member.border = 0 →
      Disjoint (nodeRect cg run v) (nodeRect cg run w)) :
    LoopRectTitleCopyReal inp o res := by
  intro execution candidate run packed hpack c q hselected _area loops hpart hcomp hrun v hreal hn hpne hposW hposH
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length ≤ v :=
    List.getElem?_eq_none_iff.mp hn
  obtain ⟨nd, hnd⟩ := Option.ne_none_iff_exists.mp hpne
  have hnd' : run.proper.nodes[v]? = some nd := hnd.symm
  have hndFalse : nd.dummy = false := hreal nd hnd'
  have hgetV : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default =
      default := by
    rw [List.getD_eq_getElem?_getD, hn, Option.getD_none]
  have hbdef : (default : Node).border = 0 := rfl
  have hfrV : frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v =
      nodeRect (componentCandidate execution.graph q.1.1 candidate) run v :=
    frameRect_of_border_zero hgetV hbdef
  have hnposW : 0 < (nodeRect (componentCandidate execution.graph q.1.1 candidate) run v).w := by
    rw [← hfrV]
    exact hposW
  have hnposH : 0 < (nodeRect (componentCandidate execution.graph q.1.1 candidate) run v).h := by
    rw [← hfrV]
    exact hposH
  refine ⟨?_, ?_⟩
  · have hfitInst := hfit execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops v nd
      hlen hnd' hndFalse hnposW hnposH
    rw [← hfrV] at hfitInst
    have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
      zip_getElem?_left hselected
    have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
      rw [Pack.pack_count hpack, List.length_map]
    have hclen : c < packed.boxes.length := by
      have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
      omega
    have hshelfC : packed.boxes[c]? = some q.2 :=
      (List.getElem?_zip_eq_some.mp hselected).2
    have hL : partRectT execution packed c (shiftRect (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX) (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY) (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)) =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH (shiftRect q.2.x q.2.y
        (shiftRect (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX) (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY) (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
      unfold partRectT
      rw [hshelfC, Option.getD_some]
    have hS : shelfRectT execution packed c =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH q.2) := by
      unfold shelfRectT
      rw [hshelfC, Option.getD_some]
    rw [hL, hS]
    refine orient_transport_contained ?_
    have hboxEq : packed.boxes[c] = q.2 :=
      Option.some.inj ((List.getElem?_eq_getElem hclen).symm.trans hshelfC)
    have hmapLen : c < (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area).length := by
      rw [List.length_map]
      exact (List.getElem?_eq_some_iff.mp hmemc).1
    have hpartget : execution.componentsAcc.parts[c] = q.1 :=
      (List.getElem?_eq_some_iff.mp hmemc).2
    have hitem : (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area)[c] =
        Pack.Item.mk q.1.2.width q.1.2.height q.1.2.area := by
      rw [List.getElem_map, hpartget]
    obtain ⟨hsw, hsh⟩ := packShelfDims hpack hclen hmapLen
    have hW : q.2.w = (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).right - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX := by
      have e1 : q.2.w = packed.boxes[c].w := by rw [hboxEq]
      have hPW : q.1.2.width = (placeComponent execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
          loops).width := by rw [hpart]
      rw [e1, hsw, hitem, hPW, lrrPlaceWidth]
    have hH : q.2.h = (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).bottom - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY := by
      have e1 : q.2.h = packed.boxes[c].h := by rw [hboxEq]
      have hPH : q.1.2.height = (placeComponent execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
          loops).height := by rw [hpart]
      rw [e1, hsh, hitem, hPH, lrrPlaceHeight]
    simp only [shiftRect, Rect.Contained]
    omega
  · intro w member hnodeW hbW
    have hsepInst := hsep (componentCandidate execution.graph q.1.1 candidate) run v w nd
      member hlen hnd' hndFalse hnposW hnposH hnodeW hbW
    have hgetW : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
        member := by
      rw [List.getD_eq_getElem?_getD, hnodeW, Option.getD_some]
    have hfrW : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        nodeRect (componentCandidate execution.graph q.1.1 candidate) run w :=
      frameRect_of_border_zero hgetW hbW
    rw [hfrV, hfrW]
    exact hsepInst

/-- Closed top case: the existing `loopRectTopReal_holds` with the foreign
sub-case discharged above. Carries only the accepted alignment seam. -/
theorem loopRectTopReal_closed {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) :
    LoopRectTopReal inp o res :=
  loopRectTopReal_holds hwf hfp (loopRectTopForeignReal_holds hwf hfp hx)

/-- Closed title case: the existing `loopRectTitleReal_holds` with the
title-copy residual discharged above. Carries only the two sliver facts. -/
theorem loopRectTitleReal_closed {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hfit : ∀ (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
      (loops : List (Nat × LoopPlacement)) (v : Nat) (nd : ProperNode),
      cg.nodes.length ≤ v → run.proper.nodes[v]? = some nd → nd.dummy = false →
      0 < (nodeRect cg run v).w → 0 < (nodeRect cg run v).h →
      (placeBounds P cg run labels loops).minX ≤ (nodeRect cg run v).x ∧
      (nodeRect cg run v).x + (nodeRect cg run v).w ≤
        (placeBounds P cg run labels loops).right ∧
      (placeBounds P cg run labels loops).minY ≤ (nodeRect cg run v).y ∧
      (nodeRect cg run v).y + (nodeRect cg run v).h ≤
        (placeBounds P cg run labels loops).bottom)
    (hsep : ∀ (cg : Graph) (run : Run) (v w : Nat) (nd : ProperNode) (member : Node),
      cg.nodes.length ≤ v → run.proper.nodes[v]? = some nd → nd.dummy = false →
      0 < (nodeRect cg run v).w → 0 < (nodeRect cg run v).h →
      cg.nodes[w]? = some member → member.border = 0 →
      Disjoint (nodeRect cg run v) (nodeRect cg run w)) :
    LoopRectTitleReal inp o res :=
  loopRectTitleReal_holds hwf hfp (loopRectTitleCopyReal_holds hwf hfp hfit hsep)

end PipelineImpl
end Layered
end Elegant
