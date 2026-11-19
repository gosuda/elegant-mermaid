import Elegant.Layered.LoopRectSamePartExecuted
import Elegant.Layered.LoopRectCrossPartProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Closed loop-rect residuals: bottom, range-degenerate, fixed (plus top/title)

The five `LoopRect*Real` defs (`LoopRectPlainSourceProof.lean`) now carry
`0 < b.rect.w → 0 < b.rect.h →`, and `flatC6LoopCase` splits on it (the
non-positive branch closes by `Polyline.not_hits_of_zero`). This file closes
the positive branch for executed layouts, combining the same-part halves
(`loopRect_exclusive_witness` plus the `loopRect<Case>_samePart` lemmas, with
witness positivity from `loopRect_frame_pos_of_rectEq`) and the cross-part
halves (`loopRect<Case>_crossPart`, same positivity) over the box-origin key
split (`loopRect_box_origin`: the exclusive scene box comes from one model
box; `keyB ∈ q.1.1` or not).

* `loopRectBottomReal_holds`, `loopRectRangeDegReal_holds`,
  `loopRectFixedReal_holds`: full proofs from `WellFormed` and
  `framedParents` alone, no residuals.
* `loopRectTopReal_holds`: full proof conditional on the existing
  `LoopRectTopForeignReal` residual (same-part non-member sub-case; the
  member sub-case is `loopRectTop_strictInside_case`, the foreign sub-case
  `loopRectTop_crossPart`).
* `LoopRectTitleCopyReal` (one named residual) plus `loopRectTitleReal_holds`:
  past the in-range shelf vehicle, the beyond-range title-copy frame needs
  (a) shelf containment of its shifted frame (the `LoopRectCrossPartProbe`
  `fit` rows for the `titleTwo` input; the prior session observed `fit=true`
  with a positive title-copy frame `(3651,0,672,3072)`), and (b) run-level
  disjointness against every plain frame (the `LoopRectSamePartTProbe`
  coinciding-frames rows, which report only out-of-range default pairs).
  Both are about one pipeline stage: the title-copy run frame and its
  placement.
-/

/-- Shared foreign-half vehicle: from loop-side shelf containment of the
transported loop rect and the foreign packed-box equation, derive `False`.
The foreign packed side is contained in its own shelf
(`part_rects_within_shelf`), so distinct shelves give disjointness
(`rect_misses_box_of_distinct_parts`); the rect equation plus `b.rect`
positivity closes through `loopRect_crossPart_false`. -/
private theorem loopRectForeign_false_of_contained
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {R : Rect}
    (hcontR : (shelfRectT execution packed c).Contained
      (partRectT execution packed c R))
    {L : Rect}
    (hL : partRectT execution packed c R = L)
    {keyB : Nat} (hkeyBlen : keyB < inp.boxes.length)
    {cB : Nat} {partB : List Nat × Part} {posB : Nat}
    (hkB : execution.componentsAcc.parts[cB]? = some partB)
    (hposB : partB.1[posB]? = some keyB)
    (hne : c ≠ cB)
    {B : Rect} {b : Box}
    (hrect : b.rect = L)
    (hbrectB : b.rect = B)
    (hpackedB : B = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD keyB default)))
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hclen : c < packed.boxes.length := by
    have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
      zip_getElem?_left hselected
    have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
    omega
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hkB).1
    omega
  obtain ⟨boxB, hboxB⟩ : ∃ boxB, packed.boxes[cB]? = some boxB :=
    ⟨packed.boxes[cB], List.getElem?_eq_getElem hcBlen⟩
  obtain ⟨candB, runB, loopsB, _areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    part_frame_lookup execution packed hpack hkB hboxB
  obtain ⟨fB, hfBdef⟩ : ∃ f : Rect, f = shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB) :=
    ⟨_, rfl⟩
  have hval : execution.packedAcc.rects.getD keyB default =
      shiftRect boxB.x boxB.y fB := by
    rw [hfBdef]
    exact hlookupB posB keyB hposB hkeyBlen
  have hiB : posB <
      (componentCandidate execution.graph partB.1 candB).nodes.length := by
    rw [loopRectCross_candidate_length]
    exact (List.getElem?_eq_some_iff.mp hposB).1
  have hfBmem : fB ∈ partB.2.rects := by
    rw [hfBdef, hpartdefB]
    exact List.mem_of_getElem?
      (loopRectCross_rects_get execution.params _ _ _ _ hiB)
  have hcontB := part_rects_within_shelf hpack hkB hcBlen fB hfBmem
  have hdisj := partsShelvesDisjoint_of_pack hpack
  have hRHS : (shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect boxB.x boxB.y fB))) = partRectT execution packed cB fB := by
    unfold partRectT
    rw [hboxB, Option.getD_some]
  have hmiss : ¬ (partRectT execution packed c R).meetsInterior B := by
    rw [hpackedB, hval, hRHS]
    exact rect_misses_box_of_distinct_parts hdisj hclen hcBlen hne hcontR hcontB
  have hdisL : Disjoint L B := by
    rw [← hL]
    exact hmiss
  exact loopRect_crossPart_false hrect hbrectB hdisL hposW hposH

/-- Fixed-owner foreign half: the loop-owner frame is in range, so its
shifted frame is in `q.1.2.rects` and the shared vehicle applies through
the containment form. -/
private theorem loopRectFixed_foreign_false
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box)
    (_hreal : RouteImpl.IsReal run.proper v)
    (_hbmem : b ∈ res.scene.boxes) (_hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))))
    {node : Node}
    (hnode : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node)
    {keyB : Nat} {sourceB : ModelBox}
    (hsourceB : inp.boxes[keyB]? = some sourceB)
    (hbrectB : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default)))
    (hforeign : keyB ∉ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hkeyBlen : keyB < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceB).1
  obtain ⟨partB, cB, posB, hkB, hposB, _hcBlen⟩ :=
    loopRect_foreignPart execution packed hpack hkeyBlen
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  have hne : c ≠ cB := by
    intro heq
    subst heq
    have hqeq : q.1 = partB := Option.some.inj (hmemc.symm.trans hkB)
    have hmem : keyB ∈ q.1.1 := by
      rw [hqeq]
      exact List.mem_of_getElem? hposB
    exact hforeign hmem
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hclen : c < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
    omega
  have hvlen : v <
      (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hR : (shiftRect (0 - (placeBounds execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minX)
    (0 - (placeBounds execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minY)
    (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v)) ∈ q.1.2.rects := by
    rw [hpart]
    exact List.mem_of_getElem?
      (loopRectCross_rects_get execution.params _ _ _ _ hvlen)
  have hcontR := part_rects_within_shelf hpack hmemc hclen _ hR
  have hshelfC : packed.boxes[c]? = some q.2 :=
    (List.getElem?_zip_eq_some.mp hselected).2
  have hL : partRectT execution packed c
      (shiftRect (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
    unfold partRectT
    rw [hshelfC, Option.getD_some]
  exact loopRectForeign_false_of_contained execution packed hpack hselected
    hcontR hL hkeyBlen hkB hposB hne hrect hbrectB rfl hposW hposH

/-- Residual (title-copy placement): the shifted frame of a beyond-range
title-copy node is shelf-contained, and the title-copy run frame is disjoint
from every plain frame. One pipeline stage: the title-copy run frame and its
placement. -/
def LoopRectTitleCopyReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {v : Nat},
    RouteImpl.IsReal run.proper v →
    (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = none →
    run.proper.nodes[v]? ≠ none →
    0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v).w →
    0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v).h →
    ((shelfRectT execution packed c).Contained
      (partRectT execution packed c
        (shiftRect (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY)
          (frameRect execution.params
            (componentCandidate execution.graph q.1.1 candidate) run v))) ∧
    ∀ {w : Nat} {member : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[w]? = some member →
      member.border = 0 →
      Disjoint
        (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v)
        (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run w))

/-- Closed bottom case: for an executed layout, the bottom-marker residual
holds. Same-part: the plain witness frame is positive (def premise through
the equation) and disjoint from the bottom-marker frame. Foreign: the
bottom-marker frame is in range, so the shared shelf vehicle applies. -/
theorem loopRectBottomReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true) :
    LoopRectBottomReal inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect _ hnodeV hbV
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    loopRect_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · exact loopRectBottom_samePart_executed hwf _hfp execution candidate run packed
      hpack c q hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hbV
      hsourceB hexclB hbrectB hmem hposW hposH
  · exact loopRectBottom_crossPart execution hwf candidate run packed hpack c q
      hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hbV
      hsourceB hbrectB hmem hposW hposH

/-- Closed range-degenerate case: for an executed layout, the degenerate
residual holds. Same-part: the out-of-range frame is the default degenerate
rect, contradicting witness positivity. Foreign: degeneracy alone gives
disjointness. -/
theorem loopRectRangeDegReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true) :
    LoopRectRangeDegReal inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect hn hp
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    loopRect_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · exact loopRectRangeDeg_samePart_executed hwf _hfp execution candidate run packed
      hpack c q hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hn hp
      hsourceB hexclB hbrectB hmem hposW hposH
  · exact loopRectRangeDeg_crossPart execution hwf candidate run packed hpack c q
      hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hn hp
      hsourceB hbrectB hmem hposW hposH

/-- Closed fixed case: for an executed layout, the fixed-source residual
holds. Same-part: at equal positions the witness discharges the existential;
at distinct positions disjointness plus positivity closes it. Foreign: the
shared shelf vehicle closes the equation, hence the existential. -/
theorem loopRectFixedReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true) :
    LoopRectFixedReal inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect _ _ _ hnodeV hbV hkeyV hsrcV hfixV
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    loopRect_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · exact loopRectFixed_samePart_executed hwf _hfp execution candidate run packed
      hpack c q hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hbV
      hkeyV hsrcV hfixV hsourceB hexclB hbrectB hmem hposW hposH
  · exact False.elim (loopRectFixed_foreign_false execution hwf candidate run packed
      hpack c q hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV
      hsourceB hbrectB hmem hposW hposH)

/-- Closed top case (modulo the existing foreign-span residual): the member
sub-case is strict containment, the foreign sub-case is the shared vehicle,
and the same-part non-member sub-case is `LoopRectTopForeignReal`. -/
theorem loopRectTopReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    (hforeign : LoopRectTopForeignReal inp o res) :
    LoopRectTopReal inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect node hnodeV hbV
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    loopRect_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · obtain ⟨w, hw, _, hwlen, _, hbord0, hpackeq⟩ :=
      loopRect_exclusive_witness execution hwf packed hpack hselected hrun hpart
        hsourceB hexclB hmem
    have hframe : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v := by
      have hww : shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run w)))) =
          shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect q.2.x q.2.y
                (shiftRect (0 - (placeBounds execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minX)
                  (0 - (placeBounds execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minY)
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
        rw [← hpackeq, ← hbrectB]
        exact hrect
      exact loopTransport_cancel hww
    have hnodeW : (componentCandidate execution.graph q.1.1 candidate).nodes[w]? =
        some ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen) :=
      List.getElem?_eq_getElem hwlen
    have hbW : ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen).border
        = 0 := by
      have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
          (componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwlen, Option.getD_some]
      rw [← hget]
      exact hbord0
    cases hcon : (((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen).clusterPath.contains node.decl) with
    | true => exact loopRectTop_strictInside_case execution hwf hcomp hrun hnodeV hbV hnodeW hbW hcon hframe
    | false => exact hforeign execution candidate run packed hpack c q hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hbV hw hbord0 hnodeW hbW hcon hframe
  · exact loopRectTop_crossPart execution hwf candidate run packed hpack c q
      hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hbV
      hsourceB hbrectB hmem hposW hposH

/-- Closed title case (modulo the title-copy residual): the beyond-range
title-copy frame is positive through the equation. Same-part: the witness
frame equals it, contradicting run-level title-vs-plain disjointness.
Foreign: shelf containment plus the shared vehicle. -/
theorem loopRectTitleReal_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    (hshelf : LoopRectTitleCopyReal inp o res) :
    LoopRectTitleReal inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect hn hpne
  have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    loopRect_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  have hres := hshelf execution candidate run packed hpack c q hselected hpart
    hcomp hrun hreal hn hpne hposV.1 hposV.2
  obtain ⟨hmemR, hdisj⟩ := hres
  by_cases hmem : keyB ∈ q.1.1
  · obtain ⟨w, hw, _, hwlen, _, hbord0, hpackeq⟩ :=
      loopRect_exclusive_witness execution hwf packed hpack hselected hrun hpart
        hsourceB hexclB hmem
    have hframe : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v := by
      have hww : shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run w)))) =
          shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect q.2.x q.2.y
                (shiftRect (0 - (placeBounds execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minX)
                  (0 - (placeBounds execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minY)
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
        rw [← hpackeq, ← hbrectB]
        exact hrect
      exact loopTransport_cancel hww
    have hpos : 0 < (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w).w ∧
        0 < (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run w).h := by
      rw [hframe]
      exact hposV
    have hnodeW : (componentCandidate execution.graph q.1.1 candidate).nodes[w]? =
        some ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen) :=
      List.getElem?_eq_getElem hwlen
    have hbW : ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen).border
        = 0 := by
      have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
          (componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwlen, Option.getD_some]
      rw [← hget]
      exact hbord0
    exact loopRect_frameNe_of_disjoint ((Disjoint.comm _ _).mp (hdisj hnodeW hbW))
      hframe hpos.1 hpos.2
  · have hkeyBlen : keyB < inp.boxes.length :=
      (List.getElem?_eq_some_iff.mp hsourceB).1
    obtain ⟨partB, cB, posB, hkB, hposB, _hcBlen⟩ :=
      loopRect_foreignPart execution packed hpack hkeyBlen
    have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
      zip_getElem?_left hselected
    have hne : c ≠ cB := by
      intro heq
      subst heq
      have hqeq : q.1 = partB := Option.some.inj (hmemc.symm.trans hkB)
      have hmemF : keyB ∈ q.1.1 := by
        rw [hqeq]
        exact List.mem_of_getElem? hposB
      exact hmem hmemF
    have hshelfC : packed.boxes[c]? = some q.2 :=
      (List.getElem?_zip_eq_some.mp hselected).2
    have hL : partRectT execution packed c
        (shiftRect (0 - (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minX)
        (0 - (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v)) =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
      unfold partRectT
      rw [hshelfC, Option.getD_some]
    exact loopRectForeign_false_of_contained execution packed hpack hselected
      hmemR hL hkeyBlen hkB hposB hne hrect hbrectB rfl hposW hposH

end PipelineImpl
end Layered
end Elegant
