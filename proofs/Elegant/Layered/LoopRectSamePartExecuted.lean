import Elegant.Layered.LoopRectRealQProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Same-part executed loop-rect cases: bottom, range-degenerate, fixed

For the same-part case (the loop-analyzed node `v` and the exclusive scene
box both belong to the selected executed part `q.1.1`), this file proves
executed forms of three of the four open same-part cases from
`LoopRectRealQProof`: bottom, range-degenerate, and fixed. Each theorem takes
the binders of the corresponding `LoopRect<Case>Real` def plus the same-part
hypothesis `hmemW` (the exclusive box's source key lies in `q.1.1`; the
`LoopRect*Real` defs have no explicit part split, so both keys are pinned to
`q`: `v`'s key is `q.1.1[v]?` — derivable for bottom, given as `hkeyV` for
fixed, absent for range-degenerate where `v` is out of range — and the
exclusive key is `hmemW`), and concludes the same-part half of the def
(`False` for bottom/range-degenerate, the non-group existential for fixed).

Proof route per case: `loopRect_exclusive_witness` turns the exclusive origin
(`hsourceW`, `hexclW`, `hmemW`, needing only `hwf`) into a plain run node `w`
with `frameRect w` transported to `b.rect`; `loopTransport_cancel` with
`hrect`/`hrectW` gives the raw `frameRect w = frameRect v`; positivity of the
witness frame comes from `loopRect_frame_pos_of_rectEq` with the def-premise
`hposW`/`hposH`; then the corresponding `loopRect<Case>_samePart` lemma
closes. The fixed case splits on `v = w` (`refl` supplies the existential,
`ne` contradicts via disjointness).

## Truth probe (`proofs/wip/Probe/LoopRectSamePartTProbe.lean`)

Executed `flowchart` layouts (`thoroughness := 1`, candidate 0) with a
fixed-size exclusive box:

* `zeroNext` (fixed `⟨0,0⟩` box `a` next to loop owner `b`): graph node
  `n0 = (border 0, w 0, h 0)`; proper node `(w 1024, h 0)` — the height stays
  `0` through `componentRun` (`out.node.h = node.h`) while the width grows.
  Frame `(-512, 0, 1024, 0)`: `0 < h` is FALSE.
* `zeroSelf` / `smallSelf` (fixed `⟨0,0⟩` / `⟨1,1⟩` box owning the self-loop):
  graph `h = 3072` — `measuredGraph` takes `max base.h loopHeight`, so loop
  ownership restores height; proper `(w 1024, h 3072)`: positive.
* Coinciding raw frames `(v2 = v3 at (0,0,0,0))` in every case are pairs of
  out-of-range default frames (`nonode`, `pnone`, hence not `IsReal`); no
  transported frame of a real node ever hit an exclusive scene rect at an
  out-of-range or bottom-marker position (`hits = 0` for `v ≥ 2`).

Consequences:

* `exclusiveBox_frame_pos` without `hnf` is FALSE in general, and
  `InputFixedFit` does not save it (`zeroNext` satisfies `InputFixedFit`
  vacuously yet its executed frame `(-512, 0, 1024, 0)` is degenerate, probe
  `degenerateEval`). The degenerate branch is now ruled out one stage up:
  the `LoopRect*Real` defs carry `0 < b.rect.w → 0 < b.rect.h →`, and
  `flatC6LoopCase` splits on it, closing the non-positive branch by
  `Polyline.not_hits_of_zero`. The positive branch supplies `hposW`/`hposH`
  here, and `loopRect_frame_pos_of_rectEq` turns them into witness-frame
  positivity. No `hnfW` premise remains.
* No `InputFixedFit` hypothesis is taken: it is vacuous for exclusive
  sources, so it can neither replace the def premise nor discharge anything
  here.
* `hne` (`v ≠ w`) comes from the `v = w` split in the fixed theorem alone;
  the key-inequality helpers are deleted.

## Title (residual; closed in `LoopRectRealClosed`)

The title same-part case needs, from `cg.nodes[v]? = none` plus
`run.proper.nodes[v]? ≠ none`, the inversion of `v` to a border-3 title copy
with its bottom proxy `t` and the rank equality
`rk v = rk t` for `titleCopySpanClearStrict_executed` (`hwf` + `hframed`),
followed by plain-vs-title-copy band separation against `w`. No proper-node
exhaustiveness (beyond-range real node is a title copy) exists in the current
tree, and the probe inputs have no groups/titles to test it against. The
title half is closed in `LoopRectRealClosed` under the narrow
`LoopRectTitleCopyReal` residual (shifted title-copy shelf containment,
measured by the `LoopRectCrossPartProbe` `fit` rows, plus run-level
title-vs-plain disjointness) instead of an unproved proxy/rank/band
hypothesis here.
-/
/-!
# From the def premise, not from the witness (this section retired `hnfW`)

The `LoopRect*Real` defs now carry `0 < b.rect.w → 0 < b.rect.h →`, so with
the rect equation the transported frame of `v` is positive
(`loopRect_frame_pos_of_rectEq`), hence so is the witness frame via `hframe`.
The per-case finishes route through `loopRect_frameNe_of_disjoint` (bottom,
fixed-ne) and the congrArg/`omega` step (range-deg) with that positivity.
The degenerate `zeroNext` branch (`meetsInterior self = false`, probe
`degenerateEval`) is ruled out at the def premise instead of at the witness,
so the non-fixed premise `hnfW` on the exclusive witness source is gone, with
the key-inequality helpers that existed only to derive `v ≠ w` from it.
-/

/-- Bottom same-part executed case: the bottom-marker frame is degenerate in
height while the same-part plain witness frame is positive (from the def premise). -/
theorem loopRectBottom_samePart_executed
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
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
    (hrun : componentRun execution.params
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
    {nodeV : Node}
    (hnodeV : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some nodeV)
    (hbV : nodeV.border = 2)
    {keyW : Nat} {sourceW : ModelBox}
    (hsourceW : inp.boxes[keyW]? = some sourceW)
    (hexclW : sourceW.exclusive = true)
    (hrectW : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD keyW default)))
    (hmemW : keyW ∈ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  obtain ⟨w, hw, _, hwlen, _, hbord0, hpackeq⟩ :=
    loopRect_exclusive_witness execution hwf packed hpack hselected hrun hpart
      hsourceW hexclW hmemW
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
      rw [← hpackeq, ← hrectW]
      exact hrect
    exact loopTransport_cancel hww
  have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
  have hpos : 0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run w).w ∧
      0 < (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w).h := by
    rw [hframe]
    exact hposV
  exact loopRectBottom_samePart execution hrun hnodeV hbV hnodeW hbW hpos hframe

/-- Range-degenerate same-part executed case: the out-of-range frame is the
default degenerate rect while the same-part plain witness frame is positive
  (with positivity from the def premise). -/
theorem loopRectRangeDeg_samePart_executed
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
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
    (hrun : componentRun execution.params
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
    (hn : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = none)
    (hp : run.proper.nodes[v]? = none)
    {keyW : Nat} {sourceW : ModelBox}
    (hsourceW : inp.boxes[keyW]? = some sourceW)
    (hexclW : sourceW.exclusive = true)
    (hrectW : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD keyW default)))
    (hmemW : keyW ∈ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  obtain ⟨w, hw, _, hwlen, _, hbord0, hpackeq⟩ :=
    loopRect_exclusive_witness execution hwf packed hpack hselected hrun hpart
      hsourceW hexclW hmemW
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
      rw [← hpackeq, ← hrectW]
      exact hrect
    exact loopTransport_cancel hww
  have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
  have hpos : 0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run w).w ∧
      0 < (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w).h := by
    rw [hframe]
    exact hposV
  exact loopRectRangeDeg_samePart execution hrun hn hp hnodeW hbW hpos hframe

/-- Fixed same-part executed case: the loop-owner key `keyV` (fixed source)
and the exclusive-witness key `keyW` both lie in `q.1.1`.
At equal positions `refl` supplies the non-group existential; at distinct
positions `ne` contradicts the frame equation via disjointness and def-premise
positivity. -/
theorem loopRectFixed_samePart_executed
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
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
    (hcomp : q.1.1 ∈ components execution.graph)
    (hrun : componentRun execution.params
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
    {nodeV : Node} {keyV : Nat} {srcV : ModelBox}
    (hnodeV : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some nodeV)
    (hbV : nodeV.border = 0)
    (_hkeyV : q.1.1[v]? = some keyV)
    (_hsrcV : inp.boxes[keyV]? = some srcV)
    (_hfixV : inp.fixedSizes.any (fun fixed => fixed.1 == srcV.id) = true)
    {keyW : Nat} {sourceW : ModelBox}
    (hsourceW : inp.boxes[keyW]? = some sourceW)
    (hexclW : sourceW.exclusive = true)
    (hrectW : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD keyW default)))
    (hmemW : keyW ∈ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    ∃ (key' : Nat) (src' : ModelBox),
      q.1.1[v]? = some key' ∧ inp.boxes[key']? = some src' ∧ src'.role ≠ .group := by
  obtain ⟨w, hw, hroleW, hwlen, _, hbord0, hpackeq⟩ :=
    loopRect_exclusive_witness execution hwf packed hpack hselected hrun hpart
      hsourceW hexclW hmemW
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
      rw [← hpackeq, ← hrectW]
      exact hrect
    exact loopTransport_cancel hww
  have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
  have hpos : 0 < (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run w).w ∧
      0 < (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w).h := by
    rw [hframe]
    exact hposV
  by_cases heq : v = w
  · exact loopRectFixed_samePart_refl hw hsourceW hroleW heq
  · exact False.elim (loopRectFixed_samePart_ne execution hcomp hrun hnodeV hbV
      hnodeW hbW heq hpos hframe)

end PipelineImpl
end Layered
end Elegant
