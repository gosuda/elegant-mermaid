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
`hrect`/`hrectW` gives the raw `frameRect w = frameRect v`; the width fact
`hlineW` comes from `loopRect_lines_get`; then the corresponding
`loopRect<Case>_samePart` lemma closes. The fixed case splits on `v = w`
(`refl` supplies the existential, `ne` contradicts via disjointness).

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
  `InputFixedFit` does not save it: `zeroNext` satisfies `InputFixedFit`
  vacuously (its only fixed entry names the exclusive box `a`; see
  `inputFixedFit_of_fixedExclusive`), yet the executed frame is degenerate.
  So there is no `exclusiveBox_frame_pos_of_fit` twin from `InputFixedFit`
  alone. The non-fixed premise `hnfW` on the exclusive witness source is
  load-bearing and is kept as a narrow residual (one box's fixed-status at
  the `measuredGraph` fixed-size lookup stage; probe-tested above). `hnfW`
  is strictly narrower than the target and is the only extra premise beyond
  `WellFormed`, `framedParents`, and the `SceneExecution` equations.
* No `InputFixedFit` hypothesis is taken: it is vacuous for exclusive
  sources, so it can neither replace `hnfW` nor discharge anything here. The
  consumer (`flatC6_closed` via `loopRectPlainSourceRealQ`) must supply
  `hnfW`/`hmemW` (or restrict the loop case to non-fixed exclusive boxes).
* `hne` (`v ≠ w`) is derived two ways: per-branch from the `v = w` split in
  the fixed theorem, and unconditionally by `loopRectFixed_keyNe_of_fixedUnfixed`
  (fixed loop-owner source vs unfixed exclusive source) composed with
  `loopRectFixed_posNe_of_keyNe`. The group-based variant
  (`loopRectFixed_keyNe_of_groupNode`) additionally needs
  `srcV.role = .group`, which `LoopRectFixedReal` does not supply — that is
  the exact missing premise for the group-flavored derivation; the
  fixed-status derivation needs nothing more.

## Title (residual, no theorem stated)

The title same-part case needs, from `cg.nodes[v]? = none` plus
`run.proper.nodes[v]? ≠ none`, the inversion of `v` to a border-3 title copy
with its bottom proxy `t` and the rank equality
`rk v = rk t` for `titleCopySpanClearStrict_executed` (`hwf` + `hframed`),
followed by plain-vs-title-copy band separation against `w`. No proper-node
exhaustiveness (beyond-range real node is a title copy) exists in the current
tree, and the probe inputs have no groups/titles to test it against. Stating
the theorem with an unproved proxy/rank/band hypothesis would be a wrapper
around the open fact, so it is left out and reported instead.
-/

/-!
# Positivity case-split analysis (`hnfW` cannot be removed this way)

Tested per follow-up: `by_cases` on `0 < (frameRect w).w ∧ 0 < (frameRect w).h`.
Positive branch: closes with the current argument taking positivity from the
case — the explicit-w/h lemmas are `loopRect_frameNe_of_disjoint` (bottom,
fixed-ne) and the congrArg/`omega` step (range-deg); no `hnfW` needed there.
Non-positive branch: the lemmas below show a degenerate frame meets nothing,
so `hframe` plus the positivity-free disjointness facts
(`bottomMarker_frame_disjoint`, `componentRun_positions_disjoint`, the
default-frame shape) yields only `Disjoint Fw Fw` — consistent, not `False`.
The `LoopRect*Real` conclusions (`False`, existential) are NOT interior
tests; the interior test appears only as `Disjoint`, i.e. `¬ meetsInterior`
(`ElegantGeometry/Disjoint.lean:9`, predicate `Rect.meetsInterior` at
`ElegantGeometry/Basic.lean:96`). The per-case finishes route through
`loopRect_frameNe_of_disjoint`, which needs `meetsInterior Fw Fw`, i.e.
positivity. Hence `hnfW` stays: it rules out the consistent degenerate
branch. Concrete evaluation: the `zeroNext` witness frame `(-512, 0, 1024, 0)`
has `meetsInterior self = false` (probe `degenerateEval`), i.e. it is
self-disjoint, so an exact equation against a same-shaped marker/default
frame would not contradict disjointness.
-/

/-- A rectangle with non-positive width or height meets nothing on its left:
its interior is empty. -/
theorem not_meetsInterior_of_nonpos_left {r s : Rect}
    (h : r.w ≤ 0 ∨ r.h ≤ 0) : ¬ r.meetsInterior s := by
  unfold Rect.meetsInterior
  omega

/-- A rectangle with non-positive width or height meets nothing on its right:
the other rectangle's interior cannot reach into its empty span. -/
theorem not_meetsInterior_of_nonpos_right {r s : Rect}
    (h : s.w ≤ 0 ∨ s.h ≤ 0) : ¬ r.meetsInterior s := by
  unfold Rect.meetsInterior
  omega

/-- A degenerate rectangle is self-disjoint: the non-positive branch of a
positivity split ends here — consistent — instead of at `False`. -/
theorem disjoint_self_of_nonpos {r : Rect} (h : r.w ≤ 0 ∨ r.h ≤ 0) :
    Disjoint r r :=
  not_meetsInterior_of_nonpos_left h

/-- Key inequality for the fixed case: a fixed loop-owner source and an
unfixed exclusive-witness source sit at different box indices (equal indices
would give one box two fixed-statuses). -/
theorem loopRectFixed_keyNe_of_fixedUnfixed
    {inp : Input} {keyV keyW : Nat} {srcV srcW : ModelBox}
    (hsrcV : inp.boxes[keyV]? = some srcV)
    (hsrcW : inp.boxes[keyW]? = some srcW)
    (hfixV : inp.fixedSizes.any (fun fixed => fixed.1 == srcV.id) = true)
    (hnfW : inp.fixedSizes.any (fun fixed => fixed.1 == srcW.id) = false) :
    keyV ≠ keyW := by
  intro hcon
  subst hcon
  have heq : srcV = srcW := Option.some.inj (hsrcV.symm.trans hsrcW)
  subst heq
  rw [hfixV] at hnfW
  exact Bool.noConfusion hnfW

/-- Position distinctness from the key inequality within one part list:
different keys at `v`, `w` mean different positions. -/
theorem loopRectFixed_posNe_of_keyNe
    {q : (List Nat × Part) × Rect} {v w keyV keyW : Nat}
    (hkeyV : q.1.1[v]? = some keyV)
    (hw : q.1.1[w]? = some keyW)
    (hne : keyV ≠ keyW) :
    v ≠ w := by
  intro hcon
  subst hcon
  have heq : keyV = keyW := Option.some.inj (hkeyV.symm.trans hw)
  exact hne heq

/-- Group-flavored key inequality: a group loop-owner source and a node
exclusive source are different boxes, hence at different indices. Needs
`hgroupV`, which `LoopRectFixedReal` does not supply (exact missing premise
for this variant; the fixed-status variant above needs nothing more). -/
theorem loopRectFixed_keyNe_of_groupNode
    {inp : Input} {keyV keyW : Nat} {srcV srcW : ModelBox}
    (hsrcV : inp.boxes[keyV]? = some srcV)
    (hsrcW : inp.boxes[keyW]? = some srcW)
    (hgroupV : srcV.role = .group)
    (hnodeW : srcW.role = .node) :
    keyV ≠ keyW := by
  intro hcon
  subst hcon
  have heq : srcV = srcW := Option.some.inj (hsrcV.symm.trans hsrcW)
  rw [heq] at hgroupV
  rw [hnodeW] at hgroupV
  exact absurd hgroupV (by decide)

/-- Bottom same-part executed case: the bottom-marker frame is degenerate in
height while the same-part plain witness frame is positive (via `hnfW`). -/
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
    (hnfW : inp.fixedSizes.any (fun fixed => fixed.1 == sourceW.id) = false) :
    False := by
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
  have hkeylenW : keyW < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceW).1
  obtain ⟨lsW, hlineW⟩ := loopRect_lines_get execution hkeylenW
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
  exact loopRectBottom_samePart execution hrun hnodeV hbV hnodeW hbW hw hsourceW
    hlineW hroleW hnfW hframe

/-- Range-degenerate same-part executed case: the out-of-range frame is the
default degenerate rect while the same-part plain witness frame is positive
(via `hnfW`). -/
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
    (hnfW : inp.fixedSizes.any (fun fixed => fixed.1 == sourceW.id) = false) :
    False := by
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
  have hkeylenW : keyW < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceW).1
  obtain ⟨lsW, hlineW⟩ := loopRect_lines_get execution hkeylenW
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
  exact loopRectRangeDeg_samePart execution hrun hn hp hnodeW hbW hw hsourceW
    hlineW hroleW hnfW hframe

/-- Fixed same-part executed case: the loop-owner key `keyV` (fixed source)
and the exclusive-witness key `keyW` (unfixed source) both lie in `q.1.1`.
At equal positions `refl` supplies the non-group existential; at distinct
positions `ne` contradicts the frame equation via disjointness and `hnfW`
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
    (hkeyV : q.1.1[v]? = some keyV)
    (hsrcV : inp.boxes[keyV]? = some srcV)
    (hfixV : inp.fixedSizes.any (fun fixed => fixed.1 == srcV.id) = true)
    {keyW : Nat} {sourceW : ModelBox}
    (hsourceW : inp.boxes[keyW]? = some sourceW)
    (hexclW : sourceW.exclusive = true)
    (hrectW : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD keyW default)))
    (hmemW : keyW ∈ q.1.1)
    (hnfW : inp.fixedSizes.any (fun fixed => fixed.1 == sourceW.id) = false) :
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
  have hkeylenW : keyW < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceW).1
  obtain ⟨lsW, hlineW⟩ := loopRect_lines_get execution hkeylenW
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
  have hkeys : keyV ≠ keyW :=
    loopRectFixed_keyNe_of_fixedUnfixed hsrcV hsourceW hfixV hnfW
  have hpos : v ≠ w := loopRectFixed_posNe_of_keyNe hkeyV hw hkeys
  by_cases heq : v = w
  · exact loopRectFixed_samePart_refl hw hsourceW hroleW heq
  · exact False.elim (loopRectFixed_samePart_ne execution hcomp hrun hnodeV hbV
      hnodeW hbW hpos hw hsourceW hlineW hroleW hnfW hframe)

end PipelineImpl
end Layered
end Elegant
