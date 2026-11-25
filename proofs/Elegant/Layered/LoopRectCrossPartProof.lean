import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.PartSeparation
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Cross-part loop rectangle clearance

The five `LoopRect<Case>Real` residuals (`LoopRectPlainSourceProof.lean`) each
say: a transported `frameRect` of a special run node `v` of the selected part
`q` never coincides with the rect of an exclusive scene box `b`. By
`loopRect_samePart_frameEq` (`LoopRectRealQProof.lean`), the box `b` either
comes from a plain node `w` of the same part (the `Or.inl` case, closed by the
same-part lemmas) or its model source key is foreign to the part (the `Or.inr`
payload: `keyB ∉ q.1.1` plus the packed transport equation for `keyB`). This
file closes the shape of the `Or.inr` case once, then instantiates it.

## The shared vehicle

`loopRect_crossPart_executed`: for an executed scene, a part-local rect `R`
of part `c` transported with `c`'s shelf never meets the interior of the
scene transport of a packed box key from a different part `cB`. Both sides
are contained in their own transported shelves (`part_rects_within_shelf`
over `R ∈ q.1.2.rects` and the `part_frame_lookup` frame of `keyB`), and
distinct shelves are disjoint (`partsShelvesDisjoint_of_pack`), so
`rect_misses_box_of_distinct_parts` closes it.

Positivity is NOT needed for this step. `Rect.meetsInterior` is a strict
inequality on open interiors
(`max a.x b.x < min (a.x + a.w) (b.x + b.w) ∧ ...`): a rect with
non-positive width or height never meets any interior, so containment in
disjoint shelves suffices unconditionally, including for degenerate rects.

## From disjointness to `False`

The residuals conclude `False` from the rect equation, so each corollary
needs positivity of the common scene rect. That positivity now comes from
the `LoopRect*Real` def premises (`hposW`/`hposH`): the shelf transports
preserve positivity up to orientation swap, and the equation carries it to
the loop rect (`loopRect_frame_pos_of_rectEq`, `loopRect_crossPart_false`).

Truth note (probed on executed layouts,
`proofs/wip/Probe/LoopRectCrossPartProbe.lean`): with a fixed-size exclusive
box of size zero in another part, the foreign scene box IS degenerate
(`zeroForeign`: box `z` fixed `0×0` has scene rect `(1024,5632,512,0)`,
height `0`; `zeroGroup`: fixed `0×0` group frame has height `0`). Hence the
bare fact (from `WellFormed` and `framedParents` alone) is not provable, and
the degenerate branch is ruled out one stage up: `flatC6LoopCase` splits on
`0 < b.rect.w ∧ 0 < b.rect.h`, closing the non-positive branch by
`Polyline.not_hits_of_zero`. `InputFixedFit` is the wrong vehicle here: it
is vacuous for exclusive sources (its conclusion requires
`box.exclusive = false`), so it cannot floor the foreign exclusive box. No
probed input shows a cross-part coincidence (every observed `hits` is a
same-part self-hit).

## Per-case status

* Top (`border = -2`), Bottom (`border = 2`): `v` is in range, so the
  shifted frame is in `q.1.2.rects` and the shared vehicle applies.
* Range-degenerate: the frame is the default degenerate rect
  (`loopRect_rangeDeg_frame`), so disjointness holds directly by degeneracy
  (`loopRect_degenerate_crossPart`); the shared vehicle is not needed.
* Fixed: the conclusion is existential. The non-fixed-owner sub-case is
  discharged by the refl witness plus `loopRectPlain_of_unfixed` in the
  dispatcher; the fixed-owner sub-case splits on the part key (same-part
  witness plus position split, foreign half by the shared vehicle), all with
  positivity from the def premise (`LoopRectRealClosed`).
* Title: the beyond-range frame is NOT in `q.1.2.rects` (candidate rects
  cover only in-range nodes), so the shared vehicle does not apply. Probed:
  the title-copy frame is positive (`(3651,0,672,3072)`) and empirically
  shelf-contained (`fit=true`). The degenerate sub-case (side-marker copies,
  e.g. height `0`) is closed here under an explicit degeneracy hypothesis;
  the positive sub-case is closed in `LoopRectRealClosed` under the narrow
  `LoopRectTitleCopyReal` residual.
* `LoopRectTopForeignReal` is NOT a cross-part statement: it quantifies the
  same selected part, candidate, and run, with `w` in the same component. It
  is the same-part foreign-span sub-case and needs the title-copy/foreign
  span seam, not shelf separation. It stays residual; this file does not
  attempt it.
-/

 /-- Local copy of the private `RankSiblingDisjoint.placeComponent_rects_get`:
 a placed component rect is the run frame shifted by the placement origin. -/
theorem loopRectCross_rects_get (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) {i : Nat}
     (hi : i < cg.nodes.length) :
     (placeComponent P cg run 0 labels loops).rects[i]? =
       some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
         (0 - (placeBounds P cg run labels loops).minY)
         (frameRect P cg run i)) := by
   unfold placeComponent placeBounds
   simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
 /-- Local copy of the private candidate length fact: a candidate graph has
 exactly the component's nodes (used for the foreign part position bound). -/
theorem loopRectCross_candidate_length (g : Graph) (comp : List Nat)
     (index : Nat) :
     (componentCandidate g comp index).nodes.length = comp.length := by
   rw [componentCandidate_nodes]
   simp only [componentGraph, List.length_map]

 theorem loopRect_foreignPart
     {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (packed : Pack.State)
     (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0
       (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun q =>
         ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
     {keyB : Nat} (hkeyBlen : keyB < inp.boxes.length) :
    ∃ (partB : List Nat × Part) (cB posB : Nat),
      execution.componentsAcc.parts[cB]? = some partB ∧
      partB.1[posB]? = some keyB ∧ cB < packed.boxes.length := by
  obtain ⟨partB, hpartBmem, entry, hentrymem, hentrykey⟩ :=
    sceneExecution_parts_entry execution hkeyBlen
  obtain ⟨cB, hcBget⟩ := List.mem_iff_getElem?.mp hpartBmem
  have hposmem : entry.1 ∈ partB.1 := (List.of_mem_zip hentrymem).1
  obtain ⟨posB, hposB⟩ := List.getElem?_of_mem hposmem
  rw [hentrykey] at hposB
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hcBget).1
    omega
  exact ⟨partB, cB, posB, hcBget, hposB, hcBlen⟩

/-- Cross-part half, once: a part-local rect transported with shelf `c`
never meets the interior of the scene transport of a packed box key from a
different part. No positivity is needed: `meetsInterior` is strict on open
interiors, so degenerate rects never meet. -/
theorem loopRect_crossPart_executed
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
    {R : Rect} (hR : R ∈ q.1.2.rects)
    {keyB : Nat} (hkeyBlen : keyB < inp.boxes.length)
    {cB : Nat} {partB : List Nat × Part} {posB : Nat}
    (hkB : execution.componentsAcc.parts[cB]? = some partB)
    (hposB : partB.1[posB]? = some keyB)
    (hne : c ≠ cB) :
    ¬ (partRectT execution packed c R).meetsInterior
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hclen : c < packed.boxes.length := by
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
  have hcontR := part_rects_within_shelf hpack hmemc hclen R hR
  have hcontB := part_rects_within_shelf hpack hkB hcBlen fB hfBmem
  have hdisj := partsShelvesDisjoint_of_pack hpack
  rw [hval]
  have hRHS : (shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect boxB.x boxB.y fB))) = partRectT execution packed cB fB := by
    unfold partRectT
    rw [hboxB, Option.getD_some]
  rw [hRHS]
  exact rect_misses_box_of_distinct_parts hdisj hclen hcBlen hne hcontR hcontB

/-- Workhorse: from the rect equation, disjointness of the two transported
rects, and positivity of the common scene rect, derive `False`. Positivity
travels from the scene rect to the loop rect through the equation. -/
theorem loopRect_crossPart_false
    {L B : Rect} {b : Box}
    (hrect : b.rect = L) (hbrectBw : b.rect = B)
    (hdis : Disjoint L B)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have heq : L = B := hrect.symm.trans hbrectBw
  have hw : 0 < L.w := by rw [← hrect]; exact hposW
  have hh : 0 < L.h := by rw [← hrect]; exact hposH
  exact loopRect_frameNe_of_disjoint hdis heq hw hh
/-- A transported degenerate rect (non-positive width or height) meets no
interior, in any direction. This is the `meetsInterior` strictness
discharging the range-degenerate case (and the degenerate title sub-case)
without any shelf argument. -/
theorem loopRect_degenerate_crossPart
    {M H qx qy lx ly : Int} {d : Direction} {fr : Rect}
    (hdeg : fr.w ≤ 0 ∨ fr.h ≤ 0)
    {B : Rect} :
    Disjoint (shiftRect M M (orientRect d H
      (shiftRect qx qy (shiftRect lx ly fr)))) B := by
  unfold Disjoint Rect.meetsInterior
  intro hmeet
  obtain ⟨h1, h2⟩ := hmeet
  cases hd : d <;> simp only [hd, shiftRect, orientRect] at h1 h2 ⊢ <;> omega

/-- Cross-part half of `LoopRectTopReal`: with the foreign origin payload
(`keyB ∉ q.1.1` plus the packed transport equation) and positivity from the
def premise, the rect equation is impossible. -/
theorem loopRectTop_crossPart
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
    (_hbord : node.border = -2)
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
  have hdis := loopRect_crossPart_executed execution packed hpack hselected
    hR hkeyBlen hkB hposB hne
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
  have hdisL : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
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
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [← hL]
    exact hdis
  exact loopRect_crossPart_false hrect hbrectB hdisL hposW hposH

/-- Cross-part half of `LoopRectBottomReal`: same shape as the top case; the
bottom-marker frame is in range, so the shifted frame is in `q.1.2.rects`
and the shared vehicle applies. -/
theorem loopRectBottom_crossPart
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
    (_hbord : node.border = 2)
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
  have hdis := loopRect_crossPart_executed execution packed hpack hselected
    hR hkeyBlen hkB hposB hne
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
  have hdisL : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
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
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [← hL]
    exact hdis
  exact loopRect_crossPart_false hrect hbrectB hdisL hposW hposH

/-- Cross-part half of `LoopRectRangeDegReal`: the out-of-range frame is the
default degenerate rect, so the transported loop rect meets no interior by
degeneracy alone; positivity from the def premise closes the equation. -/
theorem loopRectRangeDeg_crossPart
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (candidate : Nat) (run : Run)
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
    {keyB : Nat} {sourceB : ModelBox}
    (_hsourceB : inp.boxes[keyB]? = some sourceB)
    (hbrectB : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default)))
    (_hforeign : keyB ∉ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hdeg := loopRect_rangeDeg_frame (P := execution.params)
    (cg := componentCandidate execution.graph q.1.1 candidate) (run := run)
    (v := v) hn hp
  have hw0 : (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v).w = 0 :=
    congrArg Rect.w hdeg
  have hdis : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
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
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) :=
    loopRect_degenerate_crossPart (Or.inl (by omega))
  exact loopRect_crossPart_false hrect hbrectB hdis hposW hposH

/-- Degenerate sub-case of the title cross-part half: when the beyond-range
frame is degenerate, disjointness holds by degeneracy alone. The positive
sub-case is closed in `LoopRectRealClosed` (shelf containment plus run-level
disjointness, `LoopRectTitleCopyReal`); the beyond-range frame is not in
`q.1.2.rects`, so the shelf vehicle here does not apply. -/
theorem loopRectTitleDegenerate_crossPart
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (candidate : Nat) (run : Run)
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
    (_hn : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = none)
    (_hp : run.proper.nodes[v]? ≠ none)
    (hdeg : (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v).w ≤ 0 ∨
      (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v).h ≤ 0)
    {keyB : Nat} {sourceB : ModelBox}
    (_hsourceB : inp.boxes[keyB]? = some sourceB)
    (hbrectB : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default)))
    (_hforeign : keyB ∉ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hdis : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
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
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) :=
    loopRect_degenerate_crossPart hdeg
  exact loopRect_crossPart_false hrect hbrectB hdis hposW hposH


end PipelineImpl
end Layered
end Elegant
