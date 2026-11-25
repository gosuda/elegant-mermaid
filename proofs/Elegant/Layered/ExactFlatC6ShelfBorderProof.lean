import Elegant.Layered.ExactFlatC6WProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Pack
import Elegant.Layered.RouteTransport
import Elegant.Layered.ExactLoopRectProof
import Elegant.Layered.ExactFlatC5Rank

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact flat C6 shelf positivity and border-zero, W form.

Shelf (`X6_ShelfPositiveW`) is FALSE as stated: witness `twoZero`
(`a`,`b` both `⟨0,0⟩` exact, edge `a->b`) gives part `(0,3072)` and shelf
`(0,3072)` with `0<w` failing, though `WellFormed`, `framedParents` and
`layoutX` success all hold (probe `X6ShelfBorderTProbe5`: `twoZero/exact-ab`
`shelf=false`, `parts=[(0,3072)] boxes=[(0,3072)]`, `wf=true fp=true`,
`layout=ok c6=true`; the five executed exact inputs `flatWide/exact-a`,
`nested/exact-m`, `loopWide/exact-a`, `zero/exact-a`, `twoZero/exact-ab`
plus ill-formed `ill/none` cover flat two groups, nested groups, self-loop,
zero-size and wide fixed boxes named in `exactIds`, and ill-formed).
The true form the consumer needs adds the part-size premises the packing
transport preserves (`0<width`, `0<height`); proved below as
`X6_shelfPositiveW_of_partPos_holds` via `Pack.pack_dimensions` and
`shiftRect_dims`/`orientRect_dims` (no content replay needed).

Border (`X6_BorderZeroRealW`) is TRUE on the same five probes
(`X6ShelfBorderTProbe6`: `border=true` for all five `wf=true` exact inputs;
`ill/none` has `wf=false`, so the W form holds vacuously there).
Proved below as `X6_borderZeroRealW_holds` modulo the single hard residual
`X6_BorderHardW` (top `-2` impossibility). The residual is directly mirrored
by `X6ShelfBorderTProbe7` (`noMinus2`): `true` with a *witnessed* coincidence
on `flatWide/exact-a`, `nested/exact-m`, `loopWide/exact-a`; vacuous but true
on `zero/exact-a`/`twoZero/exact-ab` (no positive exclusive box coincides);
`ill/none` is outside the `hwf` premise. Discharging it would need the
`-2`-specific frame-hull argument of `XL_loopRectTopReal` (foreign-span
residual), not reproduced here. -/

/-- Conditional shelf positivity: with positive part dims, the transported
packed shelf is positive (packing preserves dims, shifts/orients preserve
positivity). Witness for the unconditional false form: `{ kind := "flowchart", boxes := [⟨"a", .node, "", true⟩, ⟨"b", .node, "", false⟩], routes := [⟨"e1", "a", "b"⟩], texts := ["a", "b"], edges := [.plain], labels := [], fixedSizes := [("a", ⟨0, 0⟩), ("b", ⟨0, 0⟩)] }` with `exactIds := ["a", "b"]`. -/
theorem X6_shelfPositiveW_of_partPos_holds (exactIds : List String) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      (packed : Pack.State)
      (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
      {c : Nat} {q : (List Nat × Part) × Rect}
      (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
      {candidate : Nat} {i : Nat} {edge : Edge}
      (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
      (_hW : 0 < q.1.2.width) (_hH : 0 < q.1.2.height),
      0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (packed.boxes[c]?.getD default))).w ∧
      0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (packed.boxes[c]?.getD default))).h := by
  intro inp o res execution _hwf _hfp packed hpacked c q hselected candidate i edge hedge hW hH
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  have hshelfC : packed.boxes[c]? = some q.2 :=
    (List.getElem?_zip_eq_some.mp hselected).2
  have hdim := Pack.pack_dimensions hpacked
  unfold Pack.dimensions at hdim
  have h1 := congrArg (fun l : List (Int × Int) => l[c]?) hdim
  simp only [List.getElem?_map, hshelfC, hmemc, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨hBw, hBh⟩ := h1
  have hget : packed.boxes[c]?.getD default = q.2 := by
    rw [hshelfC, Option.getD_some]
  rw [hget]
  have hqW : 0 < q.2.w := by rw [hBw]; exact hW
  have hqH : 0 < q.2.h := by rw [hBh]; exact hH
  have hs2 := (orientRect_dims o.direction execution.packedAcc.canvasH q.2).mpr ⟨hqW, hqH⟩
  exact (shiftRect_dims execution.params.canvasMargin
    execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH q.2)).mpr hs2
/-- Hard residual (W form top `-2` impossibility): a real run node behind a
positive foreign exclusive scene box cannot be a group top. True on the five
probes (`X6ShelfBorderTProbe6` `border=true` for all `wf=true` exact inputs
implies no `-2` with rect coincidence, since `-2≠0` would also falsify the
border bool; `ill/none` has `wf=false`, so the W form holds vacuously). -/
def X6_BorderHardW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ (candidate : Nat) (run : Run) (packed : Pack.State),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    ∀ (c : Nat) (q : (List Nat × Part) × Rect),
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {area : Int} {loops : List (Nat × LoopPlacement)},
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    q.1.1 ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = -2 → False
/-- Border-zero (W): a real node behind a positive foreign exclusive scene box
has border zero, modulo the hard top residual. `none` gives `default` border
`0` by `rfl`; `some` with border `0` is direct via `getD`; border `2` is
`XL_loopRectBottomReal_holds`; border `-2` is the hard residual. Marker shape
is `X_componentCandidate_marker_shape`, so no other borders occur. -/
theorem X6_borderZeroRealW_holds (exactIds : List String)
    (hhard : X6_BorderHardW exactIds) : X6_BorderZeroRealW exactIds := by
  intro inp o res execution hwf hfp candidate run packed hpack c q hselected
    area loops hpart hmem hrun v b hreal hbmem hexcl hw hh heq
  cases hnode : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? with
  | none =>
    have hgetD : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default =
        default := by
      rw [List.getD_eq_getElem?_getD, hnode, Option.getD_none]
    have hbdef : (default : Node).border = 0 := rfl
    rw [hgetD, hbdef]
  | some node =>
    obtain ⟨hshape, _⟩ :=
      X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq hnode
    rcases hshape with hb0 | hbtop | hbbot
    · have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default =
          node := by
        rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
      rw [hget, hb0]
    · exact False.elim (hhard execution hwf hfp candidate run packed hpack
        c q hselected hpart hmem hrun v b hreal hbmem hexcl hw hh heq hnode hbtop)
    · have hY : (0 : Int) - (placeBoundsX execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minY =
          -((placeBoundsX execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY) := by omega
      rw [hY] at heq
      exact False.elim (XL_loopRectBottomReal_holds execution candidate run packed hpack
        c q hselected hpart hmem hrun v b hreal hbmem hexcl hw hh heq hnode hbbot)




end PipelineImpl
end Layered
end Elegant
