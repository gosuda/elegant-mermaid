import Elegant.Layered.ExactLoopEnvelopeLayerProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeMissProof
import Elegant.Layered.ExactLoopEnvelopeRankProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Right-miss half of the exact loop-envelope miss, over exact runs.

Engine truth (`proofs/wip/Probe/ExactLoopEnvelopeRightTProbe.lean`, vector
profile; `fp` is `loopFootprintExt` at the looping plain owner):
- `sib`, `zero` (zero-size fixed owner), `empty-group` (empty group frame),
  `nested` (two-deep groups), `exact-a` (exact single loop, fixed size):
  every executed exact component reports no `RIGHTVIOL`, i.e. every
  same-layer box right of a border-0 loop owner starts at or past the
  extended-footprint end, on both candidates.
- `ill` (dangling route) fails preparation with `LayoutError.domain`, so the
  miss holds vacuously there.
The earlier `ExactEnvelopeSidesTProbe.lean` `checkGaps` cases (`core-plain`,
`core-plain-zero`, `core-plain-long`, `core-plain-exact-a`, `grp-owner-1`,
`core-plain-exact-fixed`, `nested-plain`, `nested-plain-exact-a`) report no
`RIGHTVIOL`/`LEFTVIOL` either; the same-layer right case with a plain later
node is exercised by `core-plain` (owner at position 0, plain sibling at
position 1, both real and in scope).

Public results (W form: no global `WellFormed` premise; only executed-run
facts are used):
- `XLEM_plainRightMiss_holds (hNonPlain : XLEM_PlainRightNonPlain _) :
  XLEM_PlainRightMiss _`: proved for original plain later nodes. The single
  narrower residual `XLEM_PlainRightNonPlain` (a later node that is not an
  original plain node) stays open; every probe same-layer case is plain.
- `X_loopEnvOtherOwner_of_parts` reduces `X_loopEnvOtherOwner` to the four
  tracked parts (other-rank, plain right/left, group owner) with no new
  residual: the rank split needs no owner-kind premise, and the same-rank
  pieces cover border-0 owners (right, left, self) and group owners directly.

Proof idea (plain twin of the group reservation): the owner's coordinate
width covers its recorded loop extent, and the same-layer separation gap
(`cluster_balance_separated` plus the zero-gap tail, with the
ownTitleAnchor case impossible by computation on border-0 endpoints, so no
title uniqueness is needed) puts every same-layer box right of the owner
past the footprint end. The loop extent recorded on the owner covers the
footprint width in both sizing branches (`exactExtent` for exact owners via
`exactGraph`, plain `extent` otherwise via the measured graph).
-/

/-- Pure x-gap: a footprint ending left of a box misses it. -/
private theorem XLEMR_rect_miss_right {fp rb : Rect}
    (h : fp.x + fp.w ≤ rb.x) : ¬ fp.meetsInterior rb := by
  unfold Rect.meetsInterior
  omega

/-- Footprint origin from the owner frame equation. -/
private theorem XLEMR_fp_of_frame {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {t : Nat}
    (hFr : frameRect default cg run t =
      RouteImpl.boxRect run.proper run.xs run.ys t) :
    (loopFootprintExt cg run labels t).x =
      (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w := by
  unfold loopFootprintExt
  simp only [hFr]

/-- Prefixed copy of `XLEMS_nonproxy_record`: exact proper nodes transfer
for non-proxy borders. -/
private theorem XLEMR_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]
/-- Prefixed copy of `XLEMS_original_plain_record`: exact original plain
nodes keep their measured record through the coordinate phases. -/
private theorem XLEMR_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := (XLEMR_nonproxy_record h hcoordinate (by rw [hborder]; decide)).1
  have hxs := (XLEMR_nonproxy_record h hcoordinate (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  exact hxs

/-- Prefixed copy of `XLEMS_coord_loopExtent`: `coordinateGraphX` preserves
the loop extent of a plain anchor. -/
private theorem XLEMR_coord_loopExtent {P : Params} {exact : List Nat}
    {p : Proper} {i : Nat} {nd : ProperNode}
    (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.node.loopExtent = nd.node.loopExtent := by
  obtain ⟨sized, hs, hb', hle⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.node.border = 0 ∧ sized.node.loopExtent = nd.node.loopExtent := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, hb, rfl⟩
    · refine ⟨_, rfl, hb, rfl⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? =
      some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · refine ⟨_, rfl, ?_⟩
    show sized.node.loopExtent = nd.node.loopExtent
    exact hle
  · exact ⟨_, rfl, hle⟩
/-- Original plain actuals keep the loop extent as well as dims. -/
private theorem XLEMR_actual_loopExtent {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      actual.node.loopExtent = node.loopExtent := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨outD, hdim, _, _, _, _⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  obtain ⟨outL, hloop, hle⟩ := XLEMR_coord_loopExtent hsource hplain
  have hdimC : run.coordinateProper.nodes[index]? = some outD := by
    rw [← hc]
    exact hdim
  have hloopC : run.coordinateProper.nodes[index]? = some outL := by
    rw [← hc]
    exact hloop
  have heq : outD = outL := Option.some.inj (hdimC.symm.trans hloopC)
  have hlabLoop : outL.node.loopExtent = node.loopExtent := hle
  refine ⟨outD, hdimC, ?_⟩
  rw [heq]
  exact hlabLoop

/-- Prefixed copy of `X_self_run_exact_eq`: exact-run index list equation. -/
private theorem XLEMR_run_exact_eq {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.exact = cg.nodes.zipIdx.filterMap
      (fun q : Node × Nat => if exact.contains q.1.decl then some q.2 else none) := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, _, h⟩ := bind_ok h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  rw [← he]
/-- Prefixed copy of `XLEM_exact_bound`: an index recorded in `run.exact`
carries an exact decl. -/
private theorem XLEMR_exact_bound {cg : Graph} {exact : List Nat} {t : Nat}
    (h : (cg.nodes.zipIdx.filterMap fun q =>
      if exact.contains q.1.decl then some q.2 else none).contains t = true) :
    t < cg.nodes.length ∧ exact.contains (cg.nodes.getD t default).decl = true := by
  have hm : t ∈ cg.nodes.zipIdx.filterMap fun q =>
      if exact.contains q.1.decl then some q.2 else none :=
    List.contains_iff_mem.mp h
  obtain ⟨q, hq, hfq⟩ := List.mem_filterMap.mp hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  rw [List.getElem?_zipIdx] at hi
  cases hni : cg.nodes[i]? with
  | none => simp [hni] at hi
  | some ni =>
    simp only [hni, Option.map_some, Nat.zero_add] at hi
    have hqq : (ni, i) = q := Option.some.inj hi
    rw [← hqq] at hfq
    dsimp only at hfq
    by_cases hc : exact.contains ni.decl = true
    · simp only [hc, ↓reduceIte] at hfq
      have hti : i = t := Option.some.inj hfq
      subst hti
      refine ⟨(List.getElem?_eq_some_iff.mp hni).1, ?_⟩
      rw [List.getD_eq_getElem?_getD, hni, Option.getD_some]
      exact hc
    · have hconj : exact.contains ni.decl = true ∧ i = t := by simpa using hfq
      exact absurd hconj.1 hc

/-- An exact decl is a real box index carrying an exact-listed id (or a
fixed group child frame). -/
private theorem XLEMR_exactDecl_box {exactIds : List String} {inp : Input}
    {d : Nat} (hmem : (exactDecls exactIds inp).contains d = true) :
    ∃ box, inp.boxes[d]? = some box ∧
      (box.id ∈ exactIds ∨
        (box.role = BoxRole.group ∧ ∃ x, (box.id, x) ∈ inp.fixedSizes)) := by
  have hm : d ∈ exactDecls exactIds inp := List.contains_iff_mem.mp hmem
  unfold exactDecls at hm
  obtain ⟨q, hq, hfq⟩ := List.mem_filterMap.mp hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  rw [List.getElem?_zipIdx] at hi
  cases hbi : inp.boxes[i]? with
  | none => simp [hbi] at hi
  | some box =>
    simp only [hbi, Option.map_some, Nat.zero_add] at hi
    have hqq : (box, i) = q := Option.some.inj hi
    rw [← hqq] at hfq
    dsimp only at hfq
    have hcase : (box.id ∈ exactIds ∨ box.role = BoxRole.group ∧
        ∃ x, (box.id, x) ∈ inp.fixedSizes) ∧ i = d := by
      simpa using hfq
    obtain ⟨hcond, rfl⟩ := hcase
    rcases hcond with hc | ⟨hgrp, hfix⟩
    · exact ⟨box, hbi, Or.inl hc⟩
    · exact ⟨box, hbi, Or.inr ⟨hgrp, hfix⟩⟩
/-- `exactGraph` assigns the exact loop extent to exact-listed (or fixed
group) boxes. -/
private theorem XLEMR_exactGraph_loopExtent {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {m : Nat} {nd : Node} (hm : g0.nodes[m]? = some nd)
    {box : ModelBox} (hbox : inp.boxes[nd.decl]? = some box)
    (hex : box.id ∈ exactIds ∨
      (box.role = BoxRole.group ∧ ∃ x, (box.id, x) ∈ inp.fixedSizes)) :
    ∃ nd', g.nodes[m]? = some nd' ∧
      nd'.loopExtent =
        (Loops.exactExtent P.slot (loopSizes g0.edges measured nd.decl P.slot)).toNat := by
  unfold exactGraph at h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  obtain ⟨nd', hnd', hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 m nd hm
  simp only [hbox] at hnd'
  have hcondFalse : (!exactIds.contains box.id &&
      !(box.role == .group && inp.fixedSizes.any (fun fixed => fixed.1 == box.id))) =
      false := by
    rcases hex with hc | ⟨hgrp, hfix⟩
    · have hcT : exactIds.contains box.id = true := List.contains_iff_mem.mpr hc
      simp only [hcT, Bool.not_true, Bool.false_and]
    · have hrT : (box.role == BoxRole.group) = true := by simp [hgrp]
      obtain ⟨x, hmemF⟩ := hfix
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true := by
        rw [List.any_eq_true]
        exact ⟨(box.id, x), hmemF, beq_self_eq_true _⟩
      simp only [hrT, hany, Bool.true_and, Bool.not_true, Bool.and_false]
  simp only [hcondFalse, Bool.false_eq_true, ↓reduceIte] at hnd'
  cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
  | none =>
    simp only [hfind] at hnd'
    cases hnd'
  | some fixed =>
    simp only [hfind] at hnd'
    split at hnd'
    · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hnd'
      cases hnd'
    · split at hnd'
      · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hnd'
        cases hnd'
      · simp only [pure, Except.pure] at hnd'
        have hred := Except.ok.inj hnd'
        subst hred
        exact ⟨_, hmem, rfl⟩
private theorem XLEMR_mapM_ok_len {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    have he : [] = out := Except.ok.inj h
    subst out
    rfl
  | cons x xs ih =>
    intro out h
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    have he : y :: rest = out := Except.ok.inj h
    subst out
    simp only [List.length_cons, ih rest hr]

/-- Prefixed copy of `sceneExecutionX_lines_len`. -/
private theorem XLEMR_lines_len {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length := XLEMR_mapM_ok_len _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Prefixed copy of `components_mem_bound`: component members index valid
graph nodes. -/
private theorem XLEMR_comp_mem_bound {g : Graph} {comp : List Nat}
    (hmem : comp ∈ components g) {v : Nat} (hv : v ∈ comp) :
    v < g.nodes.length := by
  unfold components at hmem
  dsimp only at hmem
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
  rw [← hr] at hv
  exact List.mem_range.mp (List.mem_filter.mp hv).1

/-- Prefixed copy of `componentCandidate_slot_general`. -/
private theorem XLEMR_cg_slot {g : Graph} {comp : List Nat} {candidate : Nat} :
    (componentCandidate g comp candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl
/-- Prefixed copy of `bind_ok_general`: destructure an `Except.bind`. -/
private theorem XLEMR_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => simp [hx, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Except.bind] using h⟩
/-- Prefixed copy of `orientNode_key` (decl part). -/
private theorem XLEMR_orient_decl (d : Direction) (n : Node) :
    (orientNode d n).decl = n.decl := by
  unfold orientNode
  split <;> rfl

/-- Sized nodes carry their index as decl. -/
private theorem XLEMR_init_decl_idx {P : Params} {lines : List (List Measure.Line)}
    {initial : List Node} (hmap : (lines.zipIdx).mapM
      (fun q => sizedNode P q.2 q.1) = .ok initial)
    {m : Nat} (hm : m < lines.length) :
    ∃ nd, initial[m]? = some nd ∧ nd.decl = m := by
  have hmem : lines.zipIdx[m]? = some (lines[m], m) := by
    simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hm, Option.map_some,
      Nat.zero_add]
  obtain ⟨b, hb, hmemB⟩ := (mapM_getElem? _ _ _ hmap).2 m (lines[m], m) hmem
  refine ⟨b, hmemB, ?_⟩
  unfold sizedNode at hb
  obtain ⟨size, _, hb⟩ := XLEMR_bind_ok hb
  have he := Except.ok.inj hb
  rw [← he]

/-- Sizing-phase loop extent over the measured graph: an executed graph node
stores the exact loop extent of its own loop sizes. Exact-run replay of
`graph_node_loopExtent_general` through `execution.graph0_eq`. -/
private theorem XLEMR_measured_loopExtent {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {m : Nat}
    (hm : m < execution.lines.length)
    {gnode : Node} (hg : execution.graph0.nodes[m]? = some gnode) :
    gnode.loopExtent = (Loops.extent execution.graph0.slot
      (loopSizes execution.graph0.edges execution.measured m
        execution.graph0.slot)).toNat ∧ gnode.decl = m := by
  have hlines : execution.lines.length = inp.boxes.length :=
    XLEMR_lines_len execution
  have hmB : m < inp.boxes.length := by rw [← hlines]; exact hm
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[m]? = some box :=
    ⟨_, List.getElem?_eq_getElem hmB⟩
  have hgE := execution.graph0_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨edges, _, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨metric, hmM, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨labels, hlL, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨nodes, hnodes, hgE⟩ := XLEMR_bind_ok hgE
  have hinitial_mapM : (execution.lines.zipIdx).mapM
      (fun q => sizedNode execution.params q.2 q.1) = .ok initial := hinitial
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial_mapM
  have hprepare := (Except.ok.inj hgE).symm
  let raw : Graph := { nodes := nodes, edges := edges, slot := execution.params.slot }
  change execution.graph0 =
    Compound.prepare _ execution.params.clusterPad _ raw at hprepare
  have hemetric : metric = execution.metric := Except.ok.inj (hmM.symm.trans execution.metric_eq)
  subst hemetric
  have helabels : labels = execution.measured :=
    Except.ok.inj (hlL.symm.trans execution.measured_eq)
  subst helabels
  have hslotG : execution.graph0.slot = execution.params.slot := by
    rw [hprepare]; exact rfl
  have hslotnn : 0 ≤ execution.params.slot := by
    have hvalid := checkedParams_valid execution.checked
    have h1 : 1 ≤ execution.params.slot := hvalid.2.2.1
    omega
  have hwidths : ∀ l ∈ loopSizes edges execution.measured m execution.params.slot,
      0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hextnn : 0 ≤ Loops.extent execution.params.slot
      (loopSizes edges execution.measured m execution.params.slot) := by
    unfold Loops.extent
    have hterm : ∀ q ∈ (loopSizes edges execution.measured m
        execution.params.slot).zipIdx.map
        (fun q => execution.params.slot * ((q.2 : Int) + 2) + q.1.width), 0 ≤ q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨_, hjlen, ha⟩ := List.mem_zipIdx hp
      have hmem : p.1 ∈ loopSizes edges execution.measured m execution.params.slot := by
        have h1 : p.2 <
            (loopSizes edges execution.measured m execution.params.slot).length := by
          omega
        have h2 : (loopSizes edges execution.measured m execution.params.slot)[p.2]? =
            some ((loopSizes edges execution.measured m execution.params.slot)[p.2]) :=
          List.getElem?_eq_getElem h1
        simp only [Nat.sub_zero] at ha
        rw [← ha] at h2
        exact List.mem_of_getElem? h2
      have hslot2 : (0 : Int) ≤ execution.params.slot * ((p.2 : Int) + 2) :=
        Int.mul_nonneg hslotnn (by omega)
      have hwp : 0 ≤ p.1.width := hwidths p.1 hmem
      omega
    have hfold : ∀ (acc : Int), 0 ≤ acc → ∀ (l : List Int),
        (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.foldl (· + ·) acc := by
      intro acc ha l hl
      induction l generalizing acc with
      | nil => exact ha
      | cons a rest ih =>
        simp only [List.foldl]
        exact ih _ (by have hha := hl a (List.mem_cons.mpr (Or.inl rfl)); omega)
          (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
    exact hfold 0 (Int.le_refl _) _ hterm
  obtain ⟨before, _, hbefore⟩ :=
    hinit m (execution.lines[m], m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hm,
        Option.map_some, Nat.zero_add])
  have hbeforeDecl : before.decl = m := by
    obtain ⟨bd, hbd, hbm⟩ := XLEMR_init_decl_idx hinitial_mapM hm
    have heq : bd = before := Option.some.inj (hbd.symm.trans hbefore)
    rw [← heq]
    exact hbm
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed m (orientNode o.direction before, m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have hloop : after.loopExtent =
      (Loops.extent execution.params.slot
        (loopSizes edges execution.measured m execution.params.slot)).toNat := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == box.id) = true
    · obtain ⟨entry, hfindE⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == box.id) = some entry := by
        cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
        | none =>
          obtain ⟨e2, hmF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf e2 hmF) (by rw [hid]; decide)
        | some e2 => exact ⟨e2, rfl⟩
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
        hfixed
      simp [hbox, hfindE, hany] at hstep
      split at hstep
      · cases hstep
      · split at hstep
        · cases hstep
        · have he := Except.ok.inj hstep
          subst after
          rfl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hfindN : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
        List.find?_eq_none.mpr (List.any_eq_false.mp hfixedF)
      by_cases hrole : box.role = .group
      · simp [hbox, hfindN, hrole, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
      · have hroleN : box.role = .node := by
          match h : box.role with
          | .node => rfl
          | .group => exact absurd h hrole
        simp [hbox, hfindN, hroleN, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
  have hafterDecl : after.decl = m := by
    have hstepD := hstep
    dsimp only at hstepD
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstepD
    by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == box.id) = true
    · obtain ⟨entry, hfindE⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == box.id) = some entry := by
        cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
        | none =>
          obtain ⟨e2, hmF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf e2 hmF) (by rw [hid]; decide)
        | some e2 => exact ⟨e2, rfl⟩
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
        hfixed
      simp [hbox, hfindE, hany] at hstepD
      split at hstepD
      · cases hstepD
      · split at hstepD
        · cases hstepD
        · have he := Except.ok.inj hstepD
          subst after
          simp only [XLEMR_orient_decl]
          show before.decl = m
          exact hbeforeDecl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hfindN : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
        List.find?_eq_none.mpr (List.any_eq_false.mp hfixedF)
      by_cases hrole : box.role = .group
      · simp [hbox, hfindN, hrole, hfixedF] at hstepD
        split at hstepD
        · cases hstepD
        · split at hstepD
          · cases hstepD
          · have he := Except.ok.inj hstepD
            subst after
            simp only [XLEMR_orient_decl]
            show before.decl = m
            exact hbeforeDecl
      · have hroleN : box.role = .node := by
          match h : box.role with
          | .node => rfl
          | .group => exact absurd h hrole
        simp [hbox, hfindN, hroleN, hfixedF] at hstepD
        split at hstepD
        · cases hstepD
        · split at hstepD
          · cases hstepD
          · have he := Except.ok.inj hstepD
            subst after
            simp only [XLEMR_orient_decl]
            show before.decl = m
            exact hbeforeDecl
  have hinodes : m < nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hget : nodes[m]'hinodes = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hraw : raw.nodes[m]? = some after := by
    simpa only [raw, List.getElem?_eq_getElem hinodes] using congrArg some hget
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  have hprepEq : execution.graph0 =
      Compound.prepare boxes execution.params.clusterPad titles raw :=
    hprepare
  have hbound : m < boxes.length := by
    simpa only [boxes, List.length_map] using hmB
  have hpe := prepare_loopSizes_preserved boxes execution.params.clusterPad titles raw m
    hbound execution.measured execution.params.slot
  have heg : (Compound.prepare boxes execution.params.clusterPad titles raw).edges =
      execution.graph0.edges := by
    rw [hprepEq]
  rw [heg] at hpe
  have hrawE : raw.edges = edges := rfl
  have hsizeq : loopSizes edges execution.measured m execution.params.slot =
      loopSizes execution.graph0.edges execution.measured m
        execution.graph0.slot := by
    rw [hrawE] at hpe
    rw [← hpe, hslotG]
  have hloopG : after.loopExtent = (Loops.extent execution.graph0.slot
      (loopSizes execution.graph0.edges execution.measured m
        execution.graph0.slot)).toNat := by
    rw [hloop, hsizeq, hslotG]
  have hclose : gnode.loopExtent = after.loopExtent →
      gnode.loopExtent = (Loops.extent execution.graph0.slot
        (loopSizes execution.graph0.edges execution.measured m
          execution.graph0.slot)).toNat := by
    intro hll
    rw [hll, hloopG]
  by_cases hrole : box.role = .group
  · by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes execution.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes execution.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      refine ⟨hclose hloopR, ?_⟩
      rw [h2]
      exact hafterDecl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := Compound.prepare_group_title_record boxes execution.params.clusterPad
        titles raw hinodes hboxM hrole
      have h1 : some gnode =
          (Compound.prepare boxes execution.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = (raw.nodes[m]'hinodes).loopExtent := by
        rw [h2]
      have hRl : (raw.nodes[m]'hinodes).loopExtent = after.loopExtent := by
        simp only [raw, hget]
      refine ⟨hclose (hloopR.trans hRl), ?_⟩
      have hgd : gnode.decl = m := by
        have e1 : gnode.decl = (raw.nodes[m]'hinodes).decl := by rw [h2]
        rw [e1]
        show (nodes[m]'hinodes).decl = m
        rw [hget]
        exact hafterDecl
      exact hgd
  · have hroleN : box.role = .node := by
      match h : box.role with
      | .node => rfl
      | .group => exact absurd h hrole
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes execution.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes execution.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      refine ⟨hclose hloopR, ?_⟩
      rw [h2]
      exact hafterDecl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := prepare_node_record boxes execution.params.clusterPad titles raw hraw
        hboxM hroleN
      have h1 : some gnode =
          (Compound.prepare boxes execution.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      refine ⟨hclose hloopR, ?_⟩
      rw [h2]
      exact hafterDecl
/-- A border-0 component node lives in the original segment: its component
index is below the line count. Appended group bottoms all carry border 2. -/
private theorem XLEMR_comp_mem_lines {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {cg : Graph}
    (hcg : cg = componentCandidate execution.graph comp candidate)
    {t : Nat} (hlt : t < comp.length)
    {nt : Node} (hnt : cg.nodes[t]? = some nt) (hB0 : nt.border = 0) :
    comp.getD t 0 < execution.lines.length := by
  have hlen : cg.nodes.length = comp.length := by
    rw [hcg, componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hmEq : comp.getD t 0 = comp[t] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
  have hmemC : comp.getD t 0 ∈ comp := by
    rw [hmEq]
    exact List.getElem_mem hlt
  have hmG : comp.getD t 0 < execution.graph.nodes.length :=
    XLEMR_comp_mem_bound hcomp hmemC
  have hcc : cg.nodes =
      comp.map fun key => execution.graph.nodes.getD key default := by
    rw [hcg, componentCandidate_nodes]
    rfl
  have hmemT : comp[t]? = some (comp.getD t 0) := by
    rw [hmEq]
    exact List.getElem?_eq_getElem hlt
  have h1 : execution.graph.nodes.getD (comp.getD t 0) default = nt := by
    have h1' : cg.nodes[t]? = some nt := hnt
    rw [hcc] at h1'
    rw [List.getElem?_map, hmemT, Option.map_some] at h1'
    exact Option.some.inj h1'
  obtain ⟨gnode, hgm⟩ : ∃ g,
      execution.graph.nodes[comp.getD t 0]? = some g :=
    ⟨_, List.getElem?_eq_getElem hmG⟩
  have hgnEq : gnode = nt := by
    have e1 : execution.graph.nodes.getD (comp.getD t 0) default = gnode := by
      rw [List.getD_eq_getElem?_getD, hgm]
      rfl
    rw [h1] at e1
    exact e1.symm
  have hgE := execution.graph0_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨edges, _, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨metric, _, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨labels, _, hgE⟩ := XLEMR_bind_ok hgE
  obtain ⟨nodes, hnodes, hgE⟩ := XLEMR_bind_ok hgE
  have hprepare := (Except.ok.inj hgE).symm
  let raw : Graph := { nodes := nodes, edges := edges, slot := execution.params.slot }
  change execution.graph0 =
    Compound.prepare _ execution.params.clusterPad _ raw at hprepare
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  have hprepEq : execution.graph0 =
      Compound.prepare boxes execution.params.clusterPad titles raw :=
    hprepare
  have hlenG0 : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  have hmG0 : comp.getD t 0 < execution.graph0.nodes.length := by omega
  obtain ⟨nd0, hnd0⟩ : ∃ n,
      execution.graph0.nodes[comp.getD t 0]? = some n :=
    ⟨_, List.getElem?_eq_getElem hmG0⟩
  obtain ⟨nd0', hnd0', hb0', _, _⟩ :=
    exactGraph_node_key execution.graph_eq hnd0
  have heq0 : nd0' = gnode := Option.some.inj (hnd0'.symm.trans hgm)
  have hb0nd : nd0.border ≠ 2 := by
    have hzero : nd0.border = 0 := by
      rw [← hb0', heq0, hgnEq]
      exact hB0
    omega
  have hinitial_mapM : (execution.lines.zipIdx).mapM
      (fun q => sizedNode execution.params q.2 q.1) = .ok initial := hinitial
  have hinitLen : initial.length = execution.lines.length := by
    have h := XLEMR_mapM_ok_len _ _ _ hinitial_mapM
    simpa only [List.length_zipIdx] using h
  have hnodesLen : nodes.length = initial.length := by
    have h := XLEMR_mapM_ok_len _ _ _ hnodes
    simpa only [List.length_map, List.length_zipIdx] using h
  have hrawLen : raw.nodes.length = execution.lines.length := by
    show nodes.length = execution.lines.length
    rw [hnodesLen, hinitLen]
  have hnd0' : (Compound.markNodes boxes execution.params.clusterPad titles
      raw.nodes)[comp.getD t 0]? = some nd0 := by
    have h2 : (Compound.prepare boxes execution.params.clusterPad titles
        raw).nodes[comp.getD t 0]? = some nd0 := by
      rw [← hprepEq]
      exact hnd0
    rw [Compound.prepare_nodes] at h2
    exact h2
  refine Classical.byContradiction fun hcon => ?_
  have hbot := Compound.markNodes_getElem?_bottom boxes execution.params.clusterPad
    titles raw.nodes (comp.getD t 0) (by omega) hnd0'
  have hb2 := hbot.1
  omega
/-- `exactGraph` keeps the loop extent of non-exact nodes. -/
private theorem XLEMR_exact_preserved {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {m : Nat} {nd : Node} (hm : g0.nodes[m]? = some nd)
    {box : ModelBox} (hbox : inp.boxes[nd.decl]? = some box)
    (hcond : (!exactIds.contains box.id &&
      !(box.role == .group && inp.fixedSizes.any
        (fun fixed => fixed.1 == box.id))) = true) :
    ∃ nd', g.nodes[m]? = some nd' ∧ nd'.loopExtent = nd.loopExtent := by
  unfold exactGraph at h
  obtain ⟨nodes, hnodes, h⟩ := XLEMR_bind_ok h
  have he := Except.ok.inj h
  subst he
  obtain ⟨nd', hnd', hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 m nd hm
  simp only [hbox] at hnd'
  simp only [hcond, ↓reduceIte] at hnd'
  simp only [pure, Except.pure] at hnd'
  have hred := Except.ok.inj hnd'
  subst hred
  exact ⟨_, hmem, rfl⟩

/-- Owner loop-extent cover: the recorded extent covers the footprint width
in both sizing branches. -/
private theorem XLEMR_cg_node_extent {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {cg : Graph}
    (hcg : cg = componentCandidate execution.graph comp candidate)
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    {t : Nat} (hlt : t < comp.length)
    {nt : Node} (hnt : cg.nodes[t]? = some nt)
    (hB0 : (cg.nodes.getD t default).border = 0)
    {actualT : ProperNode}
    (hcoordT : run.coordinateProper.nodes[t]? = some actualT) :
    (actualT.node.loopExtent : Int) ≥
      (if run.exact.contains t then
        Loops.exactExtent cg.slot (loopSizes cg.edges execution.measured t cg.slot)
      else Loops.extent cg.slot (loopSizes cg.edges execution.measured t cg.slot)) := by
  have hB0nt : nt.border = 0 := by
    have hget : cg.nodes.getD t default = nt := by
      rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    rw [← hget]
    exact hB0
  have hlen : cg.nodes.length = comp.length := by
    rw [hcg, componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hltCG : t < cg.nodes.length := by omega
  have hmEq : comp.getD t 0 = comp[t] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
  have hmemC : comp.getD t 0 ∈ comp := by
    rw [hmEq]
    exact List.getElem_mem hlt
  have hmG : comp.getD t 0 < execution.graph.nodes.length :=
    XLEMR_comp_mem_bound hcomp hmemC
  have hcc : cg.nodes =
      comp.map fun key => execution.graph.nodes.getD key default := by
    rw [hcg, componentCandidate_nodes]
    rfl
  have hmemT : comp[t]? = some (comp.getD t 0) := by
    rw [hmEq]
    exact List.getElem?_eq_getElem hlt
  have hgnode : execution.graph.nodes.getD (comp.getD t 0) default = nt := by
    have h1' : (comp.map fun key =>
        execution.graph.nodes.getD key default)[t]? = some nt := by
      rw [← hcc]
      exact hnt
    rw [List.getElem?_map, hmemT, Option.map_some] at h1'
    exact Option.some.inj h1'
  obtain ⟨gnode, hgm⟩ : ∃ g,
      execution.graph.nodes[comp.getD t 0]? = some g :=
    ⟨_, List.getElem?_eq_getElem hmG⟩
  have hgnEq : gnode = nt := by
    have e1 : execution.graph.nodes.getD (comp.getD t 0) default = gnode := by
      rw [List.getD_eq_getElem?_getD, hgm]
      rfl
    rw [hgnode] at e1
    exact e1.symm
  obtain ⟨actualT', hcoordT', hleT⟩ :=
    XLEMR_actual_loopExtent hrun hnt hB0nt
  have heqA : actualT' = actualT :=
    Option.some.inj (hcoordT'.symm.trans hcoordT)
  have hmlines : comp.getD t 0 < execution.lines.length :=
    XLEMR_comp_mem_lines execution hcomp hcg hlt hnt hB0nt
  have hlenG0 : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  have hmG0 : comp.getD t 0 < execution.graph0.nodes.length := by omega
  obtain ⟨nd0, hnd0⟩ : ∃ n,
      execution.graph0.nodes[comp.getD t 0]? = some n :=
    ⟨_, List.getElem?_eq_getElem hmG0⟩
  obtain ⟨nd0', hnd0', hb0', _, hdecl'⟩ :=
    exactGraph_node_key execution.graph_eq hnd0
  have heq0 : nd0' = gnode := Option.some.inj (hnd0'.symm.trans hgm)
  obtain ⟨hloop0, hdecl0⟩ :=
    XLEMR_measured_loopExtent execution hmlines hnd0
  have hslotG : execution.graph.slot = execution.graph0.slot := by
    have h := execution.graph_eq
    unfold exactGraph at h
    obtain ⟨nodesG, _, h⟩ := XLEMR_bind_ok h
    have he := Except.ok.inj h
    rw [← he]
  have hslot0 : execution.graph0.slot = execution.params.slot := by
    have h := execution.graph0_eq
    unfold measuredGraph at h
    obtain ⟨i0, _, h⟩ := XLEMR_bind_ok h
    obtain ⟨e0, _, h⟩ := XLEMR_bind_ok h
    obtain ⟨m0, _, h⟩ := XLEMR_bind_ok h
    obtain ⟨l0, _, h⟩ := XLEMR_bind_ok h
    obtain ⟨n0, _, h⟩ := XLEMR_bind_ok h
    have he := Except.ok.inj h
    rw [← he]
    rfl
  have hslotCG : cg.slot = execution.graph.slot := by
    rw [hcg]
    exact XLEMR_cg_slot
  have hslotChain : cg.slot = execution.graph0.slot := by
    rw [hslotCG, hslotG]
  have hL := componentCandidate_loopSizes_preserved execution.graph comp
    (components_nodup _ _ hcomp) candidate t hlt execution.measured cg.slot
  rw [← hcg] at hL
  rw [← hmEq, exactGraph_edges execution.graph_eq] at hL
  rw [hslotChain] at hL
  have hslotNN : 0 ≤ cg.slot := componentRunX_slot_nonneg hrun
  have hwidths : ∀ l ∈ loopSizes cg.edges execution.measured t cg.slot,
      0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hntDecl : nt.decl = nd0.decl := by
    rw [← hgnEq, ← heq0]
    exact hdecl'
  have hmemZ : (nt, t) ∈ cg.nodes.zipIdx := by
    have h1 : cg.nodes.zipIdx[t]? = some (nt, t) := by
      simp only [List.getElem?_zipIdx, hnt, Option.map_some, Nat.zero_add]
    exact List.mem_of_getElem? h1
  rw [← heqA, hleT]
  by_cases hexT : run.exact.contains t = true
  · have hmemDecl : (exactDecls exactIds inp).contains nt.decl = true := by
      have heq := XLEMR_run_exact_eq hrun
      rw [heq] at hexT
      obtain ⟨_, hdeclT⟩ := XLEMR_exact_bound hexT
      have hget : cg.nodes.getD t default = nt := by
        rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
      rw [hget] at hdeclT
      exact hdeclT
    obtain ⟨box, hbox, hex⟩ := XLEMR_exactDecl_box hmemDecl
    rw [hntDecl] at hbox
    obtain ⟨nd0e, hnd0e, hleE⟩ :=
      XLEMR_exactGraph_loopExtent execution.graph_eq hnd0 hbox hex
    have heqE : nd0e = nt := by
      have e1 : nd0e = gnode := Option.some.inj (hnd0e.symm.trans hgm)
      rw [e1]
      exact hgnEq
    have hmax0 : ∀ (acc : Int), 0 ≤ acc → ∀ (ss : List LoopLabel),
        0 ≤ ss.foldl (fun w l => max w l.width) acc := by
      intro acc ha ss
      induction ss generalizing acc with
      | nil => exact ha
      | cons s rest ih =>
        simp only [List.foldl]
        exact ih _ (Int.le_trans ha (Int.le_max_left _ _))
    have hEW : 0 ≤ Loops.exactExtent cg.slot
        (loopSizes cg.edges execution.measured t cg.slot) := by
      unfold Loops.exactExtent
      dsimp only
      split
      · exact hmax0 0 (Int.le_refl _) _
      · have hwide : 0 ≤ (loopSizes cg.edges execution.measured t
            cg.slot).foldl (fun w l => max w l.width) 0 :=
          hmax0 0 (Int.le_refl _) _
        have hnn : 0 ≤ cg.slot *
            (2 * (((loopSizes cg.edges execution.measured t
              cg.slot).length : Int)) + 1) :=
          Int.mul_nonneg hslotNN (by omega)
        omega
    have hEq : Loops.exactExtent execution.params.slot
        (loopSizes execution.graph0.edges execution.measured nd0.decl
          execution.params.slot) =
        Loops.exactExtent cg.slot
          (loopSizes cg.edges execution.measured t cg.slot) := by
      rw [hdecl0, ← hslot0, hslotChain, hL]
    simp only [hexT, ↓reduceIte]
    have hntE : nt = nd0e := heqE.symm
    rw [hntE, hleE, hEq, Int.toNat_of_nonneg hEW]
    exact Int.le_refl _
  · have hcon : run.exact.contains t = false := Bool.eq_false_iff.mpr hexT
    have hltB : comp.getD t 0 < inp.boxes.length := by
      rw [← XLEMR_lines_len execution]
      exact hmlines
    obtain ⟨boxm, hboxm⟩ : ∃ box,
        inp.boxes[comp.getD t 0]? = some box :=
      ⟨_, List.getElem?_eq_getElem hltB⟩
    have hmemB : (boxm, comp.getD t 0) ∈ inp.boxes.zipIdx := by
      have h1 : inp.boxes.zipIdx[comp.getD t 0]? = some (boxm, comp.getD t 0) := by
        simp only [List.getElem?_zipIdx, hboxm, Option.map_some, Nat.zero_add]
      exact List.mem_of_getElem? h1
    have hrunMem : (boxm.id ∈ exactIds ∨
        (boxm.role = BoxRole.group ∧
          ∃ x, (boxm.id, x) ∈ inp.fixedSizes)) →
        run.exact.contains t = true := by
      intro hexm
      have heq := XLEMR_run_exact_eq hrun
      rw [heq, List.contains_iff_mem]
      apply List.mem_filterMap.mpr
      refine ⟨(nt, t), hmemZ, ?_⟩
      have hdm : nt.decl = comp.getD t 0 := by
        rw [← hgnEq, ← heq0, hdecl']
        exact hdecl0
      have hmemD : (exactDecls exactIds inp).contains (comp.getD t 0) = true := by
        rw [List.contains_iff_mem]
        apply List.mem_filterMap.mpr
        refine ⟨(boxm, comp.getD t 0), hmemB, ?_⟩
        dsimp only
        rcases hexm with hc | ⟨hgrp, hfix⟩
        · have hcT : exactIds.contains boxm.id = true :=
            List.contains_iff_mem.mpr hc
          simp only [hcT, Bool.true_or, ↓reduceIte]
        · have hrT : (boxm.role == BoxRole.group) = true := by simp [hgrp]
          obtain ⟨x, hmemF⟩ := hfix
          have hany : inp.fixedSizes.any
              (fun fixed => fixed.1 == boxm.id) = true := by
            rw [List.any_eq_true]
            exact ⟨(boxm.id, x), hmemF, beq_self_eq_true _⟩
          simp only [hrT, hany, Bool.true_and, Bool.or_true, ↓reduceIte]
      rw [hdm, hmemD]
      rfl
    have hcond : ((!exactIds.contains boxm.id &&
        !(boxm.role == .group && inp.fixedSizes.any
          (fun fixed => fixed.1 == boxm.id)))) = true := by
      cases hc1 : exactIds.contains boxm.id with
      | true =>
        have hcT := hrunMem (Or.inl (List.contains_iff_mem.mp hc1))
        rw [hcT] at hcon
        exact Bool.noConfusion hcon
      | false =>
        cases hc2 : ((boxm.role == .group && inp.fixedSizes.any
            (fun fixed => fixed.1 == boxm.id))) with
        | true =>
          have hgrp : boxm.role = BoxRole.group := by
            have h := (Bool.and_eq_true_iff.mp hc2).1
            simpa using h
          have hfix : ∃ x, (boxm.id, x) ∈ inp.fixedSizes := by
            have h := (Bool.and_eq_true_iff.mp hc2).2
            rw [List.any_eq_true] at h
            obtain ⟨e, hmemE, heqE⟩ := h
            have hid : e.1 = boxm.id := beq_iff_eq.mp heqE
            exact ⟨e.2, by rw [← hid]; exact hmemE⟩
          have hcT := hrunMem (Or.inr ⟨hgrp, hfix⟩)
          rw [hcT] at hcon
          exact Bool.noConfusion hcon
        | false =>
          simp only [Bool.not_false, Bool.true_and]
    have hbox0 : inp.boxes[nd0.decl]? = some boxm := by
      rw [hdecl0]
      exact hboxm
    obtain ⟨nd0p, hnd0p, hleP⟩ :=
      XLEMR_exact_preserved execution.graph_eq hnd0 hbox0 hcond
    have heqP : nd0p = nt := by
      have e1 : nd0p = gnode := Option.some.inj (hnd0p.symm.trans hgm)
      rw [e1]
      exact hgnEq
    have hslotnn : 0 ≤ execution.params.slot := by
      have hvalid := checkedParams_valid execution.checked
      have h1 : 1 ≤ execution.params.slot := hvalid.2.2.1
      omega
    have hwidths0 : ∀ l ∈ loopSizes execution.graph0.edges execution.measured
        (comp.getD t 0) execution.graph0.slot, 0 ≤ l.width := by
      intro l hl
      obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
      rw [stackSize_width_eq]
      exact Labels.stackWidth_nonneg _
    have hextnn : 0 ≤ Loops.extent execution.graph0.slot
        (loopSizes execution.graph0.edges execution.measured (comp.getD t 0)
          execution.graph0.slot) := by
      unfold Loops.extent
      have hterm : ∀ q ∈ (loopSizes execution.graph0.edges execution.measured
          (comp.getD t 0) execution.graph0.slot).zipIdx.map
          (fun q => execution.graph0.slot * ((q.2 : Int) + 2) + q.1.width),
          0 ≤ q := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        obtain ⟨_, hjlen, ha⟩ := List.mem_zipIdx hp
        have hmem : p.1 ∈ loopSizes execution.graph0.edges execution.measured
            (comp.getD t 0) execution.graph0.slot := by
          have h1 : p.2 <
              (loopSizes execution.graph0.edges execution.measured
                (comp.getD t 0) execution.graph0.slot).length := by
            omega
          have h2 : (loopSizes execution.graph0.edges execution.measured
              (comp.getD t 0) execution.graph0.slot)[p.2]? =
              some ((loopSizes execution.graph0.edges execution.measured
                (comp.getD t 0) execution.graph0.slot)[p.2]) :=
            List.getElem?_eq_getElem h1
          simp only [Nat.sub_zero] at ha
          rw [← ha] at h2
          exact List.mem_of_getElem? h2
        have hslot2 : (0 : Int) ≤ execution.graph0.slot * ((p.2 : Int) + 2) := by
          have hnn : (0 : Int) ≤ execution.graph0.slot := by
            rw [hslot0]
            exact hslotnn
          exact Int.mul_nonneg hnn (by omega)
        have hwp : 0 ≤ p.1.width := hwidths0 p.1 hmem
        omega
      have hfold : ∀ (acc : Int), 0 ≤ acc → ∀ (l : List Int),
          (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.foldl (· + ·) acc := by
        intro acc ha l hl
        induction l generalizing acc with
        | nil => exact ha
        | cons a rest ih =>
          simp only [List.foldl]
          exact ih _ (by have hha := hl a (List.mem_cons.mpr (Or.inl rfl)); omega)
            (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
      exact hfold 0 (Int.le_refl _) _ hterm
    have hEq2 : Loops.extent execution.graph0.slot
        (loopSizes execution.graph0.edges execution.measured (comp.getD t 0)
          execution.graph0.slot) =
        Loops.extent cg.slot
          (loopSizes cg.edges execution.measured t cg.slot) := by
      rw [hslotChain, hL]
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    have hextnnCg : 0 ≤ Loops.extent cg.slot
        (loopSizes cg.edges execution.measured t cg.slot) := by
      rw [← hEq2]
      exact hextnn
    have e1 : (nt.loopExtent : Int) =
        ((Loops.extent cg.slot (loopSizes cg.edges execution.measured t
          cg.slot)).toNat : Int) := by
      rw [← heqP, hleP, hloop0, hEq2]
    rw [e1, Int.toNat_of_nonneg hextnnCg]
    exact Int.le_refl _
/-- Push an application inside a boolean conditional. -/
private theorem XLEMR_ifpush (c : Bool) (F G : Int → List LoopLabel → Int)
    (x : Int) (y : List LoopLabel) :
    ((if c then F else G) x y) = (if c then F x y else G x y) := by
  cases c <;> simp

/-- Right gap: the footprint of a plain loop owner ends left of every
same-layer box right of it. The owner's coordinate width covers the loop
extent; adjacent separation plus the tail give the gap. The ownTitleAnchor
case is impossible by computation on border-0 endpoints, so no title
uniqueness is needed. -/
private theorem XLEMR_right_gap {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {cg : Graph}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    {t v : Nat}
    {actualT actualV : ProperNode}
    (hcoordT : run.coordinateProper.nodes[t]? = some actualT)
    (hcoordV : run.coordinateProper.nodes[v]? = some actualV)
    (hb0T : actualT.node.border = 0)
    (hpropT : run.proper.nodes[t]? = some actualT)
    (hpropV : run.proper.nodes[v]? = some actualV)
    (hxsT : run.xs.getD t 0 = run.coordinateXs.getD t 0)
    (hxsV : run.xs.getD v 0 = run.coordinateXs.getD v 0)
    (hfp : (loopFootprintExt cg run execution.measured t).x =
      (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w)
    (hEv : (actualT.node.loopExtent : Int) ≥
      (if run.exact.contains t then
        Loops.exactExtent cg.slot (loopSizes cg.edges execution.measured t cg.slot)
      else Loops.extent cg.slot (loopSizes cg.edges execution.measured t cg.slot)))
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {pu pv : Nat} (hpu : layer[pu]? = some t) (hpv : layer[pv]? = some v)
    (hlt : pu < pv) :
    (loopFootprintExt cg run execution.measured t).x +
      (loopFootprintExt cg run execution.measured t).w ≤
      (RouteImpl.boxRect run.proper run.xs run.ys v).x := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hng, hcp, hr, hsizes, _⟩ :=
    CoordsImpl.crossCoordsClusterWith_spec hcross
  have hltLen : pu + 1 < layer.length := by
    have hjv := (List.getElem?_eq_some_iff.mp hpv).1
    omega
  obtain ⟨c, hmc⟩ : ∃ c, layer[pu + 1]? = some c :=
    ⟨_, List.getElem?_eq_getElem hltLen⟩
  have hcLt : c < run.coordinateProper.nodes.length :=
    CoordsImpl.layers_mem_lt hr hlayer hmc
  obtain ⟨nc, hcoordC⟩ : ∃ nc, run.coordinateProper.nodes[c]? = some nc :=
    ⟨_, List.getElem?_eq_getElem hcLt⟩
  have hadj := CoordsImpl.cluster_balance_separated hcross layer hlayer pu t c
    hpu hmc
  have htf : CoordsImpl.ownTitleAnchor run.coordinateProper t c = false := by
    unfold CoordsImpl.ownTitleAnchor
    simp only [hcoordT, hcoordC]
    simp [hb0T]
  have hg := CoordsImpl.clusterGap_ge_min (ng := execution.params.nodeGap)
    (cp := execution.params.clusterPad) _ _ _ htf
  have hWtn : CoordsImpl.nodeW run.coordinateProper t =
      actualT.node.w + 2 * (actualT.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hcoordT]
  have hWcn : CoordsImpl.nodeW run.coordinateProper c =
      nc.node.w + 2 * (nc.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hcoordC]
  have hWvn : CoordsImpl.nodeW run.coordinateProper v =
      actualV.node.w + 2 * (actualV.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hcoordV]
  have hwtP : RouteImpl.nodeW run.proper t = actualT.node.w := by
    simp only [RouteImpl.nodeW, hpropT]
  have hwvP : RouteImpl.nodeW run.proper v = actualV.node.w := by
    simp only [RouteImpl.nodeW, hpropV]
  have hfpW : (loopFootprintExt cg run execution.measured t).w =
      (if run.exact.contains t then
        Loops.exactExtent cg.slot (loopSizes cg.edges execution.measured t cg.slot)
      else Loops.extent cg.slot
        (loopSizes cg.edges execution.measured t cg.slot)) := by
    unfold loopFootprintExt
    simp only [XLEMR_ifpush]
  have hwcnn : 0 ≤ nc.node.w :=
    (sizesNonneg_lookup hsizes c nc hcoordC).1
  have hLtnn : (0 : Int) ≤ (actualT.node.loopExtent : Int) :=
    Int.natCast_nonneg _
  have hLvnn : (0 : Int) ≤ (actualV.node.loopExtent : Int) :=
    Int.natCast_nonneg _
  have hLcnn : (0 : Int) ≤ (nc.node.loopExtent : Int) :=
    Int.natCast_nonneg _
  have hgap1 : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by
    omega
  have eT : (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w =
      run.xs.getD t 0 - Int.fdiv (RouteImpl.nodeW run.proper t) 2 +
        RouteImpl.nodeW run.proper t := rfl
  have eV : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
      run.xs.getD v 0 - Int.fdiv (RouteImpl.nodeW run.proper v) 2 := rfl
  by_cases heq : pu + 1 = pv
  · subst heq
    have hcb : c = v := Option.some.inj (hmc.symm.trans hpv)
    rw [hcb] at hg
    have hadjV : CoordsImpl.clusterSep execution.params.nodeGap
        execution.params.clusterPad run.coordinateProper t v ≤
        run.coordinateXs.getD v 0 - run.coordinateXs.getD t 0 := by
      rw [← hcb]
      exact hadj
    rw [hfp, eT, eV, hxsT, hxsV, hwtP, hwvP, hfpW]
    unfold CoordsImpl.clusterSep CoordsImpl.coordSep at hadjV
    simp only [hWtn, hWvn] at hadjV
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
      at hadjV ⊢
    omega
  · have hlt2 : pu + 1 < pv := by omega
    have htail := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayer
      (pu + 1) pv c v (by omega) hmc hpv
    rw [hfp, eT, eV, hxsT, hxsV, hwtP, hwvP, hfpW]
    unfold CoordsImpl.clusterSep CoordsImpl.coordSep at hadj
    simp only [hWtn, hWcn] at hadj
    unfold CoordsImpl.coordSep at htail
    simp only [hWcn, hWvn] at htail
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
      at hadj htail ⊢
    omega
/-- Plain right miss, proved for original plain later nodes. The single
narrower residual `XLEM_PlainRightNonPlain` covers a later node that is not
an original plain node. -/
theorem XLEM_plainRightMiss_holds (exactIds : List String)
    (hNonPlain : XLEM_PlainRightNonPlain exactIds) :
    XLEM_PlainRightMiss exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hB0
    layer hlayer pu pv hpu hpv hlt
  by_cases hOrig : ∃ nv, cg.nodes[v]? = some nv ∧ nv.border = 0
  · obtain ⟨nv, hnv, hbv⟩ := hOrig
    subst hcg
    have hbd := sceneExecutionX_edges_bounded execution
    have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
      candidate hcomp hbd (List.mem_of_getElem? hk)
    obtain ⟨nt, hnt⟩ : ∃ nt,
        (componentCandidate execution.graph comp candidate).nodes[e.tail]? =
          some nt :=
      ⟨_, List.getElem?_eq_getElem hbnd.1⟩
    have hnb : nt.border = 0 := by
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD
          e.tail default = nt := by
        rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
      rw [← hget]
      exact hB0
    have htP : e.tail < run.proper.nodes.length :=
      componentRunX_original_nodes_covered hrun e.tail hbnd.1
    have hne2 : ((componentCandidate execution.graph comp candidate).nodes.getD
        e.tail default).border ≠ -2 := by
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD
          e.tail default = nt := by
        rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
      rw [hget]
      omega
    have hFrBox := plain_frame_eq_boxRect default _ run e.tail htP hne2
    obtain ⟨actualT, hcoordT, hpropT, hb0T, _, _, hxsT⟩ :=
      XLEMR_original_plain_record hrun hnt hnb
    obtain ⟨actualV, hcoordV, hpropV, _, _, _, hxsV⟩ :=
      XLEMR_original_plain_record hrun hnv hbv
    have hlen : (componentCandidate execution.graph comp candidate).nodes.length =
        comp.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    have hltC : e.tail < comp.length := by omega
    have hEv := XLEMR_cg_node_extent execution hcomp rfl hrun hltC hnt hB0
      hcoordT
    have hfp := XLEMR_fp_of_frame (labels := execution.measured) hFrBox
    have hgap := XLEMR_right_gap execution hrun hcoordT hcoordV hb0T hpropT
      hpropV hxsT hxsV hfp hEv hlayer hpu hpv hlt
    exact XLEMR_rect_miss_right hgap
  · exact hNonPlain inp o res execution comp candidate run orderOptions cg k e v
      hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hB0 hOrig hlayer
      hpu hpv hlt
/-- Nonstandard-owner case, reduced to the rank and same-rank parts: the
rank split needs no owner-kind premise, and the same-rank pieces cover
border-0 owners (right, left, self) and group owners directly. No new
residual. -/
theorem X_loopEnvOtherOwner_of_parts (exactIds : List String)
    (hOtherRank : XLEM_OtherRankMiss exactIds)
    (hRight : XLEM_PlainRightMiss exactIds)
    (hLeft : XLEM_LeftMiss exactIds)
    (hGrp : XLEM_GroupOwnerMiss exactIds) :
    X_loopEnvOtherOwner exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ _hdisj
  have hrunGen := hrun
  rw [componentRunX_eq_gen] at hrunGen
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hroute, _, _, _, _, _, _,
      hexact⟩ :=
    componentRunGen_spec hrunGen
  obtain ⟨_, _, _, hcov4, _⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  have hbd := sceneExecutionX_edges_bounded execution
  have hk' : (componentCandidate execution.graph comp candidate).edges[k]? =
      some e := by
    rw [← hcg]
    exact hk
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd (List.mem_of_getElem? hk')
  have hltCG : e.tail < cg.nodes.length := by
    rw [hcg]
    exact hbnd.1
  have htP : e.tail < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun e.tail hltCG
  obtain ⟨lt, hly_t, htin_t, _⟩ := hcov4 (e.tail) htP
  obtain ⟨lv, hly_v, hvin_v, _⟩ := hcov4 v hv
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hproxy).2.1
  by_cases heq : (rk run.proper.rank e.tail).toNat =
      (rk run.proper.rank v).toNat
  · have hly_v' : run.layers[(rk run.proper.rank e.tail).toNat]? = some lv := by
      rw [heq]
      exact hly_v
    have hlveq : lv = lt := Option.some.inj (hly_v'.symm.trans hly_t)
    rw [hlveq] at hvin_v
    have hmem : lt ∈ run.layers := List.mem_of_getElem? hly_t
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp htin_t
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvin_v
    by_cases hB0 : (cg.nodes.getD e.tail default).border = 0
    · by_cases hgt : pv < pu
      · exact hLeft inp o res execution comp candidate run orderOptions cg k e
          v hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hB0 hmem hpu hpv
          hgt
      · by_cases hlt2 : pu < pv
        · exact hRight inp o res execution comp candidate run orderOptions cg k
            e v hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hB0 hmem hpu
            hpv hlt2
        · have heq2 : pu = pv := by omega
          subst heq2
          exact XLEM_self_holds exactIds inp o res execution comp candidate run
            orderOptions cg k e v hcomp hcg hrun hk hloop hv hreal hscope₀
            hscope₁ hB0 hmem hpu hpv
    · exact hGrp inp o res execution comp candidate run orderOptions cg k e v
        hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hB0 hmem hpu hpv
  · have hne' : (rk run.coordinateProper.rank v).toNat ≠
        (rk run.coordinateProper.rank e.tail).toNat := by
      rw [← hrankEq]
      exact Ne.symm heq
    exact hOtherRank inp o res execution comp candidate run orderOptions cg k e
      v hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hne'
end PipelineImpl
end Layered
end Elegant
