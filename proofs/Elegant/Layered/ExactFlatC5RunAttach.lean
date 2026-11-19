import Elegant.Layered.ExactFlatC5ChosenPart
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.GroupEndpointC5
import Elegant.Layered.GroupRouteAttachment

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact run-level port attachment (`X_RunAttach`).

Replays `componentRun_group_route_attachment_of_facts` (`GroupRouteAttachment.lean`)
over `componentRunX`: the exact `GroupTopEndpointData` chain (measured-origin
transfer, coordinate record, proxy interval, rank alignment, reserve-shifted
band facts, frame facts) and the port-attachment assembly via
`route_endpoints_on_ports` on the exact run plus the exact endpoint data.
Rank-axis values (`ys`, `top`) go through the reserve stage with the
`ExactFlatC2` band lemmas. -/

/-- Bind decomposition for `Except` pipelines. -/
private theorem Xra_bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A `border = -2` graph node index is in bounds and its `getD` lookup is a
real `getElem?` lookup. -/
private theorem Xra_group_top_index {cg : Graph} {v : Nat}
    (hcb : (cg.nodes.getD v default).border = -2) :
    v < cg.nodes.length ∧ cg.nodes[v]? = some (cg.nodes.getD v default) := by
  by_cases hlt : v < cg.nodes.length
  · have hg : cg.nodes[v]? = some (cg.nodes.getD v default) := by
      rw [List.getD_eq_getElem?_getD]
      simp [List.getElem?_eq_getElem hlt]
    exact ⟨hlt, hg⟩
  · exfalso
    have hget : cg.nodes[v]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_none] at hcb
    have hz : (default : Node).border = 0 := rfl
    rw [hz] at hcb
    omega

/-- The exact candidate `-2` node ends its cluster path in its declaration. -/
private theorem Xra_group_top_decl_path {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨box, hbox, hpath⟩ := X_cg_group_box h0 h hnode hgroup
  exact ⟨by rw [hpath]; simp, by rw [hpath]; simp⟩

/-- The coordinate-graph record of an exact `-2` graph node. -/
private theorem Xra_group_top_coordinate_record {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = -2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact)
    (source := labeled) hrec (Or.inl hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · have h1 : (titleF ⟨nd, false, none, false⟩).node.h = 0 :=
      (titleF_keys _).2.2.2 (Or.inl hgroup)
    have h2 : (clearF (titleF ⟨nd, false, none, false⟩)).node.h =
        (titleF ⟨nd, false, none, false⟩).node.h := (clearF_keys _).2.2.2
    rw [h2]; exact h1

/-- Exact proxy interval over `componentRunX`. -/
private theorem Xra_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
      run.proper.nodes[index]? =
        some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf run.proper run.xs index = span.lo ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = q0.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

/-- The executed record of an exact `-2` top proxy keeps the coordinate
record's cluster path. -/
private theorem Xra_proper_clusterPath {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath := by
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    Xra_proxy_interval hrun hcoord (Or.inl hb)
  exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

/-- Exact sizing preserves node count. -/
private theorem Xra_sizeProperPortsX_length (P : Params) (exact : List Nat)
    (source : Proper) :
    (sizeProperPortsX P exact source).nodes.length = source.nodes.length := by
  simp [sizeProperPortsX]

/-- Exact original nodes are covered. -/
private theorem Xra_original_nodes_covered {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ i, i < cg.nodes.length → i < run.proper.nodes.length := by
  obtain ⟨ranks, p0, labeled, q, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have hnlen := normalize_nodes_length_le hn
  have hllen : p0.nodes.length ≤ labeled.nodes.length := by
    by_cases hle : p0.nodes.length ≤ labeled.nodes.length
    · exact hle
    · have hi : labeled.nodes.length < p0.nodes.length := by omega
      have hmap := (Labels.addLabelNodes_metadata hl).2.2.2 labeled.nodes.length
      have hget : p0.nodes[labeled.nodes.length]? =
          some p0.nodes[labeled.nodes.length] := by simp [hi]
      simp [hget] at hmap
  let titled := titleReservations (sizeProperPortsX P exact labeled)
  obtain ⟨_, _, extra, hextra, _⟩ :=
    OrderImpl.addClusterBorders_metadata titled P.clusterBorderW
  have hclen : labeled.nodes.length ≤ run.coordinateProper.nodes.length := by
    rw [← hcoord]
    unfold coordinateGraphX materializeDummyPaths clearProxyExtents
    simp only [List.length_map]
    rw [hextra]
    dsimp only [titled, titleReservations]
    simp only [List.length_zipIdx, List.length_map, List.length_append,
      Xra_sizeProperPortsX_length]
    omega
  have hplen := (proxyWidths_rel hproxy).2.2.1
  intro i hi
  rw [← hdrop]
  change i < q.nodes.length
  omega

/-- Exact pre-reserve coordinates: unfold one `componentRunX` to expose the
rank-axis output, the proxy `ys`, and the `reserveExactRanks` equation. -/
private theorem Xra_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (y_pre top_pre ys_pre : List Int),
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
      proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
      reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
        .ok (run.ys, run.top) ∧
      run.coordinateYs = y_pre := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := Xra_bind_ok h
  obtain ⟨p0, hp0, h⟩ := Xra_bind_ok h
  obtain ⟨q, hq, h⟩ := Xra_bind_ok h
  obtain ⟨ord, hord, h⟩ := Xra_bind_ok h
  obtain ⟨xs, hxs, h⟩ := Xra_bind_ok h
  obtain ⟨routed, hprojection, h⟩ := Xra_bind_ok h
  obtain ⟨lanes, hr, h⟩ := Xra_bind_ok h
  obtain ⟨yt, hy, h⟩ := Xra_bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := Xra_bind_ok h
  obtain ⟨routes, hroutes, h⟩ := Xra_bind_ok h
  have he := Except.ok.inj h
  subst he
  cases yt with
  | mk y top =>
    exact ⟨y, top, _, hy, rfl, hres, rfl⟩

/-- The pre-reserve routed `ys` of an exact group top proxy equals its layer
top. Plumbing half of the exact C5 group-endpoint fact, before the reserve
stage. -/
private theorem Xra_proxy_ys_eq_top_pre {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {y_pre top_pre ys_pre : List Int}
    (hry : rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre))
    (hyspre : proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length) :
    ys_pre.getD v 0 = top_pre.getD (rk run.coordinateProper.rank v).toNat 0 := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hlabeledNode : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ :=
    hrecords v nd hnode
  have hcoordNode : run.coordinateProper.nodes[v]? =
      some (clearF (titleF ⟨nd, false, none, false⟩)) := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (P := P) (exact := exact)
      (source := labeled) hlabeledNode (Or.inl hborder) rfl
  have hbCoord : (run.coordinateProper.nodes.getD v default).node.border = -2 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : run.coordinateProper.nodes[v]? with
    | none => simp [h] at hcoordNode
    | some n =>
      rw [h] at hcoordNode
      have heq : n = clearF (titleF ⟨nd, false, none, false⟩) := Option.some.inj hcoordNode
      have hb1 : (titleF ⟨nd, false, none, false⟩).node.border = -2 := by
        have t1 : (titleF ⟨nd, false, none, false⟩).node.border = nd.border :=
          (titleF_keys _).2.1
        rw [t1, hborder]
      have hb2 : (clearF (titleF ⟨nd, false, none, false⟩)).node.border =
          (titleF ⟨nd, false, none, false⟩).node.border :=
        (clearF_keys _).2.1
      rw [heq]
      show (clearF (titleF ⟨nd, false, none, false⟩)).node.border = -2
      rw [hb2, hb1]
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_, _, hproperLen, _, hrecPW, _⟩ := proxyWidths_rel hproxy
  obtain ⟨nd', hnd'get, _, hnd'border, _⟩ :=
    hrecPW v _ hcoordNode
  have hvProper : v < run.proper.nodes.length := Xra_original_nodes_covered hrun v hvcg
  have hproperLenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]
    exact hproperLen
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hyvv := (CoordsImpl.rankCoordsWith_spec hry).2.2.2.2.2.2
  have hylen : y_pre.length = run.coordinateProper.nodes.length := by
    rw [hyvv, List.length_map, List.length_range]
  have hvY : v < y_pre.length := by omega
  have hb2eq : ((run.coordinateProper.nodes.getD v default).node.border == -2) = true := by
    simpa only [beq_iff_eq] using hbCoord
  have hndG : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes.getD v default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvC]
  have hpy := proxyYs_getD run.coordinateProper run.layers top_pre y_pre
    (v := v) (nd := run.coordinateProper.nodes.getD v default) hndG hvY
  rw [← hyspre, hpy]
  split
  · rfl
  · rename_i hcond
    exact absurd hb2eq hcond

/-- Reserve-stage shift equations: `reserveExactRanks` adds the same
per-rank prefix-sum shift to `ys` and `top`. -/
private theorem Xra_reserve_shift {P : Params} {exactIds : List String} {inp : Input}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {y_pre top_pre ys_pre : List Int}
    (_hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    (_hry : rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre))
    (hreserve : reserveExactRanks cg (exactDecls exactIds inp) labels run.coordinateProper
      run.layers ys_pre top_pre = .ok (run.ys, run.top)) :
    (∀ r, r < top_pre.length →
      run.top.getD r 0 = top_pre.getD r 0 +
        ((cg.nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes cg.edges labels q.2 cg.slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0) ∧
    (∀ j, j < ys_pre.length →
      run.ys.getD j 0 = ys_pre.getD j 0 +
        ((cg.nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes cg.edges labels q.2 cg.slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD
          ((run.coordinateProper.rank.getD j 0).toNat) 0) := by
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htopM, h1⟩ := Xra_bind_ok hreserve
  obtain ⟨ysNew, hysM, h2⟩ := Xra_bind_ok h1
  have hpair := Except.ok.inj h2
  have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
  have hysNew_eq : ysNew = run.ys := congrArg Prod.fst hpair
  rw [htopNew_eq] at htopM
  rw [hysNew_eq] at hysM
  constructor
  · intro r hr
    have hrZ : r < (top_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hr
    have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
      have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
    obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
    have hbeq : b = top_pre[r] +
        ((cg.nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes cg.edges labels q.2 cg.slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 :=
      Measure.checkedI32_ok hb
    have e3 : top_pre.getD r 0 = top_pre[r] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
      rfl
    have e4 : run.top.getD r 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq
  · intro j hj
    have hjZ : j < (ys_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hj
    have hzin : (ys_pre.zipIdx)[j]? = some (ys_pre[j], j) := by
      have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ hysM
    obtain ⟨b, hb, hbr⟩ := hidx j _ hzin
    have hbeq : b = ys_pre[j] +
        ((cg.nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes cg.edges labels q.2 cg.slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD
          ((run.coordinateProper.rank.getD j 0).toNat) 0 :=
      Measure.checkedI32_ok hb
    have e3 : ys_pre.getD j 0 = ys_pre[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    have e4 : run.ys.getD j 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq

/-- The routed `ys` of an exact group top proxy equals its layer top,
through the reserve stage. -/
private theorem Xra_proxy_ys_eq_top {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length) :
    run.ys.getD v 0 = run.top.getD (rk run.proper.rank v).toNat 0 := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := Xra_run_pre hrun
  have hpre := Xra_proxy_ys_eq_top_pre h0 h hcomp hrun hry hyspre hnode hborder hvcg
  have hshifts := Xra_reserve_shift hrun hry hreserve
  have hysLen : ys_pre.length = run.coordinateProper.nodes.length := by
    rw [← hyspre]
    unfold proxyYs
    rw [List.length_map, List.length_zipIdx]
    exact (CoordsImpl.rankCoordsWith_length hry).1
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  have hvProper : v < run.proper.nodes.length := Xra_original_nodes_covered hrun v hvcg
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hr, _, _⟩ := componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]
    exact (proxyWidths_rel hproxy).2.2.1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hvY : v < ys_pre.length := by omega
  have hrkEq : rk run.proper.rank v = rk run.coordinateProper.rank v :=
    X_proper_rank_eq_local hrun v
  have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1).2.2.2.1
  obtain ⟨lv, hly, hin, hri0⟩ := hcov v hvProper
  have hrT : (rk run.proper.rank v).toNat < top_pre.length := by
    have hlt : (rk run.proper.rank v).toNat < run.layers.length :=
      (List.getElem?_eq_some_iff.mp hly).1
    omega
  have eys := hshifts.2 v hvY
  have etop := hshifts.1 (rk run.proper.rank v).toNat hrT
  have hrkGetD : run.proper.rank.getD v 0 = run.coordinateProper.rank.getD v 0 := hrkEq
  have hIdx : (run.coordinateProper.rank.getD v 0).toNat =
      (rk run.proper.rank v).toNat := congrArg Int.toNat hrkGetD.symm
  rw [hIdx] at eys
  rw [← hrkEq] at hpre
  omega

/-- Every exact executed node is routed at or above the band top of a group
top proxy's band, as soon as its executed rank is at least the proxy's. -/
private theorem Xra_executed_ys_ge_top_band {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hrk : rk run.proper.rank v ≤ rk run.proper.rank i) :
    run.ys.getD v 0 ≤ run.ys.getD i 0 := by
  have hbands := X_ReserveBands_holds exactIds hrun
  obtain ⟨hinBand, hdisjBands⟩ := hbands
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hordW, hx, hproxy, hdrop, hr, hroute,
    hroutes⟩ := componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]
    exact (proxyWidths_rel hproxy).2.2.1
  have hvProper : v < run.proper.nodes.length := Xra_original_nodes_covered hrun v hvcg
  have hiC : i < run.coordinateProper.nodes.length := by omega
  have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1).2.2.2.1
  obtain ⟨lv, hlyv, hinv, hrk0v⟩ := hcov v hvProper
  obtain ⟨li, hlyi, hini, hrk0i⟩ := hcov i hi
  have hysv : run.ys.getD v 0 = run.top.getD (rk run.proper.rank v).toNat 0 :=
    Xra_proxy_ys_eq_top h0 h hcomp hrun hnode hborder hvcg
  have hbandI : run.top.getD (rk run.proper.rank i).toNat 0 ≤ run.ys.getD i 0 := by
    have hrkIi : rk run.coordinateProper.rank i = ((rk run.proper.rank i).toNat : Int) := by
      have h0i : 0 ≤ rk run.proper.rank i := hrk0i
      have heq : rk run.proper.rank i = rk run.coordinateProper.rank i :=
        X_proper_rank_eq_local hrun i
      omega
    exact (hinBand (rk run.proper.rank i).toNat li i hlyi hini hiC hrkIi).1
  have htopMono : run.top.getD (rk run.proper.rank v).toNat 0 ≤
      run.top.getD (rk run.proper.rank i).toNat 0 := by
    by_cases heq : (rk run.proper.rank v).toNat = (rk run.proper.rank i).toNat
    · rw [heq]; exact Int.le_refl _
    · have hlt : (rk run.proper.rank v).toNat < (rk run.proper.rank i).toNat := by
        have h0v : 0 ≤ rk run.proper.rank v := hrk0v
        have h0i : 0 ≤ rk run.proper.rank i := hrk0i
        omega
      have hle := hdisjBands (rk run.proper.rank v).toNat (rk run.proper.rank i).toNat
        lv li hlt hlyv hlyi
      have hnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lv :=
        CoordsImpl.layerHeight_nonneg _ _
      omega
  rw [hysv]
  exact Int.le_trans htopMono hbandI

/-- Exact frame facts: a coordinate `-2` node is a non-dummy frame top with
zero height in the executed graph. -/
private theorem Xra_frame_facts {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hnode : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) (hdum : coord.dummy = false) (hh : coord.node.h = 0) :
    RouteImpl.frameKind run.proper v = -2 ∧ RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  have hrel := proxyWidths_rel hproxy
  obtain ⟨nd', hnd', hdummy, hborder', hheight⟩ := hrel.2.2.2.2.1 v _ hnode
  have hproper : run.proper.nodes[v]? = some nd' := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    exact hnd'
  refine ⟨(isTop_iff hproper).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [hdummy]; exact hdum
  · rw [hborder']; exact hb
  · have hzero : nd'.node.h = 0 := by
      rw [hheight]
      exact hh
    simp only [RouteImpl.nodeH, hproper, hzero]

/-- The exact candidate-graph form of the group-endpoint facts. -/
private theorem Xra_groupTopEndpointFactsCandidate {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (hrank : X_TopRank exactIds)
    {v : Nat}
    (hcb : ((componentCandidate graph comp candidate).nodes.getD v default).border = -2) :
    GroupTopEndpointData (componentCandidate graph comp candidate) run v := by
  obtain ⟨hvcg, hnodeCg⟩ := Xra_group_top_index hcb
  have hdeclpath := Xra_group_top_decl_path h0 h hnodeCg hcb
  obtain ⟨coord, hcoord, hcoordBorder, hcoordDum, hcoordPath, hcoordH⟩ :=
    Xra_group_top_coordinate_record h0 h hcomp hrun hnodeCg hcb
  obtain ⟨owner, span, ownerEq, hspan, hproper, _, hleft, hright⟩ :=
    Xra_proxy_interval hrun hcoord (Or.inl hcoordBorder)
  have hcoordD : run.coordinateProper.nodes.getD v default = coord := by
    rw [List.getD_eq_getElem?_getD, hcoord, Option.getD_some]
  have hproperD : run.proper.nodes.getD v default =
      { coord with node := { coord.node with w := span.hi - span.lo } } := by
    rw [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
  have hnodeCoord : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes.getD v default) := by
    rw [hcoordD]
    exact hcoord
  have hv : v < run.proper.nodes.length := Xra_original_nodes_covered hrun v hvcg
  have hframe := Xra_frame_facts hrun hnodeCoord
    (by rw [hcoordD]; exact hcoordBorder) (by rw [hcoordD]; exact hcoordDum)
    (by rw [hcoordD]; exact hcoordH)
  refine ⟨hcb, hnodeCoord, ?_, ?_, ?_, hv, ?_, ?_, ?_⟩
  · rw [hcoordD]
    exact hcoordBorder
  · rw [hcoordD, hcoordPath]
    exact hdeclpath.1
  · rw [hproperD]
    show ({ coord with node := { coord.node with w := span.hi - span.lo } } : ProperNode).node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD v default).decl = true
    rw [hcoordPath]
    exact hdeclpath.2
  · intro q hq hin
    have hqget : run.proper.nodes[q.2]? = some q.1 :=
      List.mem_zipIdx_iff_getElem?.mp hq
    have hqi : q.2 < run.proper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hqget).1
    have hqD : run.proper.nodes.getD q.2 default = q.1 := by
      rw [List.getD_eq_getElem?_getD, hqget, Option.getD_some]
    have hrk := hrank h0 h hlines hwf hfp hcomp hrun hnodeCg hcb hvcg hqi
      (by rw [hqD]; exact hin)
    exact Xra_executed_ys_ge_top_band h0 h hcomp hrun hnodeCg hcb hvcg hqi hrk
  · exact hframe.1
  · exact hframe.2

/-- A `-2` endpoint's port form is the frame top. -/
private theorem Xra_group_top_port_eq_ys
    {cg : Graph} {run : Run} {v : Nat} (_hdata : GroupTopEndpointData cg run v) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).y = run.ys.getD v 0 := by
  simp only [RouteImpl.boxRect, RouteImpl.yAt]

/-- The frame-top port form coincides with the frame's vertical top. -/
private theorem Xra_group_frame_y_eq_ys
    {cg : Graph} {run : Run} {v : Nat} (hdata : GroupTopEndpointData cg run v) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).y +
        (RouteImpl.boxRect run.proper run.xs run.ys v).h = run.ys.getD v 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hnh⟩ := hdata
  simp only [RouteImpl.boxRect, RouteImpl.yAt]
  rw [hnh]
  exact Int.add_zero _

/-- Non-proxy exact coordinate nodes transfer to the proper run unchanged. -/
private theorem Xra_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Port positions of an exact group top proxy lie within the group frame's
horizontal range. -/
private theorem Xra_group_frame_x_contains_port
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hborder : (run.coordinateProper.nodes.getD v default).node.border = -2)
    (hcborder : (cg.nodes.getD v default).border = -2)
    (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl)
    (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    (frameRect P cg run v).x ≤ px ∧
      px ≤ (frameRect P cg run v).x + (frameRect P cg run v).w := by
  obtain ⟨owner, span, ownerEq, hspan, _, _, hleft, hright⟩ :=
    Xra_proxy_interval hrun hnode (Or.inl hborder)
  have hownerEq : owner = (cg.nodes.getD v default).decl :=
    Option.some.inj (ownerEq.symm.trans howner)
  obtain ⟨li, ri, left, right, hleftGet, hrightGet, hleftBorder, hrightBorder,
    hleftOwner, hrightOwner, _, _, hlo, hhi⟩ := proxySpan_endpoint_sources hspan
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with h | h <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with h | h <;> omega
  obtain ⟨hleftProper, hleftXs⟩ := Xra_nonproxy_record hrun hleftGet hleftNotProxy
  obtain ⟨hrightProper, hrightXs⟩ := Xra_nonproxy_record hrun hrightGet hrightNotProxy
  have hleftOwner' : left.node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl := by rw [hleftOwner, hownerEq]
  have hrightOwner' : right.node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl := by rw [hrightOwner, hownerEq]
  have hleftRect : Labels.rectAt run.proper run.xs run.ys li ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD v default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(left, li), List.mem_zipIdx_iff_getElem?.mpr hleftProper, ?_⟩
    rcases hleftBorder with h | h
    · simp [h, hleftOwner']
    · simp [h, hleftOwner']
  have hrightRect : Labels.rectAt run.proper run.xs run.ys ri ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD v default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(right, ri), List.mem_zipIdx_iff_getElem?.mpr hrightProper, ?_⟩
    rcases hrightBorder with h | h
    · simp [h, hrightOwner']
    · simp [h, hrightOwner']
  have hleftLo : (Labels.rectAt run.proper run.xs run.ys li).x = span.lo := by
    have hw : RouteImpl.nodeW run.proper li = left.node.w := by
      simp only [RouteImpl.nodeW, hleftProper]
    show run.xs.getD li 0 - Int.fdiv (RouteImpl.nodeW run.proper li) 2 = span.lo
    rw [hleftXs, hlo, hw]
  have hrightHi : (Labels.rectAt run.proper run.xs run.ys ri).x +
      (Labels.rectAt run.proper run.xs run.ys ri).w = span.hi := by
    have hw : RouteImpl.nodeW run.proper ri = right.node.w := by
      simp only [RouteImpl.nodeW, hrightProper]
    show run.xs.getD ri 0 - Int.fdiv (RouteImpl.nodeW run.proper ri) 2 +
      RouteImpl.nodeW run.proper ri = span.hi
    rw [hrightXs, hhi, hw]
  have hminX := boundsOf_minX_le_rect_x _ [] _ hleftRect
  have hrightBound := rect_right_le_boundsOf_right _ [] _ hrightRect
  have hboxX : (RouteImpl.boxRect run.proper run.xs run.ys v).x = span.lo := by
    show RouteImpl.leftOf run.proper run.xs v = span.lo
    exact hleft
  have hboxW : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w = span.hi := by
    show RouteImpl.leftOf run.proper run.xs v +
      RouteImpl.nodeW run.proper v = span.hi
    exact hright
  simp only [frameRect, hcborder, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

/-- The routed port point of an exact group top proxy lies on the group
frame boundary. -/
private theorem Xra_group_frame_boundary
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hborder : (run.coordinateProper.nodes.getD v default).node.border = -2)
    (hcborder : (cg.nodes.getD v default).border = -2)
    (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl)
    (hcontains : (run.proper.nodes.getD v default).node.clusterPath.contains
      (cg.nodes.getD v default).decl = true)
    (hv : v < run.proper.nodes.length)
    (hlow : ∀ q : ProperNode × Nat, q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains (cg.nodes.getD v default).decl = true →
        run.ys.getD v 0 ≤ run.ys.getD q.2 0)
    (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run v) := by
  have hx := Xra_group_frame_x_contains_port hrun hnode hborder hcborder howner px hpx
  have hy := frameRect_top_eq_of_members (P := P) (i := v) (Y := run.ys.getD v 0)
    hcborder hcontains hv rfl hlow
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, hroute, _⟩ := componentRunX_spec hrun
  have hdims := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.1
  have hshape : ProperDimsNonneg run.proper := by
    intro i nd hget
    have hi : i < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hget).1
    have hw := hdims i hi
    have hnd : RouteImpl.nodeW run.proper i = nd.node.w ∧
        RouteImpl.nodeH run.proper i = nd.node.h := by
      simp only [RouteImpl.nodeW, RouteImpl.nodeH, hget]
      trivial
    omega
  have hdim := frameRect_dims_nonneg P cg run v hshape hv
  simp only [Validator.onBoundary]
  rw [hy]
  refine ⟨hx.1, hx.2, ?_, ?_, Or.inr (Or.inr (Or.inl rfl))⟩
  · omega
  · omega

/-- The routed port point of an exact group top proxy lies on the group
frame boundary, from the bundled endpoint facts. -/
private theorem Xra_group_top_boundary
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hdata : GroupTopEndpointData cg run v) (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run v) := by
  obtain ⟨hcborder, hnode, hborder, howner, hcontains, hv, hlow, _, _⟩ := hdata
  exact Xra_group_frame_boundary hrun hnode hborder hcborder howner hcontains
    hv hlow px hpx

/-- Exact flat group-endpoint attachment: every route whose first or last
point is a group top proxy attaches to the transported frame of that
endpoint, and every other endpoint attaches to the transported box
rectangle. Conditional on the bundled group-endpoint facts. -/
private theorem Xra_route_attachment_of_facts
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < cg.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    (hsrc : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = -2 →
      GroupTopEndpointData cg run (RouteImpl.edgeAt run.proper first).tail)
    (htgt : (cg.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border = -2 →
      GroupTopEndpointData cg run (RouteImpl.edgeAt run.proper last).head)
    (cursor : Int) (loops : List (Nat × LoopPlacement))
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ rt : EdgeRoute, ∃ start finish : Point,
      run.routes[i]? = some rt ∧ rt.original = i ∧
      (placeComponentExact P cg run cursor labels loops).routes[i]? =
        some ((cg.edges[i]).decl, rt.points.map
          (shiftPoint (cursor - (placeBoundsX P cg run labels loops).minX)
            (-(placeBoundsX P cg run labels loops).minY))) ∧
      rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
      let source := frameRect P cg run (RouteImpl.edgeAt run.proper first).tail
      let target := frameRect P cg run (RouteImpl.edgeAt run.proper last).head
      let reversed := (cg.edges.map (·.reversed)).getD i false
      let bounds := placeBoundsX P cg run labels loops
      let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
      let transportRect := fun rect => shiftRect margin margin
        (orientRect direction canvasH
          (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) rect))
      Validator.onBoundary (transport start) (transportRect (if reversed then target else source)) ∧
      Validator.onBoundary (transport finish) (transportRect (if reversed then source else target)) := by
  obtain ⟨rt, hrt, horiginal, _⟩ := componentRunX_route_of_index hrun hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, hroutes⟩ :=
    componentRunX_spec hrun
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    simpa only [horiginal] using hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    simpa only [horiginal] using hlast
  obtain ⟨px, qx, _, _, hpx0, hpx1, hqx0, hqx1, hend⟩ :=
    route_endpoints_on_ports hrouting hroutes rt hm first last hfirst' hlast'
  rw [horiginal] at hend
  have hgeometry := RouteImpl.routeWithLanes_geometry hrouting
  obtain ⟨_, hdims, _, _, hedge⟩ := RouteImpl.layersOk_spec hgeometry.1
  have hf := hedge first (RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' hfirst))
  have hl := hedge last (RouteImpl.mem_edgesOf (List.mem_of_getLast? hlast))
  have hsh := (hdims _ hf.1).2
  have hth := (hdims _ hl.2.1).2
  have hsPlain : Validator.onBoundary
      ⟨px, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (RouteImpl.boxRect run.proper run.xs run.ys (RouteImpl.edgeAt run.proper first).tail) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inr True.intro))⟩
  have htPlain : Validator.onBoundary
      ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).y⟩
      (RouteImpl.boxRect run.proper run.xs run.ys (RouteImpl.edgeAt run.proper last).head) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hqx0, hqx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
  have hsb : Validator.onBoundary
      ⟨px, if RouteImpl.frameKind run.proper (RouteImpl.edgeAt run.proper first).tail = -2 then
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y else
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (frameRect P cg run (RouteImpl.edgeAt run.proper first).tail) := by
    by_cases hg : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = -2
    · obtain ⟨-, -, -, -, -, -, -, hfk, -⟩ := hsrc hg
      simp only [hfk, ↓reduceIte]
      simpa only [RouteImpl.boxRect, RouteImpl.yAt] using
        Xra_group_top_boundary hrun (hsrc hg) px ⟨hpx0, hpx1⟩
    · rw [plain_frame_eq_boxRect' P cg run _ hf.1 hg]
      by_cases hfk : RouteImpl.frameKind run.proper
          (RouteImpl.edgeAt run.proper first).tail = -2
      · simp only [hfk, ↓reduceIte, Validator.onBoundary, RouteImpl.boxRect]
        exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
      · simp only [hfk, ↓reduceIte]
        exact hsPlain
  have hsbRev : Validator.onBoundary
      ⟨px, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (frameRect P cg run (RouteImpl.edgeAt run.proper first).tail) := by
    by_cases hg : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = -2
    · have hdata := hsrc hg
      have hy := Xra_group_frame_y_eq_ys (cg := cg) (run := run) hdata
      rw [hy]
      exact Xra_group_top_boundary hrun hdata px ⟨hpx0, hpx1⟩
    · rw [plain_frame_eq_boxRect' P cg run _ hf.1 hg]
      exact hsPlain
  have htb : Validator.onBoundary
      ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).y⟩
      (frameRect P cg run (RouteImpl.edgeAt run.proper last).head) := by
    by_cases hg : (cg.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border = -2
    · have hdata := htgt hg
      have hy := Xra_group_top_port_eq_ys (cg := cg) (run := run) hdata
      rw [hy]
      exact Xra_group_top_boundary hrun hdata qx ⟨hqx0, hqx1⟩
    · rw [plain_frame_eq_boxRect' P cg run _ hl.2.1 hg]
      exact htPlain
  have hplaced := X_placeComponentExact_route_entry_of_producer hrun cursor loops i hi hloop
  have hget : run.routes[i]'(by
      rw [componentRunX_routes_length hrun, componentRunX_proper_chains_length hrun]
      exact hi) = rt := (List.getElem?_eq_some_iff.mp hrt).2
  rw [hget] at hplaced
  split at hend
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev, ↓reduceIte]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htb
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsbRev
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsb
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htb

/-- The exact run-level port attachment holds for executed exact layouts. -/
theorem x_runAttach_holds (exactIds : List String) : X_RunAttach exactIds := by
  intro P inp o lines graph0 graph measured h0 hexact hlines hwf hfp comp hcomp candidate
    run labels orderOptions hrun i hi first last hfirst hlast cursor loops hloop
    margin direction canvasH boxX boxY
  have hrank : X_TopRank exactIds := x_topRank_holds exactIds
  have hfacts : ∀ v : Nat,
      ((componentCandidate graph comp candidate).nodes.getD v default).border = -2 →
      GroupTopEndpointData (componentCandidate graph comp candidate) run v :=
    fun v hv =>
      Xra_groupTopEndpointFactsCandidate h0 hexact hlines hwf hfp hcomp hrun hrank hv
  exact Xra_route_attachment_of_facts hrun hi hfirst hlast
    (fun hg => hfacts _ hg) (fun hg => hfacts _ hg)
    cursor loops hloop margin direction canvasH boxX boxY

end Elegant.Layered.PipelineImpl
