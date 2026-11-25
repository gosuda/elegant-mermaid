import Elegant.Layered.ExactLoopEnvelopeGroupProof
import Elegant.Layered.ExactLoopEnvelopeLayerProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-- Executed exact-run marker order for group tops: every executed exact run
satisfies the per-run witness `XLEG_GroupMarkerOrder`. Stated over
`SceneExecutionX` and successful `componentRunX` (the executed-run form, so no
extra admission is needed: all replay lemmas below use only the run equations
and the measured/exact graph equations). -/
def XLEG_GroupMarkerOrderX (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    XLEG_GroupMarkerOrder cg run execution.measured

/-- The extended footprint starts at the owner frame's right edge and has
nonnegative width in both sizing branches. Prefixed copy of `XLEG_fp_edges`
(`ExactLoopEnvelopeGroupProof.lean`); private lemmas do not resolve across
modules. -/
private theorem XLEGM_fp_edges {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {t : Nat}
    (hslot : 0 ≤ cg.slot)
    (hw : ∀ l ∈ loopSizes cg.edges labels t cg.slot, 0 ≤ l.width) :
    (loopFootprintExt cg run labels t).x =
      (frameRect default cg run t).x + (frameRect default cg run t).w ∧
    0 ≤ (loopFootprintExt cg run labels t).w := by
  have hmono : ∀ (acc : Int), 0 ≤ acc → ∀ (ss : List LoopLabel),
      0 ≤ ss.foldl (fun w l => max w l.width) acc := by
    intro acc ha ss
    induction ss generalizing acc with
    | nil => exact ha
    | cons s rest ih =>
      simp only [List.foldl]
      exact ih _ (Int.le_trans ha (Int.le_max_left _ _))
  have hwide : (0 : Int) ≤ (loopSizes cg.edges labels t cg.slot).foldl
      (fun w l => max w l.width) 0 :=
    hmono 0 (Int.le_refl _) _
  have hfold : ∀ (acc : Int), 0 ≤ acc → ∀ (l : List Int),
      (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.foldl (· + ·) acc := by
    intro acc ha l hl
    induction l generalizing acc with
    | nil => exact ha
    | cons a rest ih =>
      simp only [List.foldl]
      exact ih _ (by have hha := hl a (List.mem_cons.mpr (Or.inl rfl)); omega)
        (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
  have hterm : ∀ q ∈ (loopSizes cg.edges labels t cg.slot).zipIdx.map
      (fun q => cg.slot * ((q.2 : Int) + 2) + q.1.width), (0 : Int) ≤ q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨_, hjlen, ha⟩ := List.mem_zipIdx hp
    have h1 : p.2 < (loopSizes cg.edges labels t cg.slot).length := by omega
    have hmem : p.1 ∈ loopSizes cg.edges labels t cg.slot := by
      have h2 : (loopSizes cg.edges labels t cg.slot)[p.2]? =
          some ((loopSizes cg.edges labels t cg.slot)[p.2]) :=
        List.getElem?_eq_getElem h1
      simp only [Nat.sub_zero] at ha
      rw [← ha] at h2
      exact List.mem_of_getElem? h2
    have hslot2 : (0 : Int) ≤ cg.slot * ((p.2 : Int) + 2) :=
      Int.mul_nonneg hslot (by omega)
    have hwp : (0 : Int) ≤ p.1.width := hw p.1 hmem
    omega
  unfold loopFootprintExt
  dsimp only
  refine ⟨rfl, ?_⟩
  · by_cases hex : run.exact.contains t = true
    · simp only [hex, ↓reduceIte]
      unfold Loops.exactExtent
      dsimp only
      split
      · exact hwide
      · have hnn : (0 : Int) ≤
            (((loopSizes cg.edges labels t cg.slot).length : Int)) :=
          Int.natCast_nonneg _
        have h3 : (0 : Int) ≤ cg.slot *
            (2 * (((loopSizes cg.edges labels t cg.slot).length : Int)) + 1) :=
          Int.mul_nonneg hslot (by omega)
        omega
    · have hcon : run.exact.contains t = false := Bool.eq_false_iff.mpr hex
      simp only [hcon, Bool.false_eq_true, ↓reduceIte]
      unfold Loops.extent
      exact hfold 0 (Int.le_refl _) _ hterm
/-- Exact coordinate record from a proper record: every proper node has the
same border and height in the coordinate run. Prefixed copy of
`XLEG_proper_coord` (`ExactLoopEnvelopeGroupProof.lean`); private lemmas do
not resolve across modules. -/
private theorem XLEGM_proper_coord {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  obtain ⟨_, _, hlen, _, hAll, _⟩ := proxyWidths_rel hprox
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes]; exact hlen
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', _, hb', hh'⟩ := hAll v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [hnodes]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  exact ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm⟩

/-- Exact proper nodes transfer unchanged for non-proxy borders. Prefixed copy
of `XLEG_nonproxy_record` (`ExactLoopEnvelopeGroupProof.lean`); private lemmas
do not resolve across modules. -/
private theorem XLEGM_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
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


/-- Appended coordinate nodes are never proxy: past the labeled prefix, the
coordinate run only holds titles (border `3`) and side markers (borders
`±1`). Prefixed copy of `XLEG_appended_nonproxy`
(`ExactLoopEnvelopeGroupProof.lean`); private lemmas do not resolve across
modules. -/
private theorem XLEGM_appended_nonproxy {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    {v : Nat} {nvc : ProperNode}
    (hcoordV : run.coordinateProper.nodes[v]? = some nvc)
    (hlen : labeled.nodes.length ≤ v) :
    nvc.node.border ≠ -2 ∧ nvc.node.border ≠ 2 := by
  rw [← hc] at hcoordV
  obtain ⟨m1, hm1, _, hb1, _, _⟩ := materialize_lookup _ hcoordV
  rw [clearProxyExtents_nodes] at hm1
  obtain ⟨m2, hm2, hcm⟩ : ∃ m,
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[v]? = some m ∧ clearF m = m1 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm1)
  have hb2 : m2.node.border = m1.node.border := by
    have h := (clearF_keys m2).2.1
    rw [hcm] at h
    exact h.symm
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  rw [hx] at hm2
  by_cases hpre : v < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length
  · rw [List.getElem?_append_left hpre] at hm2
    rw [titleReservations_nodes] at hm2
    have hsz : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
      unfold sizeProperPortsX
      simp
    by_cases ht : v < (sizeProperPortsX P exact labeled).nodes.length
    · rw [List.getElem?_append_left (by simpa using ht)] at hm2
      obtain ⟨m3, hm3, htm⟩ : ∃ m,
          (sizeProperPortsX P exact labeled).nodes[v]? = some m ∧ titleF m = m2 := by
        simp only [List.getElem?_map] at hm2
        cases hl : (sizeProperPortsX P exact labeled).nodes[v]? with
        | none => simp [hl] at hm2
        | some m =>
          simp only [hl, Option.map_some, Option.some.injEq] at hm2
          exact ⟨m, rfl, hm2⟩
      have hkey := sizeProperPortsX_key P exact labeled v
      rw [hm3] at hkey
      cases hl : labeled.nodes[v]? with
      | none => simp [hl] at hkey
      | some m4 =>
        have hlt : v < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hl).1
        omega
    · have hge : (sizeProperPortsX P exact labeled).nodes.length ≤ v := Nat.le_of_not_lt ht
      have hlen : ((sizeProperPortsX P exact labeled).nodes.map titleF).length =
          (sizeProperPortsX P exact labeled).nodes.length := by simp
      have hle : ((sizeProperPortsX P exact labeled).nodes.map titleF).length ≤ v := by
        omega
      rw [List.getElem?_append_right hle, hlen] at hm2
      obtain ⟨q, _, hqeq⟩ : ∃ q, q ∈ titleNodes (sizeProperPortsX P exact labeled) ∧
          copyF q = m2 :=
        List.mem_map.mp (List.mem_of_getElem? hm2)
      have hb3 : m2.node.border = 3 := by rw [← hqeq]; rfl
      constructor <;> omega
  · have hge : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length ≤ v :=
      Nat.le_of_not_lt hpre
    rw [List.getElem?_append_right hge] at hm2
    obtain ⟨_, hbE⟩ := hall m2 (List.mem_of_getElem? hm2)
    rcases hbE with hL | hR <;> constructor <;> omega

/-- A recorded non-marker index is never a group-top position of the exact
candidate graph. Prefixed copy of `XLEG_no_group_at_b`
(`ExactLoopEnvelopeGroupProof.lean`); private lemmas do not resolve across
modules. -/
private theorem XLEGM_no_group_at_b {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {b : Nat} {actualB : ProperNode}
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2)) :
    ((componentCandidate graph comp candidate).nodes.getD b default).border ≠ -2 := by
  intro hcon
  have hdef : (default : Node).border = 0 := rfl
  by_cases hsome : ∃ nodeB : Node,
      (componentCandidate graph comp candidate).nodes[b]? = some nodeB
  · obtain ⟨nodeB, hnodeB⟩ := hsome
    have hget : (componentCandidate graph comp candidate).nodes.getD b default =
        nodeB := by
      simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
    have hbB : nodeB.border = -2 := by rw [← hget]; exact hcon
    obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ := X_cg_run_bundle h0 h hcomp hrun
    have hlab : labeled.nodes[b]? =
        some (⟨nodeB, false, none, false⟩ : ProperNode) :=
      hrecords b nodeB hnodeB
    have hcoord : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[b]? =
        some (clearF (titleF (⟨nodeB, false, none, false⟩ : ProperNode))) :=
      X_coordinateGraph_marker_record (P := P) (exact := exactDecls exactIds inp)
        hlab (Or.inl hbB) rfl
    rw [hc] at hcoord
    have hinj : clearF (titleF (⟨nodeB, false, none, false⟩ : ProperNode)) =
        actualB :=
      Option.some.inj (hcoord.symm.trans hcoordB)
    have hbdr : (clearF (titleF
        (⟨nodeB, false, none, false⟩ : ProperNode))).node.border = -2 :=
      (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hbB)
    rw [hinj] at hbdr
    exact hbne (Or.inl hbdr)
  · have hnone : (componentCandidate graph comp candidate).nodes[b]? = none := by
      cases h : (componentCandidate graph comp candidate).nodes[b]? with
      | none => rfl
      | some nodeB => exact absurd ⟨nodeB, h⟩ hsome
    have hget : (componentCandidate graph comp candidate).nodes.getD b default =
        default := by
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [hget, hdef] at hcon
    omega

/-- The frame left edge at a non-group position is the placed rect left edge.
Prefixed copy of `XLEG_frameB_x` (`ExactLoopEnvelopeGroupProof.lean`); private
lemmas do not resolve across modules. -/
private theorem XLEGM_frameB_x {P : Params} {cg : Graph} {run : Run}
    {b : Nat} {actualB : ProperNode}
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hgetNe : (cg.nodes.getD b default).border ≠ -2) :
    (frameRect P cg run b).x = (Labels.rectAt run.proper run.xs run.ys b).x := by
  have hframe : frameRect P cg run b = nodeRect cg run b := by
    unfold frameRect
    simp only []
    exact ite_eq_left (by simpa using hgetNe)
  have hrect : nodeRect cg run b = Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hproperB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hproperB]
  rw [hframe, hrect]

/-- Group-top hull equality from explicit ordered markers: every border rect
of the owner's cluster ends at or before the right marker's right edge, and
the marker belongs to the hull. Prefixed copy of `XLEG_hull_eq`
(`ExactLoopEnvelopeGroupProof.lean`); private lemmas do not resolve across
modules. -/
private theorem XLEGM_hull_eq {cg : Graph} {run : Run}
    {t : Nat} {nt : Node}
    (hnt : cg.nodes[t]? = some nt)
    (htG : nt.border = -2)
    {mL mR : Nat} {nR : ProperNode}
    (hR : run.proper.nodes[mR]? = some nR) (hbR : nR.node.border = 1)
    (hlR : nR.node.clusterPath.getLast? = some nt.decl)
    (hshare : ∀ {q : Nat} {nd : ProperNode}, run.proper.nodes[q]? = some nd →
      nd.node.clusterPath.getLast? = some nt.decl →
      ((nd.node.border = -1 →
        RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mL ∧
        RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
          RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL) ∧
      (nd.node.border = 1 →
        RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mR ∧
        RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
          RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR)))
    (hcross2 : RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL ≤
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR)
    (hnonneg : 0 ≤ RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR) :
    (frameRect default cg run t).x + (frameRect default cg run t).w =
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
  have hframe := frameRect_group_span (P := default) (run := run) hnt htG
  have hall : ∀ r ∈ groupBorderRects cg run nt.decl,
      r.x + r.w ≤ (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
    intro r hr
    obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
    rcases hbq with hbqL | hbqR
    · obtain ⟨heq1, heq2⟩ := (hshare hq hlastq).1 hbqL
      rw [hrq, rectAt_eq run.proper run.xs run.ys q,
        rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
    · obtain ⟨heq1, heq2⟩ := (hshare hq hlastq).2 hbqR
      rw [hrq, rectAt_eq run.proper run.xs run.ys q,
        rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
  have hnonnegR := hnonneg
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      groupBorderRects cg run nt.decl :=
    groupBorderRects_mem_of_record hR (Or.inr hbR) hlR
  have hRw : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    rw [rectAt_eq]
  have hzero : (0 : Int) ≤ (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w := by
    rw [hRw]
    exact hnonnegR
  have hright := boundsOf_right_le_of_all hzero hall
  have hge := (boundsOf_rect_mem hmemR).2
  have hframeRW : (frameRect default cg run t).x +
      (frameRect default cg run t).w =
      (boundsOf (groupBorderRects cg run nt.decl) []).right := by
    rw [hframe]
    dsimp only
    omega
  omega

/-- Executed group-top reservation: the footprint of a looping group top ends
left of the frame of every recorded nonmarker box right of its right marker.
Prefixed copy of `XLEG_top_reservation`
(`ExactLoopEnvelopeGroupProof.lean`); private lemmas do not resolve across
modules. -/
private theorem XLEGM_top_reservation {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {t : Nat} {mR : Nat} {nR : ProperNode}
    (hcoordR : run.coordinateProper.nodes[mR]? = some nR)
    (hproperR : run.proper.nodes[mR]? = some nR)
    (hxsR : run.xs.getD mR 0 = run.coordinateXs.getD mR 0)
    (hext : (nR.node.loopExtent : Int) ≥
      (if run.exact.contains t then Loops.exactExtent cg.slot (loopSizes cg.edges labels t cg.slot)
       else Loops.extent cg.slot (loopSizes cg.edges labels t cg.slot)))
    {b : Nat} {actualB : ProperNode}
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hxsB : run.xs.getD b 0 = run.coordinateXs.getD b 0)
    (hGb : (cg.nodes.getD b default).border ≠ -2)
    (hHull : (frameRect default cg run t).x + (frameRect default cg run t).w =
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w)
    (hsep : Int.fdiv (nR.node.w + 2 * (nR.node.loopExtent : Int)) 2 +
        Int.fdiv (actualB.node.w + 2 * (actualB.node.loopExtent : Int)) 2 + 1 ≤
        run.coordinateXs.getD b 0 - run.coordinateXs.getD mR 0) :
    (loopFootprintExt cg run labels t).x + (loopFootprintExt cg run labels t).w ≤
      (frameRect default cg run b).x := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizesNN, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hWmNN : (0 : Int) ≤ nR.node.w := (sizesNonneg_lookup hsizesNN mR nR hcoordR).1
  have hWbNN : (0 : Int) ≤ actualB.node.w := (sizesNonneg_lookup hsizesNN b actualB hcoordB).1
  have hNWmNN : 0 ≤ nR.node.w + 2 * (nR.node.loopExtent : Int) := by omega
  have hMsum : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      run.xs.getD mR 0 - Int.fdiv nR.node.w 2 + nR.node.w := by
    simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hproperR]
  have hBx : (Labels.rectAt run.proper run.xs run.ys b).x =
      run.xs.getD b 0 - Int.fdiv actualB.node.w 2 := by
    simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hproperB]
  have hframeB : (frameRect default cg run b).x =
      (Labels.rectAt run.proper run.xs run.ys b).x :=
    XLEGM_frameB_x hproperB hGb
  have hw : ∀ l ∈ loopSizes cg.edges labels t cg.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hFp := XLEGM_fp_edges (cg := cg) (run := run) (labels := labels) (t := t)
    (componentRunX_slot_nonneg hrun) hw
  rw [hFp.1, hHull, hframeB, hMsum, hBx, hxsR, hxsB]
  have hW : (loopFootprintExt cg run labels t).w =
      (if run.exact.contains t then Loops.exactExtent else Loops.extent)
        cg.slot (loopSizes cg.edges labels t cg.slot) := by
    unfold loopFootprintExt
    dsimp only
  rw [hW]
  by_cases hex : run.exact.contains t = true
  · simp only [hex, ↓reduceIte] at hext ⊢
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  · have hcon : run.exact.contains t = false := Bool.eq_false_iff.mpr hex
    simp only [hcon, Bool.false_eq_true, ↓reduceIte] at hext ⊢
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
/-- Proxy proper nodes have height zero from the coordinate record alone: the
`±2` border rules out the appended prefix (titles and side markers are
nonproxy), the labeled record then feeds the marker record, and the cleared
height transfers to the proper node. Merges `XLEG_appended_nonproxy` and
`XLEG_proxy_h_zero` (`ExactLoopEnvelopeGroupProof.lean`) so callers need no
candidate-graph record; private lemmas do not resolve across modules. -/
private theorem XLEGM_proxy_proper_h_zero {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {labeled : Proper}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hkeys : NodeKeys cg labeled)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp)
    (hb : nvp.node.border = -2 ∨ nvp.node.border = 2) :
    RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨nvc, hcoordV, hbV, hhV⟩ := XLEGM_proper_coord hrun hrec
  have hbVc : nvc.node.border = -2 ∨ nvc.node.border = 2 := by rw [hbV]; exact hb
  have hcoordV0 := hcoordV
  have hltL : v < labeled.nodes.length := by
    by_cases hgt : v < labeled.nodes.length
    · exact hgt
    · have hle : labeled.nodes.length ≤ v := Nat.le_of_not_lt hgt
      obtain ⟨hne1, hne2⟩ := XLEGM_appended_nonproxy hc hcoordV hle
      rcases hbVc with h1 | h1 <;> omega
  have hlabeledV : labeled.nodes[v]? = some labeled.nodes[v] :=
    List.getElem?_eq_getElem hltL
  have hszLen : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
    unfold sizeProperPortsX
    simp
  have hpre : v < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
    omega
  have hltS : v < (sizeProperPortsX P exact labeled).nodes.length := by omega
  have hcoordV' := hcoordV
  rw [← hc] at hcoordV'
  unfold coordinateGraphX at hcoordV'
  obtain ⟨m1, hm1, _, hb1, _, _⟩ := materialize_lookup _ hcoordV'
  rw [clearProxyExtents_nodes] at hm1
  obtain ⟨m2, hm2, hcm⟩ : ∃ m,
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[v]? = some m ∧ clearF m = m1 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm1)
  have hb2 : m2.node.border = m1.node.border := by
    have h := (clearF_keys m2).2.1
    rw [hcm] at h
    exact h.symm
  obtain ⟨extra, hx, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  rw [hx, List.getElem?_append_left hpre] at hm2
  rw [titleReservations_nodes, List.getElem?_append_left (by simpa using hltS)] at hm2
  obtain ⟨m3, hm3, htm⟩ : ∃ m,
      (sizeProperPortsX P exact labeled).nodes[v]? = some m ∧ titleF m = m2 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm2)
  have hb3 : m3.node.border = m2.node.border := by
    have h := (titleF_keys m3).2.1
    rw [htm] at h
    exact h.symm
  have hkey := sizeProperPortsX_key P exact labeled v
  rw [hm3, hlabeledV] at hkey
  have hlnB : (labeled.nodes[v]).node.border = nvc.node.border := by
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
    obtain ⟨_, hb4, _⟩ := hkey
    omega
  have hlnB2 : (labeled.nodes[v]).node.border = -2 ∨ (labeled.nodes[v]).node.border = 2 := by
    rw [hlnB]; exact hbVc
  rcases hkeys v _ hlabeledV with ⟨_, _, hdm, _, _⟩ | ⟨_, hb0, _⟩
  · have hmark := X_coordinateGraph_marker_record (P := P) (exact := exact) hlabeledV hlnB2 hdm
    rw [hc] at hmark
    have hinj : clearF (titleF (labeled.nodes[v])) = nvc :=
      Option.some.inj (hmark.symm.trans hcoordV0)
    have hz : (clearF (titleF (labeled.nodes[v]))).node.h = 0 :=
      (clearF_keys _).2.2.2.trans ((titleF_keys _).2.2.2 hlnB2)
    have hnvc0 : nvc.node.h = 0 := hinj ▸ hz
    have hnvp : nvp.node.h = 0 := by omega
    have hH : RouteImpl.nodeH run.proper v = nvp.node.h := by simp [RouteImpl.nodeH, hrec]
    rw [hH]
    exact hnvp
  · omega
/-- A proxy box meets no footprint interior: its proper height is zero, so the
y-overlap is impossible. -/
private theorem XLEGM_proxy_miss {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {labeled : Proper}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hkeys : NodeKeys cg labeled)
    {t v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp)
    (hb : nvp.node.border = -2 ∨ nvp.node.border = 2) :
    ¬ (loopFootprintExt cg run labels t).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  have hz : RouteImpl.nodeH run.proper v = 0 :=
    XLEGM_proxy_proper_h_zero hrun hc hkeys hrec hb
  have hh : (RouteImpl.boxRect run.proper run.xs run.ys v).h = 0 := by
    simpa only [RouteImpl.boxRect] using hz
  simp only [Rect.meetsInterior]
  omega


/-- A later box misses the footprint: the reservation ends the footprint left
of the box frame, and the frame starts where the placed box starts. -/
private theorem XLEGM_later_miss {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {t b : Nat} {actualB : ProperNode}
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hGb : (cg.nodes.getD b default).border ≠ -2)
    (hres : (loopFootprintExt cg run labels t).x + (loopFootprintExt cg run labels t).w ≤
      (frameRect default cg run b).x) :
    ¬ (loopFootprintExt cg run labels t).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys b) := by
  have hframeB : (frameRect default cg run b).x =
      (Labels.rectAt run.proper run.xs run.ys b).x :=
    XLEGM_frameB_x hproperB hGb
  have exB : (RouteImpl.boxRect run.proper run.xs run.ys b).x =
      (Labels.rectAt run.proper run.xs run.ys b).x := by
    rw [rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.boxRect, RouteImpl.leftOf]
  intro hmeet
  obtain ⟨hx, _hy⟩ := hmeet
  omega

/-- An earlier box misses the footprint: ordered intervals end the box left of
the right marker, whose right edge is the footprint origin. -/
private theorem XLEGM_earlier_miss {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {t mR b : Nat} {nR actualB : ProperNode}
    (hproperR : run.proper.nodes[mR]? = some nR)
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hFpX : (loopFootprintExt cg run labels t).x =
      (frameRect default cg run t).x + (frameRect default cg run t).w)
    (hHull : (frameRect default cg run t).x + (frameRect default cg run t).w =
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w)
    (hord : RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b ≤
      RouteImpl.leftOf run.proper run.xs mR) :
    ¬ (loopFootprintExt cg run labels t).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys b) := by
  have hdimR := (componentRunX_dims_nonneg hrun) mR nR hproperR
  have hwR : 0 ≤ RouteImpl.nodeW run.proper mR := by
    simp only [RouteImpl.nodeW, hproperR]
    exact hdimR.1
  have eR : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    rw [rectAt_eq]
  have eB : (RouteImpl.boxRect run.proper run.xs run.ys b).x +
      (RouteImpl.boxRect run.proper run.xs run.ys b).w =
      RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b := by
    simp only [RouteImpl.boxRect, RouteImpl.leftOf, RouteImpl.nodeW, hproperB]
  intro hmeet
  obtain ⟨hx, _hy⟩ := hmeet
  omega

/-- Group-top case: the loop owner is a `-2` node, so the marker pair bounds
the footprint through the hull and reservation (later boxes, via the executed
separation), ordered intervals (earlier boxes), boundary touch (the marker
itself), and zero height (proxy boxes). -/
private theorem XLEGM_group_top_miss {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (hord : XLEG_GroupMarkerOrder (componentCandidate graph comp candidate) run labels)
    {k : Nat} {e : Edge} (hk : (componentCandidate graph comp candidate).edges[k]? = some e)
    (hloop : e.tail = e.head) (hte : e.tail = t)
    {v : Nat} (hv : v < run.proper.nodes.length)
    {layer : List Nat} (hlayerMem : layer ∈ run.layers)
    {pu pv : Nat} (hpu : layer[pu]? = some t) (hpv : layer[pv]? = some v) :
    ¬ (loopFootprintExt (componentCandidate graph comp candidate) run labels t).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨ndV, hrecV⟩ : ∃ nd, run.proper.nodes[v]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  obtain ⟨actualV, hcoordV, hbV, _hhV⟩ := XLEGM_proper_coord hrun hrecV
  by_cases hpx : actualV.node.border = -2 ∨ actualV.node.border = 2
  · obtain ⟨_, labeled, _, hc, hkeys, _, _, _, _⟩ := X_cg_run_bundle h0 h hcomp hrun
    exact XLEGM_proxy_miss hrun hc hkeys hrecV (by rw [← hbV]; exact hpx)
  · obtain ⟨hproperV, hxsV⟩ := XLEGM_nonproxy_record hrun hcoordV hpx
    have hmemE : e ∈ (componentCandidate graph comp candidate).edges :=
      List.mem_of_getElem? hk
    have hexLoop : ∃ e_ ∈ (componentCandidate graph comp candidate).edges,
        e_.tail = t ∧ e_.head = t := ⟨e, hmemE, hte, hloop.symm.trans hte⟩
    obtain ⟨hnoLoop, hmark⟩ := hord
    obtain ⟨mL, mR, _nL, nR, _hcoordL, hcoordR, _hbL, hbR, _hlastL, hlastR,
        hext, hmemL, hshare, _hcross1, hcross2, hnonneg, hsep⟩ :=
      hmark t nt hnt hexLoop htG
    have hnpR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by rw [hbR]; decide
    obtain ⟨hproperR, hxsR⟩ := XLEGM_nonproxy_record hrun hcoordR hnpR
    have hHull : (frameRect default (componentCandidate graph comp candidate) run t).x +
        (frameRect default (componentCandidate graph comp candidate) run t).w =
        (Labels.rectAt run.proper run.xs run.ys mR).x +
          (Labels.rectAt run.proper run.xs run.ys mR).w :=
      XLEGM_hull_eq hnt htG hproperR hbR hlastR hshare hcross2 hnonneg
    have hw : ∀ l ∈ loopSizes (componentCandidate graph comp candidate).edges labels t
        (componentCandidate graph comp candidate).slot, 0 ≤ l.width := by
      intro l hl
      obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
      rw [stackSize_width_eq]
      exact Labels.stackWidth_nonneg _
    have hFp := XLEGM_fp_edges (cg := componentCandidate graph comp candidate)
      (run := run) (labels := labels) (t := t)
      (componentRunX_slot_nonneg hrun) hw
    have hGb : ((componentCandidate graph comp candidate).nodes.getD v default).border ≠ -2 :=
      XLEGM_no_group_at_b h0 h hcomp hrun hcoordV hpx
    obtain ⟨jR, hjR⟩ := hmemL hlayerMem hpu
    by_cases hlt : jR < pv
    · have hsepV := hsep hcoordV hpx hlayerMem hjR hpv hlt
      have htop := XLEGM_top_reservation hrun hcoordR hproperR hxsR hext
        hcoordV hproperV hxsV hGb hHull hsepV
      exact XLEGM_later_miss hproperV hGb htop
    · by_cases hgt : pv < jR
      · have hOi := XB_orderedIntervals_holds exactIds h0 h hcomp hrun hlayerMem hgt
          hpv hjR hcoordV hcoordR hpx hnpR
        exact XLEGM_earlier_miss hrun hproperR hproperV hFp.1 hHull hOi
      · have hjReq : pv = jR := by omega
        have hjR' : layer[pv]? = some mR := by rw [hjReq]; exact hjR
        have heqV : v = mR := Option.some.inj (hpv.symm.trans hjR')
        subst v
        have hdimR := (componentRunX_dims_nonneg hrun) mR nR hproperR
        have hwR : 0 ≤ RouteImpl.nodeW run.proper mR := by
          simp only [RouteImpl.nodeW, hproperR]
          exact hdimR.1
        have eR : (Labels.rectAt run.proper run.xs run.ys mR).x +
            (Labels.rectAt run.proper run.xs run.ys mR).w =
            (RouteImpl.boxRect run.proper run.xs run.ys mR).x +
              (RouteImpl.boxRect run.proper run.xs run.ys mR).w := by
          rw [rectAt_eq]
          simp only [RouteImpl.boxRect, RouteImpl.leftOf]
        intro hmeet
        obtain ⟨hx, _hy⟩ := hmeet
        omega
/-- Group-owner same-rank miss from the executed marker order: a looping
group top is `-2` (border `0` contradicts the group premise, border `2` has
no loop by the witness), and the marker pair closes the miss. -/
theorem XLEM_groupOwnerMiss_holds (exactIds : List String)
    (hord : XLEG_GroupMarkerOrderX exactIds) :
    XLEM_GroupOwnerMiss exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv _hreal _hscope0 _hscope1 hBne layer hlayer pu pv hpu hpv
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hmem : e ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hk
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp hbd hmem
  have hltCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
    hbnd.1
  obtain ⟨nt, hnt⟩ : ∃ nt,
      (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some nt :=
    ⟨_, List.getElem?_eq_getElem hltCG⟩
  have htri := (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq
    hnt).1
  rcases htri with hB0 | hBm2 | hB2
  · have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default = nt := by
      simp only [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    have hbEq : ((componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default).border = nt.border := by
      rw [hget]
    omega
  · exact XLEGM_group_top_miss execution.graph0_eq execution.graph_eq hcomp hrun
      hnt hBm2 (hord inp o res execution hwf hfp comp candidate run orderOptions
        (componentCandidate execution.graph comp candidate) hcomp rfl hrun)
      hk hloop rfl hv hlayer hpu hpv
  · obtain ⟨hnoLoop, _⟩ := hord inp o res execution hwf hfp comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) hcomp rfl hrun
    exact absurd ⟨e, hmem, rfl, hloop.symm⟩ (hnoLoop e.tail nt hnt hB2)

end PipelineImpl


end Layered
end Elegant
