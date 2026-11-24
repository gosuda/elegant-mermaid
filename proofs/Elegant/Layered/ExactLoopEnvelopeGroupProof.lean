import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.Pipeline
import Elegant.Layered.Route
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.Coords
import Elegant.Layered.Rank
import Elegant.Layered.SceneBounds
import Elegant.Layered.Labels
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.SizingFacts
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Group-owner same-rank miss, over exact runs.

Target: `XLEM_GroupOwnerMiss` (`ExactLoopEnvelopeLayerProof.lean`): the
extended footprint of a self-loop edge owned by a group-top (candidate border
`≠ 0`) misses every in-scope real box sharing the owner's layer.

Probe truth (`proofs/wip/Probe/ExactLoopEnvelopeGroupTProbe.lean`,
`exactIds = ["a"]`, vector profile, declaration order; `fp` is
`loopFootprintExt` at the looping group top, `scope` is both scope premises,
`disj` is footprint-vs-box disjointness over the owner's layer):

- `a-sib` (looping group `g` with member `a`, sibling `s`, edge `s→a`):
  comp nodes `[(0,-2),(1,0),(2,0),(0,2)]`, edges `[(0,0),(2,1)]`,
  `run.exact = [1]`, top layer `[5,0,4,6,2]`, `fp = {x := 11257, w := 3629}`
  (right edge `14886`). Same-layer boxes: `5`/`0`/`4`/`6` (markers, self,
  title) all scope-false; sibling `2` scope-true at `x := 16422` (right of
  `14886`). Every same-layer box `disj = true`.
- `a2-sib-rev` (edge `a→s`): top layer `[5,0,4,6]`, sibling in a lower layer;
  all same-layer boxes scope-false, all `disj = true`.
- `b-empty-nest` (empty looping group `g` nested in `G`, member `a`):
  tail `1` (inner top, border `-2`), `fp = {x := 10211, w := 3629}`
  (right edge `13840`); layer `[10,16,1,7,17,2,11]`: only member `a`
  (`2`, `x := 15376`) scope-true, `disj = true`; self `1` scope-false.
- `c-unrelated` (looping `g1` next to unrelated `g2`): tail `0`,
  `fp = {x := 7495, w := 3629}`; layer `[8,0,6,9]` all scope-false
  (no same-layer foreign box), all `disj = true`.
- `d-longlabel` (200-char loop label): `fp = {x := 21417, w := 13789}`
  (right edge `35206`); layer `[5,0,4,6]` all scope-false, all
  `disj = true`; the owner box itself ends exactly at `fp.x`
  (`x+w = 21673`), i.e. boundary-touch disjointness.

Residual: `XLEG_GroupMarkerOrder`, the exact-run ordered-marker witness for a
looping group top (right marker carrying the branch-correct loop extent, in
the owner's layer; same-span alignment and cross order of the owner's
markers; executed separation of the right marker from recorded nonproxy
boxes right of it) plus the bottom no-loop fact (a self-loop never sits on
a border-`2` candidate node; the exact-graph form of
`LoopFootprintBottomEmpty`). Strictly narrower than the target
(per-execution facts). Witness truth on the probe runs (`checkWitness` in
the probe file, same four inputs, declaration order): every border-`2`
candidate node owns no self-loop edge; every looping top has border-`1`
markers carrying exactly the needed extent (`3629` in (a)-(c), `13789` in
(d)); one right marker sits in the owner's layer in each case; no
same-span mismatch over all border-`1` mates; no separation failure for any
recorded nonproxy box right of that marker; an in-layer left marker with
true cross order and nonnegative marker right edge exists in each case
(`(5,0)`, `(16,1)`, `(8,0)`, `(5,0)` with `cross1=cross2=nonneg=true`).
-/

/-- Exact-run ordered-marker witness for a looping group top: the pair of
side markers of `t` in the coordinate run, the right marker carrying at
least the branch-correct loop extent and sitting in `t`'s layer, the
same-span alignment of `t`'s markers, their cross order, and the executed
separation of the right marker from every recorded nonproxy box right of it
in a shared layer, plus the bottom no-loop fact. Replay of
`LoopResGroupHullRightWitness` (order part) plus the
`SideMarkerSpanAligned` consequences and the reservation gap needed here,
over `componentRunX`; the bottom conjunct is the exact-graph form of
`LoopFootprintBottomEmpty`. -/
def XLEG_GroupMarkerOrder (cg : Graph) (run : Run) (labels : List MeasuredLabel) : Prop :=
  (∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = 2 →
    ¬ ∃ e_ ∈ cg.edges, e_.tail = t ∧ e_.head = t) ∧
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
    (∃ e_ ∈ cg.edges, e_.tail = t ∧ e_.head = t) → nt.border = -2 →
    ∃ (mL mR : Nat) (nL nR : ProperNode),
      run.coordinateProper.nodes[mL]? = some nL ∧
      run.coordinateProper.nodes[mR]? = some nR ∧
      nL.node.border = -1 ∧ nR.node.border = 1 ∧
      nL.node.clusterPath.getLast? = some nt.decl ∧
      nR.node.clusterPath.getLast? = some nt.decl ∧
      (nR.node.loopExtent : Int) ≥
        (if run.exact.contains t then Loops.exactExtent cg.slot (loopSizes cg.edges labels t cg.slot)
         else Loops.extent cg.slot (loopSizes cg.edges labels t cg.slot)) ∧
      (∀ {layer : List Nat}, layer ∈ run.layers → ∀ {pu : Nat}, layer[pu]? = some t →
        ∃ jR : Nat, layer[jR]? = some mR) ∧
      (∀ {q : Nat} {nd : ProperNode}, run.proper.nodes[q]? = some nd →
        nd.node.clusterPath.getLast? = some nt.decl →
        ((nd.node.border = -1 →
          RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mL ∧
          RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
            RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL) ∧
        (nd.node.border = 1 →
          RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mR ∧
          RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
            RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR))) ∧
      RouteImpl.leftOf run.proper run.xs mL ≤ RouteImpl.leftOf run.proper run.xs mR ∧
      RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL ≤
        RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ∧
      0 ≤ RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ∧
      ∀ {b : Nat} {actualB : ProperNode}, run.coordinateProper.nodes[b]? = some actualB →
        ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) →
        ∀ {layer : List Nat}, layer ∈ run.layers →
        ∀ {j iv : Nat}, layer[j]? = some mR → layer[iv]? = some b → j < iv →
        Int.fdiv (nR.node.w + 2 * (nR.node.loopExtent : Int)) 2 +
          Int.fdiv (actualB.node.w + 2 * (actualB.node.loopExtent : Int)) 2 + 1 ≤
          run.coordinateXs.getD b 0 - run.coordinateXs.getD mR 0

/-- The extended footprint starts at the owner frame's right edge and has
nonnegative width in both sizing branches. Copy of `XLEML_fp_self_edges`
without the plain frame equation: the frame is kept as is. -/
private theorem XLEG_fp_edges {cg : Graph} {run : Run} {labels : List MeasuredLabel}
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
same border and height in the coordinate run. Copy of the border/height half
of `Xb_fbs` (`ExactFlatC5Bottom.lean`); private lemmas do not resolve across
modules. -/
private theorem XLEG_proper_coord {P : Params} {exact : List Nat} {cg : Graph}
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

/-- Exact proper nodes transfer unchanged for non-proxy borders. Copy of
`XBbs_nonproxy_record` (`ExactBorderSpanRunFactsProof.lean`); private lemmas
do not resolve across modules. -/
private theorem XLEG_nonproxy_record {P : Params} {exact : List Nat}
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
`±1`). -/
private theorem XLEG_appended_nonproxy {P : Params} {exact : List Nat} {labeled : Proper}
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
/-- Proxy proper nodes have height zero: transfer the `±2` border back
through the coordinate phases to the labeled record, read the marker record,
and transport the cleared height to the proper node. -/
private theorem XLEG_proxy_h_zero {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp)
    {node : Node} (hnode : cg.nodes[v]? = some node)
    (hb : nvp.node.border = -2 ∨ nvp.node.border = 2) :
    RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨nvc, hcoordV, hbV, hhV⟩ := XLEG_proper_coord h hrec
  have hcoordV0 := hcoordV
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec h
  have hrec0 : labeled.nodes[v]? = some ⟨node, false, none, false⟩ :=
    addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  have hltL : v < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hrec0).1
  have hszLen : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
    unfold sizeProperPortsX
    simp
  have hpre : v < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
    omega
  rw [← hc] at hcoordV
  unfold coordinateGraphX at hcoordV
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
  obtain ⟨extra, hx, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  rw [hx, List.getElem?_append_left hpre] at hm2
  rw [titleReservations_nodes, List.getElem?_append_left (by simpa [hszLen] using hltL)] at hm2
  obtain ⟨m3, hm3, htm⟩ : ∃ m,
      (sizeProperPortsX P exact labeled).nodes[v]? = some m ∧ titleF m = m2 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm2)
  have hb3 : m3.node.border = m2.node.border := by
    have h := (titleF_keys m3).2.1
    rw [htm] at h
    exact h.symm
  have hkey := sizeProperPortsX_key P exact labeled v
  rw [hm3, hrec0] at hkey
  have hnb : node.border = nvc.node.border := by
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
    obtain ⟨_, hb4, _⟩ := hkey
    omega
  have hn2 : node.border = -2 ∨ node.border = 2 := by
    have : nvc.node.border = -2 ∨ nvc.node.border = 2 := by rw [hbV]; exact hb
    omega
  have hmark := X_coordinateGraph_marker_record (P := P) (exact := exact) hrec0 hn2 rfl
  rw [hc] at hmark
  have hinj : clearF (titleF ⟨node, false, none, false⟩) = nvc :=
    Option.some.inj (hmark.symm.trans hcoordV0)
  have hz : (clearF (titleF ⟨node, false, none, false⟩)).node.h = 0 :=
    (clearF_keys _).2.2.2.trans ((titleF_keys _).2.2.2 hn2)
  have hnvc0 : nvc.node.h = 0 := hinj ▸ hz
  have hnvp : nvp.node.h = 0 := by omega
  have hH : RouteImpl.nodeH run.proper v = nvp.node.h := by simp [RouteImpl.nodeH, hrec]
  rw [hH]
  exact hnvp

/-- A zero-height inner rect meets no footprint interior. Mirror of
`XCapFb_degenerateHeight_noMeet` with the degeneracy on the box side. -/
private theorem XLEG_inner_zero_noMeet (a b : Rect) (hh : b.h = 0) :
    ¬ a.meetsInterior b := by
  simp only [Rect.meetsInterior]
  omega

/-- A recorded non-marker index is never a group-top position of the exact
candidate graph. Copy of `lrt_no_group_at_b` over `componentRunX`, using the
exact titled/marker records. -/
private theorem XLEG_no_group_at_b {P : Params} {exactIds : List String} {inp : Input}
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
Run-free copy of `lrt_frameB_x`: only the proper record and the candidate
border fact are used. -/
private theorem XLEG_frameB_x {P : Params} {cg : Graph} {run : Run}
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
the marker belongs to the hull. Copy of `lgr_group_of_markers`' hull half
(`lrt_hull_eq_of_pair`); the alignment and cross order come from the
witness. -/
private theorem XLEG_hull_eq {cg : Graph} {run : Run}
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
The marker extent, hull equality, and executed separation are premises; the
cluster replay they replace stays in the witness. -/
private theorem XLEG_top_reservation {P : Params} {exact : List Nat} {cg : Graph}
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
    XLEG_frameB_x hproperB hGb
  have hw : ∀ l ∈ loopSizes cg.edges labels t cg.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hFp := XLEG_fp_edges (cg := cg) (run := run) (labels := labels) (t := t)
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

end PipelineImpl
end Layered

end Elegant
