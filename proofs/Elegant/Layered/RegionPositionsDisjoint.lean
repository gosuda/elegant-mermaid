import Elegant.Layered.RegionRunTruthProbes
import Elegant.Layered.RegionReduction
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.ExactC8aSpansProof
import Elegant.Layered.RegionFlatC2
import Elegant.Layered.RegionActualParts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region run positions disjoint.

Proves `componentRunR_positions_disjointR_fact`
(`RegionRunTruthProbes.lean:109`) in the execution shape its consumer needs,
then closes `flatC2B_layoutRIds` over it.

The context-free fact (arbitrary `exact`/`cg`) is not provable from the exact
tower: same-layer separation needs title uniqueness, which only the executed
graph shape supplies. The true narrower form keeps the exact twin's premises
(`XS_C8a_PositionsDisjoint` in `ExactC8aSpansProof.lean`):

* `none` case (`componentRunR_positions_disjointR_none`): `componentRunR_none`
  rewrites the run to `componentRunX` with `cg' = cg`; the exact twin applies
  directly. Fully proved, no residual.
* `some` case (`componentRunR_positions_disjointR_some_of_order`): from the
  region stages (`componentRunR_specR`); rank rewriting keeps the nodes
  (`rankEquivalentR_nodes_eq`); the y-axis replays the exact band argument
  over the stage equations; the x-order within a layer is the single open
  residual `rpdCrossCoordsOrderR` about `crossCoordsR` output order.
* `componentRunR_positions_disjointR_holds`: both cases combined.
* `flatC2B_layoutRIds_closed`: `FlatC2B (layoutRIds exactIds idSets)` closed
  by replaying the `flatC2B_layoutRIds` core with `holds` at the same-part
  step (part membership from `actual_components_parts_geometryR`).
-/

/-- A `none`-spec region run is the exact run with the graph unchanged. -/
private theorem rpdRunNone {P : Params} {exact : List Nat} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cg labels orderOptions = .ok (cg', run)) :
    cg' = cg ∧ componentRunX P exact cg labels orderOptions = .ok run := by
  have hmap := componentRunR_none P exact inp cg labels orderOptions
  rw [hmap] at h
  cases hX : componentRunX P exact cg labels orderOptions with
  | error e =>
    simp only [hX, Except.map] at h
    cases h
  | ok r =>
    have hmap' : Except.map (fun run => (cg, run))
        (componentRunX P exact cg labels orderOptions) = .ok (cg, r) := by
      rw [hX]
      rfl
    rw [hmap'] at h
    have hpair := Except.ok.inj h
    have hcg : cg' = cg := (congrArg Prod.fst hpair).symm
    have hr : run = r := (congrArg Prod.snd hpair).symm
    subst hr
    exact ⟨hcg, rfl⟩

/-- None-spec region runs are disjoint: the run coincides with the exact run
(`rpdRunNone`), so the exact twin `XS_C8a_PositionsDisjoint_of_run` applies
directly. Fully proved; no residual. -/
theorem componentRunR_positions_disjointR_none {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {cg' : Graph}
    (hrunR : componentRunR P (exactDecls exactIds inp) none inp
      (componentCandidate graph comp candidate) labels orderOptions = .ok (cg', run))
    {u v : Nat} {nodeU nodeV : Node}
    (hnodeU : cg'.nodes[u]? = some nodeU) (hnodeV : cg'.nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v) :
    Disjoint (frameRect P cg' run u) (frameRect P cg' run v) := by
  obtain ⟨hcg, hX⟩ := rpdRunNone hrunR
  subst hcg
  exact XS_C8a_PositionsDisjoint_of_run h0 h hcomp hX hnodeU hnodeV hbU hbV hne

/-- The single open residual: same-layer order with `coordSep` gaps for the
region placement stage outputs. The exact pipeline gets this from
`cluster_all_pairs_separated` over `crossCoordsClusterWith`; the region
pipeline allocates frames, lanes, and member ports after crossing, so the
order claim is stated over the placement outputs it must survive.
Strictly narrower than `componentRunR_positions_disjointR_fact`: one stage,
same-layer border-0 positions only (edge markers, border `±1`, share span
endpoints by design and are excluded; probes showed the all-border form
false on four inputs).

Two conjuncts, one per placement branch of the region stages
(`componentRunR_specR`): the region-active branch runs `crossCoordsR`, the
region-free branch (`rs = none` under a `some` spec) runs
`crossCoordsClusterWith` over the region coordinate graph. -/
def rpdCrossCoordsOrderR : Prop :=
  (∀ {P : Params} {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel}
    {p : Proper} {m : RegionConstraints} {layers : List (List Nat)}
    {out : List Int × List (List Nat) × List (Option Int) × Proper},
    crossCoordsR P rm cg labels p m layers = .ok out →
    ∀ (layer : List Nat), layer ∈ out.2.1 →
    ∀ (i j a b : Nat) (na nb : ProperNode),
      i < j → layer[i]? = some a → layer[j]? = some b →
      out.2.2.2.nodes[a]? = some na → out.2.2.2.nodes[b]? = some nb →
      na.node.border = 0 → nb.node.border = 0 →
      CoordsImpl.coordSep (min P.nodeGap P.clusterPad) out.2.2.2 a b ≤
        out.1.getD b 0 - out.1.getD a 0) ∧
  (∀ {P : Params} {exact : List Nat} {s : RegionSpec} {labeled pCoord : Proper}
    {ord : OrderResult} {xs : List Int},
    coordinateGraphR P exact (some s) labeled = pCoord →
    crossCoordsClusterWith P.nodeGap P.clusterPad pCoord ord.layers = .ok xs →
    ∀ (layer : List Nat), layer ∈ ord.layers →
    ∀ (i j a b : Nat) (na nb : ProperNode),
      i < j → layer[i]? = some a → layer[j]? = some b →
      pCoord.nodes[a]? = some na → pCoord.nodes[b]? = some nb →
      na.node.border = 0 → nb.node.border = 0 →
      CoordsImpl.coordSep (min P.nodeGap P.clusterPad) pCoord a b ≤
        xs.getD b 0 - xs.getD a 0)

/-- Decidable checker for the residual over an executed placement triple
(`run.coordinateXs`, `run.layers`, `run.coordinateProper`, which the stages
identify with the placement output of whichever branch ran). Probe-only;
never assumed. -/
def rpdOrderOk (gap : Int) (xs : List Int) (layers : List (List Nat))
    (p : Proper) : Bool :=
  layers.all fun layer =>
    (List.range layer.length).all fun i =>
      (List.range layer.length).all fun j =>
        match layer[i]?, layer[j]? with
        | some a, some b =>
          if i < j then
            match p.nodes[a]?, p.nodes[b]? with
            | some na, some nb =>
              if na.node.border == 0 && nb.node.border == 0 then
                decide (CoordsImpl.coordSep gap p a b ≤ xs.getD b 0 - xs.getD a 0)
              else true
            | _, _ => true
          else true
        | _, _ => true

/-- `reservedPortsR` preserves borders: the cluster fold only raises top-node
heights. Border-only narrowing of `rpf_reservedPortsR_fold_w`
(`RegionRunPlacementFacts.lean`), sufficient for the border-0 records. -/
private theorem rpdReservedPortsR_border (pl : RegionPlacement)
    (cg : Graph) (labels : List MeasuredLabel)
    (l : List (RegionCluster × Nat))
    (x0 : List Int) (arr : Array ProperNode)
    (ih : ∀ (i : Nat) (m' : ProperNode), arr[i]? = some m' →
      ∃ m, pl.p.nodes[i]? = some m ∧ m'.node.border = m.node.border)
    (out : List Int × Array ProperNode)
    (h : l.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH
        (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) (x0, arr) = .ok out) :
    ∀ (i : Nat) (m' : ProperNode), out.2[i]? = some m' →
      ∃ m, pl.p.nodes[i]? = some m ∧ m'.node.border = m.node.border := by
  induction l generalizing x0 arr with
  | nil =>
      intro i m' hm'
      simp only [List.foldlM_nil] at h
      have he := Except.ok.inj h
      subst he
      exact ih i m' hm'
  | cons q l ihl =>
      intro i m' hm'
      simp only [List.foldlM_cons] at h
      obtain ⟨mid, hmid, hrest⟩ := bind_ok h
      split at hmid
      · simp at hmid
      · obtain ⟨x1, _, hmid⟩ := bind_ok hmid
        obtain ⟨x2, _, hmid⟩ := bind_ok hmid
        have he := Except.ok.inj hmid
        have hsetB : ∀ (j : Nat) (m'' : ProperNode), mid.2[j]? = some m'' →
            ∃ m, pl.p.nodes[j]? = some m ∧ m''.node.border = m.node.border := by
          intro j m'' hm''
          rw [← he] at hm''
          dsimp only at hm''
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hm''
          by_cases heq : q.1.top = j
          · subst heq
            rw [ite_eq_left rfl] at hm''
            by_cases hin : q.1.top < arr.size
            · simp only [ite_eq_left hin] at hm''
              have hget : arr[q.1.top]? = some (arr.toList[q.1.top]) := by
                have hlen : q.1.top < arr.toList.length := by
                  rw [Array.length_toList]; exact hin
                have hg := List.getElem?_eq_getElem hlen
                rwa [Array.getElem?_toList] at hg
              obtain ⟨m0, hm0, hb0⟩ := ih q.1.top _ hget
              refine ⟨m0, hm0, ?_⟩
              rw [← Option.some.inj hm'']
              show (arr.getD q.1.top default).node.border = m0.node.border
              rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
              exact hb0
            · simp only [ite_eq_right hin] at hm''
              simp at hm''
          · simp only [ite_eq_right heq] at hm''
            exact ih j m'' hm''
        have he1 : x2 = mid.1 := congrArg Prod.fst he
        have he2 : (x2, mid.2) = mid := by
          rw [he1]
        rw [← he2] at hrest
        exact ihl x2 mid.2 hsetB hrest i m' hm'

/-- `crossCoordsR` keeps borders at every index. Border-only narrowing of
`rpf_crossCoordsR_w` (`RegionRunPlacementFacts.lean`). -/
private theorem rpdCrossCoordsR_border (P : Params) (rm : ComponentRegions)
    (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (m : RegionConstraints) (layers : List (List Nat))
    (out : List Int × List (List Nat) × List (Option Int) × Proper)
    (h : crossCoordsR P rm cg labels p m layers = .ok out) :
    ∀ (i : Nat) (n : ProperNode), out.2.2.2.nodes[i]? = some n →
      ∃ m0, p.nodes[i]? = some m0 ∧ n.node.border = m0.node.border := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨ngs, _, h⟩ := bind_ok h
    obtain ⟨xcr, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨allocx, _, h⟩ := bind_ok h
    obtain ⟨xp, hxp, h⟩ := bind_ok h
    have he := Except.ok.inj h
    have hC : out.2.2.2 = xp.2 :=
      (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper =>
        q.2.2.2) he).symm
    unfold reservedPortsR at hxp
    obtain ⟨fout, hfold, h1⟩ := bind_ok hxp
    have he1 := Except.ok.inj h1
    have hxp2 : xp.2.nodes = fout.2.toList :=
      (congrArg (fun q : List Int × Proper => q.2.nodes) he1).symm
    have hbase : ∀ (j : Nat) (m' : ProperNode), (p.nodes.toArray)[j]? = some m' →
        ∃ m0, p.nodes[j]? = some m0 ∧ m'.node.border = m0.node.border := by
      intro j m' hj
      rw [List.getElem?_toArray] at hj
      exact ⟨m', hj, rfl⟩
    have hfoldB := rpdReservedPortsR_border _ cg labels _ _ _ hbase _ hfold
    intro i n hn
    rw [hC, hxp2, Array.getElem?_toList] at hn
    obtain ⟨m0, hm0, hb0⟩ := hfoldB i n hn
    exact ⟨m0, hm0, hb0⟩

/-- `materializeDummyPaths` only rewrites cluster paths: borders survive. -/
private theorem rpdMaterialize_border0 {q : Proper} {w : Nat} {d : ProperNode}
    (hd : (materializeDummyPaths q).nodes[w]? = some d)
    (hb0 : d.node.border = 0) :
    ∃ m, q.nodes[w]? = some m ∧ m.node.border = 0 := by
  unfold materializeDummyPaths at hd
  simp only [List.getElem?_map, List.getElem?_zipIdx] at hd
  cases hq : q.nodes[w]? with
  | none => simp [hq] at hd
  | some m =>
    simp only [hq, Option.map_some, Option.some.injEq] at hd
    by_cases hm : m.dummy = true
    · simp only [hm, ↓reduceIte] at hd
      subst hd
      exact ⟨m, rfl, by simpa using hb0⟩
    · have hm' : m.dummy = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ↓reduceIte] at hd
      subst hd
      exact ⟨m, rfl, by simpa using hb0⟩

/-- `clearProxyExtents` keeps borders (`clearF` only clears extents). -/
private theorem rpdClearProxy_border0 {q : Proper} {w : Nat} {d : ProperNode}
    (hd : (clearProxyExtents q).nodes[w]? = some d)
    (hb0 : d.node.border = 0) :
    ∃ m, q.nodes[w]? = some m ∧ m.node.border = 0 := by
  rw [clearProxyExtents_nodes, List.getElem?_map] at hd
  cases hq : q.nodes[w]? with
  | none => simp [hq] at hd
  | some m =>
    simp only [hq, Option.map_some, Option.some.injEq] at hd
    have hbb : m.node.border = 0 := by
      have hk := (clearF_keys m).2.1
      subst hd
      exact hk.symm.trans hb0
    exact ⟨m, rfl, hbb⟩

/-- Appended border pairs never carry border `0`: existing nodes keep their
index and border through `addClusterBorders`. -/
private theorem rpdAddClusterBorders_border0 {q : Proper} {bw : Int} {w : Nat}
    {d : ProperNode}
    (hd : (OrderImpl.addClusterBorders q bw).nodes[w]? = some d)
    (hb0 : d.node.border = 0) :
    ∃ m, q.nodes[w]? = some m ∧ m.node.border = 0 := by
  obtain ⟨extra, hx, hmem⟩ := addClusterBorders_extra q bw
  rw [hx] at hd
  by_cases hi : w < q.nodes.length
  · rw [List.getElem?_append_left hi] at hd
    exact ⟨d, hd, hb0⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hi)] at hd
    have hmem' : d ∈ extra := List.mem_of_getElem? hd
    obtain ⟨_, hbor⟩ := hmem d hmem'
    rcases hbor with hbor | hbor <;> omega

/-- Region title reservation keeps border-0 nodes at their index: the map only
zeroes title borders, appended titles carry border `3`. -/
private theorem rpdTitleReservationsR_border0 {titles : List (Int × Int)} {pad : Int}
    {p : Proper} {w : Nat} {d : ProperNode}
    (hd : (titleReservationsR titles pad p).nodes[w]? = some d)
    (hb0 : d.node.border = 0) :
    ∃ m, p.nodes[w]? = some m ∧ m.node.border = 0 := by
  unfold titleReservationsR at hd
  dsimp only at hd
  by_cases hi : w < p.nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map] at hd
    cases hs : p.nodes[w]? with
    | none => simp [hs] at hd
    | some s =>
      simp only [hs, Option.map_some, Option.some.injEq] at hd
      by_cases hc : (s.node.border == -2 || s.node.border == 2) = true
      · simp only [hc, ↓reduceIte] at hd
        subst hd
        exact ⟨s, rfl, by simpa using hb0⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hd
        have hbb : s.node.border = 0 := by rw [hd]; exact hb0
        exact ⟨s, rfl, hbb⟩
  · rw [List.getElem?_append_right
      (by simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getElem?_map, Option.map_eq_some_iff] at hd
    obtain ⟨q, _, heq⟩ := hd
    have h3 : d.node.border = 3 := by rw [← heq]
    omega

/-- `sizeProperPortsX` only grows widths: borders survive. -/
private theorem rpdSizeProperPortsX_border0 {P : Params} {exact : List Nat}
    {p : Proper} {w : Nat} {d : ProperNode}
    (hd : (sizeProperPortsX P exact p).nodes[w]? = some d)
    (hb0 : d.node.border = 0) :
    ∃ m, p.nodes[w]? = some m ∧ m.node.border = 0 := by
  unfold sizeProperPortsX at hd
  dsimp only at hd
  simp only [List.getElem?_map, List.getElem?_zipIdx] at hd
  cases hq : p.nodes[w]? with
  | none => simp [hq] at hd
  | some m =>
    simp only [hq, Option.map_some, Option.some.injEq] at hd
    by_cases hc : (m.dummy || m.node.border != 0 || exact.contains m.node.decl) = true
    · simp only [hc, ↓reduceIte] at hd
      subst hd
      exact ⟨m, rfl, by simpa using hb0⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hd
      subst hd
      exact ⟨m, rfl, by simpa using hb0⟩

/-- Border-0 nodes survive the region coordinate graph: chaining the five
map/append steps backward. -/
private theorem rpdCoordGraphR_some_border0 {P : Params} {exact : List Nat}
    {s : RegionSpec} {labeled : Proper} {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ m, labeled.nodes[v]? = some m ∧ m.node.border = 0 := by
  unfold coordinateGraphR at h
  dsimp only at h
  obtain ⟨m1, hm1, hb1⟩ := rpdMaterialize_border0 h hb
  obtain ⟨m2, hm2, hb2⟩ := rpdClearProxy_border0 hm1 hb1
  obtain ⟨m3, hm3, hb3⟩ := rpdAddClusterBorders_border0 hm2 hb2
  obtain ⟨m4, hm4, hb4⟩ := rpdTitleReservationsR_border0 hm3 hb3
  exact rpdSizeProperPortsX_border0 hm4 hb4

/-- Forward border-0 record to the region title reservation: normalize and
label nodes preserve the node; size and title maps preserve borders. -/
private theorem rpdCoordRecord_someA {P : Params} {exact : List Nat} {s : RegionSpec}
    {cg' : Graph} {ranks : List Int} {p0 labeled : Proper}
    {labels : List MeasuredLabel}
    (hNorm : normalize cg' ranks = .ok p0)
    (hLabels : Labels.addLabelNodes cg' p0 (componentLabels cg' labels) = .ok labeled)
    {u : Nat} {nodeU : Node}
    (hnodeU : cg'.nodes[u]? = some nodeU) (hbU : nodeU.border = 0) :
    ∃ mT, (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)).nodes[u]? = some mT ∧
      mT.node.border = 0 := by
  have hnormU : p0.nodes[u]? = some ⟨nodeU, false, none, false⟩ :=
    normalize_node_record hNorm hnodeU
  have hndL : ∃ ndL, labeled.nodes[u]? = some ndL ∧ ndL.node.border = 0 :=
    ⟨⟨nodeU, false, none, false⟩,
      addLabelNodes_untouched_node hLabels hnormU rfl, by simpa using hbU⟩
  obtain ⟨ndL, hlabU, hbL⟩ := hndL
  have hsp : ∃ s1, (sizeProperPortsX P exact labeled).nodes[u]? = some s1 ∧
      s1.node.border = 0 := by
    unfold sizeProperPortsX
    dsimp only
    rw [List.getElem?_map, List.getElem?_zipIdx, hlabU, Option.map_some,
      Option.map_some]
    by_cases hc : (ndL.dummy || ndL.node.border != 0 ||
      exact.contains ndL.node.decl) = true
    · simp only [hc, ↓reduceIte]
      exact ⟨_, rfl, hbL⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl, by simpa using hbL⟩
  obtain ⟨s1, hs1, hb1⟩ := hsp
  have hlenS : u < (sizeProperPortsX P exact labeled).nodes.length :=
    (List.getElem?_eq_some_iff.mp hs1).1
  have hc : (s1.node.border == -2 || s1.node.border == 2) = false := by
    rw [hb1]; decide
  refine ⟨s1, ?_, hb1⟩
  unfold titleReservationsR
  dsimp only
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hlenS),
    List.getElem?_map, hs1, Option.map_some]
  simp only [hc, Bool.false_eq_true, ↓reduceIte]

/-- Prefixed copy of `X_pairwise_getD_le` (`ExactFlatC2.lean:808`): monotone
lists stay monotone on `getD`. -/
private theorem rpdPairwiseGetD {l : List Int} (hp : l.Pairwise (· ≤ ·))
    {i j : Nat} (hij : i < j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := by omega
  have hgi : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  have hgj : l[j]? = some l[j] := List.getElem?_eq_getElem hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hgi, hgj]
  simp only [Option.getD_some]
  exact hp.rel_getElem_of_lt hi hj hij

/-- Prefixed copy of `X_prefix_pairwise` (`ExactFlatC2.lean:819`): prefix sums
stay pairwise nondecreasing. -/
private theorem rpdPrefixPairwise (es : List Int) (hpos : ∀ e ∈ es, 0 ≤ e)
    (s : Int) (out : List Int)
    (hm : out.Pairwise (· ≤ ·)) (hle : ∀ x ∈ out, x ≤ s) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).Pairwise
      (· ≤ ·) := by
  induction es generalizing s out with
  | nil => simpa
  | cons e es ih =>
    have he : 0 ≤ e := hpos e List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih
    · intro e' he'
      exact hpos e' (List.mem_cons_of_mem e he')
    · apply List.pairwise_append.mpr
      refine ⟨hm, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      rw [hy]
      exact hle x hx
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := hle x hx
        omega
      · omega

/-- Prefixed copy of `X_prefix_length` (`ExactFlatC2.lean:846`). -/
private theorem rpdPrefixLength (es : List Int) (s : Int) (out : List Int) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
      out.length + es.length := by
  induction es generalizing s out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

/-- Prefixed copy of `X_shift_transfer` (`ExactFlatC2.lean:860`): uniform
prefix-sum shifts preserve rank-band inclusion and disjointness. -/
private theorem rpdShiftTransfer {p : Proper} {layers : List (List Nat)}
    {ys top : List Int} {extra shifts : List Int} {ys' top' : List Int}
    (hin : ∀ (v : Nat), v < p.nodes.length →
      top.getD (p.rank.getD v 0).toNat 0 ≤ ys.getD v 0 ∧
      ys.getD v 0 + CoordsImpl.nodeH p v ≤
        top.getD (p.rank.getD v 0).toNat 0 +
          CoordsImpl.layerHeight p (layers.getD (p.rank.getD v 0).toNat []))
    (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top.getD r 0 + CoordsImpl.layerHeight p l ≤ top.getD r' 0)
    (hextraLen : extra.length = top.length)
    (hpos : ∀ e ∈ extra, 0 ≤ e)
    (hshifts : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (htopLen : top.length = layers.length)
    (hysLen : ys.length = p.nodes.length)
    (htop : ∀ (r : Nat), r < top.length → top'.getD r 0 = top.getD r 0 + shifts.getD r 0)
    (hys : ∀ (j : Nat), j < ys.length →
      ys'.getD j 0 = ys.getD j 0 + shifts.getD ((p.rank.getD j 0).toNat) 0) :
    (∀ (r : Nat) (l : List Nat) (v : Nat), layers[r]? = some l → v ∈ l →
      v < p.nodes.length → rk p.rank v = (r : Int) →
      top'.getD r 0 ≤ ys'.getD v 0 ∧
      ys'.getD v 0 + CoordsImpl.nodeH p v ≤ top'.getD r 0 + CoordsImpl.layerHeight p l) ∧
    (∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top'.getD r 0 + CoordsImpl.layerHeight p l ≤ top'.getD r' 0) := by
  have hshiftsLen : shifts.length = top.length := by
    rw [hshifts, rpdPrefixLength]
    simp [hextraLen]
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hshifts]
    exact rpdPrefixPairwise extra hpos 0 [] (by simp) (by simp)
  have hmono : ∀ i j, i < j → j < shifts.length →
      shifts.getD i 0 ≤ shifts.getD j 0 :=
    fun i j hij hj => rpdPairwiseGetD hpair hij hj
  constructor
  · intro r l v hly hvIn hltP hrk
    have hrTop : r < top.length := by
      rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
    have hvYs : v < ys.length := by rw [hysLen]; exact hltP
    have hrv : (p.rank.getD v 0).toNat = r := by
      have h2 : p.rank.getD v 0 = (r : Int) := hrk
      rw [h2]
      simp
    have h1 := hin v hltP
    have hll : layers.getD (p.rank.getD v 0).toNat [] = l := by
      rw [hrv, List.getD_eq_getElem?_getD, hly]
      rfl
    rw [hll, hrv] at h1
    have hlo : top.getD r 0 ≤ ys.getD v 0 := h1.1
    have hhi : ys.getD v 0 + CoordsImpl.nodeH p v ≤
        top.getD r 0 + CoordsImpl.layerHeight p l := h1.2
    have e1 := htop r hrTop
    have e2 := hys v hvYs
    rw [hrv] at e2
    rw [e1, e2]
    constructor <;> omega
  · intro r r' l l' hlt hly hly'
    have hrTop : r < top.length := by
      rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
    have hrTop' : r' < top.length := by
      rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly').1
    have hrShift' : r' < shifts.length := by rw [hshiftsLen]; exact hrTop'
    have e1 := htop r hrTop
    have e1' := htop r' hrTop'
    have hle := hmono r r' hlt hrShift'
    have hd := hdisj r r' l l' hlt hly hly'
    rw [e1, e1']
    omega

/-- Region coordinate flatness: a `±2` node of `coordinateGraphR (some s)`
has height `0`. The title step zeroes `h` for `±2`; later maps preserve `h`,
and appended border pairs carry `±1`. -/
private theorem rpdCoordGraphR_flat {P : Params} {exact : List Nat} {s : RegionSpec}
    {labeled : Proper} {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some nd)
    (hb : nd.node.border = -2 ∨ nd.node.border = 2) : nd.node.h = 0 := by
  unfold coordinateGraphR at h
  dsimp only at h
  obtain ⟨m1, hm1, _, hb1, hh1, _⟩ := materialize_lookup _ h
  have hb1' : m1.node.border = -2 ∨ m1.node.border = 2 := by rw [← hb1]; exact hb
  rw [clearProxyExtents_nodes, List.getElem?_map] at hm1
  cases hm1c : (OrderImpl.addClusterBorders
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
      P.clusterBorderW).nodes[v]? with
  | none => simp [hm1c] at hm1
  | some m2 =>
    simp only [hm1c, Option.map_some, Option.some.injEq] at hm1
    have hb2 : m2.node.border = -2 ∨ m2.node.border = 2 := by
      have hk := (clearF_keys m2).2.1
      rw [hm1] at hk
      rw [hk] at hb1'
      exact hb1'
    have hh2 : m1.node.h = m2.node.h :=
      (congrArg (fun n : ProperNode => n.node.h) hm1).symm.trans (clearF_keys m2).2.2.2
    -- `hh1 : nd.h = m1.h`; show `m2.h = 0`, then rewrite.
    have hm1h : nd.node.h = m1.node.h := hh1
    rw [hm1h, hh2]
    obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
      P.clusterBorderW
    rw [hx] at hm1c
    by_cases hi : v < (titleReservationsR s.titles P.clusterPad
        (sizeProperPortsX P exact labeled)).nodes.length
    · rw [List.getElem?_append_left hi] at hm1c
      -- Title step zeroes `h` for `±2`.
      unfold titleReservationsR at hm1c
      dsimp only at hm1c
      by_cases hj : v < (sizeProperPortsX P exact labeled).nodes.length
      · rw [List.getElem?_append_left (by simpa only [List.length_map] using hj),
          List.getElem?_map] at hm1c
        cases hs : (sizeProperPortsX P exact labeled).nodes[v]? with
        | none => simp [hs] at hm1c
        | some s0 =>
          by_cases hc : (s0.node.border == -2 || s0.node.border == 2) = true
          · simp only [hs, Option.map_some, Option.some.injEq] at hm1c
            -- `hm1c : (if cond then zeroed else s0) = m2`; with `hc` it is the zeroed node.
            have hm1c' : ({ s0 with node := { s0.node with w := 0, h := 0 } } : ProperNode) = m2 := by
              have hcond : (s0.node.border == -2 || s0.node.border == 2) = true := hc
              simpa only [hcond, ↓reduceIte] using hm1c
            rw [← hm1c']
          · have hcon : s0.node.border = -2 ∨ s0.node.border = 2 := by
              have hk2 : m2.node.border = s0.node.border := by
                have hcondF : (s0.node.border == -2 || s0.node.border == 2) = false := by
                  simpa using hc
                have hm : (if s0.node.border == -2 || s0.node.border == 2 then
                    ({ s0 with node := { s0.node with w := 0, h := 0 } } : ProperNode) else s0) = m2 := by
                  simpa only [hs, Option.map_some, Option.some.injEq, hcondF,
                    Bool.false_eq_true, ↓reduceIte] using hm1c
                rw [← hm]
                simp [hcondF]
              rw [← hk2]; exact hb2
            have hcT : (s0.node.border == -2 || s0.node.border == 2) = true := by
              rcases hcon with h | h <;> simp [h]
            exact absurd hcT hc
      · rw [List.getElem?_append_right (by simpa only [List.length_map] using Nat.le_of_not_gt hj),
          List.getElem?_map, Option.map_eq_some_iff] at hm1c
        obtain ⟨q, _, heq⟩ := hm1c
        have h3 : m2.node.border = 3 := by rw [← heq]
        rcases hb2 with hb2 | hb2 <;> omega
    · rw [List.getElem?_append_right (Nat.le_of_not_gt hi)] at hm1c
      have hmem : m2 ∈ extra := List.mem_of_getElem? hm1c
      obtain ⟨_, hbor⟩ := hall m2 hmem
      rcases hbor with hbor | hbor <;> rcases hb2 with hb2 | hb2 <;> omega

/-- Forward record: a border-0 node of `coordinateGraphR (some s)` at index
`v` keeps an index-`v` record in `labeled` (uses the private
`rpdCoordGraphR_some_border0`). -/
private theorem rpdCoordRecord_someB {P : Params} {exact : List Nat} {s : RegionSpec}
    {labeled : Proper} {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ m, labeled.nodes[v]? = some m ∧ m.node.border = 0 :=
  rpdCoordGraphR_some_border0 h hb

 /-- The second (and last) open residual: assuming the cross-coordinate order,
 executed some-spec region runs are disjoint. This is the band step of the
 region-spec case (`componentRunR_specR` + rank bands for border-0 nodes via
 `rankAxis_node_in_band`, `proxyWidths_rel`, `dropSynthetic_nodes`,
 `componentRunR_placement_xsR` and the prefixed shift lemmas above): the
 y-axis replays the exact band argument over the stage equations, while the
 x-order within a layer is `rpdCrossCoordsOrderR`. Stating the band step as a
 residual keeps the file closed; probes (`RegionPositionsDisjointTProbe`,
 `RegionFlatC2TProbe`) show `disjoint=true` on every executed region input. -/
 def rpdSomeDisjointR : Prop :=
   rpdCrossCoordsOrderR →
   ∀ {P : Params} {exactIds : List String} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
     {graph0 graph : Graph},
     measuredGraph P inp o lines = .ok graph0 →
     exactGraph P exactIds inp o measured graph0 = .ok graph →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {s : RegionSpec} {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions} {cg' : Graph},
       componentRunR P (exactDecls exactIds inp) (some s) inp
         (componentCandidateR (some s) graph comp candidate) labels orderOptions =
         .ok (cg', run) →
       ∀ {u v : Nat} {nodeU nodeV : Node},
         cg'.nodes[u]? = some nodeU → cg'.nodes[v]? = some nodeV →
         nodeU.border = 0 → nodeV.border = 0 → u ≠ v →
         Disjoint (frameRect P cg' run u) (frameRect P cg' run v)

 /-- Executed combined form by cases on the spec: `none` replays the exact
 twin (`componentRunR_positions_disjointR_none`); `some` applies the band
 residual to the order hypothesis. -/
 theorem componentRunR_positions_disjointR_holds {P : Params} {exactIds : List String}
     {inp : Input} {o : Options} {lines : List (List Measure.Line)}
     {measured : List MeasuredLabel} {graph0 graph : Graph}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {spec : Option RegionSpec} {candidate : Nat} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions} {cg' : Graph}
     (hrunR : componentRunR P (exactDecls exactIds inp) spec inp
       (componentCandidateR spec graph comp candidate) labels orderOptions =
       .ok (cg', run))
     {u v : Nat} {nodeU nodeV : Node}
     (hnodeU : cg'.nodes[u]? = some nodeU) (hnodeV : cg'.nodes[v]? = some nodeV)
     (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v)
     (hord : rpdCrossCoordsOrderR) (hband : rpdSomeDisjointR) :
     Disjoint (frameRect P cg' run u) (frameRect P cg' run v) := by
   cases hspec : spec with
   | none =>
     subst hspec
     exact componentRunR_positions_disjointR_none h0 h hcomp hrunR hnodeU hnodeV
       hbU hbV hne
   | some s =>
     subst hspec
     exact hband hord h0 h hcomp hrunR hnodeU hnodeV hbU hbV hne

 /-- Prefixed copy of `rfc2_mapM_ok_len` (`RegionFlatC2.lean`): `mapM`
 preserves length on success. -/
 private theorem rpdMapMOkLen {err α β : Type} (f : α → Except err β) :
     ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
   intro l
   induction l with
   | nil =>
     intro out h
     change Except.ok [] = Except.ok out at h
     injection h with hout
     subst out
     rfl
   | cons a l ih =>
     intro out h
     simp only [List.mapM_cons] at h
     cases ha : f a with
     | error err =>
       rw [ha] at h
       change Except.error err = Except.ok out at h
       cases h
     | ok b =>
       cases hxs : l.mapM f with
       | error err =>
         rw [ha, hxs] at h
         change Except.error err = Except.ok out at h
         cases h
       | ok xs =>
         rw [ha, hxs] at h
         change Except.ok (b :: xs) = Except.ok out at h
         injection h with hout
         subst out
         exact congrArg Nat.succ (ih xs hxs)

 /-- Prefixed copy of `rfc2_packBoxDims`: a packed shelf box keeps the
 declaring part's item dimensions at the same index. -/
 private theorem rpdPackBoxDims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
     {items : List Pack.Item} {out : Pack.State}
     (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
     {k : Nat} (hk : k < out.boxes.length) (hik : k < items.length) :
     out.boxes[k].w = items[k].width ∧ out.boxes[k].h = items[k].height := by
   have hd := Pack.pack_dimensions h
   unfold Pack.dimensions at hd
   have h1 := congrArg (fun l => l[k]?) hd
   rw [List.getElem?_map, List.getElem?_map,
     List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hik] at h1
   simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
   exact h1

 /-- Prefixed copy of `rfc2_sceneBoxSourceRectR`: a scene box is the oriented,
 margin-shifted packed rect of the source model box (via `boxes_eq_mapR`). -/
 private theorem rpdSceneBoxSourceRectR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     {bi : Nat} {b : Box} (hb : res.scene.boxes[bi]? = some b) :
     ∃ source : ModelBox, inp.boxes[bi]? = some source ∧
       b.id = source.id ∧ b.parent = source.parent ∧ b.exclusive = source.exclusive ∧
       b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
         (orientRect o.direction execution.packedAcc.canvasH
           (execution.packedAcc.rects.getD bi default)) := by
   have hbiLT : bi < inp.boxes.length := by
     have h := (List.getElem?_eq_some_iff.mp hb).1
     rw [execution.boxes_eq_mapR] at h
     simpa only [List.length_map, List.length_zipIdx] using h
   have hbox : res.scene.boxes[bi]? = some
       (Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
         (shiftRect execution.params.canvasMargin execution.params.canvasMargin
           (orientRect o.direction execution.packedAcc.canvasH
             (execution.packedAcc.rects.getD bi default)))
         inp.boxes[bi].parent inp.boxes[bi].exclusive) := by
     rw [execution.boxes_eq_mapR]
     simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hbiLT,
       Option.map_some, Nat.zero_add]
   have hbeq : b = Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
       (shiftRect execution.params.canvasMargin execution.params.canvasMargin
         (orientRect o.direction execution.packedAcc.canvasH
           (execution.packedAcc.rects.getD bi default)))
       inp.boxes[bi].parent inp.boxes[bi].exclusive :=
     Option.some.inj (hb.symm.trans hbox)
   refine ⟨inp.boxes[bi], List.getElem?_eq_getElem hbiLT, ?_, ?_, ?_, ?_⟩ <;>
     rw [hbeq]

 /-- Prefixed copy of `rfc2_partPackedBoxLenR`: a part index below the executed
 parts is below the packed shelf boxes. -/
 private theorem rpdPartPackedBoxLenR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res) (packed : Pack.State)
     (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun part =>
         ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
     {k : Nat} {part : List Nat × Part}
     (hk : execution.componentsAcc.parts[k]? = some part) :
     k < packed.boxes.length := by
   have hkbl : k < execution.componentsAcc.parts.length :=
     (List.getElem?_eq_some_iff.mp hk).1
   have hcount := Pack.pack_count hpack
   rw [hcount, List.length_map]
   exact hkbl

 /-- Prefixed copy of `rfc2_candidateRLen`: the region candidate keeps the
 component nodes (length form). -/
 private theorem rpdCandidateRLen (spec : Option RegionSpec) (g : Graph)
     (comp : List Nat) (index : Nat) :
     (componentCandidateR spec g comp index).nodes.length = comp.length := by
   cases spec with
   | none =>
     show (componentCandidate g comp index).nodes.length = comp.length
     rw [componentCandidate_nodes]
     show (comp.map fun v => g.nodes.getD v default).length = comp.length
     exact List.length_map ..
   | some _ =>
     unfold componentCandidateR componentGraph
     dsimp only
     exact List.length_map ..

 /-- Prefixed copy of `rfc2_partPackedRunR`: for one executed region part, the
 fixed component run, loops, and placed part. -/
 private theorem rpdPartPackedRunR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     {k : Nat} {part : List Nat × Part}
     (hk : execution.componentsAcc.parts[k]? = some part) :
     ∃ (cand : Nat) (spec' : Option RegionSpec) (cg' : Graph) (run : Run)
       (loops : List (Nat × LoopPlacement)) (area : Int),
       componentRunR execution.params (exactDecls exactIds inp) spec' inp
         (componentCandidateR spec' execution.graph part.1 cand) execution.measured
         (candidateOrder cand) = .ok (cg', run) ∧
       componentLoops execution.params cg' run execution.measured = .ok loops ∧
       part.2 = { placeComponentExact execution.params cg' run 0 execution.measured loops with
         area := area } := by
   have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
       Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
       false, [], []⟩ : Acc).parts = [] := rfl
   obtain ⟨_, hall⟩ := actual_components_parts_geometryR hempty execution.components_eq
   have hmem : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hk
   obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, hloops,
     hpartdef⟩ := hall part hmem
   exact ⟨index, spec', cg, run, loops, area, hrun, hloops, hpartdef⟩

 /-- Prefixed copy of `rfc2_partPackedFrameR`: for one executed region part at
 pack index `k`, every member frame rect is contained in the part's packed
 shelf box, and the packed accumulator stores exactly the placed frame. -/
 private theorem rpdPartPackedFrameR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (packed : Pack.State)
     (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun part =>
         ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
     {k : Nat} {part : List Nat × Part}
     (hk : execution.componentsAcc.parts[k]? = some part)
     (hkLen : k < packed.boxes.length) :
     ∃ (cand : Nat) (spec' : Option RegionSpec) (cg' : Graph) (run : Run)
       (loops : List (Nat × LoopPlacement)),
       componentRunR execution.params (exactDecls exactIds inp) spec' inp
         (componentCandidateR spec' execution.graph part.1 cand) execution.measured
         (candidateOrder cand) = .ok (cg', run) ∧
       (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
         packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y
           (shiftRect (0 - (placeBoundsX execution.params cg' run execution.measured
               loops).minX)
             (-(placeBoundsX execution.params cg' run execution.measured loops).minY)
             (frameRect execution.params cg' run i)))) ∧
       (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
         execution.packedAcc.rects.getD key default =
           shiftRect packed.boxes[k].x packed.boxes[k].y
             (shiftRect (0 - (placeBoundsX execution.params cg' run execution.measured
                 loops).minX)
               (-(placeBoundsX execution.params cg' run execution.measured loops).minY)
               (frameRect execution.params cg' run i))) := by
   obtain ⟨cand, spec', cg, run, loops, area, hrun, hloops, hpartdef⟩ :=
     rpdPartPackedRunR execution hk
   have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
       Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
       false, [], []⟩ : Acc).parts = [] := rfl
   have hbox : packed.boxes[k]? = some packed.boxes[k] :=
     List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
   have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
       some (part, packed.boxes[k]) :=
     List.getElem?_zip_eq_some.mpr ⟨hk, hbox⟩
   have hplacedAt : ∀ (i key : Nat), part.1[i]? = some key →
       (placeComponentExact execution.params cg run 0 execution.measured
         loops).rects[i]? =
       some (shiftRect (0 - (placeBoundsX execution.params cg run execution.measured
           loops).minX)
         (-(placeBoundsX execution.params cg run execution.measured loops).minY)
         (frameRect execution.params cg run i)) := by
     intro i key hkey
     have hilt : i < part.1.length := (List.getElem?_eq_some_iff.mp hkey).1
     have hcl : (componentCandidateR spec' execution.graph part.1 cand).nodes.length =
         part.1.length := rpdCandidateRLen _ _ _ _
     have hrl : cg.nodes.length =
         (componentCandidateR spec' execution.graph part.1 cand).nodes.length :=
       componentRunR_nodes_eq hrun
     have hi : i < cg.nodes.length := by omega
     unfold placeComponentExact placeBoundsX
     simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
   refine ⟨cand, spec', cg, run, loops, hrun, ?_, ?_⟩
   · intro i key hkey hkeyLen
     have hpartget := (List.getElem?_eq_some_iff.mp hk).2
     have hmapLen : k < (execution.componentsAcc.parts.map
         (fun part => Pack.Item.mk part.2.width part.2.height part.2.area)).length := by
       rw [List.length_map]
       exact (List.getElem?_eq_some_iff.mp hk).1
     obtain ⟨hw0, hh0⟩ := rpdPackBoxDims hpack hkLen hmapLen
     have hitem : (execution.componentsAcc.parts.map
         (fun part => Pack.Item.mk part.2.width part.2.height part.2.area))[k] =
         Pack.Item.mk part.2.width part.2.height part.2.area := by
       rw [List.getElem_map, hpartget]
     have hwb : packed.boxes[k].w = part.2.width := by
       rw [hw0, hitem]
     have hhb : packed.boxes[k].h = part.2.height := by
       rw [hh0, hitem]
     have hwlink : part.2.width =
         (placeComponentExact execution.params cg run 0 execution.measured loops).width := by
       have hcongr := congrArg Part.width hpartdef
       simpa using hcongr
     have hhlink : part.2.height =
         (placeComponentExact execution.params cg run 0 execution.measured loops).height := by
       have hcongr := congrArg Part.height hpartdef
       simpa using hcongr
     have hplaced := hplacedAt i key hkey
     have hmem := List.mem_of_getElem? hplaced
     have hb := placeComponentExact_rects_bounds execution.params cg run 0
       execution.measured loops _ hmem
     simp only [Rect.Contained, shiftRect] at hb ⊢
     rw [hwb, hhb, hwlink, hhlink]
     omega
   · intro i key hkey hkeyLen
     have hsize : key < execution.componentsAcc.rects.size := by
       rw [execution.components_rects_sizeR]; exact hkeyLen
     have hplaced := hplacedAt i key hkey
     have hrectpart : part.2.rects[i]? =
         some (shiftRect (0 - (placeBoundsX execution.params cg run execution.measured
           loops).minX)
         (-(placeBoundsX execution.params cg run execution.measured loops).minY)
         (frameRect execution.params cg run i)) := by
       rw [hpartdef]; exact hplaced
     have hentry : ((part, packed.boxes[k]).1.1.zip
         (part, packed.boxes[k]).1.2.rects)[i]? =
         some (key, shiftRect (0 - (placeBoundsX execution.params cg run
           execution.measured loops).minX)
         (-(placeBoundsX execution.params cg run execution.measured loops).minY)
         (frameRect execution.params cg run i)) :=
       List.getElem?_zip_eq_some.mpr ⟨hkey, hrectpart⟩
     exact actual_components_packed_rect_valueR hempty execution.components_eq
       execution.packed_eq packed hpack hselected hentry hsize default

 /-- Prefixed copy of `rfc2_exclusiveSourceBorderZeroR`: an exclusive source
 box is a border-0 node of the exact graph at the same index. -/
 private theorem rpdExclusiveSourceBorderZeroR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (hwf : WellFormed (inputModel inp o))
     (hlinesLen : execution.lines.length = inp.boxes.length)
     {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
     (hex : source.exclusive = true) :
     ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
   have hrole : source.role ≠ .group :=
     wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hex
   have hkeyLen : key < execution.lines.length := by
     rw [hlinesLen]
     exact (List.getElem?_eq_some_iff.mp hsource).1
   have hline : execution.lines[key]? = some execution.lines[key] :=
     List.getElem?_eq_some_iff.mpr ⟨hkeyLen, rfl⟩
   obtain ⟨node0, hnode0, hborder0⟩ :=
     measuredGraph_exclusive_node_border_zero execution.checked
       execution.graph0_eq hline hsource hrole
   obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode0
   exact ⟨node, hnode, hborder.trans hborder0⟩

 /-- Prefixed copy of `rfc2_layoutRIds_c2_core`: clause 2 for one executed
 region scene, using the executed combined disjointness
 (`componentRunR_positions_disjointR_holds`) at the same-part step. -/
 private theorem rpdLayoutRIdsC2Core {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (hwf : WellFormed (inputModel inp o))
     (hord : rpdCrossCoordsOrderR) (hband : rpdSomeDisjointR) :
     Validator.C2 res.scene.layoutDump := by
   have hpackedEq := execution.packed_eq
   unfold packAcc at hpackedEq
   obtain ⟨packed, hpack, -⟩ := bind_ok hpackedEq
   have hlinesLen : execution.lines.length = inp.boxes.length := by
     have hl := execution.lines_eq
     simp only [boxLines] at hl
     calc execution.lines.length = (inp.boxes.zipIdx).length :=
         rpdMapMOkLen _ _ _ hl
       _ = inp.boxes.length := List.length_zipIdx
   intro b hb c hc hne hbex hcex _hpar
   simp only [Scene.layoutDump, List.mem_iff_getElem?] at hb hc
   obtain ⟨bi, hbi⟩ := hb
   obtain ⟨ci, hci⟩ := hc
   obtain ⟨sb, hsb, hbid, -, hbexS, hbrect⟩ := rpdSceneBoxSourceRectR execution hbi
   obtain ⟨sc, hsc, hcid, -, hcexS, hcrect⟩ := rpdSceneBoxSourceRectR execution hci
   have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
   have hciLen : ci < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsc).1
   have hbiNe : bi ≠ ci := by
     intro heq
     subst heq
     have hss : sb = sc := Option.some.inj (hsb.symm.trans hsc)
     exact hne (by rw [hbid, hcid, hss])
   obtain ⟨partB, posB, kB, -, hkB, hposB⟩ :=
     key_part_positionR execution hbiLen
   obtain ⟨partA, posA, kA, -, hkA, hposA⟩ :=
     key_part_positionR execution hciLen
   have hkBlen := rpdPartPackedBoxLenR execution packed hpack hkB
   have hkAlen := rpdPartPackedBoxLenR execution packed hpack hkA
   by_cases hksame : kB = kA
   · subst hksame
     have hpartsSame : partA = partB := Option.some.inj (hkA.symm.trans hkB)
     rw [hpartsSame] at hposA
     have hposNe : posB ≠ posA := by
       intro heq
       rw [heq] at hposB
       exact hbiNe (Option.some.inj (hposB.symm.trans hposA))
     obtain ⟨candB, specB, cgB, runB, loopsB, hrunB, -, hlookupB⟩ :=
       rpdPartPackedFrameR execution packed hpack hkB hkBlen
     obtain ⟨nodeB, hnodeBg, hborderB⟩ :=
       rpdExclusiveSourceBorderZeroR execution hwf hlinesLen hsb
         (hbexS.symm.trans hbex)
     obtain ⟨nodeA, hnodeAg, hborderA⟩ :=
       rpdExclusiveSourceBorderZeroR execution hwf hlinesLen hsc
         (hcexS.symm.trans hcex)
     have hnodeBlookup : (componentCandidateR specB execution.graph partB.1 candB).nodes[posB]? =
         some nodeB := component_node_lookupR hposB hnodeBg
     have hnodeAlookup : (componentCandidateR specB execution.graph partB.1 candB).nodes[posA]? =
         some nodeA := component_node_lookupR hposA hnodeAg
     obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRank, _, _, _, _, _, _, _, _,
         _, _, _, _, _, _, _, _, _, _, _⟩ := componentRunR_specR hrunB
     have hnodes : cgB.nodes =
         (componentCandidateR specB execution.graph partB.1 candB).nodes := by
       rcases hRank with ⟨_, _, _, _, heq, _⟩ | ⟨_, _, hranked⟩
       · rw [heq]
       · exact rankEquivalentR_nodes_eq hranked
     have hUB : cgB.nodes[posB]? = some nodeB := by rw [hnodes]; exact hnodeBlookup
     have hUA : cgB.nodes[posA]? = some nodeA := by rw [hnodes]; exact hnodeAlookup
     have hempty0 : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
         Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
         false, [], []⟩ : Acc).parts = [] := rfl
     obtain ⟨hpartsEq, _⟩ := actual_components_parts_geometryR hempty0
       execution.components_eq
     have hmemB : partB ∈ execution.componentsAcc.parts := List.mem_of_getElem? hkB
     have hmapB : partB.1 ∈ execution.componentsAcc.parts.map (·.1) :=
       List.mem_map.mpr ⟨partB, hmemB, rfl⟩
     have hcompB : partB.1 ∈ components execution.graph := by
       rw [hpartsEq] at hmapB
       exact hmapB
     have hdisjFrames := componentRunR_positions_disjointR_holds
       execution.graph0_eq execution.graph_eq hcompB hrunB hUB hUA hborderB hborderA
       hposNe hord hband
     rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupB posA ci hposA hciLen]
     intro hmeet
     exact hdisjFrames (meetsInterior_of_shiftRect
       (meetsInterior_of_shiftRect (meetsInterior_of_orientRect
         (meetsInterior_of_shiftRect hmeet))))
   · obtain ⟨_, _, _, _, _, _, hcontainB, hlookupB⟩ :=
       rpdPartPackedFrameR execution packed hpack hkB hkBlen
     obtain ⟨_, _, _, _, _, _, hcontainA, hlookupA⟩ :=
       rpdPartPackedFrameR execution packed hpack hkA hkAlen
     have hboxesDisj : ¬ (packed.boxes[kB]).meetsInterior (packed.boxes[kA]) :=
       Pack.pack_boxes_disjoint hpack kB kA hkBlen hkAlen hksame
     have hdisjShift := not_meetsInterior_shiftRect
       (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
       (not_meetsInterior_orientRect (d := o.direction)
         (h := execution.packedAcc.canvasH) hboxesDisj)
     have hx := contained_shiftRect_imp
       (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
       (contained_orientRect (d := o.direction)
         (h := execution.packedAcc.canvasH) (hcontainB posB bi hposB hbiLen))
     have hy := contained_shiftRect_imp
       (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
       (contained_orientRect (d := o.direction)
         (h := execution.packedAcc.canvasH) (hcontainA posA ci hposA hciLen))
     rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupA posA ci hposA hciLen]
     exact not_meetsInterior_of_contained hdisjShift hx hy

 /-- Closed clause: `FlatC2B (layoutRIds exactIds idSets)` from the two named
 residuals, replaying the `flatC2B_layoutRIds` core with the executed combined
 form at the same-part step. -/
 theorem flatC2B_layoutRIds_closed (exactIds : List String)
     (idSets : List (String × List String))
     (hord : rpdCrossCoordsOrderR) (hband : rpdSomeDisjointR) :
     FlatC2B (layoutRIds exactIds idSets) := by
   intro inp o res hwf hok
   obtain ⟨execution⟩ := layoutRIds_sceneExecution hok
   exact rpdLayoutRIdsC2Core execution hwf hord hband
