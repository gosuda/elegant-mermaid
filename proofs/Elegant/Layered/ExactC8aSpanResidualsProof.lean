import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC5Bottom
import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ForeignClusterFactsProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.SizingFacts
import Elegant.Layered.Coords
import Elegant.Layered.CgShape
import Elegant.Layered.Labels
import Elegant.Layered.Normalize
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Order
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.Pipeline
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-- File-unique prefix for all private helpers in this module. -/
private theorem c8aR_toNat_le {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) :
    a.toNat ≤ b.toNat := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha h)
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by omega
  exact Int.ofNat_le.mp h3

/-- From `toNat` order to `Int` order (copy of `Xb_toNat_le_of_nonneg`). -/
private theorem c8aR_toNat_le_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.toNat ≤ b.toNat) : a ≤ b := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by exact_mod_cast h
  omega

/-- Exact titled ranks agree with labeled ranks below the labeled length. -/
private theorem c8aR_titled_rk_eq (P : Params) (exact : List Nat) (labeled : Proper)
    (j : Nat) (hj : j < labeled.nodes.length)
    (haligned : labeled.nodes.length = labeled.rank.length) :
    rk (titleReservations (sizeProperPortsX P exact labeled)).rank j =
      rk labeled.rank j := by
  have hlt : j < labeled.rank.length := by omega
  have hlook : labeled.rank[j]? = some labeled.rank[j] :=
    List.getElem?_eq_getElem hlt
  have htitled : (titleReservations (sizeProperPortsX P exact labeled)).rank[j]? =
      labeled.rank[j]? := by
    have hrank : (titleReservations (sizeProperPortsX P exact labeled)).rank =
        labeled.rank ++
          ((sizeProperPortsX P exact labeled).nodes.zipIdx.filter fun q =>
            q.1.node.border == -2).map (fun q => rk (sizeProperPortsX P exact labeled).rank q.2) := by
      unfold titleReservations
      simp only [sizeProperPortsX_rank]
    rw [hrank, List.getElem?_append_left hlt]
  simp only [rk, List.getD_eq_getElem?_getD, htitled, hlook, Option.getD_some]

/-- Exact coordinate ranks agree with labeled ranks below the labeled length. -/
private theorem c8aR_coord_rk_eq (P : Params) (exact : List Nat) (labeled : Proper)
    (j : Nat) (hj : j < labeled.nodes.length)
    (haligned : labeled.nodes.length = labeled.rank.length) :
    rk (coordinateGraphX P exact labeled).rank j = rk labeled.rank j := by
  have hlt : j < labeled.rank.length := by omega
  have hlook : labeled.rank[j]? = some labeled.rank[j] :=
    List.getElem?_eq_getElem hlt
  obtain ⟨extra, heq⟩ := (coordinateGraphX_anchor_prefix P exact labeled).2
  have hcoord : (coordinateGraphX P exact labeled).rank[j]? = labeled.rank[j]? := by
    rw [heq, List.getElem?_append_left hlt]
  simp only [rk, List.getD_eq_getElem?_getD, hcoord, hlook, Option.getD_some]

private theorem c8aR_proper_rk_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) (v : Nat)
    (hv : v < run.proper.nodes.length) : 0 ≤ rk run.proper.rank v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hok).2.2.2.1
  obtain ⟨_, _, _, hnn⟩ := hcov v hv
  exact hnn

/-- A candidate `-2` node ends its cluster path in its declaration (exact). -/
private theorem c8aR_top_getLast {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hb : uNode.border = -2) :
    uNode.clusterPath.getLast? = some uNode.decl := by
  obtain ⟨_, _, hpath⟩ := X_cg_group_box h0 h hu hb
  rw [hpath, List.getLast?_append]
  simp

/-- A titled `-2` anchor with the same path-last as the candidate top is the
candidate top index (exact replay of `titledTopPin`). -/
private theorem c8aR_titledTopPin {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {labeled : Proper}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩)
    {u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hbU : uNode.border = -2)
    {top : ProperNode × Nat}
    (htopMem : top ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx)
    (hbTop : top.1.node.border = -2)
    (hlastTop : top.1.node.clusterPath.getLast? = some uNode.decl) :
    top.2 = u := by
  have htopLookup : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htopMem
  have hrequested : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[u]? =
      some (titleF ⟨uNode, false, none, false⟩) :=
    X_titled_marker_record (hrecords u uNode hu) (Or.inl hbU)
  have hrequestedBorder : (titleF ⟨uNode, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hbU
  have howner : top.1.node.clusterPath.getLast? =
      (titleF ⟨uNode, false, none, false⟩).node.clusterPath.getLast? := by
    have hpathTop : (titleF ⟨uNode, false, none, false⟩).node.clusterPath =
        uNode.clusterPath :=
      (titleF_keys _).2.2.1
    have hlastU : uNode.clusterPath.getLast? = some uNode.decl :=
      c8aR_top_getLast h0 h hu hbU
    rw [hpathTop, hlastU]
    exact hlastTop
  exact X_titled_group_owner_unique h0 h hcomp hkeys hrecords htopLookup hrequested
    hbTop hrequestedBorder howner
/-- Exact prepared rank transport (copy of `Xb_prepared_rk`). -/
private theorem c8aR_prepared_rk {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk run.coordinateProper.rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  have hlabLen : index < labeled.rank.length :=
    (List.getElem?_eq_some_iff.mp hlabLookup).1
  obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
  have hcoordLookup : run.coordinateProper.rank[index]? = some rr.ranks[index] := by
    rw [← hc, heq, List.getElem?_append_left hlabLen]
    exact hlabLookup
  simp only [rk, List.getD_eq_getElem?_getD, hcoordLookup, hrrLookup, Option.getD_some]

/-- Title-reservation rank prefix for exact sizing (copy of `Xb_titled_rank_prefix`). -/
private theorem c8aR_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

/-- Exact titled rank transport (copy of `Xb_titled_rk`). -/
private theorem c8aR_titled_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact labeled)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  obtain ⟨_, heq⟩ := c8aR_titled_rank_prefix P exact labeled
  have htitledLookup : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? =
      some rr.ranks[index] := by
    rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlabLookup).1]
    exact hlabLookup
  have heq2 : rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq2, ?_⟩
  rw [heq2]
  exact rankWithBudget_rk_nonneg hrr index

/-- Non-proxy exact coordinate nodes transfer (copy of `Xb_nonproxy`). -/
private theorem c8aR_nonproxy {P : Params} {exact : List Nat}
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

/-- Exact coordinate record (copy of `Xb_fbs`). -/
private theorem c8aR_fbs {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', -, hb', hh'⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [← hdrop]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  refine ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm, ?_⟩
  intro hnp
  obtain ⟨hfull, -⟩ := c8aR_nonproxy hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]
/-- Exact bordered-graph node classification (copy of `Xb_coord0_lookup`). -/
private theorem c8aR_coord0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := sizeProperPortsX_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification (copy of `Xb_coord_lookup`). -/
private theorem c8aR_coord_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases c8aR_coord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

/-- Exact proxy frames are flat (copy of `Xb_pc_frame_flat`). -/
private theorem c8aR_pc_frame_flat {P : Params} {exact : List Nat} {labeled : Proper}
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hb : nd.node.border = -2 ∨ nd.node.border = 2) : nd.node.h = 0 := by
  rcases c8aR_coord_lookup P exact labeled h with ⟨m, hm, _, _, _, hf⟩ | ⟨_, h1⟩ |
    ⟨i, q, hq, _, _, h1, _⟩
  · exact hf hb
  · omega
  · omega


/-- Exact coordinate-run rank equality (copy of `Xb_coord_rank_eq`). -/
private theorem c8aR_coord_run_eq {P : Params} {exact : List Nat} {labeled : Proper} {run : Run}
    (hcoord : coordinateGraphX P exact labeled = run.coordinateProper)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {x : Nat} (hx : x < labeled.nodes.length) :
    rk run.coordinateProper.rank x = rk labeled.rank x := by
  have hxr : x < labeled.rank.length := by omega
  have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
    List.getElem?_eq_getElem hxr
  obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
  have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
    rw [← hcoord, heq, List.getElem?_append_left hxr]
    exact hlab
  simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

/-- Exact titled rank record (copy of `Xb_titled_rank_record`). -/
private theorem c8aR_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := c8aR_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Exact title-copy rank record (copy of `Xb_titled_copy_rank_record`). -/
private theorem c8aR_titled_copy_rank_record {P : Params} {exact : List Nat} {labeled : Proper}
    (haligned : labeled.nodes.length = labeled.rank.length)
    {position : Nat} {entry : ProperNode × Nat}
    (hentry : (titleNodes (sizeProperPortsX P exact labeled))[position]? = some entry) :
    (titleReservations (sizeProperPortsX P exact labeled)).rank[labeled.nodes.length + position]? =
      some (rk labeled.rank entry.2) := by
  have hsized : (sizeProperPortsX P exact labeled).rank = labeled.rank := rfl
  have hrank : (titleReservations (sizeProperPortsX P exact labeled)).rank =
      labeled.rank ++ (titleNodes (sizeProperPortsX P exact labeled)).map
        (fun value => rk labeled.rank value.2) := by
    have h0 : (titleReservations (sizeProperPortsX P exact labeled)).rank =
        (sizeProperPortsX P exact labeled).rank ++
          (titleNodes (sizeProperPortsX P exact labeled)).map
            (fun value => rk (sizeProperPortsX P exact labeled).rank value.2) := by
      unfold titleReservations titleNodes sizeProperPortsX
      rfl
    rw [h0, hsized]
  rw [hrank, List.getElem?_append_right (by omega)]
  have hindex : labeled.nodes.length + position - labeled.rank.length = position := by omega
  rw [hindex, List.getElem?_map, hentry]
  rfl

/-- Exact titled rank in coordinate graph (copy of `Xb_coord_titled_rank_record`). -/
private theorem c8aR_coord_titled_rank_record {P : Params} {exact : List Nat} {labeled : Proper}
    {index : Nat} {rank : Int}
    (h : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? = some rank) :
    (coordinateGraphX P exact labeled).rank[index]? = some rank := by
  obtain ⟨extraC, heqC⟩ := coordinateGraphX_anchor_prefix P exact labeled
  obtain ⟨extraA, heqA⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hlen : index < (titleReservations (sizeProperPortsX P exact labeled)).rank.length :=
    (List.getElem?_eq_some_iff.mp h).1
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank[index]? =
      some rank := by
    have hrfl : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank =
        (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank := rfl
    rw [hrfl, heqA, List.getElem?_append_left hlen]
    exact h
  have hmat : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank[index]? =
      some rank := by
    have hrfl2 : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank =
        (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank := rfl
    rw [hrfl2]
    exact hclear
  have hrfl3 : (coordinateGraphX P exact labeled).rank =
      (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank := rfl
  rw [hrfl3]
  exact hmat

/-- Exact proxy span record (copy of `Xb_proxy_interval`). -/
private theorem c8aR_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right
/-- Exact coordinate title-copy source (copy of `Xb_title_rank_source`). -/
private theorem c8aR_title_rank_source {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper}
    (hkeys : NodeKeys cg labeled) (hshape : CgShape cg)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {titleIndex : Nat} {title : ProperNode}
    (htitle : (coordinateGraphX P exact labeled).nodes[titleIndex]? = some title)
    (hborder : title.node.border = 3) :
    ∃ (originalIndex : Nat) (original : ProperNode),
      labeled.nodes[originalIndex]? = some original ∧
      original.node.border = -2 ∧ original.dummy = false ∧
      title.dummy = false ∧ title.node.clusterPath = original.node.clusterPath ∧
      rk (coordinateGraphX P exact labeled).rank titleIndex = rk labeled.rank originalIndex := by
  rcases c8aR_coord_lookup P exact labeled htitle with
    ⟨original, horiginal, _, hb, _, _⟩ | ⟨_, hside⟩ |
    ⟨position, entry, hentry, hindex, hd, _, hp⟩
  · rcases hkeys titleIndex original horiginal with
      ⟨before, hbefore, _, hbeforeBorder, _⟩ | ⟨_, hplain, _⟩
    · have hnot := hshape.2 before (List.mem_of_getElem? hbefore)
      exact (hnot (hbeforeBorder.symm.trans (hb.symm.trans hborder))).elim
    · omega
  · rcases hside with hside | hside <;> omega
  · obtain ⟨hsized, hsizedBorder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hsourceDummy, hsourceBorder, hsourcePath⟩ :=
      X_sizeProperPorts_node_origin P exact labeled hsized
    have hsourceGroup : original.node.border = -2 := hsourceBorder.symm.trans hsizedBorder
    have horiginalReal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · omega
    have hentryReal : entry.1.dummy = false := hsourceDummy.trans horiginalReal
    have htitleReal : title.dummy = false := hd.trans hentryReal
    have htitlePath : title.node.clusterPath = original.node.clusterPath :=
      (hp hentryReal).trans hsourcePath
    have htitledRank := c8aR_titled_copy_rank_record haligned hentry
    have hcoordinateRank := c8aR_coord_titled_rank_record htitledRank
    refine ⟨entry.2, original, horiginal, hsourceGroup, horiginalReal,
      htitleReal, htitlePath, ?_⟩
    rw [hindex]
    simp only [rk, List.getD_eq_getElem?_getD, hcoordinateRank, Option.getD_some]



/-- Prefix take (copy of `Xb_take_is_prefix`). -/
private theorem c8aR_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

private theorem c8aR_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

private theorem c8aR_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := c8aR_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact c8aR_take_is_prefix q p.length

private theorem c8aR_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := c8aR_prefix_take_eq h1
  have hle1 : p.length ≤ q.length := by
    obtain ⟨r, rfl⟩ := h1
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hle2 : q.length ≤ p.length := by
    obtain ⟨r, rfl⟩ := h2
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hlen : p.length = q.length := by omega
  have e2 : q.take q.length = q := by simp
  rw [← hlen] at e2
  exact e.symm.trans e2

private theorem c8aR_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      c8aR_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (c8aR_prefix_antisymm hp h2) hne

private theorem c8aR_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

private theorem c8aR_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

private theorem c8aR_le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

private theorem c8aR_filter_ne_nil {α : Type} {l : List α}
    (h : l.isEmpty = false) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

/-- Exact nested-bottom rank induction (copy of `Xb_nested_bottom_rank`). -/
private theorem c8aR_nested_bottom_rank {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr) :
    ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node, ∀ ba bb : Node × Nat,
      (componentCandidate graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.clusterPath <+: nb.clusterPath →
      nb.clusterPath.length - na.clusterPath.length = delta →
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == na.decl) = some ba →
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == nb.decl) = some bb →
      rk rr.ranks bb.2 ≤ rk rr.ranks ba.2 := by
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ba bb ha hbA hb hbB hpre hdelta hba hbb
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := X_cg_top_unique h0 h hcomp ha hb hbA hbB heq
      subst hab
      have hdecl : na.decl = nb.decl := by
        have hlastA : na.clusterPath.getLast? = some na.decl := by
          obtain ⟨box, hbox, hpathA⟩ := X_cg_group_box h0 h ha hbA
          exact c8aR_cg_path_last hpathA
        have hlastB : nb.clusterPath.getLast? = some nb.decl := by
          obtain ⟨box, hbox, hpathB⟩ := X_cg_group_box h0 h hb hbB
          exact c8aR_cg_path_last hpathB
        have h := congrArg List.getLast? heq
        rw [hlastA, hlastB] at h
        exact Option.some.inj h
      rw [hdecl] at hba
      have hbb_eq : bb = ba := Option.some.inj (hbb.symm.trans hba)
      rw [hbb_eq]
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        c8aR_prefix_length_lt hpre heq
      have hbne : nb.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape h0 h hb).2 hbB
      have hna_ne : na.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape h0 h ha).2 hbA
      obtain ⟨u, hu⟩ := X_candidate_parent_top_exists h0 h hlines hwf hframed hcomp candidate
        (x := (nb, b)) (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpre hlt hna_ne
      have huPred := List.find?_some hu
      simp only [Bool.and_eq_true, beq_iff_eq] at huPred
      obtain ⟨huBorder, huPath⟩ := huPred
      have huMem : u ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_of_find?_eq_some hu
      have huLookup : (componentCandidate graph comp candidate).nodes[u.2]? = some u.1 :=
        List.mem_zipIdx_iff_getElem?.mp huMem
      have hdropLen : u.1.clusterPath.length = nb.clusterPath.length - 1 := by
        rw [huPath]
        exact List.length_dropLast ..
      have hnbpos : 0 < nb.clusterPath.length :=
        Nat.pos_of_ne_zero (fun h => hbne (List.length_eq_zero_iff.mp h))
      have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
      have hpreU : na.clusterPath <+: u.1.clusterPath :=
        c8aR_prefix_of_common_prefix hpre (huPath ▸ c8aR_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      obtain ⟨ubot, hubot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp huLookup huBorder
      have hIH := ih _ hdeltaU a u.2 na u.1 ba ubot ha hbA huLookup huBorder hpreU rfl hba hubot
      have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
      have hinterv := ranked_compound_child_interval (parent := (u.1, u.2)) (child := (nb, b)) hrr
        (List.mem_zipIdx_iff_getElem?.mpr huLookup) huBorder hubot
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpathUB hbb
      omega

/-- Original member rank bound (copy of `Xb_origRankLe`). -/
private theorem c8aR_origRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds) :
    ∀ {idx : Nat} {n : Node},
    (componentCandidate graph comp candidate).nodes[idx]? = some n →
    n.clusterPath.contains ndT.decl = true →
    rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hfindV : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndV.decl) = some (ndV, v) :=
    X_bottom_find_eq h0 h hcomp hvGet hbordV
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
    rw [← hdecl]; exact hfindV
  have htopOuter : ((ndT, t) : Node × Nat) ∈
      (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htGet
  have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := c8aR_prepared_rk hrr hc hranks (List.getElem?_eq_some_iff.mp hvGet).1
    exact h1
  let cg := componentCandidate graph comp candidate
  let maxLen := ((cg.nodes.filter fun n => n.border == -2).map
    (fun n => n.clusterPath.length)).foldr max 0
  have hbound : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath.length ≤ maxLen := by
    intro index node hnode hgroup
    have hmem : node ∈ cg.nodes.filter (fun n => n.border == -2) :=
      List.mem_filter.mpr ⟨List.mem_of_getElem? hnode, by simp [hgroup]⟩
    have hmap : node.clusterPath.length ∈
        (cg.nodes.filter fun n => n.border == -2).map
          (fun n => n.clusterPath.length) :=
      List.mem_map_of_mem hmem
    exact c8aR_le_foldr_max hmap
  have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath ≠ [] := by
    intro index node hnode hgroup hnil
    exact (X_componentCandidate_marker_shape h0 h hnode).2 hgroup hnil
  have main : ∀ fuel idx n, cg.nodes[idx]? = some n →
      n.clusterPath.contains ndT.decl = true →
      maxLen - n.clusterPath.length = fuel → rk rr.ranks idx ≤ rk rr.ranks v := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro idx n hidx hcontains hfuel
      rcases (X_componentCandidate_marker_shape h0 h hidx).1 with hplain | hgroup | hbottom
      · have hinterval := ranked_compound_member_interval hrr htopOuter hbordT
          hbotFindOuter (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hplain hcontains
        have hle : rk rr.ranks idx + 1 ≤ rk rr.ranks v := hinterval.2
        omega
      · obtain ⟨rrB, labeledB, bottomTB, hrrB, hcB, hkB, hreadyB, hrecordsB, hranksB,
            htitledB, hfindB⟩ :=
          X_group_bottom_source h0 h hcomp hrun hidx hgroup
        obtain ⟨origB, horigB, hborderB, hpathB, hrecordB, hfindCB⟩ :=
          X_bottom_constraint_source h0 h hkB hrecordsB hidx hgroup hfindB
        have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
          rw [hpathB]; exact hcontains
        have resolveB : rk rr.ranks bottomTB.2 ≤ rk rr.ranks v := by
          by_cases hdeq : origB.decl = ndT.decl
          · have hmemB := List.find?_some hfindCB
            simp only [Bool.and_eq_true, beq_iff_eq] at hmemB
            have hndeq : n.decl = ndT.decl := hmemB.2.symm.trans hdeq
            rw [hndeq] at hfindCB
            have heq : (origB, bottomTB.2) = (ndV, v) :=
              Option.some.inj (hfindCB.symm.trans hbotFindOuter)
            have hbv : bottomTB.2 = v := congrArg Prod.snd heq
            rw [hbv]
            exact Int.le_refl _
          · have hleB : rk run.coordinateProper.rank bottomTB.2 ≤
              rk run.coordinateProper.rank v :=
              hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
                horigB hborderB hdeq hpathBmem
            have e1 : rk run.coordinateProper.rank bottomTB.2 =
                rk rr.ranks bottomTB.2 := by
              have h1 := c8aR_prepared_rk hrr hc hranks
                (List.getElem?_eq_some_iff.mp horigB).1
              exact h1
            omega
        cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
            entry.1.border == 0 && entry.1.clusterPath.contains n.decl).isEmpty with
        | false =>
          obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
            (c8aR_filter_ne_nil hmemCase)
          obtain ⟨hmemberZip, hmemberCond⟩ := List.mem_filter.mp hmember
          obtain ⟨hmemberPlain, hmemberInside⟩ := Bool.and_eq_true_iff.mp hmemberCond
          have hmemberPlain' : member.1.border = 0 := by simpa using hmemberPlain
          have hmemberInside' : member.1.clusterPath.contains n.decl = true := by
            simpa using hmemberInside
          have hinterval := ranked_compound_member_interval hrr
            (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
            hmemberZip hmemberPlain' hmemberInside'
          have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks member.2 := hinterval.1
          have hR : rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottomTB.2 := hinterval.2
          omega
        | true =>
          cases hchildCase : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
              fun entry => entry.1.clusterPath.dropLast == n.clusterPath).isEmpty with
          | false =>
            obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _
              (c8aR_filter_ne_nil hchildCase)
            obtain ⟨hchildTop, hchildPathEq⟩ := List.mem_filter.mp hchildMem
            obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
            have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
            have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
            obtain ⟨rrC, labeledC, bottomTC, hrrC, hcC, hkC, hreadyC, hrecordsC, hranksC,
                htitledC, hfindC⟩ :=
              X_group_bottom_source h0 h hcomp hrun hchildIndex hchildGroup'
            obtain ⟨childOriginal, horigC, hborderC, hpathC, hrecordC, hchildFind'⟩ :=
              X_bottom_constraint_source h0 h hkC hrecordsC hchildIndex
                hchildGroup' hfindC
            have hchildPair : cg.nodes.zipIdx.find? (fun entry =>
                entry.1.border == 2 && entry.1.decl == child.1.decl) =
                some (childOriginal, bottomTC.2) := hchildFind'
            have hpathEq : child.1.clusterPath.dropLast = n.clusterPath := by
              simpa using hchildPathEq
            have hdirect := ranked_compound_child_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
              hchildZip hchildGroup' hpathEq hchildPair
            have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks child.2 := hdirect.1
            have hne : n.clusterPath ≠ [] := hnonempty idx n hidx hgroup
            have hchildNonEmpty : child.1.clusterPath ≠ [] := by
              intro hempty
              rw [hempty, List.dropLast_nil] at hpathEq
              exact hne hpathEq.symm
            have hlenC : child.1.clusterPath.length = n.clusterPath.length + 1 := by
              rw [← hpathEq, List.length_dropLast]
              have hchildLen := List.length_pos_iff.mpr hchildNonEmpty
              omega
            have hboundChild := hbound child.2 child.1 hchildIndex hchildGroup'
            have hpos : 0 < fuel := by omega
            have hfuelChild : maxLen - child.1.clusterPath.length = fuel - 1 := by omega
            have hcontainsC : child.1.clusterPath.contains ndT.decl = true := by
              have hsub : n.clusterPath <+: child.1.clusterPath := by
                rw [← hpathEq]; exact c8aR_dropLast_is_prefix _
              have hmemN : ndT.decl ∈ n.clusterPath :=
                List.contains_iff_mem.mp hcontains
              have hmemC : ndT.decl ∈ child.1.clusterPath :=
                List.Sublist.mem hmemN (List.IsPrefix.sublist hsub)
              exact List.contains_iff_mem.mpr hmemC
            have hih := ih (fuel - 1) (by omega) child.2 child.1 hchildIndex
              hcontainsC hfuelChild
            omega
          | true =>
            have hempty := ranked_empty_group_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB hmemCase hchildCase
            have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks bottomTB.2 := hempty
            omega
      · by_cases hdeq : n.decl = ndT.decl
        · have hfindEq : (componentCandidate graph comp candidate).nodes.zipIdx.find?
              (fun entry => entry.1.border == 2 && entry.1.decl == n.decl) =
              some (n, idx) :=
            X_bottom_find_eq h0 h hcomp hidx hbottom
          rw [hdeq] at hfindEq
          have heq : (n, idx) = (ndV, v) :=
            Option.some.inj (hfindEq.symm.trans hbotFindOuter)
          have hiv : idx = v := congrArg Prod.snd heq
          rw [hiv]
          exact Int.le_refl _
        · have hleB : rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v :=
            hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
              hidx hbottom hdeq hcontains
          have e1 : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
            have h1 := c8aR_prepared_rk hrr hc hranks
              (List.getElem?_eq_some_iff.mp hidx).1
            exact h1
          omega
  intro idx n hidx hcontains
  have hrr_le := main (maxLen - n.clusterPath.length) idx n hidx hcontains rfl
  have eI : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
    have h1 := c8aR_prepared_rk hrr hc hranks
      (List.getElem?_eq_some_iff.mp hidx).1
    exact h1
  omega
/-- Exact side-marker rank bound (copy of `Xb_sideRankLe`). -/
private theorem c8aR_sideRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hcontains : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
    (hside : q.1.node.border = -1 ∨ q.1.node.border = 1) :
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := c8aR_fbs hrun hqget
  have hsideC : nvc.node.border = -1 ∨ nvc.node.border = 1 := by
    rw [hborderEq]; exact hside
  have hncX : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
    rw [hc]; exact hnc
  have hcoordXrfl : (coordinateGraphX P (exactDecls exactIds inp) labeled).rank =
      (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).rank := rfl
  have horiginal := X_side_original hready hncX hsideC
  obtain ⟨top, htopMem, bottom, hfindB, hpathEq, hnn, htonat, hhi⟩ :=
    addClusterBorders_side_rank_bounds _ _ hready horiginal hsideC
  have htopGet : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
  have htopBorder : top.1.node.border = -2 := by
    simpa using (List.mem_filter.mp htopMem).2
  obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
    X_titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
  have htopCgBorder : topOrig.border = -2 := htopBorderEq.symm.trans htopBorder
  have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
    rw [htopRecord]; exact (titleF_keys _).2.2.1
  have hnotProxy : ¬(nvc.node.border = -2 ∨ nvc.node.border = 2) := by
    rintro (h | h) <;> omega
  have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath :=
    hpathImp hnotProxy
  have htopContains : top.1.node.clusterPath.contains ndT.decl = true := by
    rw [← hpathEq, hnvcPath, ← hdeclT]; exact hcontains
  have htopOrigContains : topOrig.clusterPath.contains ndT.decl = true := by
    rw [← htopPath]; exact htopContains
  have hfindB' : ((titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == topOrig.clusterPath) = some bottom := by
    rw [← htopPath]; exact hfindB
  obtain ⟨origB, horigB, hborderB, hpathB, _, _⟩ :=
    X_bottom_constraint_source h0 h hk hrecords htopCg
      htopCgBorder hfindB'
  have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
    rw [hpathB]; exact htopOrigContains
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) =
      some (ndV, v) := by
    rw [← hdecl]; exact X_bottom_find_eq h0 h hcomp hvGet hbordV
  have hBle : rk run.coordinateProper.rank bottom.2 ≤
      rk run.coordinateProper.rank v := by
    by_cases hdeq : origB.decl = ndT.decl
    · have hfindBdec := X_bottom_find_eq h0 h hcomp horigB hborderB
      rw [hdeq] at hfindBdec
      have heq := Option.some.inj (hfindBdec.symm.trans hbotFindOuter)
      have hbv : bottom.2 = v := congrArg Prod.snd heq
      rw [hbv]
      exact Int.le_refl _
    · exact hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
        horigB hborderB hdeq hpathBmem
  have hBcoord : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
    have hlt : bottom.2 < (componentCandidate graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp horigB).1
    have h1 := c8aR_prepared_rk hrr hc hranks hlt
    exact h1
  have hBtitle : rk (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2 =
      rk rr.ranks bottom.2 := by
    have h1 := c8aR_titled_rk (P := P) (exact := exactDecls exactIds inp) hrr hranks
      (List.getElem?_eq_some_iff.mp horigB).1
    exact h1.1
  have hBnn : 0 ≤ rk rr.ranks bottom.2 := rankWithBudget_rk_nonneg hrr bottom.2
  have hbotnn : 0 ≤ rk run.coordinateProper.rank bottom.2 := by
    rw [hBcoord]; exact hBnn
  have htonat : (rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2).toNat ≤
      (rk run.coordinateProper.rank bottom.2).toNat := by
    rw [hcoordXrfl, hBcoord, ← hBtitle]; exact hhi
  have hqb : rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2 ≤
      rk run.coordinateProper.rank bottom.2 :=
    c8aR_toNat_le_of_nonneg hnn hbotnn htonat
  have hq : rk run.coordinateProper.rank q.2 ≤
      rk run.coordinateProper.rank bottom.2 := by
    have hQ : rk run.coordinateProper.rank q.2 =
        rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2 := by
      rw [hc]
    rw [hQ]; exact hqb
  exact Int.le_trans hq hBle

/-- Exact title-copy rank bound (copy of `Xb_titleRankLe`). -/
private theorem c8aR_titleRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hcontains : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
    (hb3 : q.1.node.border = 3) :
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := c8aR_fbs hrun hqget
  have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
    rw [hc]; exact hnc
  have hb3C : nvc.node.border = 3 := by rw [hborderEq]; exact hb3
  obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath,
      htitleRank⟩ :=
    c8aR_title_rank_source hk hshape haligned hncL hb3C
  have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath := by
    apply hpathImp
    rintro (h | h) <;> omega
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  have horigContains : original.node.clusterPath.contains ndT.decl = true := by
    rw [← htitlePath, hnvcPath, ← hdeclT]; exact hcontains
  rcases hk originalIndex original horiginal with
    ⟨n, hn, _, hborderN, hpathN⟩ | ⟨hdT, _, _⟩
  · have hnBorder : n.border = -2 := hborderN.symm.trans hOrigBorder
    have hncN : n.clusterPath.contains ndT.decl = true := by
      rw [← hpathN]; exact horigContains
    have hle := c8aR_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
      hnest hn hncN
    have hrankEq : rk run.coordinateProper.rank q.2 = rk labeled.rank originalIndex := by
      rw [← hc]; exact htitleRank
    have hlabEq : rk labeled.rank originalIndex =
        rk run.coordinateProper.rank originalIndex := by
      have h1 : originalIndex < labeled.nodes.length :=
        (List.getElem?_eq_some_iff.mp horiginal).1
      exact (c8aR_coord_run_eq hc haligned h1).symm
    rw [hrankEq, hlabEq]; exact hle
  · exact absurd (hdT.symm.trans hOrigReal) (by decide)

/-- Member rank bound by classification (copy of `Xb_memberRankLe`). -/
private theorem c8aR_memberRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl) :
    ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
    q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  have hnest : Xb_NestedExact exactIds := Xb_NestedExact_holds exactIds
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  intro q hq hcontains
  have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, _⟩ := c8aR_fbs hrun hqget
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
    rwa [← hc] at hnc
  rcases c8aR_coord_lookup P (exactDecls exactIds inp) labeled hncL with
    ⟨m, hm, hmd, hb, hp, -⟩ | hside | ⟨_, _, _, _, _, hb3, _⟩
  · by_cases hqd : q.1.dummy = true
    · exact X_bottomDummyRankLe exactIds hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet
        hbordV hbordT hdecl q hq hcontains hqd
    · have hqdF : q.1.dummy = false := by simpa using hqd
      by_cases hbS : nvc.node.border = -1 ∨ nvc.node.border = 1 ∨ nvc.node.border = 3
      · have hqbS : q.1.node.border = -1 ∨ q.1.node.border = 1 ∨
            q.1.node.border = 3 := by
          rcases hbS with h | h | h
          · exact Or.inl (by rw [← hborderEq]; exact h)
          · exact Or.inr (Or.inl (by rw [← hborderEq]; exact h))
          · exact Or.inr (Or.inr (by rw [← hborderEq]; exact h))
        rcases hqbS with hb1 | hb2 | hb3q
        · exact c8aR_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
            hdecl hnest q hq hcontains (Or.inl hb1)
        · exact c8aR_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
            hdecl hnest q hq hcontains (Or.inr hb2)
        · exact c8aR_titleRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
            hdecl hnest q hq hcontains hb3q
      · by_cases hbP : nvc.node.border = -2 ∨ nvc.node.border = 2
        · obtain ⟨owner, span, _, _, hproper, _, _⟩ := c8aR_proxy_interval hrun hnc hbP
          have hqq : q.1 =
              { nvc with node := { nvc.node with w := span.hi - span.lo } } :=
            Option.some.inj (hqget.symm.trans hproper)
          have hdu : nvc.dummy = q.1.dummy := by rw [hqq]
          have hmdF : m.dummy = false := by rw [← hmd, hdu]; exact hqdF
          have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
          rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
          · have hncN : n.clusterPath.contains ndT.decl = true := by
              rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
            exact c8aR_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
              hdecl hnest hn hncN
          · rw [hdT] at hmdF
            simp at hmdF
        · obtain ⟨hrecFull, -⟩ := c8aR_nonproxy hrun hnc hbP
          have hqq : q.1 = nvc := Option.some.inj (hqget.symm.trans hrecFull)
          have hmdF : m.dummy = false := by rw [← hmd, ← hqq]; exact hqdF
          have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
          rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
          · have hncN : n.clusterPath.contains ndT.decl = true := by
              rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
            exact c8aR_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
              hdecl hnest hn hncN
          · rw [hdT] at hmdF
            simp at hmdF
  · rcases hside.2 with hb1 | hb2
    · exact c8aR_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
        hdecl hnest q hq hcontains (Or.inl (by rw [← hborderEq]; exact hb1))
    · exact c8aR_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
        hdecl hnest q hq hcontains (Or.inr (by rw [← hborderEq]; exact hb2))
  · exact c8aR_titleRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
      hdecl hnest q hq hcontains (by rw [← hborderEq]; exact hb3)

/-- Bottom original decl equals top decl when paths agree (exact). -/
private theorem c8aR_bottom_decl_eq {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hbU : uNode.border = -2)
    {orig : Node} (hpath : orig.clusterPath = uNode.clusterPath)
    (hborder : orig.border = 2)
    {idx : Nat} (hidx : (componentCandidate graph comp candidate).nodes[idx]? = some orig) :
    orig.decl = uNode.decl := by
  have hlastU : uNode.clusterPath.getLast? = some uNode.decl :=
    c8aR_top_getLast h0 h hu hbU
  obtain ⟨_, _, hpathB⟩ := X_cg_bottom_box h0 h hidx hborder
  have hlastB : orig.clusterPath.getLast? = some orig.decl := by
    rw [hpathB, List.getLast?_append]
    simp
  rw [hpath] at hlastB
  rw [hlastU] at hlastB
  exact Option.some.inj hlastB.symm

/-- Per-declaration member-rank bounds (exact replay of `perDecl` in
`ForeignMemberRankBoundsProof`). Proves ordering plus universal member bounds
for one group decl from its titled anchors. -/
private theorem c8aR_perDecl {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {a : Nat} {aNode : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some aNode)
    (hba : aNode.border = -2)
    {labeled : Proper} {rr : RankImpl.RankResult}
    (hcoord : coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper)
    (_halignedL : labeled.nodes.length = labeled.rank.length)
    (hkeys : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr)
    (hranks : ∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩)
    {top bot : ProperNode × Nat}
    (hmem : top ∈
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx)
    (hbTop : top.1.node.border = -2)
    (hlast : top.1.node.clusterPath.getLast? = some aNode.decl)
    (hfind : ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
      (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath)) = some bot) :
    ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat :
        Nat) : Int)) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains aNode.decl =
        true →
      ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat :
          Nat) : Int)))) := by
  have htopPin : top.2 = a :=
    c8aR_titledTopPin h0 h hcomp hkeys hrecords ha hba hmem hbTop hlast
  have htopLookup : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hreqMem : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[a]? =
      some (titleF ⟨aNode, false, none, false⟩) :=
    X_titled_marker_record (hrecords a aNode ha) (Or.inl hba)
  have htopIsReq : top.1 = titleF ⟨aNode, false, none, false⟩ := by
    rw [htopPin] at htopLookup
    exact Option.some.inj (htopLookup.symm.trans hreqMem)
  have htopPathEq : top.1.node.clusterPath = aNode.clusterPath := by
    rw [htopIsReq]; exact (titleF_keys _).2.2.1
  have hfind' : ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
      (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == aNode.clusterPath)) = some bot := by
    rw [← htopPathEq]; exact hfind
  obtain ⟨origB, horigB, hborderB, hpathB, _, hfindBdec⟩ :=
    X_bottom_constraint_source (exact := exactDecls exactIds inp) h0 h hkeys hrecords ha hba hfind'
  have hdeclB : origB.decl = aNode.decl :=
    c8aR_bottom_decl_eq h0 h ha hba hpathB hborderB horigB
  have haLt : a < (componentCandidate graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp ha).1
  have hbotLt : bot.2 < (componentCandidate graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp horigB).1
  have htopRkEq : rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2 =
      rk rr.ranks a := by
    have h1 := (c8aR_titled_rk (P := P) (exact := exactDecls exactIds inp) hrr hranks haLt).1
    rw [htopPin]; exact h1
  have hbotRkEq : rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2 =
      rk rr.ranks bot.2 := by
    have h1 := (c8aR_titled_rk (P := P) (exact := exactDecls exactIds inp) hrr hranks hbotLt).1
    exact h1
  have htopNn : 0 ≤ rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2 := by
    rw [htopRkEq]; exact rankWithBudget_rk_nonneg hrr a
  have hbotNn : 0 ≤ rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2 := by
    rw [hbotRkEq]; exact rankWithBudget_rk_nonneg hrr bot.2
  have hordRr : rk rr.ranks a ≤ rk rr.ranks bot.2 := by
    obtain ⟨rr2, _, hrr2, _, _, _, _, hlt⟩ := X_group_top_lt_bottom h0 h hcomp hrun
    have hrrEq : rr2 = rr := Except.ok.inj (hrr2.symm.trans hrr)
    have hle := hlt a aNode (origB, bot.2) ha hba hfindBdec
    rw [hrrEq] at hle
    have hstep : rk rr.ranks a ≤ rk rr.ranks a + 1 := by omega
    exact Int.le_trans hstep hle
  have hordNat : (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat ≤
      (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat := by
    have hle : rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2 ≤
        rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2 := by
      rw [htopRkEq, hbotRkEq]; exact hordRr
    exact c8aR_toNat_le htopNn hle
  have hord : ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat :
        Nat) : Int)) := by
    exact_mod_cast hordNat
  have hmemAll : (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains aNode.decl =
        true →
      ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat :
          Nat) : Int)))) := by
    intro v hv hcv
    have hcastT : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat : Int) = rk run.proper.rank a := by
      have hproperA : rk run.proper.rank a = rk rr.ranks a := by
        have erv : rk run.proper.rank a = rk run.coordinateProper.rank a :=
          X_proper_rank_eq_local hrun a
        have eco : rk run.coordinateProper.rank a = rk rr.ranks a :=
          c8aR_prepared_rk hrr hcoord hranks haLt
        omega
      rw [htopRkEq]
      have hnn : 0 ≤ rk rr.ranks a := rankWithBudget_rk_nonneg hrr a
      have h1 : (((rk rr.ranks a).toNat : Int)) = rk rr.ranks a :=
        Int.toNat_of_nonneg hnn
      rw [h1]
      exact hproperA.symm
    have hcastB : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat : Int) = rk run.coordinateProper.rank bot.2 := by
      have eco : rk run.coordinateProper.rank bot.2 = rk rr.ranks bot.2 :=
        c8aR_prepared_rk hrr hcoord hranks hbotLt
      rw [hbotRkEq]
      have hnn : 0 ≤ rk rr.ranks bot.2 := rankWithBudget_rk_nonneg hrr bot.2
      have h1 : (((rk rr.ranks bot.2).toNat : Int)) = rk rr.ranks bot.2 :=
        Int.toNat_of_nonneg hnn
      rw [h1]
      exact eco.symm
    have haProperLt : a < run.proper.nodes.length :=
      componentRunX_original_nodes_covered hrun a haLt
    have hqv : run.proper.nodes[v]? =
        some (run.proper.nodes.getD v default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
        Option.getD_some]
    have hq : (run.proper.nodes.getD v default, v) ∈
        run.proper.nodes.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hqv
    have hTop : rk run.proper.rank a ≤ rk run.proper.rank v := by
      have htopRank : X_TopRank exactIds := x_topRank_holds exactIds
      have haLtCg : a < (componentCandidate graph comp candidate).nodes.length := haLt
      exact htopRank h0 h hlines hwf hfp hcomp hrun ha hba haLtCg hv hcv
    have hgetA :
        (componentCandidate graph comp candidate).nodes.getD a default =
          aNode := by
      rw [List.getD_eq_getElem?_getD, ha, Option.getD_some]
    have hcq : ((run.proper.nodes.getD v default, v)).1.node.clusterPath.contains
        ((componentCandidate graph comp candidate).nodes.getD a default).decl =
          true := by
      rw [hgetA]; exact hcv
    have hBot : rk run.coordinateProper.rank v ≤
        rk run.coordinateProper.rank bot.2 :=
      c8aR_memberRankLe h0 h hlines hwf hfp hcomp hrun horigB ha
        hborderB hba hdeclB _ hq hcq
    have hTopInt : rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2 ≤ rk run.proper.rank v := by
      have hproperA : rk run.proper.rank a = rk rr.ranks a := by
        have erv : rk run.proper.rank a = rk run.coordinateProper.rank a :=
          X_proper_rank_eq_local hrun a
        have eco : rk run.coordinateProper.rank a = rk rr.ranks a :=
          c8aR_prepared_rk hrr hcoord hranks haLt
        omega
      rw [htopRkEq, ← hproperA]
      exact hTop
    have hBotInt : rk run.proper.rank v ≤ rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2 := by
      have erv : rk run.proper.rank v = rk run.coordinateProper.rank v :=
        X_proper_rank_eq_local hrun v
      have eco : rk run.coordinateProper.rank bot.2 = rk rr.ranks bot.2 :=
        c8aR_prepared_rk hrr hcoord hranks hbotLt
      rw [erv, hbotRkEq, ← eco]
      exact hBot
    have hcastTop : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat : Int) =
        rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2 :=
      Int.toNat_of_nonneg htopNn
    have hcastBot : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat : Int) =
        rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2 :=
      Int.toNat_of_nonneg hbotNn
    have hgoalTop : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat : Int) =
        rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2 := hcastTop
    have hgoalBot : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2).toNat : Int) =
        rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bot.2 := hcastBot
    rw [hgoalTop, hgoalBot]
    exact ⟨hTopInt, hBotInt⟩
  exact ⟨hord, hmemAll⟩

/-- Narrower lookup residual for the anchor cover: every executed proper node
whose cluster path carries a declaration yields its `-2` group marker in the
same component candidate. Single fact, no rank content; strictly narrower
than `XSc8a_AnchorCover` (which adds the titled pair and rank bounds). -/
def C8aR_TopLookup (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl low : Nat} {lowNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      ∃ (u : Nat) (uNode : Node),
        (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧
        uNode.border = -2 ∧ uNode.decl = decl

/-- Exact member-rank bounds: member ranks of a foreign cluster lie between its
titled top and bottom marker ranks (exact replay of `ForeignMemberRankBounds`,
the single residual behind `XS_C8a_ForeignClusterRankSpans`). -/
theorem XSc8a_memberBounds_holds (exactIds : List String) :
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∀ {labeled : Proper} {rr : RankImpl.RankResult},
    coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper →
    labeled.nodes.length = labeled.rank.length →
    NodeKeys (componentCandidate graph comp candidate) labeled →
    rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr →
    (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank) →
    (∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩) →
    ∀ {topU botU topW botW : ProperNode × Nat},
    topU ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx →
    topU.1.node.border = -2 →
    topU.1.node.clusterPath.getLast? = some uNode.decl →
    ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topU.1.node.clusterPath) = some botU →
    topW ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx →
    topW.1.node.border = -2 →
    topW.1.node.clusterPath.getLast? = some wNode.decl →
    ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topW.1.node.clusterPath) = some botW →
    ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat :
        Nat) : Int)) ∧
    ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat :
        Nat) : Int)) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains uNode.decl = true →
      ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat :
          Nat) : Int)))) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains wNode.decl = true →
      ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat :
          Nat) : Int)))) := by
  intro P inp o lines measured graph0 graph h0 h hlines hwf hfp comp hcomp candidate run labels orderOptions hrun u w uNode wNode hu hw hbU hbW hne labeled rr hcoord halignedL hkeys hrr hranks hrecords topU botU topW botW htopU hbUtop hlastU hbotU htopW hbWtop hlastW hbotW
  obtain ⟨hordU, hmemU⟩ := c8aR_perDecl h0 h hlines hwf hfp hcomp hrun hu hbU hcoord halignedL hkeys hrr hranks hrecords htopU hbUtop hlastU hbotU
  obtain ⟨hordW, hmemW⟩ := c8aR_perDecl h0 h hlines hwf hfp hcomp hrun hw hbW hcoord halignedL hkeys hrr hranks hrecords htopW hbWtop hlastW hbotW
  exact ⟨hordU, hordW, hmemU, hmemW⟩

/-- Exact anchor cover from the lookup residual (replay of
`sideMarkerAnchorCover` over the exact run). The titled pair comes from
`X_titled_marker_record` + `X_prepared_group_bottom`; the member-rank bounds
come from `c8aR_perDecl` (top via `x_topRank_holds`, bottom via
`c8aR_memberRankLe`); the reserve stage shifts ranks but adds none. -/
theorem XSc8a_anchorCover_holds (exactIds : List String) (hlook : C8aR_TopLookup exactIds) :
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl : Nat} {low high : Nat} {lowNd highNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      run.proper.nodes[high]? = some highNd →
      highNd.node.clusterPath.contains decl = true →
      ∃ (labeled : Proper),
        coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper ∧
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.length =
          (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank.length ∧
        ∃ (top bottom : ProperNode × Nat),
          top ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧
          top.1.node.border = -2 ∧
          top.1.node.clusterPath.getLast? = some decl ∧
          ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
            (fun entry => entry.1.node.border == 2 &&
              entry.1.node.clusterPath == top.1.node.clusterPath) =
              some bottom) ∧
          (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat ≤
            (rk run.proper.rank low).toNat ∧
          (rk run.proper.rank high).toNat ≤
            (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank
              bottom.2).toNat := by
  intro P inp o lines measured graph0 graph h0 h hlines hwf hfp comp hcomp candidate run labels orderOptions hrun decl low high lowNd highNd hlow hcontainLow hhigh hcontainHigh
  obtain ⟨u, uNode, hu, hbU, hdeclU⟩ := hlook h0 h hlines hwf hfp hcomp hrun hlow hcontainLow
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have halignedT : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.length =
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank.length :=
    X_titleReservations_node_rank_alignment P haligned
  have hlabU : labeled.nodes[u]? = some ⟨uNode, false, none, false⟩ :=
    hrecords u uNode hu
  have htopU : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[u]? =
      some (titleF ⟨uNode, false, none, false⟩) :=
    X_titled_marker_record hlabU (Or.inl hbU)
  have htopMem : (titleF (⟨uNode, false, none, false⟩ : ProperNode), u) ∈
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopU
  have hbTop : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.border = -2 := by
    rw [(titleF_keys _).2.1]; exact hbU
  have hlastTop : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast? =
      some decl := by
    have hpath : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath =
        uNode.clusterPath := (titleF_keys _).2.2.1
    have hlastU := c8aR_top_getLast h0 h hu hbU
    rw [hpath, hlastU, hdeclU]
  obtain ⟨bottom, _, hfindB⟩ :=
    X_prepared_group_bottom h0 h hcomp hrun hc hk hready hrecords hu hbU
  have htopPath : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath =
      uNode.clusterPath := (titleF_keys _).2.2.1
  have hfindB' : ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
      (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
        entry.1.node.clusterPath ==
          (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)) = some bottom := by
    rw [htopPath]; exact hfindB
  have hlastU' : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast? =
      some uNode.decl := by
    rw [htopPath]; exact c8aR_top_getLast h0 h hu hbU
  have hgetLow : run.proper.nodes.getD low default = lowNd := by
    rw [List.getD_eq_getElem?_getD, hlow, Option.getD_some]
  have hgetHigh : run.proper.nodes.getD high default = highNd := by
    rw [List.getD_eq_getElem?_getD, hhigh, Option.getD_some]
  have hcontainLowU : (run.proper.nodes.getD low default).node.clusterPath.contains uNode.decl = true := by
    rw [hgetLow, hdeclU]; exact hcontainLow
  have hcontainHighU : (run.proper.nodes.getD high default).node.clusterPath.contains uNode.decl = true := by
    rw [hgetHigh, hdeclU]; exact hcontainHigh
  have hlowLt : low < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hlow).1
  have hhighLt : high < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hhigh).1
  obtain ⟨_, hmemAll⟩ := c8aR_perDecl h0 h hlines hwf hfp hcomp hrun hu hbU hc haligned hk hrr hranks hrecords htopMem hbTop hlastU' hfindB'
  have hLow := (hmemAll low hlowLt hcontainLowU).1
  have hHigh := (hmemAll high hhighLt hcontainHighU).2
  have hlowNn : 0 ≤ rk run.proper.rank low := c8aR_proper_rk_nonneg hrun low hlowLt
  have hhighNn : 0 ≤ rk run.proper.rank high := c8aR_proper_rk_nonneg hrun high hhighLt
  have hloNat : (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank u).toNat ≤
      (rk run.proper.rank low).toNat := by
    have hcastL : (((rk run.proper.rank low).toNat : Int)) = rk run.proper.rank low :=
      Int.toNat_of_nonneg hlowNn
    have hle : ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank u).toNat : Int) ≤
        rk run.proper.rank low := hLow
    rw [← hcastL] at hle
    exact Int.ofNat_le.mp hle
  have hhiNat : (rk run.proper.rank high).toNat ≤
      (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2).toNat := by
    have hcastH : (((rk run.proper.rank high).toNat : Int)) = rk run.proper.rank high :=
      Int.toNat_of_nonneg hhighNn
    have hle : rk run.proper.rank high ≤
        ((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2).toNat : Int) := hHigh
    rw [← hcastH] at hle
    exact Int.ofNat_le.mp hle
  exact ⟨labeled, hc, halignedT, (titleF (⟨uNode, false, none, false⟩ : ProperNode), u), bottom,
    htopMem, hbTop, hlastTop, hfindB', hloNat, hhiNat⟩

end PipelineImpl


end Layered
end Elegant
