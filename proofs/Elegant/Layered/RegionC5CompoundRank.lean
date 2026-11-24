import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionLabelPlacementProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.RegionActualParts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem rk_expanded_at (n : Nat) (remap : Nat → Nat) (ranks : List Int)
    {i : Nat} (hi : i < n) :
    rk ((List.range n).map fun v => rk ranks (remap v)) i = rk ranks (remap i) := by
  simp only [rk, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

theorem rankEquivalentR_compound_feasible {rm : ComponentRegions} {cg cg' : Graph}
    {ranks : List Int} {budget : Bool}
    (hrun : rankEquivalentR rm cg = .ok (ranks, cg', budget))
    {e : Edge} (he : e ∈ Compound.constraints cg)
    (ht : e.tail < cg.nodes.length) (hh : e.head < cg.nodes.length) :
    e.minLen ≤ rk ranks e.head - rk ranks e.tail := by
  let n := cg.nodes.length
  let reps := representatives n rm.clusters rm.sets
  let kept := (List.range n).filter fun i => reps.getD i i == i
  let remap := fun i : Nat => kept.idxOf (reps.getD i i)
  let semanticEdges := cg.edges.filter fun e => e.tail != e.head
  let combined := regionRankingEdges cg
  unfold rankEquivalentR at hrun
  dsimp only at hrun
  split at hrun
  · have hfalse : False := by
      simp only [bind, Except.bind] at hrun
      exact absurd hrun (by simp)
    exact hfalse.elim
  · obtain ⟨conds, hconds, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨flags, _, hrun⟩ := bind_ok hrun
    obtain ⟨ranked, hrank, hrun⟩ := bind_ok hrun
    let rankEdges := conds.map fun ce =>
      if ce.synthetic then Edge.mk ce.tail ce.head ce.minLen ce.decl false
      else
        let f := flags.1.getD ce.index false
        let f0 := (combined.getD ce.index default).reversed
        if f != f0 then Edge.mk ce.head ce.tail ce.minLen ce.decl f
        else Edge.mk ce.tail ce.head ce.minLen ce.decl f
    let rankedGraph : Graph :=
      { nodes := kept.map fun i => cg.nodes.getD i default, edges := rankEdges, slot := cg.slot }
    change rankWithBudget rankedGraph = .ok ranked at hrank
    have hR := congrArg Prod.fst (Except.ok.inj hrun)
    change (List.range n).map (fun i => rk ranked.ranks (remap i)) = ranks at hR
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    let k := semanticEdges.length + j
    have hle : semanticEdges.length ≤ k := Nat.le_add_right _ _
    let tagged : Edge := { e with decl := cg.edges.length + j }
    have hcombined : combined[k]? = some tagged := by
      change (semanticEdges ++ ((Compound.constraints cg).zipIdx.map fun q =>
        { q.1 with decl := cg.edges.length + q.2 }))[k]? =
          some ({ e with decl := cg.edges.length + j } : Edge)
      rw [List.getElem?_append_right hle]
      have hk : k - semanticEdges.length = j := Nat.add_sub_cancel_left _ _
      rw [hk]
      simp only [List.getElem?_map, List.getElem?_zipIdx, hj, Nat.zero_add, Option.map_some]
    have hindexed : combined.zipIdx[k]? = some (tagged, k) := by
      simp only [List.getElem?_zipIdx, hcombined, Option.map_some, Nat.zero_add]
    let cond : Edge × Nat → Except LayoutError CondEdge := fun q =>
      if remap q.1.tail == remap q.1.head then .error LayoutError.domain
      else .ok (CondEdge.mk (remap q.1.tail) (remap q.1.head) q.1.decl q.1.minLen
        (decide (semanticEdges.length ≤ q.2)) q.2)
    change combined.zipIdx.mapM cond = .ok conds at hconds
    obtain ⟨_, hlookups⟩ := mapM_getElem? cond _ _ hconds
    obtain ⟨ce, hce, hceLookup⟩ := hlookups k _ hindexed
    have hceEq : ce = CondEdge.mk (remap e.tail) (remap e.head) tagged.decl e.minLen true k := by
      have hsynthetic : decide (semanticEdges.length ≤ k) = true := decide_eq_true hle
      dsimp only [cond] at hce
      split at hce
      · cases hce
      · rw [hsynthetic] at hce
        exact (Except.ok.inj hce).symm
    let rankedEdge := Edge.mk (remap e.tail) (remap e.head) e.minLen tagged.decl false
    have hRankEdge : rankedEdge ∈ rankedGraph.edges := by
      change rankedEdge ∈ rankEdges
      refine List.mem_map.mpr ⟨ce, List.mem_of_getElem? hceLookup, ?_⟩
      subst ce
      rfl
    have rankedOk : rank rankedGraph = .ok ranked.ranks := by
      simp only [RankImpl.rank, hrank]
    have hp := rank_feasible rankedGraph ranked.ranks rankedOk rankedEdge hRankEdge
    rw [← hR, rk_expanded_at _ _ _ hh, rk_expanded_at _ _ _ ht]
    exact hp

theorem componentRunR_compound_feasible {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {e : Edge} (he : e ∈ Compound.constraints cg)
    (ht : e.tail < cg.nodes.length) (hh : e.head < cg.nodes.length) :
    e.minLen ≤ rk run.proper.rank e.head - rk run.proper.rank e.tail := by
  obtain ⟨_, ranks, _, p0, labeled, pCoord, _, _, _, _, placed, q0, _, _, hs⟩ :=
    componentRunR_stages hrun
  have hfeasible : e.minLen ≤ rk ranks e.head - rk ranks e.tail := by
    rcases hs.hRank with ⟨rr, _, hrr, rfl, _, _⟩ | ⟨rm, _, hrr⟩
    · have hr : rank (Compound.rankingGraph cg) = .ok rr.ranks := by
        simp only [RankImpl.rank, hrr]
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
      let tagged : Edge := { e with decl := cg.edges.length + j }
      have hmem : tagged ∈ (Compound.rankingGraph cg).edges := by
        unfold Compound.rankingGraph
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨(e, j), List.mem_zipIdx_iff_getElem?.mpr hj, rfl⟩))
      exact rank_feasible _ _ hr tagged hmem
    · exact rankEquivalentR_compound_feasible hrr he ht hh
  have hranksLen : ranks.length = cg.nodes.length := by
    have hn := hs.hNorm
    unfold NormalizeImpl.normalize at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i hvalid
        have hnormalized : ranks.length = cg'.nodes.length := hvalid.2.1
        exact hnormalized.trans (componentRunR_nodes_eq hrun)
      · cases hn
  obtain ⟨extra₀, hnormRank⟩ := normalize_rank_prefix hs.hNorm
  have hlabels := (Labels.addLabelNodes_metadata hs.hLabels).2.1
  obtain ⟨extra₁, hcoordRank⟩ := (coordinateGraphR_label_prefix P exact spec labeled).2
  rw [hs.hCoord] at hcoordRank
  have hplacedRank : placed.rank = pCoord.rank := by
    rcases hs.hPlaced with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    · rw [h]
    · exact (crossCoordsR_label_metadata h).2.1
  have hfinalRank : run.proper.rank = placed.rank := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hs.hProxy).2.1
  have hsame (v : Nat) (hv : v < cg.nodes.length) : rk run.proper.rank v = rk ranks v := by
    have hv' : v < ranks.length := by rwa [hranksLen]
    have hvl : v < labeled.rank.length := by
      rw [hlabels, hnormRank, List.length_append]
      omega
    rw [hfinalRank, hplacedRank, hcoordRank, NormalizeImpl.rk_append_left hvl,
      hlabels, hnormRank, NormalizeImpl.rk_append_left hv']
  rw [hsame _ ht, hsame _ hh]
  exact hfeasible

end Elegant.Layered.PipelineImpl
