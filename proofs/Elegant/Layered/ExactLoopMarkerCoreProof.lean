import Elegant.Layered.ExactGroupMarkerOrderProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Every executed exact group top has both side markers at its own layer. -/
theorem xleg_loopMarkerCoreX_holds (exactIds : List String) : XLEG_LoopMarkerCoreX exactIds := by
  intro inp o res execution comp candidate run orderOptions cg hcomp hcg hrun t nt hnode _ hgroup
  subst cg
  obtain ⟨rr, labeled, bottom, hrr, hc, hkeys, hready, hrecords, hranks, htitled, hbottom⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hgroup
  obtain ⟨original, horiginal, _, _, _, hdeclFind⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq
      hkeys hrecords hnode hgroup hbottom
  obtain ⟨rr', _, hrr', _, _, _, _, hinterval⟩ :=
    X_group_top_lt_bottom execution.graph0_eq execution.graph_eq hcomp hrun
  have hsameRankResult : rr' = rr := Except.ok.inj (hrr'.symm.trans hrr)
  subst rr'
  have hstrict : rk rr.ranks t + 1 ≤ rk rr.ranks bottom.2 :=
    hinterval t nt (original, bottom.2) hnode hgroup hdeclFind
  let titled := titleReservations (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)
  let top : ProperNode := titleF ⟨nt, false, none, false⟩
  have htop : (top, t) ∈ titled.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr htitled
  have htopBorder : top.node.border = -2 := (titleF_keys _).2.1.trans hgroup
  have htopPath : top.node.clusterPath = nt.clusterPath := (titleF_keys _).2.2.1
  have hpairBottom : (titled.nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 && entry.1.node.clusterPath == top.node.clusterPath) = some bottom := by
    rw [htopPath]
    exact hbottom
  obtain ⟨_, _, hinv, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph (componentCandidate execution.graph comp candidate))
    (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hrankLen : rr.ranks.length = (componentCandidate execution.graph comp candidate).nodes.length :=
    hinv.1
  obtain ⟨_, hprefix⟩ : ∃ extra, titled.rank = labeled.rank ++ extra := ⟨_, rfl⟩
  have hrank (i : Nat) (hi : i < rr.ranks.length) : rk titled.rank i = rk rr.ranks i := by
    have hbase : rr.ranks[i]? = some rr.ranks[i] := List.getElem?_eq_getElem hi
    have hlabeled := hranks i rr.ranks[i] hbase
    rw [hprefix, NormalizeImpl.rk_append_left (List.getElem?_eq_some_iff.mp hlabeled).1]
    simp only [rk, List.getD_eq_getElem?_getD, hlabeled, hbase, Option.getD_some]
  have htopBound : t < rr.ranks.length := hrankLen ▸ (List.getElem?_eq_some_iff.mp hnode).1
  have hbottomBound : bottom.2 < rr.ranks.length :=
    hrankLen ▸ (List.getElem?_eq_some_iff.mp horiginal).1
  have hhi : (rk titled.rank t).toNat ≤ (rk titled.rank bottom.2).toNat := by
    rw [hrank t htopBound, hrank bottom.2 hbottomBound]
    omega
  obtain ⟨mL, mR, hleft, hright, hleftRank, hrightRank⟩ :=
    emb_rank_pair execution.params (exactDecls exactIds inp) labeled hready.2.2.2.1
      htop htopBorder hpairBottom (Nat.le_refl (rk titled.rank t).toNat) hhi
  rw [hc] at hleft hright hleftRank hrightRank
  have htopRecord : run.coordinateProper.nodes[t]? = some (clearF top) := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (hrecords t nt hnode) (Or.inl hgroup) rfl
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq hnode hgroup
  have hlast : top.node.clusterPath.getLast? = some nt.decl := by
    rw [htopPath, hpath]
    simp
  have htitleBound : t < titled.rank.length :=
    hready.2.2.2.1 ▸ (List.getElem?_eq_some_iff.mp htitled).1
  have htopRank : rk run.coordinateProper.rank t = rk titled.rank t := by
    rw [← hc]
    change rk (OrderImpl.addClusterBorders titled execution.params.clusterBorderW).rank t = _
    obtain ⟨_, hborderRanks⟩ := addClusterBorders_rank_prefix titled execution.params.clusterBorderW
    rw [hborderRanks, NormalizeImpl.rk_append_left htitleBound]
  have hmarkerLayer {i : Nat}
      (hi : run.coordinateProper.rank[i]? = some ((rk titled.rank t).toNat : Int)) :
      OrderImpl.lay run.coordinateProper i = OrderImpl.lay run.coordinateProper t := by
    have hmarkerRank : rk run.coordinateProper.rank i = ((rk titled.rank t).toNat : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hi, Option.getD_some]
    simp only [OrderImpl.lay, hmarkerRank, htopRank, Int.toNat_natCast]
  exact ⟨mL, mR, _, _, clearF top, htopRecord, hleft, hright, rfl, rfl, hlast, hlast,
    hmarkerLayer hleftRank, hmarkerLayer hrightRank⟩

end Elegant.Layered.PipelineImpl
