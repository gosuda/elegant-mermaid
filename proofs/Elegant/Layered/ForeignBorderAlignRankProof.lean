import Elegant.Layered.ForeignClusterFactsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Foreign border alignment and rank spans.

This module closes two of the three phase residuals behind
`ForeignBorderSpansSeparated` (`ForeignBorderSpansProof`):

* `foreignBorderChainXAligned` is proved outright from `ForeignBorderSideUps`.
  The side chain supplied by `foreignBorderSideBlocked` is a
  `BorderChainBlock` on every pass; `cluster_pass_block_x_eq` aligns each
  pass on the two markers and `balance_block_x_eq` carries the equality to
  the balanced coordinate. Marker widths (`addClusterBorders_side_width`
  below) and the `run.xs`-to-`leftOf` transport
  (`componentRun_border_record`) finish the goal.
* `foreignClusterRankSpans` is proved from `ForeignRankPairAnchors` plus one
  named rank-phase residual, `ForeignMemberRankBounds`, below: the per-rank
  marker pairs are built outright from `coordinateGraph_rank_pair`, while the
  member-rank intervals (every proper node whose path contains the group
  declaration lies between the anchor ranks) stay open. The residual is
  stated with `toNat` anchor ranks, so no nonnegativity transport is needed
  to connect it to the pair construction.
-/

/-! ## Alignment: side markers carry the border width -/

/-- Every side marker emitted by `addClusterBorders` carries the border
width. Source nodes have no side markers (`BorderConstructionReady`), and
each fold step only appends `borderLeft`/`borderRight` records built with
`width`. -/
private theorem addClusterBorders_side_width (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper => ∀ n ∈ cur.nodes,
        n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
    · intro n hn hs
      rcases hs with hs | hs
      · exact ((hready.1 n hn).1 hs).elim
      · exact ((hready.1 n hn).2 hs).elim
    · intro state hstate entry hentry
      unfold OrderImpl.borderStep
      split
      · exact hstate
      · apply OrderImpl.foldl_inv
          (fun cur : Proper => ∀ n ∈ cur.nodes,
            n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
        · exact hstate
        · intro st hst off _
          intro n hn hs
          have hn' : n ∈ st.nodes ++
              [OrderImpl.borderLeft entry width,
                OrderImpl.borderRight entry width] := hn
          rcases List.mem_append.mp hn' with hold | hnew
          · exact hst n hold hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
            rcases hnew with rfl | rfl <;> rfl
  exact hP node (List.mem_of_getElem? hnode) hside

/-- Cross-coordinate placement: two same-side border markers of one
declaration share one closed `x`-interval. Proved outright from the
alignment-phase residual. -/
theorem foreignBorderChainXAligned (hups : ForeignBorderSideUps) :
    ForeignBorderChainXAligned := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    a b na nb ha hb hsideA hsideB hborder howner
  obtain ⟨hproperA, hxsA⟩ := componentRun_border_record hrun ha hsideA
  obtain ⟨hproperB, hxsB⟩ := componentRun_border_record hrun hb hsideB
  obtain ⟨labeled, hcoordL, hready⟩ :=
    componentRun_titled_border_ready hgraph hcomp hrun
  have hbwf : OrderImpl.BordersWellFormed run.coordinateProper :=
    componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hneA : na.node.clusterPath ≠ [] := hbwf.1 a na ha hsideA
  cases hlast : na.node.clusterPath.getLast? with
  | none =>
    exact absurd (List.getLast?_eq_none_iff.mp hlast) hneA
  | some decl =>
    have hlastB : nb.node.clusterPath.getLast? = some decl := by
      rw [← howner]; exact hlast
    have hcoordA : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW).nodes[a]? =
        some na :=
      coordinateGraph_side_original hready (by rw [hcoordL]; exact ha) hsideA
    have hwA : na.node.w = P.clusterBorderW :=
      addClusterBorders_side_width _ _ hready hcoordA hsideA
    have hcoordB : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW).nodes[b]? =
        some nb :=
      coordinateGraph_side_original hready (by rw [hcoordL]; exact hb) hsideB
    have hwB : nb.node.w = P.clusterBorderW :=
      addClusterBorders_side_width _ _ hready hcoordB hsideB
    obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ :=
      componentRun_spec hrun
    obtain ⟨pos, hcl, hcase⟩ := Elegant.Layered.crossCoordsClusterWith_ok hcross
    rcases hcase with ⟨hempty, _⟩ | ⟨x0, x1, x2, x3, hp0, hp1, hp2, hp3, hbal⟩
    · have halt : a < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp ha).1
      omega
    · have halt : a < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp ha).1
      have hblt : b < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp hb).1
      have hpass : ∀ {k : Nat}, k < 4 → ∀ {x : Array Int},
          CoordsImpl.clusterPass P.nodeGap P.clusterPad
            (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
            (CoordsImpl.typeOneConflicts
              (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k =
            .ok x → x[a]! = x[b]! := by
        intro k hk x hx
        obtain ⟨chain, hiff, hblock⟩ :=
          foreignBorderSideBlocked (decl := decl) (side := na.node.border)
            hups hgraph hcomp hrun hsideA hk hcl
            ((Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad)
              (p := CoordsImpl.borderAlignment run.coordinateProper run.layers)
              (layers := run.layers)
              (marked := CoordsImpl.typeOneConflicts
                (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
              (k := k) hcl).1)
        have hmemA : a ∈ chain :=
          (hiff a).mpr ⟨na, ha, rfl, hwA, hlast⟩
        have hmemB : b ∈ chain :=
          (hiff b).mpr ⟨nb, hb, hborder.symm, hwB, hlastB⟩
        have hne : chain ≠ [] := List.ne_nil_of_mem hmemA
        obtain ⟨r, hrchain, hrr, hrrin, hmem⟩ := hblock hne
        obtain ⟨_, hnr, _, _, _⟩ := (hiff r).mp hrchain
        have hrlt : r < run.coordinateProper.nodes.length :=
          (List.getElem?_eq_some_iff.mp hnr).1
        have hplen : (CoordsImpl.borderAlignment run.coordinateProper run.layers).nodes.length =
            run.coordinateProper.nodes.length := rfl
        have ea := Elegant.Layered.cluster_pass_block_x_eq
          (p := CoordsImpl.borderAlignment run.coordinateProper run.layers)
          hcl hx hrr hrrin (hmem a hmemA)
          (by rw [hplen]; exact halt) (by rw [hplen]; exact hrlt)
        have eb := Elegant.Layered.cluster_pass_block_x_eq
          (p := CoordsImpl.borderAlignment run.coordinateProper run.layers)
          hcl hx hrr hrrin (hmem b hmemB)
          (by rw [hplen]; exact hblt) (by rw [hplen]; exact hrlt)
        rw [ea, eb]
      have e0 := hpass (k := 0) (by decide) (x := x0) hp0
      have e1 := hpass (k := 1) (by decide) (x := x1) hp1
      have e2 := hpass (k := 2) (by decide) (x := x2) hp2
      have e3 := hpass (k := 3) (by decide) (x := x3) hp3
      have hbal' : run.coordinateXs[a]! = run.coordinateXs[b]! :=
        Elegant.Layered.balance_block_x_eq hbal halt hblt e0 e1 e2 e3
      have hxs : run.coordinateXs.getD a 0 = run.coordinateXs.getD b 0 := by
        have ea' : run.coordinateXs[a]! = run.coordinateXs.getD a 0 := by
          rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rfl
        have eb' : run.coordinateXs[b]! = run.coordinateXs.getD b 0 := by
          rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rfl
        rw [← ea', ← eb', hbal']
      have hnW : RouteImpl.nodeW run.proper a = RouteImpl.nodeW run.proper b := by
        simp only [RouteImpl.nodeW, hproperA, hproperB, hwA, hwB]
      have hleft : RouteImpl.leftOf run.proper run.xs a =
          RouteImpl.leftOf run.proper run.xs b := by
        unfold RouteImpl.leftOf RouteImpl.xAt
        rw [hxsA, hxsB, hxs, hnW]
      exact ⟨hleft, by rw [hleft, hnW]⟩

/-! ## Rank spans: member intervals stay open -/

/-- Rank-phase residual: member-rank intervals for two executed group
declarations. Given the titled top/bottom anchors backing the per-rank pair
cover, every proper node whose cluster path contains the declaration lies
between the anchor ranks, and the anchor ranks are ordered. The bounds are
stated with `toNat` anchor ranks, matching the pair cover. This is the
executed constraint-edge rank bracket (top anchor above, bottom anchor
below) transported to proper level; it is about ranks only, pinned to the
same three execution equations as the goal. -/
def ForeignMemberRankBounds : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∀ {labeled : Proper},
    coordinateGraph P labeled = run.coordinateProper →
    ∀ {topU botU topW botW : ProperNode × Nat},
    topU ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx →
    topU.1.node.border = -2 →
    topU.1.node.clusterPath.getLast? = some uNode.decl →
    ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topU.1.node.clusterPath) = some botU →
    topW ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx →
    topW.1.node.border = -2 →
    topW.1.node.clusterPath.getLast? = some wNode.decl →
    ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topW.1.node.clusterPath) = some botW →
    ((((rk (titleReservations (sizeProperPorts P labeled)).rank topU.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPorts P labeled)).rank botU.2).toNat :
        Nat) : Int)) ∧
    ((((rk (titleReservations (sizeProperPorts P labeled)).rank topW.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPorts P labeled)).rank botW.2).toNat :
        Nat) : Int)) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains uNode.decl = true →
      ((((rk (titleReservations (sizeProperPorts P labeled)).rank topU.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPorts P labeled)).rank botU.2).toNat :
          Nat) : Int)))) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains wNode.decl = true →
      ((((rk (titleReservations (sizeProperPorts P labeled)).rank topW.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPorts P labeled)).rank botW.2).toNat :
          Nat) : Int))))

/-- Rank assignment: two executed group declarations each carry a closed
rank interval with a left/right border marker pair at every rank. The pairs
are built outright from the rank-phase residual; the member intervals come
from `ForeignMemberRankBounds`. -/
theorem foreignClusterRankSpans (hanch : ForeignRankPairAnchors)
    (hmem : ForeignMemberRankBounds) : ForeignClusterRankSpans := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    u w uNode wNode hu hw hbU hbW hne
  obtain ⟨labeled, hcoord, haligned, hU⟩ :=
    hanch hgraph hcomp hrun hu hw hbU hbW hne
  obtain ⟨topU, botU, htopU, hbUtop, hlastU, hbotU, hW⟩ := hU
  obtain ⟨topW, botW, htopW, hbWtop, hlastW, hbotW⟩ := hW
  have hpairU : ∀ {rank : Nat},
      (rk (titleReservations (sizeProperPorts P labeled)).rank topU.2).toNat ≤ rank →
      rank ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank botU.2).toNat →
      ∃ (mLU mRU : Nat) (nLU nRU : ProperNode),
        run.coordinateProper.nodes[mLU]? = some nLU ∧
        nLU.node.border = -1 ∧ nLU.node.clusterPath.getLast? = some uNode.decl ∧
        rk run.coordinateProper.rank mLU = (rank : Int) ∧
        run.coordinateProper.nodes[mRU]? = some nRU ∧
        nRU.node.border = 1 ∧ nRU.node.clusterPath.getLast? = some uNode.decl ∧
        rk run.coordinateProper.rank mRU = (rank : Int) := by
    intro rank hlo hhi
    obtain ⟨lU, rU, hLU, hRU, hrlU, hrrU⟩ :=
      coordinateGraph_rank_pair P labeled haligned htopU hbUtop hbotU hlo hhi
    rw [hcoord] at hLU hRU hrlU hrrU
    have hrkLU : rk run.coordinateProper.rank lU = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrlU, Option.getD_some]
    have hrkRU : rk run.coordinateProper.rank rU = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrrU, Option.getD_some]
    exact ⟨lU, rU, _, _, hLU, rfl, hlastU, hrkLU, hRU, rfl, hlastU, hrkRU⟩
  have hpairW : ∀ {rank : Nat},
      (rk (titleReservations (sizeProperPorts P labeled)).rank topW.2).toNat ≤ rank →
      rank ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank botW.2).toNat →
      ∃ (mLW mRW : Nat) (nLW nRW : ProperNode),
        run.coordinateProper.nodes[mLW]? = some nLW ∧
        nLW.node.border = -1 ∧ nLW.node.clusterPath.getLast? = some wNode.decl ∧
        rk run.coordinateProper.rank mLW = (rank : Int) ∧
        run.coordinateProper.nodes[mRW]? = some nRW ∧
        nRW.node.border = 1 ∧ nRW.node.clusterPath.getLast? = some wNode.decl ∧
        rk run.coordinateProper.rank mRW = (rank : Int) := by
    intro rank hlo hhi
    obtain ⟨lW, rW, hLW, hRW, hrlW, hrrW⟩ :=
      coordinateGraph_rank_pair P labeled haligned htopW hbWtop hbotW hlo hhi
    rw [hcoord] at hLW hRW hrlW hrrW
    have hrkLW : rk run.coordinateProper.rank lW = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrlW, Option.getD_some]
    have hrkRW : rk run.coordinateProper.rank rW = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrrW, Option.getD_some]
    exact ⟨lW, rW, _, _, hLW, rfl, hlastW, hrkLW, hRW, rfl, hlastW, hrkRW⟩
  obtain ⟨hordU, hordW, hmemU, hmemW⟩ :=
    hmem hgraph hcomp hrun hu hw hbU hbW hne hcoord
      htopU hbUtop hlastU hbotU htopW hbWtop hlastW hbotW
  refine ⟨_, _, _, _, hordU, hordW, hmemU, hmemW, ?_, ?_⟩
  · intro r hrU hrW
    have h0r : 0 ≤ r := by omega
    have hrcast : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0r
    have hlo : (rk (titleReservations (sizeProperPorts P labeled)).rank topU.2).toNat ≤
        r.toNat := by omega
    have hhi : r.toNat ≤
        (rk (titleReservations (sizeProperPorts P labeled)).rank botU.2).toNat := by omega
    obtain ⟨mL, mR, nL, nR, hL, hbL, hoL, hrL, hR, hbR, hoR, hrR⟩ :=
      hpairU hlo hhi
    refine ⟨mL, mR, nL, nR, hL, hbL, hoL, ?_, hR, hbR, hoR, ?_⟩
    · rw [← hrcast]; exact hrL
    · rw [← hrcast]; exact hrR
  · intro r hrU hrW
    have h0r : 0 ≤ r := by omega
    have hrcast : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0r
    have hlo : (rk (titleReservations (sizeProperPorts P labeled)).rank topW.2).toNat ≤
        r.toNat := by omega
    have hhi : r.toNat ≤
        (rk (titleReservations (sizeProperPorts P labeled)).rank botW.2).toNat := by omega
    obtain ⟨mL, mR, nL, nR, hL, hbL, hoL, hrL, hR, hbR, hoR, hrR⟩ :=
      hpairW hlo hhi
    refine ⟨mL, mR, nL, nR, hL, hbL, hoL, ?_, hR, hbR, hoR, ?_⟩
    · rw [← hrcast]; exact hrL
    · rw [← hrcast]; exact hrR

end Elegant.Layered.PipelineImpl
