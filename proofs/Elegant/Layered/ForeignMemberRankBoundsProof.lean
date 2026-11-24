import Elegant.Layered.ForeignBorderAlignRankProof
import Elegant.Layered.RunStagePathFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Member ranks of a foreign cluster lie between its titled top and bottom
marker ranks. The `find?`-selected top and bottom are pinned to the
candidate top (`titledTopPin`) and bottom (`titledBottomPin` with the bottom
from `foreignBottomInCandidate`); the bounds then come from `topMemberRankLe`
and `bottomMemberRankCover` transported from proper/coordinate level to the
titled graph. Anchor order follows by instantiating the member bound at the
top marker itself, whose proper record keeps the candidate cluster path
through the coordinate, proxy-width, and synthetic-drop stages. -/
theorem foreignMemberRankBounds : ForeignMemberRankBounds := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
    orderOptions hrun
  have hrkEq : ∀ {labeled : Proper}
      (hcoord : coordinateGraph P labeled = run.coordinateProper)
      (halignedL : labeled.nodes.length = labeled.rank.length)
      (j : Nat), j < labeled.nodes.length →
      rk (titleReservations (sizeProperPorts P labeled)).rank j =
        rk run.proper.rank j := by
    intro labeled hcoord halignedL j hjLt
    have hjLen : j < labeled.rank.length := by
      rw [← halignedL]; exact hjLt
    have e1 : rk (titleReservations (sizeProperPorts P labeled)).rank j =
        rk labeled.rank j := by
      obtain ⟨_, heq⟩ := titled_rank_prefix P labeled
      have h1 : (titleReservations (sizeProperPorts P labeled)).rank[j]? =
          labeled.rank[j]? := by
        rw [heq, List.getElem?_append_left hjLen]
      simp only [rk, List.getD_eq_getElem?_getD, h1]
    have e2 : rk (coordinateGraph P labeled).rank j = rk labeled.rank j := by
      have hlook : labeled.rank[j]? = some labeled.rank[j] :=
        List.getElem?_eq_getElem hjLen
      have hcr := coordinateGraph_rank_record (P := P) hlook
      simp only [rk, List.getD_eq_getElem?_getD, hlook, hcr, Option.getD_some]
    have e3 : run.proper.rank = run.coordinateProper.rank :=
      proper_rank_eq_coordinate hrun
    rw [e1, e3, ← hcoord]
    exact e2.symm
  have toNatMono : ∀ {x y : Int}, 0 ≤ x → x ≤ y → x.toNat ≤ y.toNat := by
    intro x y ha h
    have h1 : (x.toNat : Int) = x := Int.toNat_of_nonneg ha
    have h2 : (y.toNat : Int) = y := Int.toNat_of_nonneg (Int.le_trans ha h)
    have h3 : (x.toNat : Int) ≤ (y.toNat : Int) := by omega
    exact Int.ofNat_le.mp h3
  have properNonneg : ∀ (v : Nat), v < run.proper.nodes.length →
      0 ≤ rk run.proper.rank v := by
    intro v hv
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouteEx, _, _, _, _⟩ :=
      componentRun_spec hrun
    have hcov :=
      (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteEx).1).2.2.2.1
    obtain ⟨_, _, _, hnn⟩ := hcov v hv
    exact hnn
  have perDecl : ∀ {labeled : Proper}
      (hcoord : coordinateGraph P labeled = run.coordinateProper)
      (halignedL : labeled.nodes.length = labeled.rank.length)
      (hkeys : NodeKeys (componentCandidate graph comp candidate) labeled)
      (hrecords : ∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩)
      {a : Nat} {aNode : Node}
      (ha : (componentCandidate graph comp candidate).nodes[a]? = some aNode)
      (hba : aNode.border = -2)
      {top bot : ProperNode × Nat}
      (hmem : top ∈
        (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx)
      (hbTop : top.1.node.border = -2)
      (hlast : top.1.node.clusterPath.getLast? = some aNode.decl)
      (hfind : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath)) = some bot),
      ((rk (titleReservations (sizeProperPorts P labeled)).rank top.2).toNat :
        Int) ≤
        ((rk (titleReservations (sizeProperPorts P labeled)).rank bot.2).toNat :
          Int) ∧
      ∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains aNode.decl =
          true →
        ((rk (titleReservations (sizeProperPorts P labeled)).rank top.2).toNat :
          Int) ≤ rk run.proper.rank v ∧
        rk run.proper.rank v ≤
          ((rk (titleReservations (sizeProperPorts P labeled)).rank bot.2).toNat :
            Int) := by
    intro labeled hcoord halignedL hkeys hrecords a aNode ha hba top bot hmem
      hbTop hlast hfind
    obtain ⟨iB, bNode, hBUlook, hBUbord, hBUdecl, _hBUpath⟩ :=
      foreignBottomInCandidate hgraph hcomp hrun ha hba
    have htopPin : top.2 = a :=
      titledTopPin hgraph hcomp hkeys hrecords ha hba hmem hbTop hlast
    have htopLookup :
        (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
          some top.1 :=
      List.mem_zipIdx_iff_getElem?.mp hmem
    rw [htopPin] at htopLookup
    have hreq : (titleReservations (sizeProperPorts P labeled)).nodes[a]? =
        some (titleF ⟨aNode, false, none, false⟩) :=
      titled_marker_record (hrecords a aNode ha) (Or.inl hba)
    have htop1 : top.1 = titleF ⟨aNode, false, none, false⟩ :=
      Option.some.inj (htopLookup.symm.trans hreq)
    rw [htop1] at hfind
    have hlastA : aNode.clusterPath.getLast? = some aNode.decl := by
      obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source ha (by omega)
      obtain ⟨_, _, _, _, hpath⟩ := measuredGraph_group_origin hgraph hsource hba
      rw [hpath]; simp
    have hlastTitleF :
        (titleF ⟨aNode, false, none, false⟩).node.clusterPath.getLast? =
          some aNode.decl := by
      rw [(titleF_keys _).2.2.1]; exact hlastA
    have hbotPin : bot.2 = iB :=
      titledBottomPin hgraph hcomp hkeys ha hBUlook hBUbord hBUdecl rfl
        hlastTitleF hfind
    have haLt : a < labeled.nodes.length :=
      (List.getElem?_eq_some_iff.mp (hrecords a aNode ha)).1
    have hiBLt : iB < labeled.nodes.length :=
      (List.getElem?_eq_some_iff.mp (hrecords iB bNode hBUlook)).1
    have hrkTopEq := hrkEq hcoord halignedL a haLt
    have hrkBotEq := hrkEq hcoord halignedL iB hiBLt
    have haProperLt : a < run.proper.nodes.length :=
      componentRun_original_nodes_covered hrun a
        (List.getElem?_eq_some_iff.mp ha).1
    have hiBProperLt : iB < run.proper.nodes.length :=
      componentRun_original_nodes_covered hrun iB
        (List.getElem?_eq_some_iff.mp hBUlook).1
    have hcastT : ((rk (titleReservations (sizeProperPorts P labeled)).rank a).toNat :
        Int) = rk run.proper.rank a := by
      rw [hrkTopEq]
      exact Int.toNat_of_nonneg (properNonneg a haProperLt)
    have hcastB : ((rk (titleReservations (sizeProperPorts P labeled)).rank iB).toNat :
        Int) = rk run.proper.rank iB := by
      rw [hrkBotEq]
      exact Int.toNat_of_nonneg (properNonneg iB hiBProperLt)
    have hmemAll : ∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains aNode.decl =
          true →
        ((rk (titleReservations (sizeProperPorts P labeled)).rank top.2).toNat :
          Int) ≤ rk run.proper.rank v ∧
        rk run.proper.rank v ≤
          ((rk (titleReservations (sizeProperPorts P labeled)).rank bot.2).toNat :
            Int) := by
      intro v hv hcv
      have hqv : run.proper.nodes[v]? =
          some (run.proper.nodes.getD v default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
          Option.getD_some]
      have hq : (run.proper.nodes.getD v default, v) ∈
          run.proper.nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hqv
      have hTop : rk run.proper.rank a ≤ rk run.proper.rank v :=
        topMemberRankLe hgraph hlines hwf hfp hcomp hrun ha hba _ hq hcv
      have hgetA :
          (componentCandidate graph comp candidate).nodes.getD a default =
            aNode := by
        rw [List.getD_eq_getElem?_getD, ha, Option.getD_some]
      have hcq : ((run.proper.nodes.getD v default, v)).1.node.clusterPath.contains
          ((componentCandidate graph comp candidate).nodes.getD a default).decl =
            true := by
        rw [hgetA]; exact hcv
      have hBot : rk run.coordinateProper.rank v ≤
          rk run.coordinateProper.rank iB :=
        bottomMemberRankCover hgraph hlines hwf hfp hcomp hrun hBUlook ha
          hBUbord hba hBUdecl _ hq hcq
      rw [htopPin, hbotPin, hcastT, hcastB]
      refine ⟨hTop, ?_⟩
      rw [proper_rank_eq_coordinate hrun]
      exact hBot
    have hcontainsA :
        (run.proper.nodes.getD a default).node.clusterPath.contains aNode.decl =
          true := by
      obtain ⟨qnC, hC, _, _, _, hpathC⟩ :=
        coordinateGraph_decl_prefix (hrecords a aNode ha)
      have hC' : run.coordinateProper.nodes[a]? = some qnC := by
        rw [← hcoord]; exact hC
      obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
        componentRun_spec hrun
      obtain ⟨qnQ, hQ, _, _, _, hpathQ⟩ := proxyWidths_decl_path hproxy hC'
      obtain ⟨qnP, hP, _, _, _, hpathP⟩ := dropSynthetic_decl hQ
      rw [hdrop] at hP
      have hpath : qnP.node.clusterPath = aNode.clusterPath :=
        hpathP.trans (hpathQ.trans (hpathC rfl))
      have hget : run.proper.nodes.getD a default = qnP := by
        rw [List.getD_eq_getElem?_getD, hP, Option.getD_some]
      rw [hget, hpath]
      exact List.contains_iff_mem.mpr (List.mem_of_getLast? hlastA)
    have hmemA := hmemAll a haProperLt hcontainsA
    rw [htopPin, hbotPin] at hmemA
    have hnn : 0 ≤ rk (titleReservations (sizeProperPorts P labeled)).rank a :=
      hrkTopEq ▸ properNonneg a haProperLt
    have hle : rk (titleReservations (sizeProperPorts P labeled)).rank a ≤
        rk (titleReservations (sizeProperPorts P labeled)).rank iB := by
      rw [hrkTopEq, hrkBotEq]
      have h2 := hmemA.2
      rw [hcastB] at h2
      exact h2
    refine ⟨?_, hmemAll⟩
    rw [htopPin, hbotPin]
    exact Int.ofNat_le.mpr (toNatMono hnn hle)
  intro u w uNode wNode hu hw hbU hbW _hne labeled _rr hcoord halignedL hkeys
    _hrr _hranks hrecords topU botU topW botW htopU hbUtop hlastU hbotU htopW
    hbWtop hlastW hbotW
  exact ⟨(perDecl hcoord halignedL hkeys hrecords hu hbU htopU hbUtop hlastU
    hbotU).1,
    (perDecl hcoord halignedL hkeys hrecords hw hbW htopW hbWtop hlastW
    hbotW).1,
    (perDecl hcoord halignedL hkeys hrecords hu hbU htopU hbUtop hlastU
    hbotU).2,
    (perDecl hcoord halignedL hkeys hrecords hw hbW htopW hbWtop hlastW
    hbotW).2⟩

/-- Closed rank-span form: both premises are proved facts. -/
theorem foreignClusterRankSpans' : ForeignClusterRankSpans :=
  foreignClusterRankSpans foreignRankPairAnchors' foreignMemberRankBounds

end Elegant.Layered.PipelineImpl
