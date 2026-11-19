import Elegant.Layered.LoopResGroupHullRightWitnessProof
import Elegant.Layered.BottomClearanceNesting

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- TRUTH FIRST: `LoopResGroupHullRightMember` as stated (in
`LoopResGroupHullRightWitnessProof`) is FALSE. Witness
(`LoopResGroupHullRightMemberProbe`: `emptyNested`, input boxes `[O group, G in
O]`, route `G -> G`, no plain boxes, no labels): `WellFormed` and
`framedParents` hold, `layout` succeeds, and on every candidate `0..4` the run
succeeds with `t = G` (`decl = 1`, `border = -2`, self-loop edge `(1, 1)`) and
`pos = O` (`decl = 0`, `border = -2`, `0 ∈ [0, 1] = clusterPath G`), yet no
border-`0` node `w` has `clusterPath.contains 1 = true` (`hasW = false`). The
candidate nodes are exactly the two group tops and two bottoms, so an empty
looping group has no plain member at all. The same probe shows the ordered
right markers DO share a layer there (`wit = true` on every candidate, e.g.
candidate 0 layer `[8, 14, 1, 5, 15, 9]` holds G-right `15` before O-right `9`
alongside the G top `1` and G title `5`). Hence this file proves the ordered
marker witness with NO member premise: the (b) branch below replays the member
bracket argument with the looping group's own top rank as the shared-layer
carrier. The only unproved ingredient is transitive ancestor rank nesting
(`LoopResGroupHullRightAncestorRanks`), checked by `#eval` on `emptyNested`,
`nestedGrp`, and a three-level empty nest. -/
def LoopResGroupHullRightAncestorRanks {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (_hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) : Prop :=
  ∀ {rr : RankImpl.RankResult},
    rankWithBudget (Compound.rankingGraph
      (componentCandidate execution.graph comp candidate)) = .ok rr →
    ∀ {a b : Nat} {na nb : Node},
      (componentCandidate execution.graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.clusterPath <+: nb.clusterPath →
      rk rr.ranks a ≤ rk rr.ranks b ∧
      ∀ {ba bb : Node × Nat},
        ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
          entry.1.border == 2 && entry.1.decl == na.decl) = some ba →
        ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
          entry.1.border == 2 && entry.1.decl == nb.decl) = some bb →
        rk rr.ranks bb.2 ≤ rk rr.ranks ba.2

/-- Group-path prefix for nested groups (prefixed copy of `wgr_group_prefix` in
`LoopResGroupHullRightWitnessProof`, since private lemmas do not resolve
across modules): the ancestor's cluster path prefixes the inner group's
cluster path. -/
private theorem lrw_group_prefix {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate t pos : Nat} {nt np : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) (hmem : np.decl ∈ nt.clusterPath) :
    np.clusterPath <+: nt.clusterPath := by
  have hne0t : nt.border ≠ 0 := by omega
  have hne0p : np.border ≠ 0 := by omega
  obtain ⟨keyt, hkeyt, hgt⟩ :=
    componentCandidate_nonplain_source hnt hne0t
  obtain ⟨keyp, hkeyp, hgp⟩ :=
    componentCandidate_nonplain_source hnp hne0p
  obtain ⟨boxT, hboxT, hdeclT, hpathT⟩ :=
    execution.group_node_path_source hgt htG
  obtain ⟨boxP, hboxP, hdeclP, hpathP⟩ :=
    execution.group_node_path_source hgp hgrp
  have htNe : t ≠ pos := Ne.symm hne
  have hnod := components_nodup execution.graph comp hcomp
  have hlenT : t < comp.length := (List.getElem?_eq_some_iff.mp hkeyt).1
  have hkeyNe : keyt ≠ keyp := by
    intro hkk
    have hmap : comp[t]? = comp[pos]? := by rw [hkeyt, hkeyp, hkk]
    exact htNe ((List.Nodup.getElem?_inj hlenT hnod).mp hmap)
  have hmem' : keyp ∈ nt.clusterPath := by rw [← hdeclP]; exact hmem
  rw [hpathT] at hmem'
  rcases List.mem_append.mp hmem' with hleft | hright
  · have hpre := Compound.path_ancestor_prefix (inputModel inp o) hwf hboxP hboxT hleft
    have hpathP' : np.clusterPath =
      Compound.path (inputModel inp o).boxes boxP ++ [keyp] := hpathP
    have hpathT' : nt.clusterPath =
      Compound.path (inputModel inp o).boxes boxT ++ [keyt] := hpathT
    have hpre2 : np.clusterPath <+: Compound.path (inputModel inp o).boxes boxT := by
      rw [hpathP']; exact hpre
    have hsub : Compound.path (inputModel inp o).boxes boxT <+:
        Compound.path (inputModel inp o).boxes boxT ++ [keyt] := ⟨[keyt], rfl⟩
    have hcomb := hpre2.trans hsub
    rw [← hpathT'] at hcomb
    exact hcomb
  · have hEq : keyp = keyt := List.mem_singleton.mp hright
    exact absurd hEq hkeyNe.symm

/-- Distinct candidate indices give distinct group decls (prefixed copy of
`wgr_decl_ne` in `LoopResGroupHullRightWitnessProof`). -/
private theorem lrw_decl_ne {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate t pos : Nat} {nt np : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) : np.decl ≠ nt.decl := by
  have hne0t : nt.border ≠ 0 := by omega
  have hne0p : np.border ≠ 0 := by omega
  obtain ⟨keyt, hkeyt, hgt⟩ := componentCandidate_nonplain_source hnt hne0t
  obtain ⟨keyp, hkeyp, hgp⟩ := componentCandidate_nonplain_source hnp hne0p
  obtain ⟨_, _, hdeclT, _⟩ := execution.group_node_path_source hgt (by omega)
  obtain ⟨_, _, hdeclP, _⟩ := execution.group_node_path_source hgp (by omega)
  have htNe : t ≠ pos := Ne.symm hne
  have hnod := components_nodup execution.graph comp hcomp
  have hlenT : t < comp.length := (List.getElem?_eq_some_iff.mp hkeyt).1
  have hkeyNe : keyt ≠ keyp := by
    intro hkk
    have hmap : comp[t]? = comp[pos]? := by rw [hkeyt, hkeyp, hkk]
    exact htNe ((List.Nodup.getElem?_inj hlenT hnod).mp hmap)
  rw [hdeclP, hdeclT]
  exact Ne.symm hkeyNe

/-- Markers of the looping group and its ancestor at the looping top's rank:
for executable candidates both groups get a left/right marker pair at
`(rk rr.ranks t).toNat` (`coordinateGraph_rank_pair`), the looping group's own
rank from `componentRun_group_top_lt_bottom` and the ancestor's from the
ancestor-rank residual. Needs no plain member: the group's own top rank is the
shared-layer carrier. -/
private theorem lrw_pair_markers {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun)
    {t pos : Nat} {nt np : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) (hmem : np.decl ∈ nt.clusterPath) :
    ∃ (leftT rightT leftP rightP : Nat) (nLT nRT nLP nRP : ProperNode),
      run.coordinateProper.nodes[leftT]? = some nLT ∧
      run.coordinateProper.nodes[rightT]? = some nRT ∧
      run.coordinateProper.nodes[leftP]? = some nLP ∧
      run.coordinateProper.nodes[rightP]? = some nRP ∧
      nLT.node.border = -1 ∧ nRT.node.border = 1 ∧
      nLP.node.border = -1 ∧ nRP.node.border = 1 ∧
      nLT.node.clusterPath = nt.clusterPath ∧ nRT.node.clusterPath = nt.clusterPath ∧
      nLP.node.clusterPath = np.clusterPath ∧ nRP.node.clusterPath = np.clusterPath ∧
      nRT.node.clusterPath.getLast? = some nt.decl ∧
      nRP.node.clusterPath.getLast? = some np.decl ∧
      rk run.coordinateProper.rank leftT = rk run.coordinateProper.rank rightT ∧
      rk run.coordinateProper.rank leftP = rk run.coordinateProper.rank rightP ∧
      rk run.coordinateProper.rank rightT = rk run.coordinateProper.rank rightP ∧
      nLT.dummy = false ∧ nRT.dummy = false ∧ nLP.dummy = false ∧ nRP.dummy = false := by
  have hpre := lrw_group_prefix execution hwf hcomp hnt htG hnp hgrp hne hmem
  obtain ⟨rr, labeled, bottomT, hrr, hc, hk, hready, hrecords, hranks, htitledT, hfindT⟩ :=
    componentRun_group_bottom_source execution.graph_eq hcomp hrun hnt htG
  obtain ⟨bottomP, htitledP, hfindP⟩ :=
    componentRun_prepared_group_bottom execution.graph_eq hcomp hrun hc hk hready
      hrecords hnp hgrp
  obtain ⟨origBT, hcgBT, _, _, _, hcgFindT⟩ :=
    candidate_titled_bottom_constraint_source execution.graph_eq hk hrecords hnt htG hfindT
  obtain ⟨origBP, hcgBP, _, _, _, hcgFindP⟩ :=
    candidate_titled_bottom_constraint_source execution.graph_eq hk hrecords hnp hgrp hfindP
  obtain ⟨rr2, _, hrr2, _, _, _, _, htopLT⟩ :=
    componentRun_group_top_lt_bottom execution.graph_eq hcomp hrun
  have hrrEq : rr2 = rr := Except.ok.inj (hrr2.symm.trans hrr)
  have hleT : rk rr.ranks t ≤ rk rr.ranks bottomT.2 := by
    have h := htopLT t nt (origBT, bottomT.2) hnt htG hcgFindT
    rw [hrrEq] at h
    dsimp only at h
    omega
  obtain ⟨hleTop, hbotFn⟩ := hres hrr hnp hgrp hnt htG hpre
  have hleP : rk rr.ranks t ≤ rk rr.ranks bottomP.2 := by
    have h := hbotFn hcgFindP hcgFindT
    dsimp only at h
    omega
  have htLen : t < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnt).1
  have hbtLen : bottomT.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hcgBT).1
  have hpLen : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnp).1
  have hbpLen : bottomP.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hcgBP).1
  have htopRkT := (prepared_titled_original_rk (P := execution.params) hrr hranks htLen).1
  have hbotRkT := (prepared_titled_original_rk (P := execution.params) hrr hranks hbtLen).1
  have htopRkP := (prepared_titled_original_rk (P := execution.params) hrr hranks hpLen).1
  have hbotRkP := (prepared_titled_original_rk (P := execution.params) hrr hranks hbpLen).1
  have hnnT : 0 ≤ rk rr.ranks t := rankWithBudget_rk_nonneg hrr t
  have hnnBT : 0 ≤ rk rr.ranks bottomT.2 := rankWithBudget_rk_nonneg hrr bottomT.2
  have hnnBP : 0 ≤ rk rr.ranks bottomP.2 := rankWithBudget_rk_nonneg hrr bottomP.2
  have htopBorderT : (titleF ⟨nt, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans htG
  have htopBorderP : (titleF ⟨np, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgrp
  have hnnP : 0 ≤ rk rr.ranks pos := rankWithBudget_rk_nonneg hrr pos
  have hbottomT : ((titleReservations (sizeProperPorts execution.params labeled)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == (titleF ⟨nt, false, none, false⟩).node.clusterPath) =
      some bottomT := by
    simpa only [(titleF_keys _).2.2.1] using hfindT
  have hbottomP : ((titleReservations (sizeProperPorts execution.params labeled)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == (titleF ⟨np, false, none, false⟩).node.clusterPath) =
      some bottomP := by
    simpa only [(titleF_keys _).2.2.1] using hfindP
  have hloT : (rk (titleReservations (sizeProperPorts execution.params labeled)).rank t).toNat ≤
      (rk rr.ranks t).toNat := by rw [htopRkT]; omega
  have hhiT : (rk rr.ranks t).toNat ≤
      (rk (titleReservations (sizeProperPorts execution.params labeled)).rank
        bottomT.2).toNat := by
    have hhiT' : (rk rr.ranks t).toNat ≤ (rk rr.ranks bottomT.2).toNat := by omega
    have hhiTc : (rk rr.ranks t).toNat ≤
        (rk (titleReservations (sizeProperPorts execution.params labeled)).rank
          bottomT.2).toNat := by
      rw [hbotRkT]; exact hhiT'
    exact hhiTc
  have hloP : (rk (titleReservations (sizeProperPorts execution.params labeled)).rank
        pos).toNat ≤ (rk rr.ranks t).toNat := by
    have hloP' : (rk rr.ranks pos).toNat ≤ (rk rr.ranks t).toNat := by omega
    have hloPc : (rk (titleReservations (sizeProperPorts execution.params labeled)).rank
        pos).toNat ≤ (rk rr.ranks t).toNat := by
      rw [htopRkP]; exact hloP'
    exact hloPc
  have hhiP : (rk rr.ranks t).toNat ≤
      (rk (titleReservations (sizeProperPorts execution.params labeled)).rank
        bottomP.2).toNat := by
    have hhiP' : (rk rr.ranks t).toNat ≤ (rk rr.ranks bottomP.2).toNat := by omega
    have hhiPc : (rk rr.ranks t).toNat ≤
        (rk (titleReservations (sizeProperPorts execution.params labeled)).rank
          bottomP.2).toNat := by
      rw [hbotRkP]; exact hhiP'
    exact hhiPc
  obtain ⟨leftT, rightT, hleftT, hrightT, hleftRankT, hrightRankT⟩ :=
    coordinateGraph_rank_pair execution.params labeled hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitledT) htopBorderT hbottomT
      (rank := (rk rr.ranks t).toNat) hloT hhiT
  obtain ⟨leftP, rightP, hleftP, hrightP, hleftRankP, hrightRankP⟩ :=
    coordinateGraph_rank_pair execution.params labeled hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitledP) htopBorderP hbottomP
      (rank := (rk rr.ranks t).toNat) hloP hhiP
  have hnatT : ((rk rr.ranks t).toNat : Int) = rk rr.ranks t := by omega
  have hleftValT : rk (coordinateGraph execution.params labeled).rank leftT =
      rk rr.ranks t := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRankT, Option.getD_some] using hnatT
  have hrightValT : rk (coordinateGraph execution.params labeled).rank rightT =
      rk rr.ranks t := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRankT, Option.getD_some] using hnatT
  have hleftValP : rk (coordinateGraph execution.params labeled).rank leftP =
      rk rr.ranks t := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRankP, Option.getD_some] using hnatT
  have hrightValP : rk (coordinateGraph execution.params labeled).rank rightP =
      rk rr.ranks t := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRankP, Option.getD_some] using hnatT
  rw [hc] at hleftT hrightT hleftP hrightP hleftValT hrightValT hleftValP hrightValP
  obtain ⟨keyt, _, hgt⟩ := componentCandidate_nonplain_source hnt (by omega)
  obtain ⟨_, _, hdeclT, hpathT⟩ := execution.group_node_path_source hgt htG
  obtain ⟨keyp, _, hgp⟩ := componentCandidate_nonplain_source hnp (by omega)
  obtain ⟨_, _, hdeclP, hpathP⟩ := execution.group_node_path_source hgp hgrp
  have hpathT0 : (titleF ⟨nt, false, none, false⟩).node.clusterPath = nt.clusterPath :=
    (titleF_keys _).2.2.1
  have hpathP0 : (titleF ⟨np, false, none, false⟩).node.clusterPath = np.clusterPath :=
    (titleF_keys _).2.2.1
  have hgetT0 : (titleF ⟨nt, false, none, false⟩).node.clusterPath.getLast? =
      some nt.decl := by
    rw [hpathT0, hpathT, hdeclT]
    simp
  have hgetP0 : (titleF ⟨np, false, none, false⟩).node.clusterPath.getLast? =
      some np.decl := by
    rw [hpathP0, hpathP, hdeclP]
    simp
  refine ⟨leftT, rightT, leftP, rightP, _, _, _, _, hleftT, hrightT, hleftP, hrightP,
    rfl, rfl, rfl, rfl, hpathT0, hpathT0, hpathP0, hpathP0, hgetT0, hgetP0,
    hleftValT.trans hrightValT.symm, hleftValP.trans hrightValP.symm,
    hrightValT.trans hrightValP.symm, rfl, rfl, rfl, rfl⟩


/-- The ordered-marker witness from the looping group's own markers: both
right markers share the looping top's layer, ordered inner-before-outer. The
layer membership comes from equal ranks, the order from `order_border_ends`
with the transported group prefix. Needs no plain member. -/
private theorem lrw_pair_witness {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun)
    {t pos : Nat} {nt np : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) (hmem : np.decl ∈ nt.clusterPath) :
    ∃ (mRt mRp : Nat) (nRt nRp : ProperNode) (layer : List Nat) (j iv : Nat),
      run.coordinateProper.nodes[mRt]? = some nRt ∧
      nRt.node.border = 1 ∧ nRt.node.clusterPath.getLast? = some nt.decl ∧
      run.coordinateProper.nodes[mRp]? = some nRp ∧
      nRp.node.border = 1 ∧ nRp.node.clusterPath.getLast? = some np.decl ∧
      layer ∈ run.layers ∧ layer[j]? = some mRt ∧ layer[iv]? = some mRp ∧ j < iv := by
  obtain ⟨leftT, rightT, leftP, rightP, nLT, nRT, nLP, nRP, hcoordLT, hcoordRT,
      hcoordLP, hcoordRP, hbLT, hbRT, hbLP, hbRP, hpathLT, hpathRT, hpathLP, hpathRP,
      hgetT, hgetP, hrkTT, hrkPP, hrkTP, _hdumLT, hdumRT, _hdumLP, hdumRP⟩ :=
    lrw_pair_markers execution hwf hcomp hrun hres hnt htG hnp hgrp hne hmem
  have hmarkPre : nRP.node.clusterPath <+: nRT.node.clusterPath := by
    rw [hpathRP, hpathRT]
    exact lrw_group_prefix execution hwf hcomp hnt htG hnp hgrp hne hmem
  have hdeclNe := lrw_decl_ne execution hcomp hnt htG hnp hgrp hne
  have hlayTP : OrderImpl.lay run.coordinateProper rightT =
      OrderImpl.lay run.coordinateProper rightP := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrkTP
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ := componentRun_spec hrun
  have hwfB := componentRun_coordinate_bordersWellFormed execution.graph_eq hcomp hrun
  obtain ⟨hrT, hmemT⟩ := ExecutedBorderOrder.node_layer _ _ _ horder hcoordRT
  obtain ⟨hrP, hmemP⟩ := ExecutedBorderOrder.node_layer _ _ _ horder hcoordRP
  rw [← hlayTP] at hmemP
  have heqL : ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) [] =
      ord.layers[OrderImpl.lay run.coordinateProper rightT] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrT, Option.getD_some]
  have hlayer : ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) [] ∈
      ord.layers := by
    rw [heqL]
    exact List.getElem_mem hrT
  obtain ⟨j, hj, heqj⟩ := List.mem_iff_getElem.mp hmemT
  obtain ⟨iv, hiv, heqiv⟩ := List.mem_iff_getElem.mp hmemP
  have hj' : (ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) [])[j]? =
      some rightT := by
    simp only [List.getElem?_eq_getElem hj, heqj]
  have hiv' : (ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) [])[iv]? =
      some rightP := by
    simp only [List.getElem?_eq_getElem hiv, heqiv]
  have horderEq : OrderImpl.order run.coordinateProper orderOptions =
      .ok ord.layers := by
    simp only [OrderImpl.order, horder]
  have hneIdx : rightT ≠ rightP := by
    intro heq
    subst heq
    have heqN := Option.some.inj (hcoordRT.symm.trans hcoordRP)
    have hcon : (some nt.decl : Option Nat) = some np.decl := by
      rw [← hgetT, ← hgetP, heqN]
    exact hdeclNe (Option.some.inj hcon.symm)
  have hordRes := OrderImpl.order_border_ends run.coordinateProper orderOptions
    ord.layers horderEq hwfB
    (ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) []) hlayer
    iv j rightP rightT nRP nRT hiv' hj' hcoordRP hcoordRT hneIdx.symm hdumRP hdumRT hmarkPre
  have hlt : j < iv := hordRes.2 hbRP
  have hlayerRun : ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) [] ∈
      run.layers := by
    rw [← hlayers]
    exact hlayer
  exact ⟨rightT, rightP, nRT, nRP,
    ord.layers.getD (OrderImpl.lay run.coordinateProper rightT) [], j, iv,
    hcoordRT, hbRT, hgetT, hcoordRP, hbRP, hgetP, hlayerRun, hj', hiv', hlt⟩

/-- The ordered-marker witness holds for every executed plain run, with no
member premise: when the member fact holds the imported proof applies,
otherwise the looping group's own markers carry the shared layer. The only
open ingredient is transitive ancestor rank nesting. -/
theorem loopResGroupHullRightWitness_closed {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun) :
    LoopResGroupHullRightWitness
      (componentCandidate execution.graph comp candidate) run := by
  by_cases hmem : LoopResGroupHullRightMember
    (componentCandidate execution.graph comp candidate)
  · exact loopResGroupHullRightWitness_holds hwf hfp execution hcomp hrun hmem
  · intro t nt hnt _het htG pos np hnp hgrp hne hmem2
    clear hmem
    exact lrw_pair_witness execution hwf hcomp hrun hres hnt htG hnp hgrp hne hmem2

/-- Closed group-hull residual modulo the ancestor-rank residual (unique doubly
primed name): `loopResGroupHullRight_holds` (first file) with the witness
discharged via `loopResGroupHullRightWitness_closed`. Only ancestor rank
nesting plus the accepted alignment seam stay open. -/
theorem loopResGroupHullRight_closed'' {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun) :
    LoopResGroupHullRight execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hwit := loopResGroupHullRightWitness_closed hwf hfp execution hcomp hrun hres
  exact loopResGroupHullRight_holds hwf hfp hx execution hcomp hrun hwit

/-- Closed ancestor-hull cover modulo the ancestor-rank residual (unique doubly
primed name): `loopHullRightCover_holds` (first file) with the group hull
discharged via `loopResGroupHullRight_closed''`. -/
theorem loopHullRightCover_closed'' {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun) :
    LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hGrp := loopResGroupHullRight_closed'' hwf hframed hx execution hcomp hrun hres
  exact loopHullRightCover_holds hwf hframed execution hcomp hrun hGrp

end PipelineImpl

end Layered
end Elegant
