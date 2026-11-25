import Elegant.Layered.LoopResGroupHullRightProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.Order

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Plain-member witness for the ordered-marker witness: the inner looping group
has a plain descendant. Strictly narrower than the marker witness (membership
only, no markers or order). True on the nested group-loop probes
(`LoopGroupHullRightTProbe` nestedGrp/nestedLong/sibRight: `m` in the looping
group on every candidate). -/
def LoopResGroupHullRightMember (cg : Graph) : Prop :=
  forall (t : Nat) (nt : Node), cg.nodes[t]? = some nt ->
    (Exists fun e => e ∈ cg.edges /\ e.tail = t /\ e.head = t) ->
    nt.border = -2 ->
    forall (pos : Nat) (np : Node), cg.nodes[pos]? = some np -> np.border = -2 ->
      pos ≠ t -> np.decl ∈ nt.clusterPath ->
      Exists fun (w : Nat) => Exists fun (nw : Node) =>
        cg.nodes[w]? = some nw /\ nw.border = 0 /\ nw.clusterPath.contains nt.decl = true
/-- Group-path prefix for nested groups: the ancestor's cluster path prefixes
the inner group's cluster path. From the global keys via `comp` nodup
(distinct indices give distinct keys, hence distinct decls), the boxes via
`group_node_path_source`, and `Compound.path_ancestor_prefix`. -/
private theorem wgr_group_prefix {inp : Input} {o : Options} {res : FamilyResult}
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
/-- Membership transitively through the inner path: a plain member of the inner
group is also a member of the ancestor. From the inner prefix
(`component_member_path_prefix`) and the ancestor decl in the inner path. -/
private theorem wgr_mem_trans {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate t w : Nat} {nt nw np : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (hnw : (componentCandidate execution.graph comp candidate).nodes[w]? = some nw)
    (hb0 : nw.border = 0)
    (hinsideT : nw.clusterPath.contains nt.decl = true)
    (hmem : np.decl ∈ nt.clusterPath) :
    nw.clusterPath.contains np.decl = true := by
  have hpref := execution.component_member_path_prefix hwf hnt htG hnw hb0 hinsideT
  obtain ⟨suf, hsuf⟩ := hpref
  have hmemW : np.decl ∈ nt.clusterPath ++ suf := List.mem_append.mpr (Or.inl hmem)
  rw [List.contains_eq_mem, decide_eq_true_eq, ← hsuf]
  exact hmemW
/-- Marker-path prefix from the group prefix: the explicit `borderRight` markers
carry their groups' cluster paths definitionally (`borderRight` copies the anchor
path, `titleF` preserves it), so the group prefix transports. -/
private theorem wgr_marker_prefix {t pos : Nat} {nt np : Node}
    (hpre : np.clusterPath <+: nt.clusterPath)
    (w : Int) :
    (OrderImpl.borderRight (titleF ⟨np, false, none, false⟩, pos) w).node.clusterPath <+:
      (OrderImpl.borderRight (titleF ⟨nt, false, none, false⟩, t) w).node.clusterPath := by
  have hL : (OrderImpl.borderRight (titleF ⟨np, false, none, false⟩, pos)
      w).node.clusterPath = np.clusterPath := by
    simp only [OrderImpl.borderRight, (titleF_keys _).2.2.1]
  have hR : (OrderImpl.borderRight (titleF ⟨nt, false, none, false⟩, t)
      w).node.clusterPath = nt.clusterPath := by
    simp only [OrderImpl.borderRight, (titleF_keys _).2.2.1]
  rw [hL, hR]
  exact hpre

/-- Distinct candidate indices give distinct group decls (via `comp` nodup and
`group_node_path_source` decl-equals-key). -/
private theorem wgr_decl_ne {inp : Input} {o : Options} {res : FamilyResult}
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


/-- The ordered-marker witness holds for executed runs modulo the plain-member
residual. From the plain member in the inner group (hence also in the ancestor
via `wgr_mem_trans`), both brackets share the member's layer; the group prefix
(`wgr_group_prefix` transported to the explicit markers) plus `order_border_ends`
puts the inner right marker before the ancestor's. -/
theorem loopResGroupHullRightWitness_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hmemW : LoopResGroupHullRightMember
      (componentCandidate execution.graph comp candidate)) :
    LoopResGroupHullRightWitness
      (componentCandidate execution.graph comp candidate) run := by
  intro t nt hnt het htG pos np hnp hgrp hne hmem
  obtain ⟨w, nw, hnw, hb0, hinsideT⟩ := hmemW t nt hnt het htG pos np hnp hgrp hne hmem
  have hpre := wgr_group_prefix execution hwf hcomp hnt htG hnp hgrp hne hmem
  have hinsideP := wgr_mem_trans execution hwf hnt htG hnw hb0 hinsideT hmem
  obtain ⟨_, ordT, leftT, rightT, hordT, hlayT, _, _, _, _, _, _, hleftT, hrightT,
      hbrackT⟩ :=
    execution.component_member_bracket hwf hcomp hrun hnt htG hnw hb0 hinsideT
  obtain ⟨_, ordP, leftP, rightP, hordP, hlayP, _, _, _, _, _, _, hleftP, hrightP,
      hbrackP⟩ :=
    execution.component_member_bracket hwf hcomp hrun hnp hgrp hnw hb0 hinsideP
  have hordEq : ordT = ordP := by
    have h := hordT.symm.trans hordP
    exact Except.ok.inj h
  obtain ⟨liT, miT, riT, hliT, hmiT, hriT, _, _⟩ := hbrackT.positions
  obtain ⟨liP, miP, riP, hliP, hmiP, hriP, _, _⟩ := hbrackP.positions
  have hmarkPre := wgr_marker_prefix (t := t) (pos := pos) hpre execution.params.clusterBorderW
  have hdeclNe := wgr_decl_ne execution hcomp hnt htG hnp hgrp hne
  have hgetT : (OrderImpl.borderRight (titleF ⟨nt, false, none, false⟩, t)
      execution.params.clusterBorderW).node.clusterPath.getLast? = some nt.decl := by
    have hpathEq : (OrderImpl.borderRight (titleF ⟨nt, false, none, false⟩, t)
        execution.params.clusterBorderW).node.clusterPath = nt.clusterPath := by
      simp only [OrderImpl.borderRight, (titleF_keys _).2.2.1]
    rw [hpathEq]
    have hne0t : nt.border ≠ 0 := by omega
    obtain ⟨keyt2, _, hgt2⟩ := componentCandidate_nonplain_source hnt hne0t
    obtain ⟨_, _, hdeclT2, hpathT2⟩ := execution.group_node_path_source hgt2 htG
    rw [hpathT2, hdeclT2]
    simp
  have hgetP : (OrderImpl.borderRight (titleF ⟨np, false, none, false⟩, pos)
      execution.params.clusterBorderW).node.clusterPath.getLast? = some np.decl := by
    have hpathEq : (OrderImpl.borderRight (titleF ⟨np, false, none, false⟩, pos)
        execution.params.clusterBorderW).node.clusterPath = np.clusterPath := by
      simp only [OrderImpl.borderRight, (titleF_keys _).2.2.1]
    rw [hpathEq]
    have hne0p : np.border ≠ 0 := by omega
    obtain ⟨keyp2, _, hgp2⟩ := componentCandidate_nonplain_source hnp hne0p
    obtain ⟨_, _, hdeclP2, hpathP2⟩ := execution.group_node_path_source hgp2 hgrp
    rw [hpathP2, hdeclP2]
    simp
  have hneIdx : rightT ≠ rightP := by
    intro heq
    subst heq
    have heqN := Option.some.inj (hrightT.symm.trans hrightP)
    have hcon : (some nt.decl : Option Nat) = some np.decl := by
      rw [← hgetT, ← hgetP, heqN]
    exact hdeclNe (Option.some.inj hcon.symm)
  have hwfB := componentRun_coordinate_bordersWellFormed
    execution.graph_eq hcomp hrun
  have horder : OrderImpl.order run.coordinateProper orderOptions =
      .ok ordT.layers := by simp only [OrderImpl.order, hordT]
  have hlayEq : ordP.layers = ordT.layers := by rw [hordEq]
  have hLayEqW : ordP.layers.getD (OrderImpl.lay run.coordinateProper w) [] =
      ordT.layers.getD (OrderImpl.lay run.coordinateProper w) [] := by rw [hordEq]
  have hriP' : (ordT.layers.getD (OrderImpl.lay run.coordinateProper w) [])[riP]? = some rightP := by
    rw [← hLayEqW]; exact hriP
  have hlayerMem : (ordT.layers.getD (OrderImpl.lay run.coordinateProper w) [])
      ∈ ordT.layers := hbrackT.layer_mem
  have hordRes := OrderImpl.order_border_ends run.coordinateProper orderOptions
    ordT.layers horder hwfB
      (ordT.layers.getD (OrderImpl.lay run.coordinateProper w) []) hlayerMem
      riP riT rightP rightT
      (OrderImpl.borderRight (titleF ⟨np, false, none, false⟩, pos)
        execution.params.clusterBorderW)
      (OrderImpl.borderRight (titleF ⟨nt, false, none, false⟩, t)
        execution.params.clusterBorderW)
      hriP' hriT hrightP hrightT hneIdx.symm rfl rfl hmarkPre
  have hlt : riT < riP := hordRes.2 rfl
  have hlayerRun : (ordT.layers.getD (OrderImpl.lay run.coordinateProper w) [])
      ∈ run.layers := by rw [← hlayT]; exact hbrackT.layer_mem
  exact ⟨rightT, rightP,
    (OrderImpl.borderRight (titleF ⟨nt, false, none, false⟩, t)
      execution.params.clusterBorderW),
    (OrderImpl.borderRight (titleF ⟨np, false, none, false⟩, pos)
      execution.params.clusterBorderW),
    (ordT.layers.getD (OrderImpl.lay run.coordinateProper w) []), riT, riP,
    hrightT, rfl, hgetT, hrightP, rfl, hgetP, hlayerRun, hriT, hriP', hlt⟩



/-- Closed group-hull residual modulo the plain-member residual: the ordered
witness from `loopResGroupHullRightWitness_holds` discharges the witness premise
of `loopResGroupHullRight_holds` (first file). Only the member existence plus
the accepted alignment seam stay open. -/
theorem loopResGroupHullRight_closed {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hmemW : LoopResGroupHullRightMember
      (componentCandidate execution.graph comp candidate)) :
    LoopResGroupHullRight execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hwit := loopResGroupHullRightWitness_holds hwf hfp execution hcomp hrun hmemW
  exact loopResGroupHullRight_holds hwf hfp hx execution hcomp hrun hwit

/-- Closed ancestor-hull cover modulo the plain-member residual (unique primed
name): `loopHullRightCover_closed` (first file) with the witness discharged via
`loopResGroupHullRight_closed`. -/
theorem loopHullRightCover_closed' {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hmemW : LoopResGroupHullRightMember
      (componentCandidate execution.graph comp candidate)) :
    LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hGrp := loopResGroupHullRight_closed hwf hframed hx execution hcomp hrun hmemW
  exact loopHullRightCover_holds hwf hframed execution hcomp hrun hGrp

end PipelineImpl

end Layered
end Elegant
