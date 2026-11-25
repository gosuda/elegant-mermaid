import Elegant.Layered.RegionC5ActiveSelected
import Elegant.Layered.RegionDifferentLayerClearance
import Elegant.Layered.StrictMemberFrameProof

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- Distinct executed rank bands retain their strict separation after exact reserves. -/
theorem componentRunR_strictRankBandGap {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {r s : Nat} {layer nextLayer : List Nat} (hrs : r < s)
    (hr : run.layers[r]? = some layer) (hs : run.layers[s]? = some nextLayer) :
    run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper layer <
      run.top.getD s 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, _, ⟨_, top⟩, ysMid, stages⟩ :=
    componentRunR_stages hrun
  obtain ⟨extra, shifts, _, hnonneg, hprefix, hshiftLen, htop, _⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top stages.hReserve
  have hsTop : s < top.length := by
    rw [(CoordsImpl.rankCoordsWith_length stages.hYt).2]
    exact (List.getElem?_eq_some_iff.mp hs).1
  have hrTop := Nat.lt_trans hrs hsTop
  have hsShift : s < shifts.length := by rwa [hshiftLen]
  have hrShift := Nat.lt_trans hrs hsShift
  have hmono : shifts.Pairwise (· ≤ ·) := by
    rw [hprefix]
    exact reserveShift_prefix_pairwise extra hnonneg 0 [] (by simp) (by simp)
  have hstep : shifts.getD r 0 ≤ shifts.getD s 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hrShift, List.getElem?_eq_getElem hsShift]
    exact hmono.rel_getElem_of_lt hrShift hsShift hrs
  have hgap := rankAxis_band_top_strict stages.hYt r s layer nextLayer hrs hr hs
  rw [htop r hrTop, htop s hsTop, stages.hCoordProper]
  omega

/-- The direct child group's semantic markers stay strictly between the
parent's markers in either executed region ranking branch. -/
theorem componentRunR_compound_child_strictRankWindow {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {parent parentBottom child childBottom : Node × Nat}
    (hp : parent ∈ cg.nodes.zipIdx) (hpRole : parent.1.border = -2)
    (hpBottom : (cg.nodes.zipIdx.find? fun q =>
      q.1.border == 2 && q.1.decl == parent.1.decl) = some parentBottom)
    (hc : child ∈ cg.nodes.zipIdx) (hcRole : child.1.border = -2)
    (hpath : child.1.clusterPath.dropLast = parent.1.clusterPath)
    (hcBottom : (cg.nodes.zipIdx.find? fun q =>
      q.1.border == 2 && q.1.decl == child.1.decl) = some childBottom) :
    rk run.proper.rank parent.2 < rk run.proper.rank child.2 ∧
      rk run.proper.rank childBottom.2 < rk run.proper.rank parentBottom.2 := by
  obtain ⟨hupper, hlower⟩ :=
    compound_child_constraint_edges hp hpRole hpBottom hc hcRole hpath hcBottom
  have feasible (edge : Edge) (he : edge ∈ Compound.constraints cg) :
      edge.minLen ≤ rk run.proper.rank edge.head - rk run.proper.rank edge.tail := by
    obtain ⟨ht, hh⟩ := constraints_bounded cg edge he
    exact componentRunR_compound_feasible hrun he ht hh
  have ht := feasible _ hupper
  have hb := feasible _ hlower
  dsimp only at ht hb
  exact ⟨by omega, by omega⟩

/-- Both rank-axis margins of an active leaf frame. A fixed-size group is a
leaf here when the executed candidate has border zero, including a zero-size leaf. -/
theorem componentRunR_active_leaf_strictVertical {P : Params} {exactIds : List String}
    {spec : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some spec) inp cg labels orderOptions =
      .ok (cg', run))
    (hactive : newComponentRegions (some spec) P inp cg = .ok (some rm))
    {top member : Node × Nat} {bottom : Node × Nat}
    (htop : cg'.nodes[top.2]? = some top.1) (htopRole : top.1.border = -2)
    (hbottom : cg'.nodes.zipIdx.find? (fun q => q.1.border == 2 && q.1.decl == top.1.decl) =
      some bottom)
    (hmember : cg'.nodes[member.2]? = some member.1) (hplain : member.1.border = 0)
    (htopPath : top.1.clusterPath.contains top.1.decl = true)
    (hbottomPath : bottom.1.clusterPath.contains top.1.decl = true)
    (hmemberPath : member.1.clusterPath.contains top.1.decl = true) :
    (frameRect P cg' run top.2).y < (frameRect P cg' run member.2).y ∧
    (frameRect P cg' run member.2).y + (frameRect P cg' run member.2).h <
      (frameRect P cg' run top.2).y + (frameRect P cg' run top.2).h := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hnodes : cg'.nodes = cg.nodes := by
    rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, h⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq h
  have htopIn : top ∈ cg.nodes.zipIdx := by
    rw [← hnodes]
    exact List.mem_zipIdx_iff_getElem?.mpr htop
  have hmemberIn : member ∈ cg.nodes.zipIdx := by
    rw [← hnodes]
    exact List.mem_zipIdx_iff_getElem?.mpr hmember
  have hbottomIn : bottom ∈ cg'.nodes.zipIdx := List.mem_of_find?_eq_some hbottom
  have hbottomGet := List.mem_zipIdx_iff_getElem?.mp hbottomIn
  have hbottomPred : (bottom.1.border == 2 && bottom.1.decl == top.1.decl) = true :=
    List.find?_some (p := fun q : Node × Nat => q.1.border == 2 && q.1.decl == top.1.decl) hbottom
  have hbottomKey : bottom.1.border = 2 ∧ bottom.1.decl = top.1.decl := by
    obtain ⟨hborder, hdecl⟩ := Bool.and_eq_true_iff.mp hbottomPred
    exact ⟨beq_iff_eq.mp hborder, beq_iff_eq.mp hdecl⟩
  have hbottomRole := hbottomKey.1
  obtain ⟨hBefore, hAfter⟩ := componentRunR_compound_leaf_rank_window hrun htopIn htopRole
    (by rwa [← hnodes]) hmemberIn hplain hmemberPath
  obtain ⟨_, topActual, htc, hta, _, _, htcRole, _, _, htaPath, _⟩ :=
    componentRunR_active_marker_records hrun hactive htop (Or.inl htopRole)
  obtain ⟨_, botActual, hbc, hba, _, _, hbcRole, _, _, hbaPath, hzero⟩ :=
    componentRunR_active_marker_records hrun hactive hbottomGet (Or.inr hbottomRole)
  obtain ⟨lmember, hlm, _, hmLo, hmHi⟩ :=
    (componentRunR_plain_rank_bands (exactIds := exactIds) hrun).1 hmember hplain
  have hLayerOk : RouteImpl.layersOk run.proper run.layers = true := by
    rcases stages.hLanes with ⟨_, h⟩ | ⟨_, h⟩
    · exact (RouteImpl.routeWithLanes_geometry h).1
    · obtain ⟨base, hbase, _, _⟩ := routeWithLanesR_spec h
      exact (RouteImpl.route_spec hbase).1
  have hcoverage := (RouteImpl.layersOk_spec hLayerOk).2.2.2.1
  let r := fun v => (rk run.proper.rank v).toNat
  obtain ⟨ltop, hlt, _, htNonneg⟩ :=
    hcoverage top.2 (List.getElem?_eq_some_iff.mp hta).1
  obtain ⟨lbottom, hlb, _, hbNonneg⟩ :=
    hcoverage bottom.2 (List.getElem?_eq_some_iff.mp hba).1
  have hmNonneg : 0 ≤ rk run.proper.rank member.2 := by omega
  have htm : r top.2 < r member.2 := by dsimp only [r]; omega
  have hmb : r member.2 < r bottom.2 := by dsimp only [r]; omega
  have hget (v : Nat) (layer : List Nat) (hv : run.layers[r v]? = some layer) :
      run.layers.getD (r v) [] = layer := by
    rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
  change run.layers[r member.2]? = some lmember at hlm
  have hgapTop := componentRunR_strictRankBandGap (exactIds := exactIds) hrun htm hlt hlm
  have hgapBottom := componentRunR_strictRankBandGap (exactIds := exactIds) hrun hmb hlm hlb
  have hhi := hget bottom.2 lbottom hlb
  have hty := ((componentRunR_boundaryRankBands (exactIds := exactIds) hrun).1 htc (by
    intro h
    have he : (-2 : Int) = 2 := (htcRole.trans htopRole).symm.trans h
    omega)).2.2.1 (htcRole.trans htopRole)
  have hby := ((componentRunR_boundaryRankBands (exactIds := exactIds) hrun).1 hbc
    (fun _ => (hzero hbottomRole).1)).2.2.2 (hbcRole.trans hbottomRole)
  have htHeight := CoordsImpl.layerHeight_nonneg run.coordinateProper ltop
  have hbHeight := CoordsImpl.layerHeight_nonneg run.coordinateProper lbottom
  have hgetTop : cg'.nodes.getD top.2 default = top.1 := by
    simp only [List.getD_eq_getElem?_getD, htop, Option.getD_some]
  have htHull := frameRect_member_vertical (P := P) (cg := cg') (run := run)
    (i := top.2) (q := (topActual, top.2)) (by rw [hgetTop]; exact htopRole)
    (List.mk_mem_zipIdx_iff_getElem?.mpr hta) (by rw [hgetTop, htaPath]; exact htopPath)
  have hbHull := frameRect_member_vertical (P := P) (cg := cg') (run := run)
    (i := top.2) (q := (botActual, bottom.2)) (by rw [hgetTop]; exact htopRole)
    (List.mk_mem_zipIdx_iff_getElem?.mpr hba) (by rw [hgetTop, hbaPath]; exact hbottomPath)
  have htY : (frameRect P cg' run top.2).y ≤ run.ys.getD top.2 0 := htHull.1
  have hbY : run.ys.getD bottom.2 0 ≤
      (frameRect P cg' run top.2).y + (frameRect P cg' run top.2).h := by
    simpa only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt, RouteImpl.nodeH, hba,
      (hzero hbottomRole).2, Int.add_zero] using hbHull.2
  change run.ys.getD top.2 0 = run.top.getD (r top.2) 0 at hty
  change run.ys.getD bottom.2 0 = run.top.getD (r bottom.2) 0 +
    CoordsImpl.layerHeight run.coordinateProper (run.layers.getD (r bottom.2) []) at hby
  rw [hhi] at hby
  change run.top.getD (r member.2) 0 ≤ (frameRect P cg' run member.2).y at hmLo
  change (frameRect P cg' run member.2).y + (frameRect P cg' run member.2).h ≤
    run.top.getD (r member.2) 0 + CoordsImpl.layerHeight run.coordinateProper lmember at hmHi
  exact ⟨by omega, by omega⟩

end Elegant.Layered.PipelineImpl

