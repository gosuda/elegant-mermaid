import Elegant.Layered.RegionRunSpec
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.RegionFlatC4

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private def c5RankIndex (run : Run) (v : Nat) : Nat := (rk run.proper.rank v).toNat

private def c5BandHeight (run : Run) (r : Nat) : Int :=
  CoordsImpl.layerHeight run.coordinateProper (run.layers.getD r [])

theorem componentRunR_boundaryRankBands {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run)) :
    (∀ {v : Nat} {nd : ProperNode}, run.coordinateProper.nodes[v]? = some nd →
      (nd.node.border = 2 → nd.node.h = 0) →
      let r := c5RankIndex run v
      run.top.getD r 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤ run.top.getD r 0 + c5BandHeight run r ∧
      (nd.node.border = -2 → run.ys.getD v 0 = run.top.getD r 0) ∧
      (nd.node.border = 2 → run.ys.getD v 0 = run.top.getD r 0 + c5BandHeight run r)) ∧
    (∀ {r s : Nat}, r < s → s < run.layers.length →
      run.top.getD r 0 + c5BandHeight run r ≤ run.top.getD s 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, ⟨y, top⟩, ysMid, hs⟩ :=
    componentRunR_stages hrun
  have hry := hs.hYt
  obtain ⟨hyLen, htopLen⟩ := CoordsImpl.rankCoordsWith_length hry
  have hysLen : ysMid.length = placed.nodes.length := by
    rw [← hs.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hyLen
  obtain ⟨extra, shifts, _, heNonneg, hprefix, hshiftLen, htopShift, hyShift⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top hs.hReserve
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hprefix]
    exact reserveShift_prefix_pairwise extra heNonneg 0 [] (by simp) (by simp)
  have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
    rcases hs.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
    · exact (RouteImpl.routeWithLanes_geometry hlanes).1
    · obtain ⟨base, hbase, _, _⟩ := routeWithLanesR_spec hlanes
      exact (RouteImpl.route_spec hbase).1
  have hcoverage := (RouteImpl.layersOk_spec hlayers).2.2.2.1
  have hrank : run.proper.rank = placed.rank := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hs.hProxy).2.1
  have hnodes : run.proper.nodes = q0.nodes := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  have hlength : run.proper.nodes.length = placed.nodes.length := by
    rw [hnodes]
    exact (proxyWidths_rel hs.hProxy).2.2.1
  constructor
  · intro v nd hv hflat
    let r := c5RankIndex run v
    have hvPlaced : placed.nodes[v]? = some nd := by simpa only [hs.hCoordProper] using hv
    have hvC := (List.getElem?_eq_some_iff.mp hvPlaced).1
    have hvP : v < run.proper.nodes.length := by rwa [hlength]
    obtain ⟨layer, hlayer, hmem, hrNN⟩ := hcoverage v hvP
    change run.layers[r]? = some layer at hlayer
    have hr : rk placed.rank v = (r : Int) := by
      rw [← hrank]
      exact (Int.toNat_of_nonneg hrNN).symm
    have hindex : (rk placed.rank v).toNat = r := by rw [← hrank] <;> rfl
    have hgetLayer : run.layers.getD r [] = layer := by
      rw [List.getD_eq_getElem?_getD, hlayer, Option.getD_some]
    have hheight : CoordsImpl.nodeH placed v = nd.node.h := by
      simp only [CoordsImpl.nodeH, hvPlaced]
    have hheightFinal : RouteImpl.nodeH run.proper v = nd.node.h := by
      unfold RouteImpl.nodeH
      rw [hnodes]
      exact (nodeH_proxy hs.hProxy v).trans hheight
    have hlh := CoordsImpl.layerHeight_nonneg placed layer
    have hnh := CoordsImpl.layerHeight_ge (p := placed) hmem
    rw [hheight] at hnh
    have hrBound : r < top.length := by
      rw [htopLen]
      exact (List.getElem?_eq_some_iff.mp hlayer).1
    have hyBand := CoordsImpl.rankAxis_node_in_band (r := r) hry hlayer hmem hvC hr
    rw [hheight] at hyBand
    have hyV := hyShift v (by rw [hysLen]; exact hvC)
    change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD (rk placed.rank v).toNat 0 at hyV
    rw [hindex] at hyV
    have htV := htopShift r hrBound
    have hbefore := proxyYs_getD placed run.layers top y hvPlaced (by rwa [hyLen])
    rw [hs.hYsMid, hindex, hgetLayer] at hbefore
    change run.top.getD r 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤ run.top.getD r 0 + c5BandHeight run r ∧
      (nd.node.border = -2 → run.ys.getD v 0 = run.top.getD r 0) ∧
      (nd.node.border = 2 → run.ys.getD v 0 = run.top.getD r 0 + c5BandHeight run r)
    rw [c5BandHeight, hs.hCoordProper, hgetLayer, hheightFinal, htV, hyV]
    by_cases htop : nd.node.border = -2
    · have htopT : (nd.node.border == -2) = true := beq_iff_eq.mpr htop
      rw [ite_eq_left htopT] at hbefore
      rw [hbefore]
      exact ⟨by omega, by omega, fun _ => rfl, fun h => by omega⟩
    · have htopF : (nd.node.border == -2) ≠ true := fun h => htop (beq_iff_eq.mp h)
      rw [ite_eq_right htopF] at hbefore
      by_cases hbottom : nd.node.border = 2
      · have hbottomT : (nd.node.border == 2) = true := beq_iff_eq.mpr hbottom
        rw [ite_eq_left hbottomT] at hbefore
        rw [hbefore, hflat hbottom]
        exact ⟨by omega, by omega, fun h => (htop h).elim, fun _ => by omega⟩
      · have hbottomF : (nd.node.border == 2) ≠ true := fun h => hbottom (beq_iff_eq.mp h)
        rw [ite_eq_right hbottomF] at hbefore
        rw [hbefore]
        exact ⟨by omega, by omega, fun h => (htop h).elim, fun h => (hbottom h).elim⟩
  · intro r s hrs hsLayer
    have hrLayer : r < run.layers.length := by omega
    have hr : r < top.length := by rwa [htopLen]
    have ht : s < top.length := by rwa [htopLen]
    have hrShift : r < shifts.length := by rwa [hshiftLen]
    have hsShift : s < shifts.length := by rwa [hshiftLen]
    have hmono : shifts.getD r 0 ≤ shifts.getD s 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hrShift, List.getElem?_eq_getElem hsShift]
      simp only [Option.getD_some]
      exact hpair.rel_getElem_of_lt hrShift hsShift hrs
    have hseq := CoordsImpl.rankAxis_bands_disjoint hry r s run.layers[r] run.layers[s]
      hrs (List.getElem?_eq_getElem hrLayer) (List.getElem?_eq_getElem hsLayer)
    have hget : run.layers.getD r [] = run.layers[r] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrLayer, Option.getD_some]
    rw [c5BandHeight, hs.hCoordProper, hget, htopShift r hr, htopShift s ht]
    omega

end Elegant.Layered.PipelineImpl
