import Elegant.Layered.RegionPositionsDisjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region positions some-spec order proof.

Proves the region-free half of `rpdCrossCoordsOrderR`
(`RegionPositionsDisjoint.lean`): the plain `crossCoordsClusterWith` branch
keeps same-layer border-0 order with `coordSep` gaps, with no title-uniqueness
premise. The `ownTitleAnchor` case is impossible for border-0 left endpoints,
so the `cluster_all_pairs_separated` argument goes through via the
`ht = false` branch (`cluster_balance_separated`, `clusterGap_ge_min`,
`cluster_zero_pairs_separated`).

Narrows the rest to ONE executed residual: the region-active
(`crossCoordsR` output) order for successful `componentRunR` runs, stated over
`run.coordinateXs` / `run.layers` / `run.coordinateProper`. The universal
`rpdCrossCoordsOrderR` implies the residual by stage equations
(`componentRunR_specR`); the plain half proved here discharges the
region-free case. The y-band step toward `rpdSomeDisjointR` stays open in the
imported module.

 Truth (`proofs/wip/Probe/RegionPositionsSomeTProbe.lean`, `lake env lean`
 re-ran 2026-11-19): `order=true, disjoint=true` on two-region with spec,
 nested, zero-size fixed `G1`, and self-loop runs; `run error domain` on the
 empty-boxes and dangling-route inputs (rejected before placement, so no order
 claim is made). The all-border position form stays false by design (side
 markers share span endpoints); only border-0 is ordered here.
-/

/-- Executed region-active order (single residual): for a successful
`componentRunR` whose placement ran `crossCoordsR`, the run's coordinate
outputs keep same-layer border-0 order with `coordSep` gaps. Strictly narrower
than the universal first conjunct of `rpdCrossCoordsOrderR` (one executed run,
not all placements); true on the probe (`order=true`). -/
 def rpsActiveOrderR : Prop :=
   ∀ {P : Params} {exact : List Nat} {s : RegionSpec} {inp : Input}
     {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions},
     componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run) →
     ∀ (layer : List Nat), layer ∈ run.layers →
     ∀ (i j a b : Nat) (na nb : ProperNode),
       i < j → layer[i]? = some a → layer[j]? = some b →
       run.coordinateProper.nodes[a]? = some na →
       run.coordinateProper.nodes[b]? = some nb →
       na.node.border = 0 → nb.node.border = 0 →
       CoordsImpl.coordSep (min P.nodeGap P.clusterPad) run.coordinateProper a b ≤
         run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0

 /-- `ownTitleAnchor` never fires with a border-0 left endpoint: both
 disjuncts need the left node at border `±2` or `3`. -/
 private theorem rpsOwnTitleAnchor_border0_false {p : Proper} {a b : Nat}
     {na nb : ProperNode} (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
     (hb0 : na.node.border = 0) : CoordsImpl.ownTitleAnchor p a b = false := by
   unfold CoordsImpl.ownTitleAnchor
   rw [ha, hb]
   simp [hb0]

 /-- Plain border-0 order without title uniqueness: for border-0 endpoints the
 title-anchor case is impossible, so the adjacent-plus-zero-tail argument
 closes every pair. -/
 private theorem rpsPlainBorder0_all {ng cp : Int} {p : Proper}
     {layers : List (List Nat)} {xs : List Int}
     (h : CoordsImpl.crossCoordsClusterWith ng cp p layers = .ok xs) :
     ∀ (layer : List Nat), layer ∈ layers →
     ∀ (i j a b : Nat) (na nb : ProperNode),
       i < j → layer[i]? = some a → layer[j]? = some b →
       p.nodes[a]? = some na → p.nodes[b]? = some nb →
       na.node.border = 0 → nb.node.border = 0 →
       CoordsImpl.coordSep (min ng cp) p a b ≤ xs.getD b 0 - xs.getD a 0 := by
   obtain ⟨hn, hp, hr, hs, _⟩ := CoordsImpl.crossCoordsClusterWith_spec h
   intro layer hl i j a b na nb hij ha hb hna hnb hb0a hb0b
   have hjLen : j < layer.length := (List.getElem?_eq_some_iff.mp hb).1
   have hi1Le : i + 1 ≤ j := by omega
   have hi1Lt : i + 1 < layer.length := by omega
   obtain ⟨c, hc⟩ : ∃ c, layer[i + 1]? = some c := by
     cases he : layer[i + 1]? with
     | none => have := List.getElem?_eq_none_iff.mp he; omega
     | some c => exact ⟨c, rfl⟩
   have hcLen : c < p.nodes.length := CoordsImpl.layers_mem_lt hr hl hc
   obtain ⟨nc, hnc⟩ : ∃ nc, p.nodes[c]? = some nc := by
     cases he : p.nodes[c]? with
     | none => have := List.getElem?_eq_none_iff.mp he; omega
     | some nc => exact ⟨nc, rfl⟩
   have hadj := CoordsImpl.cluster_balance_separated h layer hl i a c ha hc
   have htf : CoordsImpl.ownTitleAnchor p a c = false :=
     rpsOwnTitleAnchor_border0_false hna hnc hb0a
   have hg := CoordsImpl.clusterGap_ge_min (ng := ng) (cp := cp) p a c htf
   have hhalf : 0 ≤ Int.fdiv (CoordsImpl.nodeW p c) 2 := by
     rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
     exact Int.ediv_nonneg (CoordsImpl.nodeW_nonneg hs c) (by decide)
   by_cases heq : i + 1 = j
   · have hcb : c = b := by rw [heq, hb] at hc; exact Option.some.inj hc.symm
     subst hcb
     unfold CoordsImpl.clusterSep CoordsImpl.coordSep at hadj
     unfold CoordsImpl.coordSep
     omega
   · have hlt : i + 1 < j := by omega
     have htail := CoordsImpl.cluster_zero_pairs_separated h layer hl (i + 1) j c b hlt hc hb
     unfold CoordsImpl.clusterSep CoordsImpl.coordSep at hadj
     unfold CoordsImpl.coordSep
     omega

 /-- The region-free half of `rpdCrossCoordsOrderR`: the plain
 `crossCoordsClusterWith` order for border-0 nodes, with no uniqueness
 premise. Proved; the `crossCoordsR` half is the residual below. -/
 theorem rpsPlainOrderR_holds :
     (∀ {P : Params} {exact : List Nat} {s : RegionSpec} {labeled pCoord : Proper}
       {ord : OrderResult} {xs : List Int},
       coordinateGraphR P exact (some s) labeled = pCoord →
       CoordsImpl.crossCoordsClusterWith P.nodeGap P.clusterPad pCoord ord.layers =
         .ok xs →
       ∀ (layer : List Nat), layer ∈ ord.layers →
       ∀ (i j a b : Nat) (na nb : ProperNode),
         i < j → layer[i]? = some a → layer[j]? = some b →
         pCoord.nodes[a]? = some na → pCoord.nodes[b]? = some nb →
         na.node.border = 0 → nb.node.border = 0 →
         CoordsImpl.coordSep (min P.nodeGap P.clusterPad) pCoord a b ≤
           xs.getD b 0 - xs.getD a 0) := by
   intro P exact s labeled pCoord ord xs hCoord hcross
   exact rpsPlainBorder0_all hcross

 /-- Reduction: the universal order implies the executed some-spec order, by
 cases on the placement branch of `componentRunR_specR`. -/
 theorem rpsActiveOrderR_of_rpd (h : rpdCrossCoordsOrderR) : rpsActiveOrderR := by
   intro P exact s inp cg cg' run labels orderOptions hrun
   obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
     reserved, placedProper, q0, yt, ysMid, hRs, hRank, hNorm, hLabels, hCoord,
     hMin, hOrd, hLabelWidths, hPlaced, hProxy, hDrop, hLanes, hYt, hYsMid,
     hReserve, hRoutes, hRouting, hCoordProper, hCoordYs, hBudget, hExact⟩ :=
     componentRunR_specR hrun
   intro layer hlayer i j a b na nb hij ha hb hna hnb hb0a hb0b
   rcases hPlaced with ⟨hrsN, hcross, hLayers, hres, hpp⟩ | ⟨rm, m, hrsS, hmin, hcross⟩
   · have hPC : run.coordinateProper = pCoord := by
       rw [hCoordProper, hpp]
     have hna' : pCoord.nodes[a]? = some na := by
       rw [← hPC]
       exact hna
     have hnb' : pCoord.nodes[b]? = some nb := by
       rw [← hPC]
       exact hnb
     have hlayer' : layer ∈ ord.layers := by
       rw [← hLayers]
       exact hlayer
     have hgoal := h.2 hCoord hcross layer hlayer' i j a b na nb hij ha hb hna' hnb' hb0a hb0b
     rw [hPC]
     exact hgoal
   · have hna' : placedProper.nodes[a]? = some na := by
       rw [← hCoordProper]
       exact hna
     have hnb' : placedProper.nodes[b]? = some nb := by
       rw [← hCoordProper]
       exact hnb
     have hgoal := h.1 hcross layer hlayer i j a b na nb hij ha hb hna' hnb' hb0a hb0b
     rw [hCoordProper]
     exact hgoal

end PipelineImpl
end Layered
end Elegant
