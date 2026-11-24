import Elegant.Layered.RegionC7SelectedReversed
import Elegant.Layered.RegionC5RankBand
import Elegant.Layered.RegionDifferentLayerClearance

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private abbrev forwardLabelRank (run : Run) (edge : Edge) : Int :=
  rk run.proper.rank edge.tail + Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2

private theorem executedForwardAnchorBandSource {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions} {k : Nat} {edge : Edge}
    {first : MeasuredLabel}
    (hrun : componentRunR P exact spec inp candidate labels order = .ok (cg, run))
    (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
    (hfirst : (routeLabels labels edge.decl).head? = some first) :
    ∃ (i : Nat) (nd : ProperNode) (row : List Nat),
      labelAnchorIndex run.proper k (forwardLabelRank run edge) = some i ∧
      run.coordinateProper.nodes[i]? = some nd ∧ nd.node.border = 0 ∧
      run.layers[(rk run.proper.rank i).toNat]? = some row ∧
      (stackSize cg.slot (routeLabels labels edge.decl)).height ≤ RouteImpl.nodeH run.proper i := by
  obtain ⟨_, _, _, p₀, labeled, pCoord, _, _, _, _, placed, _, _, _, s⟩ := componentRunR_stages hrun
  obtain ⟨halign₀, hwf⟩ := normalize_node_rank_alignment s.hNorm
  obtain ⟨hrank, hkeys⟩ := addLabelNodes_anchor_keys s.hLabels
  have hlen : labeled.nodes.length = p₀.nodes.length := by
    simpa only [List.length_map] using congrArg List.length hkeys
  have halign : labeled.nodes.length = labeled.rank.length := by rw [hlen, hrank, halign₀]
  obtain ⟨ht, hh, _⟩ := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hk)
  have htail : edge.tail < labeled.rank.length := by
    rw [← halign, hlen]
    exact Nat.lt_of_lt_of_le ht (normalize_nodes_length_le s.hNorm)
  have hhead : edge.head < labeled.rank.length := by
    rw [← halign, hlen]
    exact Nat.lt_of_lt_of_le hh (normalize_nodes_length_le s.hNorm)
  obtain ⟨i, before, hi, hbefore, _, hheight⟩ := componentLabels_selected_size hk hne hfirst s.hLabels
  have hkey := labelAnchorIndex_node_edge hi hbefore
  have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain s.hNorm) s.hLabels
  have hb : before.node.border = 0 := hplain before (List.mem_of_getElem? hbefore) (by simp [hkey])
  obtain ⟨coord, hc, hcb, _, hch⟩ := regionCoordinatePlainDims P exact spec hbefore hb
  rw [s.hCoord] at hc
  obtain ⟨nd, hnd, hnb, hnh, hkeysPlaced, hrankPlaced⟩ :
      ∃ nd, placed.nodes[i]? = some nd ∧ nd.node.border = 0 ∧ coord.node.h ≤ nd.node.h ∧
        placed.nodes.map ProperNode.edge = pCoord.nodes.map ProperNode.edge ∧
        placed.rank = pCoord.rank := by
    rcases s.hPlaced with ⟨_, _, _, _, heq⟩ | ⟨_, _, _, _, hcross⟩
    · rw [heq]
      exact ⟨coord, hc, hcb, Int.le_refl _, rfl, rfl⟩
    · obtain ⟨nd, hnd, hb', _, hh'⟩ := regionCrossPlainDims hcross hc
      obtain ⟨hkeys', hrank', _, _⟩ := crossCoordsR_label_metadata hcross
      exact ⟨nd, hnd, hb'.trans hcb, hh', hkeys', hrank'⟩
  have hrouteNode : run.proper.nodes[i]? = some nd := by
    rw [← s.hDrop, OrderImpl.dropSynthetic_nodes]
    exact proxyWidths_plain_node s.hProxy hnd hnb
  have hprefix := coordinateGraphR_label_prefix P exact spec labeled
  rw [s.hCoord] at hprefix
  have hprefixIdx := labelAnchorIndex_prefix halign hprefix.1 hprefix.2 hi
  obtain ⟨extra, hr⟩ := hprefix.2
  have hkeysFinal : run.proper.nodes.map ProperNode.edge = pCoord.nodes.map ProperNode.edge := by
    rw [← s.hDrop, OrderImpl.dropSynthetic_nodes, proxyWidths_edge_keys s.hProxy, hkeysPlaced]
  have hrankFinal : run.proper.rank = pCoord.rank := by
    rw [← s.hDrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel s.hProxy).2.1, hrankPlaced]
  have htailFinal : rk run.proper.rank edge.tail = rk labeled.rank edge.tail := by
    rw [hrankFinal, hr, NormalizeImpl.rk_append_left htail]
  have hheadFinal : rk run.proper.rank edge.head = rk labeled.rank edge.head := by
    rw [hrankFinal, hr, NormalizeImpl.rk_append_left hhead]
  have hanchor : labelAnchorIndex run.proper k (forwardLabelRank run edge) = some i := by
    change labelAnchorIndex run.proper k
      (rk run.proper.rank edge.tail + Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) = some i
    rw [htailFinal, hheadFinal]
    unfold labelAnchorIndex at hprefixIdx ⊢
    rwa [hkeysFinal, hrankFinal]
  have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
    rcases s.hLanes with ⟨_, h⟩ | ⟨_, h⟩
    · exact (RouteImpl.routeWithLanes_geometry h).1
    · exact (rcbRouteWithLanesR_geometry h).1
  obtain ⟨row, hrow, _, _⟩ := (RouteImpl.layersOk_spec hlayers).2.2.2.1 i
    (List.getElem?_eq_some_iff.mp hrouteNode).1
  refine ⟨i, nd, row, hanchor, ?_, hnb, hrow, ?_⟩
  · rwa [s.hCoordProper]
  · simp only [RouteImpl.nodeH, hrouteNode]
    rw [← hheight, hch]
    exact hnh

def R7_SelectedForwardDifferentPlainRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail ≠ pair.edge.head ∧ pair.edge.reversed = false ∧
    (∃ node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0) ∧
    (rk pair.run.proper.rank pair.target).toNat ≠ (forwardLabelRank pair.run pair.edge).toNat

theorem r7Selected_forwardDifferentPlainRank_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hpair : R7_SelectedForwardDifferentPlainRank pair) :
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨hne, hrev, ⟨node, hnode, hplain⟩, hdifferent⟩ := hpair
  let spec := r7Eff idSets o execution.params execution.lines pair.rs
  have hrun : componentRunR execution.params (exactDecls exactIds inp) spec inp
      (componentCandidateR spec execution.graph pair.part.1 pair.candidate)
      execution.measured (candidateOrder pair.candidate) = .ok (pair.cg, pair.run) := pair.run_eq
  obtain ⟨first, anchor, hfirst, hfind, henv⟩ := forward_envelope_eq hne hrev pair.envelope_eq
  obtain ⟨i, nd, row, hi, hcoord, hcb, hrow, hh⟩ :=
    executedForwardAnchorBandSource hrun pair.edge_eq hne hfirst
  rw [labelAnchorIndex_eq] at hi
  have hindex : anchor.2 = i := by
    simpa only [forwardLabelRank, hfind, Option.map_some, Option.some.injEq] using hi
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  have hrank : rk pair.run.proper.rank i = forwardLabelRank pair.run pair.edge := by
    rw [← hindex]
    exact hpred.2
  let arank := (rk pair.run.proper.rank i).toNat
  let vrank := (rk pair.run.proper.rank pair.target).toNat
  have hranks : vrank ≠ arank := by simpa only [vrank, arank, hrank] using hdifferent
  change pair.run.layers[arank]? = some row at hrow
  have hrowD : pair.run.layers.getD arank [] = row := by
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
  have hband := (componentRunR_boundaryRankBands (exactIds := exactIds) hrun).1 hcoord (by
    intro h
    omega)
  have htop := hband.1
  change pair.run.top.getD arank 0 ≤ pair.run.ys.getD i 0 at htop
  have hbottom := hband.2.1
  change pair.run.ys.getD i 0 + RouteImpl.nodeH pair.run.proper i ≤ pair.run.top.getD arank 0 +
    CoordsImpl.layerHeight pair.run.coordinateProper (pair.run.layers.getD arank []) at hbottom
  rw [hrowD] at hbottom
  have hy : pair.envelope.y = pair.run.ys.getD i 0 := by
    rw [henv, hindex]
    rfl
  have hslot : 0 ≤ pair.cg.slot := by
    rw [r7ComponentRun_slot_of_scene execution (comp := pair.part.1) (candidate := pair.candidate) hrun]
    exact Int.le_trans (by decide) (componentRunR_slot_pos hrun)
  let sizes := (routeLabels execution.measured pair.edge.decl).map (fun x => (x.width, x.height))
  have hsizes : ∀ s ∈ sizes, 0 ≤ s.2 := by
    intro s hs
    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hs
    exact (execution.measured_nonnegR item (List.mem_filter.mp hitem).1).2.1
  have hstack := (List.of_mem_zip pair.stack).2
  have hlabelTop := Labels.stackRects_lower pair.envelope.x pair.cg.slot hslot sizes
    pair.envelope.y hsizes pair.rect hstack
  have hlabelBottom := Labels.stackRects_upper pair.envelope.x pair.cg.slot hslot sizes
    pair.envelope.y hsizes pair.rect hstack
  rw [stackSize_height_eq] at hh
  change Labels.stackHeight pair.cg.slot sizes ≤ RouteImpl.nodeH pair.run.proper i at hh
  have hlower : pair.run.top.getD arank 0 ≤ pair.rect.y := by omega
  have hupper : pair.rect.y + pair.rect.h ≤ pair.run.top.getD arank 0 +
      CoordsImpl.layerHeight pair.run.coordinateProper row := by omega
  obtain ⟨hplainBands, horder⟩ := componentRunR_plain_rank_bands (exactIds := exactIds) hrun
  obtain ⟨vrow, hvrow, _, hvTop, hvBottom⟩ := hplainBands hnode hplain
  change pair.run.layers[vrank]? = some vrow at hvrow
  have hbPlain : (pair.cg.nodes.getD pair.target default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some, hplain]
    decide
  rw [plain_frame_eq_boxRect execution.params pair.cg pair.run pair.target pair.target_size hbPlain]
    at hvTop hvBottom
  let victim := RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target
  change pair.run.top.getD vrank 0 ≤ victim.y at hvTop
  change victim.y + victim.h ≤ pair.run.top.getD vrank 0 +
    CoordsImpl.layerHeight pair.run.coordinateProper vrow at hvBottom
  change R7_OverlapRowsXGap pair.rect victim
  intro hover _ _
  rcases Nat.lt_or_gt_of_ne hranks with hlt | hgt
  · have hsep := horder (r := vrank) (s := arank) hlt hvrow hrow
    have hclear : victim.y + victim.h ≤ pair.rect.y :=
      Int.le_trans hvBottom (Int.le_trans hsep hlower)
    have hover' : pair.rect.y < victim.y + victim.h :=
      Int.lt_of_le_of_lt (Int.le_max_left _ _)
        (Int.lt_of_lt_of_le hover (Int.min_le_right _ _))
    exact (Int.not_lt_of_ge hclear hover').elim
  · have hsep := horder (r := arank) (s := vrank) hgt hrow hvrow
    have hclear : pair.rect.y + pair.rect.h ≤ victim.y :=
      Int.le_trans hupper (Int.le_trans hsep hvTop)
    have hover' : victim.y < pair.rect.y + pair.rect.h :=
      Int.lt_of_le_of_lt (Int.le_max_right _ _)
        (Int.lt_of_lt_of_le hover (Int.min_le_left _ _))
    exact (Int.not_lt_of_ge hclear hover').elim

def R7_SelectedRouteAfterForwardDifferentPlainRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel → ¬ R7_SelectedSettledLoop pair →
    ¬ R7_SelectedReversedPlainPair pair → ¬ R7_SelectedForwardDifferentPlainRank pair →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

theorem r7SelectedRoute_iff_afterForwardDifferentPlainRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    R7_SelectedRouteAfterReversedPlain execution ↔ R7_SelectedRouteAfterForwardDifferentPlainRank execution := by
  classical
  constructor
  · intro h l b pair hl hb hex hscope hloop hrev _
    exact h l b pair hl hb hex hscope hloop hrev
  · intro h l b pair hl hb hex hscope hloop hrev
    by_cases hforward : R7_SelectedForwardDifferentPlainRank pair
    · exact r7Selected_forwardDifferentPlainRank_clear pair hforward
    · exact h l b pair hl hb hex hscope hloop hrev hforward

end Elegant.Layered.PipelineImpl
