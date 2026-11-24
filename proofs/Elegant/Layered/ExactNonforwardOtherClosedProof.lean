import Elegant.Layered.ExactRouteNonforwardClearProof
import Elegant.Layered.ExactFlatC6ScopeRestProof
import Elegant.Layered.ExactGroupOverlapPlainGapProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A plain owner reserves the extended loop footprint over all proper nodes,
including positive-height label dummies and titles. Other ranks clear the
reservation vertically; same-rank nodes clear its horizontal interval. -/
theorem xnonfwd_plainOwner_extMiss {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {k v : Nat} {e : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[k]? = some e)
    (hself : e.tail = e.head)
    (hplain : ((componentCandidate execution.graph comp candidate).nodes.getD e.tail default).border = 0)
    (hv : v < run.proper.nodes.length) :
    ¬ (loopFootprintExt (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).meetsInterior (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured e.tail
  let box := RouteImpl.boxRect run.proper run.xs run.ys v
  change ¬ foot.meetsInterior box
  have htGraph := (candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)).1
  have ht := componentRunX_original_nodes_covered hrun e.tail htGraph
  have hnotTop : (cg.nodes.getD e.tail default).border ≠ -2 := by
    change (cg.nodes.getD e.tail default).border = 0 at hplain
    rw [hplain]
    decide
  have hfr := plain_frame_eq_boxRect default cg run e.tail ht hnotTop
  have hfootX : foot.x = RouteImpl.leftOf run.proper run.xs e.tail +
      RouteImpl.nodeW run.proper e.tail := by
    change (frameRect default cg run e.tail).x + (frameRect default cg run e.tail).w = _
    rw [hfr] <;> rfl
  by_cases heq : v = e.tail
  · subst v
    apply rect_disjoint_of_x
    right
    change RouteImpl.leftOf run.proper run.xs e.tail + RouteImpl.nodeW run.proper e.tail ≤ foot.x
    rw [hfootX] <;> exact Int.le_refl _
  obtain ⟨target, htarget⟩ : ∃ target, run.proper.nodes[v]? = some target :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  by_cases hproxy : target.node.border = -2 ∨ target.node.border = 2
  · exact XLEM_plainRightProxyMiss_holds exactIds inp o res execution comp candidate run
      orderOptions cg e v hcomp rfl hrun target htarget hproxy
  obtain ⟨coord, hcoord, hbCoord, _⟩ := XLEM_proper_coord hrun htarget
  have hnp : ¬ (coord.node.border = -2 ∨ coord.node.border = 2) := by rwa [hbCoord]
  let rt := (rk run.proper.rank e.tail).toNat
  let rv := (rk run.proper.rank v).toNat
  obtain ⟨lv, hvLayer, _, hvTop, hvBottom⟩ := componentRunX_node_rank_band hrun hv
  obtain ⟨lt, htLayer, htTop, htBelow⟩ := XLEM_footBelow_holds exactIds
    (XLEM_plainReserve_holds exactIds) inp o res execution comp candidate run orderOptions cg k e
    hcomp rfl hrun hedge hself hnotTop
  rw [← X_proper_rank_eq_local hrun e.tail] at htLayer htTop htBelow
  rcases Nat.lt_trichotomy rt rv with hbefore | hrank | hafter
  · exact rect_disjoint_of_y (Or.inl (Int.le_trans (htBelow rv lv hbefore hvLayer) hvTop))
  · change run.layers[rt]? = some lt at htLayer
    change run.layers[rv]? = some lv at hvLayer
    rw [← hrank, htLayer] at hvLayer
    have hLayerEq : lt = lv := Option.some.inj hvLayer
    subst lv
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
    have hcovered := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
    obtain ⟨tl, htl, htMem, _⟩ := hcovered e.tail ht
    obtain ⟨vl, hvl, hvMem, _⟩ := hcovered v hv
    change run.layers[rt]? = some tl at htl
    change run.layers[rv]? = some vl at hvl
    have htSame : tl = lt := Option.some.inj (htl.symm.trans htLayer)
    rw [← hrank] at hvl
    have hvSame : vl = lt := Option.some.inj (hvl.symm.trans htLayer)
    rw [htSame] at htMem
    rw [hvSame] at hvMem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htMem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvMem
    have hl := List.mem_of_getElem? htLayer
    rcases Nat.lt_trichotomy i j with hij | hij | hji
    · exact XLEM_plainRightGap_of_nonproxy exactIds inp o res execution comp candidate
        run orderOptions cg k e v hcomp rfl hrun hedge hplain target htarget hproxy hl hi hj hij
    · subst j
      exact (heq (Option.some.inj (hj.symm.trans hi))).elim
    · obtain ⟨owner, howner⟩ : ∃ owner, cg.nodes[e.tail]? = some owner :=
        ⟨_, List.getElem?_eq_getElem htGraph⟩
      have hb : owner.border = 0 := by
        change (cg.nodes.getD e.tail default).border = 0 at hplain
        simpa only [List.getD_eq_getElem?_getD, howner, Option.getD_some] using hplain
      obtain ⟨_, _, labeled, _, hnorm, hlabeled, hcoordinates, _⟩ := componentRunX_spec hrun
      have hrecord := addLabelNodes_untouched_node hlabeled (normalize_node_record hnorm howner) rfl
      obtain ⟨nd, hnd, _, hborder, _, _⟩ := coordinateGraphX_plain_anchor_dims
        (exact := exactDecls exactIds inp) execution.params hrecord hb
      rw [hcoordinates] at hnd
      have hnpOwner : ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by rw [hborder]; decide
      have hordered := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
        hcomp hrun hl hji hj hi hcoord hnd hnp hnpOwner
      obtain ⟨actual, ha⟩ : ∃ actual, run.proper.nodes[e.tail]? = some actual :=
        ⟨_, List.getElem?_eq_getElem ht⟩
      have hw : 0 ≤ RouteImpl.nodeW run.proper e.tail := by
        simpa only [RouteImpl.nodeW, ha] using (componentRunX_dims_nonneg hrun e.tail actual ha).1
      apply rect_disjoint_of_x
      right
      change RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤ foot.x
      rw [hfootX]
      omega
  · have hgap := (X_ReserveBands_holds exactIds hrun).2 rv rt lv lt hafter hvLayer htLayer
    exact rect_disjoint_of_y (Or.inr (Int.le_trans hvBottom (Int.le_trans hgap htTop)))

private theorem loopStack_max_ge (get : LoopLabel → Int) (sizes : List LoopLabel)
    (initial : Int) :
    initial ≤ sizes.foldl (fun q label => max q (get label)) initial := by
  induction sizes generalizing initial with
  | nil => exact Int.le_refl _
  | cons label rest ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

/-- True group frames reserve the full vertical loop stack in the measured
title record. The extended rectangle is only needed for exact plain owners,
whose routed height can be smaller than the loop's reserved rank band. -/
private theorem groupFootprint_eq {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {k : Nat} {e : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[k]? = some e)
    (hself : e.tail = e.head) {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some owner)
    (hgroup : owner.border = -2) :
    loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured e.tail =
      loopFootprint (componentCandidate execution.graph comp candidate) run execution.measured e.tail := by
  let cg := componentCandidate execution.graph comp candidate
  let sizes := loopSizes cg.edges execution.measured e.tail cg.slot
  have hloops : ∃ loop ∈ cg.edges, loop.tail = e.tail ∧ loop.head = e.tail :=
    ⟨e, List.mem_of_getElem? hedge, rfl, hself.symm⟩
  have hsize : stackSize cg.slot (routeLabels execution.measured e.decl) ∈ sizes := by
    unfold sizes loopSizes loopEdges
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨List.mem_of_getElem? hedge,
      by simp [hself]⟩, rfl⟩
  have hwidth : ∀ s ∈ sizes, 0 ≤ s.width := by
    intro s hs
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hs
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hslot : 0 < cg.slot := by
    have hcg : cg.slot = execution.graph.slot := by
      unfold cg componentCandidate
      dsimp only
      split
      · split <;> rfl
      · unfold cycleGraph
        split <;> rfl
    have hg := execution.graph_eq
    unfold exactGraph at hg
    obtain ⟨_, _, hg⟩ := bind_ok hg
    have hs : execution.graph.slot = execution.graph0.slot := by rw [← Except.ok.inj hg]
    obtain ⟨_, _, _, _, _, _, hslot, hprep, _⟩ :=
      measuredGraph_loop_reservation_before_prepare execution.graph0_eq
    have hslot0 : execution.graph0.slot = execution.params.slot := by rw [hprep]; exact hslot
    have hvalid := (checkedParams_valid execution.checked).2.2.1
    rw [hcg, hs, hslot0]
    omega
  have hpositive : 0 < (loopFootprintExt cg run execution.measured e.tail).w := by
    change 0 < (if run.exact.contains e.tail then Loops.exactExtent else Loops.extent)
      cg.slot sizes
    cases hx : run.exact.contains e.tail with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hge := Loops.outer_label_extent cg.slot sizes (by omega) hwidth _ hsize
      have hmul := Int.mul_pos hslot (show 0 < (sizes.length : Int) + 1 by omega)
      have hw := hwidth _ hsize
      omega
    | true =>
      have hne : sizes.isEmpty = false := by
        cases h : sizes with
        | nil => simp [h] at hsize
        | cons => rfl
      simp only [↓reduceIte, Loops.exactExtent, hne, Bool.false_eq_true]
      have hw := loopStack_max_ge (·.width) sizes 0
      have hmul := Int.mul_pos hslot (show 0 < 2 * (sizes.length : Int) + 1 by omega)
      omega
  have hmarkers := XLEG_groupMarkerOrderX_of_leaves exactIds
    (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
    (xleg_loopMarkerSpanX_holds exactIds)
    inp o res execution hwf hfp comp candidate run orderOptions cg hcomp rfl hrun
  obtain ⟨_, _, _, marker, _, hm, _, hb, _, hpathM, hreserve, _, _, _, _, _, _⟩ :=
    hmarkers.2 e.tail owner howner hloops hgroup
  have hext := xleg_rightMarker_copies_extent execution.graph0_eq execution.graph_eq
    hcomp hrun howner hgroup hm hb hpathM
  have hstored : 0 < owner.loopExtent := by
    rw [hext] at hreserve
    have hwidthEq : (loopFootprintExt cg run execution.measured e.tail).w =
        (if run.exact.contains e.tail then Loops.exactExtent cg.slot sizes
         else Loops.extent cg.slot sizes) := by
      change (if run.exact.contains e.tail then Loops.exactExtent else Loops.extent)
        cg.slot sizes = _
      cases run.exact.contains e.tail <;> rfl
    rw [hwidthEq] at hpositive
    change (if run.exact.contains e.tail then Loops.exactExtent cg.slot sizes
      else Loops.extent cg.slot sizes) ≤ (owner.loopExtent : Int) at hreserve
    omega
  have hrequired := required_height_le_group_top execution hcomp howner hgroup hstored
  change Loops.requiredHeight cg.slot sizes ≤ owner.h at hrequired
  obtain ⟨v, hv⟩ := group_title_record hrun howner hgroup
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq howner hgroup
  have htitlePath : (copyF (⟨owner, false, none, false⟩, e.tail)).node.clusterPath.contains
      owner.decl = true := by
    change owner.clusterPath.contains owner.decl = true
    simp [hpath]
  have hmemb : Labels.rectAt run.proper run.xs run.ys v ∈ groupMemberRects cg run owner.decl :=
    fbs_groupMemberRects_mem hv htitlePath
  have hframe : owner.h ≤ (frameRect default cg run e.tail).h := by
    have hh := boundsOf_height_ge_member hmemb
    rw [rectAt_eq] at hh
    change RouteImpl.nodeH run.proper v ≤ _ at hh
    simp only [RouteImpl.nodeH, hv, copyF] at hh
    rw [frameRect_group_span howner hgroup]
    exact hh
  have hband := loopStack_max_ge (·.height) sizes (2 * cg.slot)
  change 2 * cg.slot ≤ Loops.band cg.slot sizes at hband
  have hmul := Int.mul_nonneg (show 0 ≤ (sizes.length : Int) by omega)
    (show 0 ≤ Loops.band cg.slot sizes by omega)
  unfold Loops.requiredHeight at hrequired
  rw [Int.mul_assoc] at hrequired
  have hfit : (sizes.length : Int) * Loops.band cg.slot sizes ≤
      (frameRect default cg run e.tail).h := by omega
  let frame := frameRect default cg run e.tail
  unfold loopFootprintExt loopFootprint
  exact congrArg (fun height => Rect.mk (frame.x + frame.w) frame.y
    ((if run.exact.contains e.tail then Loops.exactExtent else Loops.extent) cg.slot sizes) height)
    (Int.max_eq_left hfit)

theorem xnonfwd_extMissW_holds (exactIds : List String) : XNonfwd_ExtMissW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hedge hself hv
  subst cg
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨target, htarget⟩ : ∃ target, run.proper.nodes[v]? = some target :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  by_cases hproxy : target.node.border = -2 ∨ target.node.border = 2
  · exact XLEM_plainRightProxyMiss_holds exactIds inp o res execution comp candidate run
      orderOptions cg e v hcomp rfl hrun target htarget hproxy
  have ht := (candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)).1
  obtain ⟨owner, howner⟩ : ∃ owner, cg.nodes[e.tail]? = some owner :=
    ⟨_, List.getElem?_eq_getElem ht⟩
  rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq howner).1 with
    hplain | hgroup | hbottom
  · have hb : (cg.nodes.getD e.tail default).border = 0 := by
      simp only [List.getD_eq_getElem?_getD, howner, Option.getD_some, hplain]
    exact xnonfwd_plainOwner_extMiss execution hcomp hrun hedge hself hb hv
  · obtain ⟨coord, hcoord, hb, _⟩ := XLEM_proper_coord hrun htarget
    have hnp : ¬ (coord.node.border = -2 ∨ coord.node.border = 2) := by rwa [hb]
    rw [groupFootprint_eq execution hwf hfp hcomp hrun hedge hself howner hgroup]
    exact scopeRest_groupLoop execution hwf hfp hcomp hrun hedge hself howner hgroup hcoord hnp
  · exact (exactBottomNoLoopX execution comp candidate run orderOptions hcomp cg rfl hrun
      e.tail owner howner hbottom ⟨e, List.mem_of_getElem? hedge, rfl, hself.symm⟩).elim
namespace NonforwardOtherWitness

private def node (id parent : String) : ModelBox :=
  { id := id, parent := parent, role := .node, exclusive := true }

private def group (id parent : String) : ModelBox :=
  { id := id, parent := parent, role := .group, exclusive := false }

private def route (id fromId toId : String) : ModelRoute :=
  { id := id, fromId := fromId, toId := toId }

/-- An ordinary node intervenes between the outer and inner groups. The outer
constraints cover the ordinary member, but do not extend to the inner group's
bottom. Routes delay the inner group and a foreign frame past that marker band. -/
def input (foreignFirst : Bool) (span width : Int) (loopCount : Nat) : Input :=
  { kind := "flowchart"
    boxes := if foreignFirst then [node "v" "", group "G" "", node "n" "G", group "H" "n"]
      else [group "G" "", node "n" "G", group "H" "n", node "v" ""]
    texts := []
    routes := (List.range loopCount).map (fun i => route ("loop" ++ toString i) "G" "G") ++
      [route "foreign" "n" "v", route "descend" "v" "H"]
    edges := List.replicate loopCount .plain ++
      [{ EdgeOptions.plain with minLength := span }, EdgeOptions.plain]
    labels := [{ id := "loop-label", owner := "loop0", text := "a loop label" }]
    fixedSizes := [("v", ⟨width, 256⟩)] }

def firstHit (inp : Input) (o : Options) : Except LayoutError
    (Option (List Nat × Nat × Nat × Nat × Int × Bool × Rect × Rect)) := do
  let exactIds := ["v"]
  let _ ← layoutX exactIds inp o
  let p ← checkedParams o.profile inp.kind
  let metric ← metricOf o.profile
  let wrap := Measure.wrapTarget metric.profile p.wrapWidth (if o.profile == .cell then o.maxWidth else 0)
  let lines ← boxLines metric wrap inp
  let labels ← measureLabels p metric wrap inp o.direction
  let graph0 ← measuredGraph p inp o lines
  let graph ← exactGraph p exactIds inp o labels graph0
  pure ((components graph).findSome? fun comp => (List.range 5).findSome? fun candidate => do
    let cg := componentCandidate graph comp candidate
    let run ← (componentRunX p (exactDecls exactIds inp) cg labels (candidateOrder candidate)).toOption
    cg.edges.zipIdx.findSome? fun (edge, k) =>
      if edge.tail != edge.head then none else
        let foot := loopFootprintExt cg run labels edge.tail
        run.proper.nodes.zipIdx.findSome? fun (target, v) =>
          let box := RouteImpl.boxRect run.proper run.xs run.ys v
          if v != edge.tail && decide (foot.meetsInterior box) then
            some (comp, candidate, k, v, target.node.border, target.dummy, foot, box)
          else none)

end NonforwardOtherWitness
end Elegant.Layered.PipelineImpl
