import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RunLocalSeparationsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Executed leftover route-label clearance

Proves `RouteLabelLeftoverPair` for an executed component run: a placed label
against an in-bounds frame whose proper node is a nonzero dummy, or a real
node failing the scope check.

* Nonzero dummy: impossible. A position `pos < cg.nodes.length` of the proper
  graph is an original candidate node, never a routing or label dummy
  (`componentRun_source_isReal`: dummies are appended after the original
  nodes by `normalize`, and later stages preserve per-index dummy flags).
* Real node failing the scope check: cleared by the forward separation
  argument with the scope premises dropped (`forwardRealClearScopeFree`
  below, the scope-free form of `runLocalForwardSeparation`). The scope
  premises are unused by that proof: a forward label sits at a middle rank,
  so nodes on other ranks are separated in `y` by the rank bands and nodes
  on its own rank in `x` by the layer order, endpoint boxes included.
* Group frames and non-forward edges are handled by the already-proved
  group cases (`case_group_inside`, `RouteLabelForeignClear`) and
  `RouteNonforwardLabelClear`, exactly as in `route_run_clear_inlined`.
-/

/-- A `findIdx?` hit carries its element and predicate. Copy of the helper in
`RouteRunClearCases.lean` (which keeps it private). -/
private theorem findIdxHitElem {α : Type} {l : List α} (p : α → Bool) (j : Nat)
    (h : l.findIdx? p = some j) :
    ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

/-- `nodeRect` is `RouteImpl.boxRect` at the same index, under a proper lookup.
Copy of the helper in `RouteRunClearCases.lean` (which keeps it private). -/
private theorem nodeRect_eq_boxRect {cg : Graph} {run : Run} {pos : Nat} {pn : ProperNode}
    (hlook : run.proper.nodes[pos]? = some pn) :
    nodeRect cg run pos = RouteImpl.boxRect run.proper run.xs run.ys pos := by
  have hget : run.proper.nodes.getD pos default = pn := by
    rw [List.getD_eq_getElem?_getD, hlook, Option.getD_some]
  have hw : RouteImpl.nodeW run.proper pos = pn.node.w := by
    unfold RouteImpl.nodeW
    simp only [hlook]
  have hh : RouteImpl.nodeH run.proper pos = pn.node.h := by
    unfold RouteImpl.nodeH
    simp only [hlook]
  unfold nodeRect RouteImpl.boxRect RouteImpl.xAt RouteImpl.yAt
  rw [hget, hw, hh]

/-- Non-group frame positions read the node rect. Copy of the helper in
`RouteRunClearCases.lean` (which keeps it private). -/
private theorem frameRect_eq_nodeRect_of_plain {P : Params} {cg : Graph}
    {run : Run} {pos : Nat} {nd : Node} (hnd : cg.nodes[pos]? = some nd)
    (hplain : nd.border ≠ -2) :
    frameRect P cg run pos = nodeRect cg run pos := by
  have hget : cg.nodes.getD pos default = nd := by
    rw [List.getD_eq_getElem?_getD, hnd, Option.getD_some]
  have hb : ((cg.nodes.getD pos default).border != -2) = true := by
    rw [hget]
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]

/-- Scope-free forward clearance: every stack rect of a forward label
envelope is axis-separated from the box of every real proper node. This is
the scope-free form of `runLocalForwardSeparation`: the scope premises are
unused by that proof (a forward label sits at a middle rank, so nodes on
other ranks are separated in `y` by the rank bands and nodes on its own
rank in `x` by the layer order, endpoint boxes included). -/
theorem forwardRealClearScopeFree {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRun execution.params cg execution.measured orderOptions = .ok run)
    (hk : cg.edges[k]? = some e)
    (hne : e.tail ≠ e.head)
    (hrev : e.reversed = false)
    (henv : labelEnvelope execution.params cg run execution.measured k e = some env)
    (hv : v < run.proper.nodes.length)
    (hreal : RouteImpl.IsReal run.proper v)
    (hr : r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height))) :
    RectAxisSeparated r (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  have hslot := componentRun_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  have hP := execution_valid execution
  have hnd : (cg.edges.map (·.decl)).Nodup := by
    rw [hcg]
    exact componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  have hshape : CgShape cg := by
    rw [hcg]
    exact componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (measuredGraph_shape execution.graph_eq) candidate
  have hfacts := componentRun_labelFacts hP hnd hshape hrun
  have hrun' : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run := by
    rw [← hcg]
    exact hrun
  obtain ⟨first, q, hfirst, hqfind, henv_eq⟩ := forward_envelope_eq hne hrev henv
  have hpred := List.find?_some hqfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨aindex, and, hanchor, hnodeA, _hedgeA, hdummyA, hborderA, hwA, hhA⟩ :=
    forward_anchor_full hrun hk hne hfirst
  rw [labelAnchorIndex_eq] at hanchor
  have hu : q.2 = aindex := by
    rw [hqfind] at hanchor
    exact Option.some.inj hanchor
  have hmem : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hqfind)
  rw [hu] at hmem
  have hq1 : q.1 = and := Option.some.inj (hmem.symm.trans hnodeA)
  rw [hq1, hu] at hpred
  have hrk_u : rk run.proper.rank aindex =
      (rk run.proper.rank e.tail +
        Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) :=
    hpred.2
  have hu_len : aindex < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnodeA).1
  have hWu : RouteImpl.nodeW run.proper aindex = and.node.w := by
    unfold RouteImpl.nodeW
    rw [hnodeA]
  have hHu : RouteImpl.nodeH run.proper aindex = and.node.h := by
    unfold RouteImpl.nodeH
    rw [hnodeA]
  have hfm : first ∈ routeLabels execution.measured e.decl := by
    cases hrfl : routeLabels execution.measured e.decl with
    | nil => simp [hrfl] at hfirst
    | cons hd tl =>
      have heq : hd = first := by
        have h2 := hfirst
        rw [hrfl] at h2
        simpa using h2
      subst heq
      exact List.mem_cons_self
  have hg0 : 0 ≤ first.gutter := (hlab first ((List.mem_filter.mp hfm).1)).2.2
  have hsizes : ∀ s ∈ (routeLabels execution.measured e.decl).map fun l => (l.width, l.height),
      0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1, (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  have hsizes2 : ∀ s ∈ (routeLabels execution.measured e.decl).map fun l => (l.width, l.height),
      0 ≤ s.2 := fun s hs => (hsizes s hs).2
  have hle : Labels.stackHeight cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) ≤
      RouteImpl.nodeH run.proper aindex := by
    rw [hHu, hhA, ← stackSize_height_eq]
    exact Int.le_refl _
  have hrx : r.x = env.x := (stackRects_entry hr).1
  have hrw : r.w ≤ Labels.stackWidth
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) :=
    stackRect_width_le hr
  have henvx : env.x = RouteImpl.xAt run.xs aindex -
      Int.fdiv (RouteImpl.nodeW run.proper aindex) 2 + first.gutter := by
    rw [henv_eq, hu]
    exact textRectAt_left _ _ _ _ _
  have henvy : env.y = RouteImpl.yAt run.ys aindex := by
    rw [henv_eq, hu]
    exact textRectAt_y _ _ _ _ _
  have _henvw : env.w = RouteImpl.nodeW run.proper aindex - first.gutter := by
    rw [henv_eq, hu]
    rfl
  have henvh : env.h = RouteImpl.nodeH run.proper aindex := by
    rw [henv_eq, hu]
    rfl
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop', hrLanes, _hroutEq, hyT,
      hysEq, _hrts⟩ :=
    componentRun_spec hrun
  have hlay : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hrLanes).1
  have hcov := (RouteImpl.layersOk_spec hlay).2.2.2.1
  obtain ⟨lu, hlu_mem, hu_mem, hu_nn⟩ := hcov aindex hu_len
  obtain ⟨qv, hqv⟩ : ∃ qv, run.proper.nodes[v]? = some qv :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  obtain ⟨lv, hlv_mem, hv_mem, hv_nn⟩ := hcov v hv
  have hrkU : rk run.proper.rank aindex = ((rk run.proper.rank aindex).toNat : Int) :=
    (Int.toNat_of_nonneg hu_nn).symm
  have hrkV : rk run.proper.rank v = ((rk run.proper.rank v).toNat : Int) :=
    (Int.toNat_of_nonneg hv_nn).symm
  have hbandU := hfacts.node_in_band _ _ _ hlu_mem hu_mem hu_len hrkU
  have hbandV := hfacts.node_in_band _ _ _ hlv_mem hv_mem hv hrkV
  have htop : ∀ r r' (lr lr' : List Nat), r < r' → run.layers[r]? = some lr →
      run.layers[r']? = some lr' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.proper lr ≤
        run.top.getD r' 0 := by
    intro r r' lr lr' hrr h1 h2
    rw [layerHeight_eq_route]
    exact hfacts.bands_disjoint r r' lr lr' hrr h1 h2
  by_cases heq : (rk run.proper.rank aindex).toNat = (rk run.proper.rank v).toNat
  · -- Same rank: horizontal separation by the layer order.
    have hlv_eq : lv = lu := by
      have h2 : run.layers[(rk run.proper.rank aindex).toNat]? = some lv := by
        rw [heq]
        exact hlv_mem
      exact Option.some.inj (h2.symm.trans hlu_mem)
    have hlayer_mem : lu ∈ run.layers := List.mem_of_getElem? hlu_mem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu_mem
    have hvmem : v ∈ lu := hlv_eq ▸ hv_mem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
    have hne_uv : v ≠ aindex := by
      intro heq2
      subst heq2
      have h1 := hreal and hnodeA
      rw [hdummyA] at h1
      cases h1
    have hij : i ≠ j := by
      intro heq2
      apply hne_uv
      have hi' : lu[j]? = some aindex := heq2 ▸ hi
      exact (Option.some.inj (hi'.symm.trans hj)).symm
    obtain ⟨pu, hpu, hpu_border, _hpu_dummy, _hpu_h⟩ :=
      proper_to_coord_node hrun hnodeA hu_len
    obtain ⟨pv, hpv, hpv_border, _hpv_dummy, _hpv_h⟩ :=
      proper_to_coord_node hrun hqv hv
    have hpu0 : pu.node.border = 0 := by
      rw [hpu_border]
      exact hborderA
    by_cases hfr : qv.node.border = -2 ∨ qv.node.border = 2
    · -- Foreign frame on the same band: band-edge separation.
      have hpv2 : pv.node.border = qv.node.border := hpv_border
      rcases hfr with hb2 | hb2
      · have hbeq : (pv.node.border == -2) = true := by simp [hpv2, hb2]
        have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
          obtain ⟨_, _, _, _, _, _, hyvv⟩ := CoordsImpl.rankCoordsWith_spec hyT
          rw [hyvv, List.length_map, List.length_range]
        have hlen_cy : v < run.coordinateYs.length := by
          have hplen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
            have h1 := (proxyWidths_rel hproxy).2.2.1
            have h2 : run.proper.nodes = routed.nodes := by
              rw [← hdrop']
              exact OrderImpl.dropSynthetic_nodes _
            rw [h2]
            exact h1
          rw [hcylen, ← hplen]
          exact hv
        have hqr : run.proper.rank = run.coordinateProper.rank := by
          have h1 := (proxyWidths_rel hproxy).2.1
          rw [← hdrop']
          simpa only [OrderImpl.dropSynthetic_rank] using h1
        have hrk_eq : (rk run.coordinateProper.rank v).toNat =
            (rk run.proper.rank aindex).toNat := by
          rw [← hqr, ← heq]
        have hLH : CoordsImpl.layerHeight run.coordinateProper lu =
            RouteImpl.layerHeight run.proper lu := by
          rw [layerHeight_eq_route]
          have hHH : (fun w => RouteImpl.nodeH run.proper w) =
              (fun w => RouteImpl.nodeH run.coordinateProper w) := by
            funext w
            have h1 := nodeH_proxy hproxy w
            have h2 : run.proper.nodes = routed.nodes := by
              rw [← hdrop']
              exact OrderImpl.dropSynthetic_nodes _
            have h3 : RouteImpl.nodeH run.proper w = RouteImpl.nodeH routed w := by
              unfold RouteImpl.nodeH
              rw [h2]
            rw [h3]
            exact h1
          simp only [RouteImpl.layerHeight, hHH]
        have hget : run.layers.getD (rk run.proper.rank aindex).toNat [] = lu := by
          rw [List.getD_eq_getElem?_getD, hlu_mem]
          rfl
        have hyv : RouteImpl.yAt run.ys v =
            run.top.getD (rk run.proper.rank aindex).toNat 0 := by
          have hys_eq : run.ys =
             proxyYs run.coordinateProper run.layers run.top run.coordinateYs := hysEq.symm
          rw [hys_eq]
          unfold RouteImpl.yAt
          have hpg := proxyYs_getD run.coordinateProper run.layers run.top
            run.coordinateYs hpv hlen_cy
          rw [hpg, hbeq]
          simp only [↓reduceIte]
          rw [hrk_eq]
        have hframe : RouteImpl.IsFrame run.proper v := by
          rw [isFrame_iff hqv]
          exact ⟨hreal qv hqv, Or.inl hb2⟩
        have hfh : RouteImpl.nodeH run.proper v = 0 := hfacts.frame_flat v hframe
        apply Or.inr; apply Or.inr; apply Or.inr
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
           RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
        have hboxh : (RouteImpl.boxRect run.proper run.xs run.ys v).h =
           RouteImpl.nodeH run.proper v := boxRect_h _ _ _ _
        have hlo : env.y ≤ r.y := stackRect_lower_le hslot hsizes2 hr
        rw [henvy] at hlo
        omega
      · have hbeq : (pv.node.border == -2) = false := by simp [hpv2, hb2]
        have hbeq2 : (pv.node.border == 2) = true := by simp [hpv2, hb2]
        have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
          obtain ⟨_, _, _, _, _, _, hyvv⟩ := CoordsImpl.rankCoordsWith_spec hyT
          rw [hyvv, List.length_map, List.length_range]
        have hlen_cy : v < run.coordinateYs.length := by
          have hplen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
            have h1 := (proxyWidths_rel hproxy).2.2.1
            have h2 : run.proper.nodes = routed.nodes := by
              rw [← hdrop']
              exact OrderImpl.dropSynthetic_nodes _
            rw [h2]
            exact h1
          rw [hcylen, ← hplen]
          exact hv
        have hqr : run.proper.rank = run.coordinateProper.rank := by
          have h1 := (proxyWidths_rel hproxy).2.1
          rw [← hdrop']
          simpa only [OrderImpl.dropSynthetic_rank] using h1
        have hrk_eq : (rk run.coordinateProper.rank v).toNat =
            (rk run.proper.rank aindex).toNat := by
          rw [← hqr, ← heq]
        have hLH : CoordsImpl.layerHeight run.coordinateProper lu =
            RouteImpl.layerHeight run.proper lu := by
          rw [layerHeight_eq_route]
          have hHH : (fun w => RouteImpl.nodeH run.proper w) =
              (fun w => RouteImpl.nodeH run.coordinateProper w) := by
            funext w
            have h1 := nodeH_proxy hproxy w
            have h2 : run.proper.nodes = routed.nodes := by
              rw [← hdrop']
              exact OrderImpl.dropSynthetic_nodes _
            have h3 : RouteImpl.nodeH run.proper w = RouteImpl.nodeH routed w := by
              unfold RouteImpl.nodeH
              rw [h2]
            rw [h3]
            exact h1
          simp only [RouteImpl.layerHeight, hHH]
        have hget : run.layers.getD (rk run.proper.rank aindex).toNat [] = lu := by
          rw [List.getD_eq_getElem?_getD, hlu_mem]
          rfl
        have hyv : RouteImpl.yAt run.ys v =
            run.top.getD (rk run.proper.rank aindex).toNat 0 +
              RouteImpl.layerHeight run.proper lu := by
          have hys_eq : run.ys =
             proxyYs run.coordinateProper run.layers run.top run.coordinateYs := hysEq.symm
          rw [hys_eq]
          unfold RouteImpl.yAt
          have hpg := proxyYs_getD run.coordinateProper run.layers run.top
            run.coordinateYs hpv hlen_cy
          rw [hpg, hbeq, hbeq2]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hrk_eq, hget, hLH]
        apply Or.inr; apply Or.inr; apply Or.inl
        have hup : r.y + r.h ≤ env.y +
            Labels.stackHeight cg.slot
              ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) :=
          stackRect_upper_le hslot hsizes2 hr
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
           RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
        rw [hbox, hyv]
        omega
    · -- Both non-frames: layer order.
      have hnb1 : ¬ (pu.node.border = -2 ∨ pu.node.border = 2) := by
        rw [hpu0]
        omega
      have hnb2 : ¬ (pv.node.border = -2 ∨ pv.node.border = 2) := by
        rw [hpv_border]
        exact hfr
      have e1 : Int.fdiv (RouteImpl.nodeW run.proper aindex) 2 =
          RouteImpl.nodeW run.proper aindex / 2 := fdiv2_ediv _
      have e2 : Int.fdiv (RouteImpl.nodeW run.proper v) 2 =
          RouteImpl.nodeW run.proper v / 2 := fdiv2_ediv _
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · have hord := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp
          hrun' hlayer_mem hlt hi hj hpu hpv hnb1 hnb2
        apply Or.inl
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
            RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
         boxRect_left _ _ _ _
        rw [hrx, henvx, hbox, e1, e2]
        unfold RouteImpl.leftOf at hord
        have hwle : Labels.stackWidth
            ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) +
            first.gutter ≤ RouteImpl.nodeW run.proper aindex := by
          rw [hWu, ← stackSize_width_eq]
          exact hwA
        omega
      · have hord := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp
          hrun' hlayer_mem hgt hj hi hpv hpu hnb2 hnb1
        apply Or.inr; apply Or.inl
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
            RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
         boxRect_left _ _ _ _
        have hboxw : (RouteImpl.boxRect run.proper run.xs run.ys v).w =
            RouteImpl.nodeW run.proper v :=
         boxRect_w _ _ _ _
        rw [hrx, henvx, hbox, hboxw, e1, e2]
        unfold RouteImpl.leftOf at hord
        omega
  · -- Different ranks: band separation.
    have hne2 : (rk run.proper.rank aindex).toNat ≠ (rk run.proper.rank v).toNat := heq
    rcases Nat.lt_or_gt_of_ne hne2 with hlt | hgt
    · have hband := rank_band_above hlu_mem hlv_mem hlt htop hbandU hbandV.1
      apply Or.inr; apply Or.inr; apply Or.inl
      have hup : r.y + r.h ≤ env.y +
          Labels.stackHeight cg.slot
            ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) :=
        stackRect_upper_le hslot hsizes2 hr
      have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
         RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
      rw [hbox]
      omega
    · have hband := rank_band_below hlu_mem hlv_mem hgt htop hbandU.1 hbandV
      apply Or.inr; apply Or.inr; apply Or.inr
      have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
         RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
      have hboxh : (RouteImpl.boxRect run.proper run.xs run.ys v).h =
         RouteImpl.nodeH run.proper v := boxRect_h _ _ _ _
      have hlo : env.y ≤ r.y := stackRect_lower_le hslot hsizes2 hr
      rw [henvy] at hlo
      rw [hbox, hboxh]
      omega

/-- Executed `RouteLabelLeftoverPair`: a placed label clears every in-bounds
frame whose proper node is a nonzero dummy or a scope-failing real node.
Nonzero dummies are impossible at original indices
(`componentRun_source_isReal`); scope-failing real nodes of forward edges
are cleared by the scope-free forward separation (`forwardRealClearScopeFree`,
whose scope premises are unused); group frames go through the dummy-inside
and foreign-disjointness cases, and non-forward edges through
`RouteNonforwardLabelClear`, exactly as in `route_run_clear_inlined`. -/
theorem routeLabelLeftoverPair_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hstrict : StrictDummyFrameLinked execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hbracket : BracketMarkersAtRank) (hrank : ForeignClusterRankSpans)
    (hxalign : ForeignBorderChainXAligned)
    (hforeign : RouteLabelForeignClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hloop : RouteNonforwardLabelClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    RouteLabelLeftoverPair execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl pos hpos pn hlook hcase
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
    placedLabels_pair_inv hnd hmem
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := findIdxHitElem _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  have hml : l₀ = ml :=
    (measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)).symm
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdecls : ((componentCandidate execution.graph comp candidate).edges.map
      Edge.decl).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  have heq : edge = edge' := by
    have hmap : ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl)[edge]? =
        ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge < ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl).length := by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdecls.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  subst hEE
  have hv : pos < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hlook).1
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      (componentCandidate execution.graph comp candidate).slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hne : (componentCandidate execution.graph comp candidate).nodes[pos]? ≠ none := by
    intro h
    rw [List.getElem?_eq_none_iff] at h
    omega
  obtain ⟨nd, hnd⟩ := Option.ne_none_iff_exists'.mp hne
  by_cases hfw : e.tail = e.head ∨ e.reversed = true
  · exact hloop k rect l₀ edge e hmem hmem0 hidx hedge hdecl hfw pos hpos
  · have hne' : e.tail ≠ e.head := fun h => hfw (Or.inl h)
    have hnr : e.reversed = false := by
      cases hr : e.reversed with
      | true => rw [hr] at hfw; simp at hfw
      | false => rfl
    by_cases hgrp : nd.border = -2
    · obtain ⟨ndd, d, hddummy, hdfind⟩ := dummy_ex_labeled_of_run execution hcomp hrun
        edge e hedge hne' hnr ⟨l₀, hmem0, hdecl.symm⟩
      by_cases hpc : nd.decl ∈ ndd.node.clusterPath
      · have h2 := routeLabelInDummy_of_run execution hcomp hrun
        have hS := case_group_inside hmem hmem0 hidx hedge hdecl hne' hnr hnd hgrp
          hddummy hdfind hpc hstrict h2
        exact Or.inr hS
      · have himp : SeamsImplyForeign execution.params
            (componentCandidate execution.graph comp candidate) run :=
          fun hb' hr' hx' =>
            foreignFramesDisjoint_of_run execution hwf hframed hcomp hrun hb' hr' hx'
        have hD := hforeign hbracket hrank hxalign himp k rect l₀ edge e hmem hmem0 hidx
          hedge hdecl hne' hnr d ndd hddummy hdfind pos nd hnd hgrp hpc
        exact Or.inl hD
    · have hfr : frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos =
          nodeRect (componentCandidate execution.graph comp candidate) run pos :=
        frameRect_eq_nodeRect_of_plain hnd hgrp
      have hbr : nodeRect (componentCandidate execution.graph comp candidate) run pos =
          RouteImpl.boxRect run.proper run.xs run.ys pos :=
        nodeRect_eq_boxRect hlook
      rcases hcase with ⟨hdummy, _⟩ | ⟨hI, _⟩
      · have hreal := componentRun_source_isReal hrun hnd
        have hfalse := hreal pn hlook
        rw [hdummy] at hfalse
        exact absurd hfalse (by decide)
      · have hsep := forwardRealClearScopeFree execution comp candidate run orderOptions
          _ edge e env pos rect hcomp rfl hrun hedge hne' hnr henv hv hI hmemstk
        have hdis := RectAxisSeparated_of_not_meetsInterior hsep
        rw [hfr, hbr]
        apply Or.inl
        unfold Disjoint
        rw [Rect.meetsInterior_comm]
        exact hdis

end Elegant.Layered.PipelineImpl
