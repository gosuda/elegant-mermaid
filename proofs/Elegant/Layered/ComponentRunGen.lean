import Elegant.Layered.Pipeline
import Elegant.Layered.ExactPipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

def coordinateGen (sizeHook : Proper → Proper) (P : Params) (p : Proper) : Proper :=
  materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders (titleReservations (sizeHook p)) P.clusterBorderW))

def componentRunGen (P : Params) (sizeHook : Proper → Proper) (reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)) (exactOut : List Nat) (cg : Graph) (labels : List MeasuredLabel) (orderOptions : OrderOptions) : Except LayoutError Run := do
  let rr ← rankWithBudget (Compound.rankingGraph cg)
  let p0 ← normalize cg rr.ranks
  let p ← Labels.addLabelNodes cg p0 (componentLabels cg labels)
  let p := coordinateGen sizeHook P p
  let ord ← orderWithBudget p orderOptions
  let coordinateXs ← crossCoordsClusterWith P.nodeGap P.clusterPad p ord.layers
  let routed ← proxyWidths p coordinateXs
  let routeProper := OrderImpl.dropSynthetic routed.1
  let xs := routed.2
  let lanes ← RouteImpl.routeWithLanes P.slot routeProper ord.layers xs (cg.edges.map (·.reversed)) (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width)
  let r := lanes.routing
  let yt ← rankCoordsWith P.rankGap P.slot p ord.layers (r.gaps.map (·.slots))
  let ys := proxyYs p ord.layers yt.2 yt.1
  let (ys', top') ← reserveHook p ord.layers ys yt.2
  let routes ← RouteImpl.routePointsWithLanes P.slot routeProper ord.layers xs ys' top' lanes
  pure ⟨routeProper, ord.layers, xs, ys', top', r, routes, rr.budgetExhausted || ord.budgetExhausted, lanes, p, coordinateXs, yt.1, exactOut⟩

theorem componentRun_eq_gen (P : Params) (cg : Graph) (labels : List MeasuredLabel) (orderOptions : OrderOptions) : componentRun P cg labels orderOptions = componentRunGen P (sizeProperPorts P) (fun _ _ ys top => .ok (ys, top)) [] cg labels orderOptions := by
  unfold componentRun componentRunGen coordinateGen coordinateGraph
  rfl

theorem componentRunX_eq_gen (P : Params) (exact : List Nat) (cg : Graph) (labels : List MeasuredLabel) (orderOptions : OrderOptions) : componentRunX P exact cg labels orderOptions = componentRunGen P (sizeProperPortsX P exact) (reserveExactRanks cg exact labels) (cg.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none) cg labels orderOptions := by
  unfold componentRunX componentRunGen coordinateGen coordinateGraphX
  rfl

structure RunHooksSpec (sizeHook : Proper → Proper) (reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)) : Prop where
  size_length : ∀ (p : Proper), (sizeHook p).nodes.length = p.nodes.length
  size_key : ∀ (p : Proper) (v : Nat), ((sizeHook p).nodes[v]?).map (fun (nd : ProperNode) => (nd.dummy, nd.node.border, nd.node.clusterPath)) = (p.nodes[v]?).map (fun (nd : ProperNode) => (nd.dummy, nd.node.border, nd.node.clusterPath))
  size_chains : ∀ (p : Proper), (sizeHook p).chains = p.chains
  reserve_length : ∀ (p : Proper) (layers : List (List Nat)) (ys top ys' top' : List Int), reserveHook p layers ys top = .ok (ys', top') → ys'.length = ys.length ∧ top'.length = top.length

theorem componentRunGen_spec {P : Params} {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)} {exactOut : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions} (h : componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run) : ∃ ranks p0 labeled q0 y_pre top_pre ys_pre, normalize cg ranks = .ok p0 ∧ Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled ∧ coordinateGen sizeHook P labeled = run.coordinateProper ∧ (∃ ord, orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers) ∧ crossCoordsClusterWith P.nodeGap P.clusterPad run.coordinateProper run.layers = .ok run.coordinateXs ∧ proxyWidths run.coordinateProper run.coordinateXs = .ok (q0, run.xs) ∧ OrderImpl.dropSynthetic q0 = run.proper ∧ RouteImpl.routeWithLanes P.slot run.proper run.layers run.xs (cg.edges.map (·.reversed)) (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width) = .ok run.lanes ∧ run.lanes.routing = run.routing ∧ rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧ proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧ reserveHook run.coordinateProper run.layers ys_pre top_pre = .ok (run.ys, run.top) ∧ run.coordinateYs = y_pre ∧ RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top run.lanes = .ok run.routes ∧ run.exact = exactOut := by
  unfold componentRunGen at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨pL, hpL, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨routed, hprojection, h⟩ := bind_ok h
  obtain ⟨lanes, hr, h⟩ := bind_ok h
  obtain ⟨⟨y, top⟩, hy, h⟩ := bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  exact ⟨rr.ranks, p0, pL, routed.1, y, top, _, hp0, hpL, rfl, ⟨ord, hord, rfl⟩, hxs, hprojection, rfl, hr, rfl, hy, rfl, hres, rfl, hroutes, rfl⟩

theorem coordinateGen_chains {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)} (hs : RunHooksSpec sizeHook reserveHook) (P : Params) (p : Proper) : (coordinateGen sizeHook P p).chains = p.chains := by
  unfold coordinateGen materializeDummyPaths clearProxyExtents
  have hTitle : (titleReservations (sizeHook p)).chains = (sizeHook p).chains := rfl
  have hSize : (sizeHook p).chains = p.chains := hs.size_chains p
  have hMeta := (OrderImpl.addClusterBorders_metadata (titleReservations (sizeHook p)) P.clusterBorderW).2.1
  rw [hMeta, hTitle, hSize]

private theorem gen_zipIdx_filter_length (xs : List ProperNode) (n : Nat) : (((xs.zipIdx n).filter (fun (q : ProperNode × Nat) => q.1.node.border == -2)).length = (xs.filter (fun (nd : ProperNode) => nd.node.border == -2)).length) := by
  induction xs generalizing n with
  | nil => simp [List.zipIdx_nil]
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.filter_cons]
    by_cases hx : x.node.border == -2
    · simp [hx, ih]
    · simp [hx, ih]

private theorem gen_filter_border_length (xs ys : List ProperNode) (hLen : xs.length = ys.length) (hBorder : ∀ (v : Nat), (xs[v]?).map (fun (nd : ProperNode) => nd.node.border) = (ys[v]?).map (fun (nd : ProperNode) => nd.node.border)) : (xs.filter (fun (nd : ProperNode) => nd.node.border == -2)).length = (ys.filter (fun (nd : ProperNode) => nd.node.border == -2)).length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hLen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hLen
    | cons y ys =>
      have hLenTail : xs.length = ys.length := by simpa using hLen
      have hEq : x.node.border = y.node.border := by
        have h0 := hBorder 0
        simpa using h0
      have hHead : (x.node.border == -2) = (y.node.border == -2) := by rw [hEq]
      have hTail : ∀ (v : Nat), (xs[v]?).map (fun (nd : ProperNode) => nd.node.border) = (ys[v]?).map (fun (nd : ProperNode) => nd.node.border) := by
        intro v
        have hSv := hBorder (v + 1)
        simpa using hSv
      have ihtail := ih ys hLenTail hTail
      simp only [List.filter_cons]
      rw [hHead]
      by_cases hc : y.node.border == -2
      · simp [hc, ihtail]
      · simp [hc, ihtail]

theorem titleReservations_length_eq {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)} (hs : RunHooksSpec sizeHook reserveHook) (p : Proper) : (titleReservations (sizeHook p)).nodes.length = (titleReservations p).nodes.length := by
  have hLen : (sizeHook p).nodes.length = p.nodes.length := hs.size_length p
  have hBorder : ∀ (v : Nat), ((sizeHook p).nodes[v]?).map (fun (nd : ProperNode) => nd.node.border) = (p.nodes[v]?).map (fun (nd : ProperNode) => nd.node.border) := by
    intro v
    have h := hs.size_key p v
    cases h1 : (sizeHook p).nodes[v]? with
    | none =>
      simp [h1] at h
      cases h2 : p.nodes[v]? with
      | none => rfl
      | some b => simp [h2] at h
    | some a =>
      cases h2 : p.nodes[v]? with
      | none => simp [h1, h2] at h
      | some b =>
        simp [h1, h2] at h ⊢
        obtain ⟨_, hB, _⟩ := h
        rw [hB]
  have hTitleNodes : (titleNodes (sizeHook p)).length = (titleNodes p).length := by
    unfold titleNodes
    have e1 := gen_zipIdx_filter_length (sizeHook p).nodes 0
    have e2 := gen_zipIdx_filter_length p.nodes 0
    rw [e1, e2]
    exact gen_filter_border_length _ _ hLen hBorder
  have e1 : (titleReservations (sizeHook p)).nodes.length = (sizeHook p).nodes.length + (titleNodes (sizeHook p)).length := by
    rw [titleReservations_nodes]
    simp [List.length_append, List.length_map]
  have e2 : (titleReservations p).nodes.length = p.nodes.length + (titleNodes p).length := by
    rw [titleReservations_nodes]
    simp [List.length_append, List.length_map]
  rw [e1, e2, hLen, hTitleNodes]

theorem componentRunGen_ys_length {P : Params} {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)} {exactOut : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions} (hs : RunHooksSpec sizeHook reserveHook) (h : componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run) : run.ys.length = run.coordinateProper.nodes.length := by
  obtain ⟨_, _, _, _, y_pre, top_pre, ys_pre, _, _, _, _, _, _, _, _, _, hry, hyspre, hres, _, _, _⟩ := componentRunGen_spec h
  have hyLen : y_pre.length = run.coordinateProper.nodes.length := (CoordsImpl.rankCoordsWith_length hry).1
  have hysLen : ys_pre.length = y_pre.length := by
    rw [← hyspre]
    simp [proxyYs]
  have hresLen := hs.reserve_length run.coordinateProper run.layers ys_pre top_pre run.ys run.top hres
  rw [hresLen.1, hysLen, hyLen]

theorem runHooksSpec_plain (P : Params) : RunHooksSpec (sizeProperPorts P) (fun _ _ ys top => .ok (ys, top)) where
  size_length := fun p => by simp [sizeProperPorts]
  size_key := fun p v => by
    cases hv : p.nodes[v]? with
    | none => simp [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hv]
    | some nd =>
      simp only [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
      by_cases hc : (nd.dummy || nd.node.border != 0) = true
      · simp [hc]
      · simp [hc]
  size_chains := fun p => rfl
  reserve_length := fun p layers ys top ys' top' h => by
    have hpair := Except.ok.inj h
    cases hpair
    exact ⟨rfl, rfl⟩

private theorem gen_mapM_ok_length {err α β : Type} (f : α → Except err β) : ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

theorem runHooksSpec_exact (P : Params) (exact : List Nat) (cg : Graph) (labels : List MeasuredLabel) : RunHooksSpec (sizeProperPortsX P exact) (reserveExactRanks cg exact labels) where
  size_length := fun p => by simp [sizeProperPortsX]
  size_key := fun p v => by
    cases hv : p.nodes[v]? with
    | none => simp [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hv]
    | some nd =>
      simp only [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
      split <;> rfl
  size_chains := fun p => rfl
  reserve_length := fun p layers ys top ys' top' h => by
    unfold reserveExactRanks at h
    obtain ⟨topNew, htopM, h1⟩ := bind_ok h
    obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
    have hpair := Except.ok.inj h2
    have htopLen := gen_mapM_ok_length _ _ _ htopM
    have hysLen := gen_mapM_ok_length _ _ _ hysM
    simp at htopLen hysLen
    cases hpair
    exact ⟨hysLen, htopLen⟩

end PipelineImpl
end Layered
end Elegant
