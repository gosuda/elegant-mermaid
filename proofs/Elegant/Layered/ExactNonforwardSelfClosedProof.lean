import Elegant.Layered.ExactNonfwdExtMissProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ForeignNonGroupSpansProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The routing rectangle for a group top is a rank-local proxy, not its
full `frameRect`. Its right endpoint comes from a side marker at that rank;
the frame's horizontal hull includes that marker along with all other ranks. -/
private theorem groupProxy_right_le_frame {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRunX P exact cg labels opts = .ok run)
    {v : Nat} {owner : Node} {coord : ProperNode}
    (howner : cg.nodes[v]? = some owner) (hgroup : owner.border = -2)
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hborder : coord.node.border = -2)
    (hpath : coord.node.clusterPath.getLast? = some owner.decl) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
      (frameRect P cg run v).x + (frameRect P cg run v).w := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨decl, span, hlast, hspan, _, _, _, hright⟩ :=
    proxyWidths_proxy_interval hproxy hcoord (Or.inl hborder)
  have hdecl : decl = owner.decl := Option.some.inj (hlast.symm.trans hpath)
  obtain ⟨_, i, _, marker, _, hmarker, _, hside, _, hmarkerLast, _, _, _, hhi⟩ :=
    proxySpan_endpoint_sources hspan
  have hnproxy : ¬ (marker.node.border = -2 ∨ marker.node.border = 2) := by
    rcases hside with h | h <;> omega
  obtain ⟨hfinal, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 i marker hmarker hnproxy
  have hnodes : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  have hmarker' : run.proper.nodes[i]? = some marker := by
    simpa only [hnodes] using hfinal
  have hxs : run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
  have hmember := groupBorderRects_mem_of_record (cg := cg) hmarker' hside
    (hmarkerLast.trans (congrArg some hdecl))
  have hbound := (boundsOf_rect_mem hmember).2
  have hmarkerHi : (Labels.rectAt run.proper run.xs run.ys i).x +
      (Labels.rectAt run.proper run.xs run.ys i).w = span.hi := by
    change RouteImpl.leftOf run.proper run.xs i + RouteImpl.nodeW run.proper i = span.hi
    simp only [RouteImpl.leftOf, RouteImpl.xAt, hxs, RouteImpl.nodeW, hmarker']
    exact hhi.symm
  have hownerHi : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w = span.hi := by
    change RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v = span.hi
    simpa only [RouteImpl.leftOf, RouteImpl.nodeW, hnodes] using hright
  rw [hmarkerHi] at hbound
  rw [hownerHi, frameRect_group_span howner hgroup]
  dsimp only
  omega

/-- In an executed exact candidate the routing box cannot reach past its
owner frame. Non-group tops have equal rectangles; group tops use the proxy
interval in the frame's horizontal hull. The bound includes zero-size boxes. -/
theorem X_componentRun_owner_right_le_frame {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate : Nat} {cg : Graph} {run : Run} {opts : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured opts = .ok run)
    {v : Nat} (hv : v < run.proper.nodes.length) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
      (frameRect execution.params cg run v).x + (frameRect execution.params cg run v).w := by
  by_cases hgroup : (cg.nodes.getD v default).border = -2
  · have hget : cg.nodes[v]? = some (cg.nodes.getD v default) := by
      cases hlook : cg.nodes[v]? with
      | none =>
        exfalso
        exact (by decide : (default : Node).border ≠ -2)
          (by simpa only [List.getD_eq_getElem?_getD, hlook, Option.getD_none] using hgroup)
      | some _ => simp only [List.getD_eq_getElem?_getD, hlook, Option.getD_some]
    have hrun' : componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured opts = .ok run := by
      rw [← hcg]
      exact hrun
    have howner : (componentCandidate execution.graph comp candidate).nodes[v]? =
        some (cg.nodes.getD v default) := by
      rw [← hcg]
      exact hget
    obtain ⟨_, labeled, _, hcoord, _, _, hrecords, _, _⟩ :=
      X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun'
    obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq howner hgroup
    let node : ProperNode := ⟨cg.nodes.getD v default, false, none, false⟩
    have hrecord : labeled.nodes[v]? = some node := hrecords v _ howner
    have hcoordNode := X_coordinateGraph_marker_record (P := execution.params)
      (exact := exactDecls exactIds inp) hrecord (Or.inl hgroup) rfl
    rw [hcoord] at hcoordNode
    have hb : (clearF (titleF node)).node.border = -2 :=
      (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
    have hp : (clearF (titleF node)).node.clusterPath.getLast? =
        some (cg.nodes.getD v default).decl := by
      rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1]
      change (cg.nodes.getD v default).clusterPath.getLast? = some (cg.nodes.getD v default).decl
      rw [hpath]
      simp
    exact groupProxy_right_le_frame hrun hget hgroup hcoordNode hb hp
  · simp only [plain_frame_eq_boxRect execution.params cg run v hv hgroup, Int.le_refl]

/-- As in the C6 owner case, the extended loop footprint starts at the
frame's right boundary. The routing box ends no later, so there is no
interior intersection, irrespective of vertical overlap. -/
theorem XNonfwd_extMissGroupSelfY_holds (exactIds : List String) :
    XNonfwd_ExtMissGroupSelfYOverlap exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e
    hcomp hcg hrun _hk _hloop hv _hborder _hy
  exact not_meetsInterior_of_left_le
    (X_componentRun_owner_right_le_frame execution hcomp hcg hrun hv)

end Elegant.Layered.PipelineImpl
