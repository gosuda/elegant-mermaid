import Elegant.Layered.LaneBandsFindRouteFactsProof

set_option autoImplicit false

namespace Elegant.Layered.LaneBands

private theorem mapM_routes_points_orthogonal
    {f : Route → Except LayoutError Route} {routes out : List Route}
    (h : routes.mapM f = .ok out)
    (hPoint : ∀ r ∈ routes, ∀ r', f r = .ok r' → Polyline.isOrthogonal r'.points = true) :
    ∀ r' ∈ out, Polyline.isOrthogonal r'.points = true := by
  intro r' hr'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr'
  obtain ⟨hlen, hget⟩ := mapM_except_spec f routes out h
  have hiOut := (List.getElem?_eq_some_iff.mp hi).1
  have hiIn : i < routes.length := by
    rw [← hlen]
    exact hiOut
  obtain ⟨r, moved, hin, hout, hmove⟩ := hget i hiIn hiOut
  have heq : moved = r' := Option.some.inj (hout.symm.trans hi)
  subst moved
  exact hPoint r (List.mem_of_getElem? hin) r' hmove

private theorem moveRoute_points_orthogonal {axis : Axis} {move : Move} {r r' : Route}
    (h : (do pure { r with points := ← r.points.mapM (move.point axis) }
      : Except LayoutError Route) = .ok r')
    (hAll : Polyline.isOrthogonal r.points = true) : Polyline.isOrthogonal r'.points = true := by
  obtain ⟨points, hpoints, hroute⟩ := bindOk_inv h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hroute
  subst r'
  exact isOrthogonal_mapM_move r.points points hpoints hAll

private theorem applyPin_points_orthogonal {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned)
    (hAll : ∀ r ∈ s.routes, Polyline.isOrthogonal r.points = true) :
    ∀ r ∈ pinned.routes, Polyline.isOrthogonal r.points = true := by
  obtain ⟨_, _, shiftedRoutes, _, _, _, hroutes, _, hfold⟩ := applyPin_shifted h
  have hframe : pinned.routes = shiftedRoutes :=
    (foldReplaceFrame_all bands pin.axis _ pinned hfold).2.2.2.2.2.2.1
  rw [hframe]
  refine mapM_routes_points_orthogonal hroutes ?_
  intro r hr r' hroute
  cases hdelta : pin.route r.id with
  | none =>
    simp only [hdelta, Pure.pure, Except.pure, Except.ok.injEq] at hroute
    subst r'
    exact hAll r hr
  | some delta =>
    simp only [hdelta] at hroute
    exact moveRoute_points_orthogonal hroute (hAll r hr)

private theorem rerouteBands_points_orthogonal {axis : Axis} {sp : Spacing} {bend : Int}
    {bands : List Band} {pin : Pin} {original : List Route} {s routed : Scene}
    (h : rerouteBands axis sp bend bands pin original s = .ok routed)
    (hAll : ∀ r ∈ s.routes, Polyline.isOrthogonal r.points = true) :
    ∀ r ∈ routed.routes, Polyline.isOrthogonal r.points = true := by
  intro r' hr'
  obtain ⟨r, hr, old, _, _, _, _, _, _, hcase⟩ :=
    c4c5_reroute_mem axis sp bend bands pin original s routed h r' hr'
  rcases hcase with ⟨hpoints, _⟩ |
    ⟨_, _, fb, tb, ends, obs, points, _, _, _, _, hends, _, hfind, hpoints⟩
  · rw [hpoints]
    exact hAll r hr
  · rw [hpoints]
    exact findRouteOrthoPin_holds axis sp pin fb tb old.points ends obs bend points hends hfind

private theorem shiftAll_points_orthogonal {axis : Axis} {delta : Int} {s shifted : Scene}
    (h : shiftAll axis delta s = .ok shifted)
    (hAll : ∀ r ∈ s.routes, Polyline.isOrthogonal r.points = true) :
    ∀ r ∈ shifted.routes, Polyline.isOrthogonal r.points = true := by
  unfold shiftAll at h
  obtain ⟨_, _, h⟩ := bindOk_inv h
  obtain ⟨_, _, h⟩ := bindOk_inv h
  obtain ⟨routes, hroutes, h⟩ := bindOk_inv h
  obtain ⟨_, _, h⟩ := bindOk_inv h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst shifted
  show ∀ r ∈ routes, Polyline.isOrthogonal r.points = true
  refine mapM_routes_points_orthogonal hroutes ?_
  intro r hr r' hroute
  exact moveRoute_points_orthogonal hroute (hAll r hr)

/-- Lane-band pinning preserves geometric orthogonality, regardless of route flags.
Each move applies one function to the cross coordinate and leaves the rank coordinate unchanged.
Routes kept by the router therefore need no coverage, endpoint-lookup, or ID assumptions. -/
theorem pinBands_points_orthogonal {boxes : List ModelBox} {o : Options} {s pinned : Scene}
    (hAll : ∀ r ∈ s.routes, Polyline.isOrthogonal r.points = true)
    (h : pinBands boxes o s = .ok pinned) :
    ∀ r ∈ pinned.routes, Polyline.isOrthogonal r.points = true := by
  by_cases hlanes : lanesOf boxes = []
  · have heq := Except.ok.inj (h.symm.trans (pinBands_no_lanes hlanes))
    subst pinned
    exact hAll
  · obtain ⟨axisSpacing, axis, bands, moved, routed, origin, strip, stripScene,
      _, _, _, happ, hroute, horigin, _, hstrip, hgrow⟩ := pinBands_spec hlanes h
    have hMoved := applyPin_points_orthogonal happ hAll
    have hRouted := rerouteBands_points_orthogonal hroute hMoved
    have hOrigin : ∀ r ∈ origin.routes, Polyline.isOrthogonal r.points = true := by
      rcases restoreOrigin_cases horigin with rfl | ⟨_, _, hshift⟩
      · exact hRouted
      · exact shiftAll_points_orthogonal hshift hRouted
    intro r hr
    rw [(growCanvas_frame hgrow).2.1, hstrip, relocateLabels_routes] at hr
    exact hOrigin r hr

end Elegant.Layered.LaneBands
