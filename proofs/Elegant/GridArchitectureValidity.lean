import Elegant.GridArchitectureRouteFacts
import Elegant.GridFacts
import ElegantGeometry.Validator
import Elegant.GridArchitectureLevelFacts

set_option autoImplicit false

namespace Elegant.Grid.Architecture

theorem validator_C4_translate (dx dy : Int) (rawPoints : List (List Point))
    (d : _root_.LayoutDump)
    (hcorr : ∀ r ∈ d.routes, r.orthogonal = true →
      ∃ raw ∈ rawPoints, r.points =
        List.map (fun v => (⟨v.x + dx, v.y + dy⟩ : Point)) raw ∧
        _root_.Polyline.isOrthogonal raw = true) :
    _root_.Validator.C4 d := by
  intro r hr hort
  obtain ⟨raw, _, hmap, horth⟩ := hcorr r hr hort
  rw [hmap, isOrthogonal_map_translate dx dy raw]
  exact horth

theorem validator_C5_of_correspondence (dx dy : Int) (d : _root_.LayoutDump)
    (boxSpan : String → Span)
    (first last : _root_.Route → Point)
    (hboxes : ∀ (id : String) (b : _root_.Box), d.box? id = some b →
      b.rect.x = (boxSpan id).x0 + dx ∧ b.rect.y = (boxSpan id).y0 + dy ∧
      b.rect.w = (boxSpan id).x1 - (boxSpan id).x0 ∧
      b.rect.h = (boxSpan id).y1 - (boxSpan id).y0)
    (hends : ∀ r ∈ d.routes,
      r.points.head? = some (⟨(first r).x + dx, (first r).y + dy⟩ : Point) ∧
      r.points.getLast? = some (⟨(last r).x + dx, (last r).y + dy⟩ : Point))
    (hbound : ∀ r ∈ d.routes, SpanBoundary (first r) (boxSpan r.fromId) ∧
      SpanBoundary (last r) (boxSpan r.toId))
    (hlookup : ∀ r ∈ d.routes, ∃ fb tb, d.box? r.fromId = some fb ∧
      d.box? r.toId = some tb ∧ fb.id = r.fromId ∧ tb.id = r.toId) :
    _root_.Validator.C5 d := by
  intro r hr
  obtain ⟨hhead, hlast⟩ := hends r hr
  obtain ⟨fb, tb, hfb, htb, _, _⟩ := hlookup r hr
  obtain ⟨hfirst, hlastB⟩ := hbound r hr
  obtain ⟨hfx, hfy, hfw, hfh⟩ := hboxes r.fromId fb hfb
  obtain ⟨htx, hty, htw, hth⟩ := hboxes r.toId tb htb
  exact ⟨_, _, fb, tb, hhead, hlast, hfb, htb,
    spanBoundary_onBoundary dx dy (boxSpan r.fromId) (first r) fb.rect
      (⟨(first r).x + dx, (first r).y + dy⟩ : Point) hfx hfy hfw hfh rfl rfl hfirst,
    spanBoundary_onBoundary dx dy (boxSpan r.toId) (last r) tb.rect
      (⟨(last r).x + dx, (last r).y + dy⟩ : Point) htx hty htw hth rfl rfl hlastB⟩

theorem translateRect_shape (dx dy : Int) (r : Span) (rect : Rect)
    (h : translateRect dx dy r = .ok rect) :
    (r.x0 = r.x1 ∧ r.y0 = r.y1 ∧ rect = ⟨0, 0, 0, 0⟩) ∨
    (rect.x = r.x0 + dx ∧ rect.y = r.y0 + dy ∧
      rect.w = r.x1 - r.x0 ∧ rect.h = r.y1 - r.y0) := by
  unfold translateRect at h
  by_cases hdeg : r.x0 = r.x1 ∧ r.y0 = r.y1
  · simp [hdeg] at h
    cases h
    exact Or.inl ⟨hdeg.1, hdeg.2, rfl⟩
  · simp [hdeg] at h
    split at h
    · cases h
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    · cases h

private theorem mapM_index {α β ε : Type} {f : α → Except ε β}
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ hy : i < ys.length, f xs[i] = .ok ys[i] := by
  obtain ⟨hlen, hpairs⟩ := mapM_ok_pairs xs ys h
  have hy : i < ys.length := by omega
  refine ⟨hy, hpairs xs[i] ys[i] ?_⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨i, ?_, ?_⟩
  · simp only [List.length_zip]
    omega
  · simp only [List.getElem_zip]

private theorem mapM_ok_pointwise (dx dy : Int) (xs ys : List Point)
    (h : xs.mapM (translatePoint dx dy) = .ok ys) :
    ys = xs.map (fun v => (⟨v.x + dx, v.y + dy⟩ : Point)) := by
  have hlen := (mapM_ok_pairs xs ys h).1
  apply List.ext_getElem
  · simp only [List.length_map]
    exact hlen.symm
  · intro i hi hj
    have hx : i < xs.length := by simpa only [List.length_map] using hj
    obtain ⟨hy, hpoint⟩ := mapM_index xs ys h i hx
    obtain ⟨hxadd, hyadd⟩ := translatePoint_add dx dy xs[i] ys[i] hpoint
    simp only [List.getElem_map]
    rw [← hxadd, ← hyadd]

theorem build_scene_C4 (m : Model) (scene : Scene) (capped : Bool)
    (h : Elegant.Kinds.Architecture.build m = .ok (scene, capped)) :
    _root_.Validator.C4 scene.layoutDump := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Elegant.Kinds.Architecture.build_success m scene capped h
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  subst scene
  refine validator_C4_translate dx dy rawRoutes _ ?_
  intro r hr _
  change r ∈ dumpRoutes at hr
  rw [hdumpRoutes] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp hq)
  have hedgesLen := (mapM_ok_pairs _ _ hedges).1
  have hrawLen : rawRoutes.length = edges.length := by
    rw [hrawRoutes]
    simp only [Grid.Architecture.routes, List.length_map,
      Grid.Architecture.assignPorts]
    simp
  have hiraw : q.2 < rawRoutes.length := by omega
  obtain ⟨hiroutes, htranslate⟩ := mapM_index rawRoutes routes hroutes q.2 hiraw
  have hmap := mapM_ok_pointwise dx dy rawRoutes[q.2] routes[q.2] htranslate
  have hgetD : routes.getD q.2 [] = routes[q.2] := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_some_iff.mpr ⟨hiroutes, rfl⟩]
    rfl
  refine ⟨rawRoutes[q.2], List.getElem_mem hiraw, ?_, ?_⟩
  · change routes.getD q.2 [] = _
    rw [hgetD]
    exact hmap
  · apply arch_routes_axis_orthogonal p pitch nodeInput edges resolved geometry
    rw [← hrawRoutes]
    exact List.getElem_mem hiraw

theorem content_points_contains_initial (points : List Point) (initial : Span) :
    (points.foldl (fun bounds point =>
      bounds.union ⟨point.x, point.y, point.x, point.y⟩) initial).contains initial := by
  induction points generalizing initial with
  | nil => simp only [List.foldl_nil, Span.contains]; omega
  | cons point points ih =>
    rw [List.foldl_cons]
    have hnext := ih (initial.union ⟨point.x, point.y, point.x, point.y⟩)
    have hfirst := union_contains_left initial
      (⟨point.x, point.y, point.x, point.y⟩ : Span)
    unfold Span.contains at *
    omega

theorem content_routes_contains_initial (routes : List (List Point)) (initial : Span) :
    (routes.foldl (fun bounds route => route.foldl
      (fun bounds point => bounds.union ⟨point.x, point.y, point.x, point.y⟩) bounds)
      initial).contains initial := by
  induction routes generalizing initial with
  | nil => simp only [List.foldl_nil, Span.contains]; omega
  | cons route routes ih =>
    rw [List.foldl_cons]
    have hnext := ih (route.foldl (fun bounds point =>
      bounds.union ⟨point.x, point.y, point.x, point.y⟩) initial)
    have hfirst := content_points_contains_initial route initial
    unfold Span.contains at *
    omega

theorem content_contains_shape (g : Geometry) (routes : List (List Point))
    (shape : Span)
    (hshape : shape ∈ g.boxes ++ g.labels ++ g.frames ++ g.titles ++ g.badges) :
    (content g routes).contains shape := by
  have hbase := fold_union_contains_member
    (g.boxes ++ g.labels ++ g.frames ++ g.titles ++ g.badges) emptySpan shape hshape
  have hroutes := content_routes_contains_initial routes
    ((g.boxes ++ g.labels ++ g.frames ++ g.titles ++ g.badges).foldl Span.union emptySpan)
  unfold content
  dsimp only
  unfold Span.contains at *
  omega

theorem label_bounds_contains_initial (labels : List Span) (initial : Span) :
    (labels.foldl (fun bounds r =>
      if r.x0 < r.x1 ∧ r.y0 < r.y1 then bounds.union r else bounds) initial).contains
      initial := by
  induction labels generalizing initial with
  | nil => simp only [List.foldl_nil, Span.contains]; omega
  | cons label labels ih =>
    rw [List.foldl_cons]
    split
    · have hnext := ih (initial.union label)
      have hfirst := union_contains_left initial label
      unfold Span.contains at *
      omega
    · exact ih initial

theorem translateRect_contained_in_canvas
    (bounds source : Span) (margin : Int) (rect : Rect)
    (hmargin : 0 ≤ margin) (hcontains : bounds.contains source)
    (hwidth : 0 ≤ bounds.x1 - bounds.x0 + 2 * margin)
    (hheight : 0 ≤ bounds.y1 - bounds.y0 + 2 * margin)
    (h : translateRect (margin - bounds.x0) (margin - bounds.y0) source = .ok rect) :
    (⟨0, 0, bounds.x1 - bounds.x0 + 2 * margin,
      bounds.y1 - bounds.y0 + 2 * margin⟩ : Rect).Contained rect := by
  rcases translateRect_shape _ _ _ _ h with ⟨_, _, rfl⟩ | ⟨hx, hy, hw, hh⟩
  · simp only [Rect.Contained]
    omega
  · unfold Span.contains at hcontains
    simp only [Rect.Contained]
    rw [hx, hy, hw, hh]
    omega

theorem translateRect_source_ordered (dx dy : Int) (source : Span) (rect : Rect)
    (h : translateRect dx dy source = .ok rect) :
    source.x0 ≤ source.x1 ∧ source.y0 ≤ source.y1 := by
  unfold translateRect at h
  by_cases hdeg : source.x0 = source.x1 ∧ source.y0 = source.y1
  · exact ⟨by omega, by omega⟩
  · simp only [hdeg, ↓reduceIte, pure, Except.pure] at h
    split at h
    · rename_i hvalid
      exact ⟨by omega, by omega⟩
    · cases h

theorem normalized_content_contains_shape (g : Geometry) (routes : List (List Point))
    (shape : Span)
    (hshape : shape ∈ g.boxes ++ g.labels ++ g.frames ++ g.titles ++ g.badges)
    (hordered : shape.x0 ≤ shape.x1 ∧ shape.y0 ≤ shape.y1) :
    (if content g routes = emptySpan then (⟨0, 0, 0, 0⟩ : Span)
      else content g routes).contains shape := by
  have hcontent := content_contains_shape g routes shape hshape
  split
  · rename_i hempty
    rw [hempty] at hcontent
    simp only [Span.contains, emptySpan] at hcontent
    omega
  · exact hcontent

private theorem mapM_output_origin {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
  have hlen := (mapM_ok_pairs xs ys h).1
  have hiy : i < ys.length := (List.getElem?_eq_some_iff.mp hi).1
  have hix : i < xs.length := by omega
  obtain ⟨_, hmap⟩ := mapM_index xs ys h i hix
  have heq : ys[i] = y := (List.getElem?_eq_some_iff.mp hi).2
  exact ⟨xs[i], List.getElem_mem hix, heq ▸ hmap⟩

private theorem getD_contained (rects : List Rect) (canvas : Rect)
    (hzero : canvas.Contained ⟨0, 0, 0, 0⟩)
    (hrects : ∀ rect ∈ rects, canvas.Contained rect) (i : Nat) :
    canvas.Contained (rects.getD i ⟨0, 0, 0, 0⟩) := by
  rw [List.getD_eq_getElem?_getD]
  cases hget : rects[i]? with
  | none => exact hzero
  | some rect =>
    exact hrects rect (List.mem_of_getElem? hget)

theorem build_scene_C1 (m : Model) (scene : Scene) (capped : Bool)
    (h : Elegant.Kinds.Architecture.build m = .ok (scene, capped)) :
    _root_.Validator.C1 scene.layoutDump := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Elegant.Kinds.Architecture.build_success m scene capped h
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  subst scene
  have hcanvasW : 0 ≤ width := by omega
  have hcanvasH : 0 ≤ height := by omega
  have hmargin0 : 0 ≤ margin := by
    rw [hmargin]
    cases profile <;> decide
  let canvas : Rect := ⟨0, 0, width, height⟩
  have hzero : canvas.Contained ⟨0, 0, 0, 0⟩ := by
    dsimp only [canvas, Rect.Contained]
    omega
  have hshape : ∀ source ∈
      geometry.boxes ++ geometry.labels ++ geometry.frames ++ geometry.titles ++ geometry.badges,
      ∀ rect, translateRect dx dy source = .ok rect → canvas.Contained rect := by
    intro source hsource rect hrect
    have hordered := translateRect_source_ordered dx dy source rect hrect
    have hbase : bounds0.contains source := by
      rw [hbounds0, hrawBounds]
      exact normalized_content_contains_shape geometry rawRoutes source hsource hordered
    have houter := label_bounds_contains_initial rawLabels bounds0
    rw [← hbounds] at houter
    have hcontained : bounds.contains source := by
      unfold Span.contains at *
      omega
    dsimp only [canvas]
    rw [hwidth, hheight]
    apply translateRect_contained_in_canvas bounds source margin rect hmargin0 hcontained
    · omega
    · omega
    · rw [← hdx, ← hdy]
      exact hrect
  have hboxesInside : ∀ rect ∈ boxes, canvas.Contained rect := by
    intro rect hrect
    obtain ⟨source, hsource, htranslate⟩ := mapM_output_origin hboxes hrect
    apply hshape source ?_ rect htranslate
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hsource)))
  have hframesInside : ∀ rect ∈ frames, canvas.Contained rect := by
    intro rect hrect
    obtain ⟨source, hsource, htranslate⟩ := mapM_output_origin hframes hrect
    apply hshape source ?_ rect htranslate
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr hsource))
  intro box hbox
  change box ∈ dumpBoxes at hbox
  obtain ⟨modelBox, _, hrecord⟩ := mapM_output_origin hdumpBoxes hbox
  change canvas.Contained box.rect
  by_cases hgroup : (modelBox.role == .group) = true
  · simp only [hgroup, ↓reduceIte] at hrecord
    cases hfound : groups.findIdx? (fun q => q.id == modelBox.id) with
    | none => simp [hfound] at hrecord
    | some i =>
      simp only [hfound, bind, Except.bind, pure, Except.pure] at hrecord
      cases Except.ok.inj hrecord
      exact getD_contained frames canvas hzero hframesInside i
  · simp only [hgroup] at hrecord
    cases hfound : nodes.findIdx? (fun q => q.id == modelBox.id) with
    | none => simp [hfound] at hrecord
    | some i =>
      simp only [hfound, bind, Except.bind, pure, Except.pure] at hrecord
      cases Except.ok.inj hrecord
      exact getD_contained boxes canvas hzero hboxesInside i

theorem translateRect_shape_of_positive_height (dx dy : Int) (r : Span) (rect : Rect)
    (height : r.y0 < r.y1) (translated : translateRect dx dy r = .ok rect) :
    rect.x = r.x0 + dx ∧ rect.y = r.y0 + dy ∧
      rect.w = r.x1 - r.x0 ∧ rect.h = r.y1 - r.y0 := by
  rcases translateRect_shape dx dy r rect translated with degenerate | shape
  · omega
  · exact shape

theorem geometry_box_positive_height (p : GeometryParams) (pitch : Pitch)
    (nodes : List Node) (groups : List Group) (resolved : Resolved)
    (n : Nat) (bound : n < nodes.length)
    (height : 0 < (nodes.getD n default).icon.h)
    (label : 0 ≤ (nodes.getD n default).label.h) (thickness : 0 ≤ p.thickness) :
    ((geometry p pitch nodes groups resolved).boxes.getD n default).y0 <
      ((geometry p pitch nodes groups resolved).boxes.getD n default).y1 := by
  have extra : 0 ≤ (if (nodes.getD n default).label.h > 0 then p.thickness else 0) := by
    split <;> omega
  rw [geometry_box_at p pitch nodes groups resolved n bound,
    geometry_icon_at p pitch nodes groups resolved n bound]
  dsimp only [sized]
  omega

theorem routes_index_endpoints (p : GeometryParams) (pitch : Pitch)
    (nodes : List Node) (groups : List Group) (edges : List Edge) (resolved : Resolved)
    (nodeSizes : ∀ node ∈ nodes, 0 ≤ node.icon.w ∧ 0 ≤ node.icon.h ∧ 0 ≤ node.label.h)
    (edgeBounds : ∀ edge ∈ edges, edge.a < nodes.length ∧ edge.b < nodes.length)
    (thickness : 0 ≤ p.thickness) (i : Nat) (hi : i < edges.length) :
    ∃ first last,
      ((routes p pitch nodes edges resolved
        (geometry p pitch nodes groups resolved)).getD i []).head? = some first ∧
      ((routes p pitch nodes edges resolved
        (geometry p pitch nodes groups resolved)).getD i []).getLast? = some last ∧
      SpanBoundary first
        ((geometry p pitch nodes groups resolved).boxes.getD edges[i].a default) ∧
      SpanBoundary last
        ((geometry p pitch nodes groups resolved).boxes.getD edges[i].b default) := by
  have bounds := edgeBounds edges[i] (List.getElem_mem hi)
  have sizeAt : ∀ n, n < nodes.length →
      0 ≤ (nodes.getD n default).icon.w ∧
      0 ≤ (nodes.getD n default).icon.h ∧
      0 ≤ (nodes.getD n default).label.h := by
    intro n hn
    apply nodeSizes
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
      Option.getD_some] using List.getElem_mem hn
  simp only [routes, assignPorts, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, Nat.zero_add]
  refine ⟨_, _, (path_endpoints _ _ _ _).1, (path_endpoints _ _ _ _).2, ?_, ?_⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact geometry_port_on_boundary p pitch nodes groups resolved edges[i].a bounds.1
      edges[i].sideA _ _ (assigned_slot_le_length _ _) (sizeAt _ bounds.1).1
      (sizeAt _ bounds.1).2.1 (sizeAt _ bounds.1).2.2 thickness
  · simp only [↓reduceIte]
    exact geometry_port_on_boundary p pitch nodes groups resolved edges[i].b bounds.2
      edges[i].sideB _ _ (assigned_slot_le_length _ _) (sizeAt _ bounds.2).1
      (sizeAt _ bounds.2).2.1 (sizeAt _ bounds.2).2.2 thickness

theorem decoded_edges_lookup (nodes : List ModelBox) (source : List ModelRoute)
    (edges : List Edge) (sideOf : Elegant.Side → Side)
    (decoded : source.mapM (fun r => do
      let some a := nodes.findIdx? (fun b => b.id == r.fromId) |
        throw LayoutError.domain
      let some b := nodes.findIdx? (fun b => b.id == r.toId) |
        throw LayoutError.domain
      pure (⟨a, b, sideOf r.fromSide, sideOf r.toSide⟩ : Edge)) =
        (Except.ok edges : Except LayoutError (List Edge))) :
    source.length = edges.length ∧
      ∀ (i : Nat) (hi : i < source.length),
        ∃ (he : i < edges.length),
          nodes.findIdx? (fun b => b.id == source[i].fromId) = some edges[i].a ∧
          nodes.findIdx? (fun b => b.id == source[i].toId) = some edges[i].b ∧
          ∃ (ha : edges[i].a < nodes.length) (hb : edges[i].b < nodes.length),
            nodes[edges[i].a].id = source[i].fromId ∧
            nodes[edges[i].b].id = source[i].toId := by
  refine ⟨(mapM_ok_pairs source edges decoded).1, ?_⟩
  intro i hi
  obtain ⟨he, hdecode⟩ := mapM_index source edges decoded i hi
  cases ha : nodes.findIdx? (fun b => b.id == source[i].fromId) with
  | none => simp [ha] at hdecode
  | some a =>
    cases hb : nodes.findIdx? (fun b => b.id == source[i].toId) with
    | none => simp [ha, hb] at hdecode
    | some b =>
      simp only [ha, hb, pure, Except.pure] at hdecode
      have hedge : edges[i] =
          (⟨a, b, sideOf source[i].fromSide, sideOf source[i].toSide⟩ : Edge) :=
        (Except.ok.inj hdecode).symm
      have hapos := (List.findIdx?_eq_some_iff_findIdx_eq.mp ha).1
      have hbpos := (List.findIdx?_eq_some_iff_findIdx_eq.mp hb).1
      have haid := (List.findIdx?_eq_some_iff_getElem.mp ha).2.1
      have hbid := (List.findIdx?_eq_some_iff_getElem.mp hb).2.1
      refine ⟨he, ?_, ?_, ?_⟩
      · simp only [hedge]
      · simp only [hedge]
      · refine ⟨by simpa only [hedge] using hapos,
          by simpa only [hedge] using hbpos, ?_, ?_⟩
        · simpa only [hedge, beq_iff_eq] using haid
        · simpa only [hedge, beq_iff_eq] using hbid

theorem build_scene_route_correspondence (m : Model) (scene : Scene) (capped : Bool)
    (built : Elegant.Kinds.Architecture.build m = .ok (scene, capped)) :
    ∃ (dx dy : Int) (rawRoutes : List (List Point)),
      rawRoutes.length = m.routes.length ∧
      ∀ route ∈ scene.layoutDump.routes,
        ∃ (i : Nat) (hi : i < m.routes.length) (raw : List Point),
          rawRoutes.getD i [] = raw ∧
          route.id = m.routes[i].id ∧
          route.fromId = m.routes[i].fromId ∧
          route.toId = m.routes[i].toId ∧
          route.points = raw.map
            (fun point => (⟨point.x + dx, point.y + dy⟩ : Point)) := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Elegant.Kinds.Architecture.build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  have hedgesLen := (mapM_ok_pairs _ _ hedges).1
  have hrawLen : rawRoutes.length = m.routes.length := by
    rw [hrawRoutes]
    simp only [Grid.Architecture.routes, List.length_map,
      Grid.Architecture.assignPorts, List.length_zipIdx]
    omega
  refine ⟨dx, dy, rawRoutes, hrawLen, ?_⟩
  intro route member
  subst scene
  change route ∈ dumpRoutes at member
  rw [hdumpRoutes] at member
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp member
  have hsource := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hsource
  have hiraw : q.2 < rawRoutes.length := by omega
  obtain ⟨hiroutes, htranslated⟩ := mapM_index rawRoutes routes hroutes q.2 hiraw
  have hgetD : routes.getD q.2 [] = routes[q.2] := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_some_iff.mpr ⟨hiroutes, rfl⟩]
    rfl
  refine ⟨q.2, hi, rawRoutes[q.2], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiraw,
      Option.getD_some]
  · change q.1.id = m.routes[q.2].id
    rw [hget]
  · change q.1.fromId = m.routes[q.2].fromId
    rw [hget]
  · change q.1.toId = m.routes[q.2].toId
    rw [hget]
  · change routes.getD q.2 [] = _
    rw [hgetD]
    exact mapM_ok_pointwise dx dy rawRoutes[q.2] routes[q.2] htranslated

theorem build_scene_decoded_route_correspondence
    (m : Model) (scene : Scene) (capped : Bool)
    (built : Elegant.Kinds.Architecture.build m = .ok (scene, capped)) :
    ∃ (nodes : List ModelBox) (nodeInput : List Node) (groups : List Group)
      (p : GeometryParams) (pitch : Pitch) (resolved : Resolved)
      (edges : List Edge) (dx dy : Int),
      nodes = m.boxes.filter (fun b => b.role != .group) ∧
      nodeInput.length = nodes.length ∧ edges.length = m.routes.length ∧
      ∀ route ∈ scene.layoutDump.routes,
        ∃ (i : Nat) (hi : i < m.routes.length) (he : i < edges.length)
          (ha : edges[i].a < nodes.length) (hb : edges[i].b < nodes.length),
          route.id = m.routes[i].id ∧
          route.fromId = nodes[edges[i].a].id ∧
          route.toId = nodes[edges[i].b].id ∧
          nodes.findIdx? (fun b => b.id == route.fromId) = some edges[i].a ∧
          nodes.findIdx? (fun b => b.id == route.toId) = some edges[i].b ∧
          route.points =
            ((routes p pitch nodeInput edges resolved
              (geometry p pitch nodeInput groups resolved)).getD i []).map
                (fun point => (⟨point.x + dx, point.y + dy⟩ : Point)) := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Elegant.Kinds.Architecture.build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  obtain ⟨hedgesLen, hdecode⟩ := decoded_edges_lookup nodes m.routes edges _ hedges
  have hcaptionsLen := (mapM_ok_pairs _ _ hcaptions).1
  have hnodesLen := (mapM_ok_pairs _ _ hnodeInput).1
  have hnodeLength : nodeInput.length = nodes.length := by
    simp only [List.length_zip] at hnodesLen
    omega
  have hrawLen : rawRoutes.length = m.routes.length := by
    rw [hrawRoutes]
    simp only [Grid.Architecture.routes, List.length_map,
      Grid.Architecture.assignPorts, List.length_zipIdx]
    omega
  refine ⟨nodes, nodeInput, groupInput, p, pitch, resolved, edges, dx, dy,
    hnodes, hnodeLength, hedgesLen.symm, ?_⟩
  intro route member
  subst scene
  change route ∈ dumpRoutes at member
  rw [hdumpRoutes] at member
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp member
  have hsource := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hsource
  obtain ⟨he, hfindA, hfindB, ha, hb, hidA, hidB⟩ := hdecode q.2 hi
  have hiraw : q.2 < rawRoutes.length := by omega
  obtain ⟨hiroutes, htranslated⟩ := mapM_index rawRoutes routes hroutes q.2 hiraw
  have hgetD : routes.getD q.2 [] = routes[q.2] := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_some_iff.mpr ⟨hiroutes, rfl⟩]
    rfl
  refine ⟨q.2, hi, he, ha, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change q.1.id = m.routes[q.2].id
    rw [hget]
  · change q.1.fromId = nodes[edges[q.2].a].id
    rw [← hget]
    exact hidA.symm
  · change q.1.toId = nodes[edges[q.2].b].id
    rw [← hget]
    exact hidB.symm
  · change nodes.findIdx? (fun b => b.id == q.1.fromId) = _
    rw [← hget]
    exact hfindA
  · change nodes.findIdx? (fun b => b.id == q.1.toId) = _
    rw [← hget]
    exact hfindB
  · change routes.getD q.2 [] = _
    rw [hgetD]
    have hpoints := mapM_ok_pointwise dx dy rawRoutes[q.2] routes[q.2] htranslated
    have hrawAt : rawRoutes[q.2] = rawRoutes.getD q.2 [] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiraw,
        Option.getD_some]
    rw [hrawAt, hrawRoutes, hgeometry] at hpoints
    exact hpoints

private theorem model_box_id_unique (xs : List ModelBox)
    (unique : (xs.map (·.id)).Nodup) (a b : ModelBox)
    (ha : a ∈ xs) (hb : b ∈ xs) (equal : a.id = b.id) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨b, hb, equal.symm⟩))
    · rcases List.mem_cons.mp hb with h | hb
      · have absent := unique.1
        have present : b.id ∈ xs.map (·.id) :=
          List.mem_map.mpr ⟨a, ha, equal⟩
        rw [h] at present
        exact False.elim (absent present)
      · exact ih unique.2 ha hb

private theorem mapped_box_find
    (xs : List ModelBox) (ys : List _root_.Box)
    (f : ModelBox → Except LayoutError _root_.Box)
    (mapped : xs.mapM f = .ok ys)
    (ids : ∀ x ∈ xs, ∀ y, f x = .ok y → y.id = x.id)
    (unique : (xs.map (·.id)).Nodup)
    (x : ModelBox) (member : x ∈ xs) (y : _root_.Box)
    (actual : f x = .ok y) :
    ys.find? (fun b => b.id == x.id) = some y := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons a xs ih =>
    cases head : f a with
    | error error => simp [List.mapM_cons, head] at mapped
    | ok b =>
      cases tail : xs.mapM f with
      | error error => simp [List.mapM_cons, head, tail] at mapped
      | ok bs =>
        have output : ys = b :: bs := by
          simpa [List.mapM_cons, head, tail] using mapped.symm
        rw [output]
        have bid := ids a (by simp) b head
        by_cases same : a.id = x.id
        · have ax := model_box_id_unique (a :: xs) unique a x (by simp) member same
          subst a
          have byeq : b = y := Except.ok.inj (head.symm.trans actual)
          have yid : y.id = x.id := ids x (by simp) y actual
          simp [List.find?, byeq, yid]
        · have xin : x ∈ xs := by
            rcases List.mem_cons.mp member with h | h
            · subst a; exact False.elim (same rfl)
            · exact h
          have rest := ih bs tail (fun z hz => ids z (by simp [hz]))
            (List.nodup_cons.mp (by simpa only [List.map_cons] using unique)).2
            xin
          have different : (b.id == x.id) = false := by simp [bid, same]
          simpa only [List.find?, different] using rest

theorem build_scene_C5 (m : Model) (scene : Scene) (capped : Bool)
    (wellFormed : WellFormed m)
    (built : Elegant.Kinds.Architecture.build m = .ok (scene, capped)) :
    _root_.Validator.C5 scene.layoutDump := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Elegant.Kinds.Architecture.build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  have hiw0 : 0 < iw := by
    rw [hiw]
    split
    · split
      · split
        · exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) (Int.le_max_left _ _)
        · exact Int.mul_pos (by assumption) (by decide)
      · cases profile <;> decide
    · cases profile <;> decide
  have hih0 : 0 < ih := by
    rw [hih]
    split
    · split
      · split
        · exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) (Int.le_max_left _ _)
        · exact Int.mul_pos (by assumption) (by decide)
      · cases profile <;> decide
    · cases profile <;> decide
  have hlh0 : 0 ≤ lh := by rw [hlh]; cases profile <;> decide
  have hthickness0 : 0 ≤ p.thickness := by
    rw [hp]
    dsimp only
    rw [hthickness]
    cases profile <;> decide
  have nodeLength : nodeInput.length = nodes.length := by
    have hc := (mapM_ok_pairs _ _ hcaptions).1
    have hn := (mapM_ok_pairs _ _ hnodeInput).1
    simp only [List.length_zip] at hn
    omega
  have nodeSizes : ∀ node ∈ nodeInput,
      0 < node.icon.w ∧ 0 < node.icon.h ∧ 0 ≤ node.label.h := by
    intro node member
    obtain ⟨q, hq, decoded⟩ := mapM_output_origin hnodeInput member
    change ((if q.1.parent.isEmpty then (Except.ok (-1) : Except LayoutError Int)
      else match groups.findIdx? (fun b => b.id == q.1.parent) with
        | some i => .ok (Int.ofNat i)
        | none => .error .domain) >>= _) = .ok node at decoded
    cases parent : (if q.1.parent.isEmpty then (Except.ok (-1) : Except LayoutError Int)
      else match groups.findIdx? (fun b => b.id == q.1.parent) with
        | some i => .ok (Int.ofNat i)
        | none => .error .domain) with
    | error error =>
      rw [parent] at decoded
      contradiction
    | ok parent =>
      rw [parent] at decoded
      simp only [pure, Except.pure] at decoded
      cases decoded
      dsimp only
      have junctionPositive :
          0 < LayoutConst.architecture_junction_size.get profile := by
        cases profile <;> decide
      constructor
      · split <;> omega
      constructor
      · split <;> first | omega | (split <;> omega)
      · change 0 ≤ min COORD_LIMIT ((q.2.length : Int) * lh)
        exact Int.le_min.mpr ⟨by decide, Int.mul_nonneg (by omega) hlh0⟩
  obtain ⟨edgeLength, decodedEdges⟩ := decoded_edges_lookup nodes m.routes edges _ hedges
  have edgeBounds : ∀ edge ∈ edges,
      edge.a < nodeInput.length ∧ edge.b < nodeInput.length := by
    intro edge member
    obtain ⟨i, hi⟩ := List.getElem?_of_mem member
    have hie : i < edges.length := (List.getElem?_eq_some_iff.mp hi).1
    have his : i < m.routes.length := by omega
    obtain ⟨_, _, _, ha, hb, _, _⟩ := decodedEdges i his
    have heq := (List.getElem?_eq_some_iff.mp hi).2
    rw [← heq, nodeLength]
    exact ⟨ha, hb⟩
  have dumpIds : ∀ source ∈ m.boxes, ∀ target,
      (do
        let r ← if source.role == .group then
          match groups.findIdx? (fun q => q.id == source.id) with
          | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
          | none => throw LayoutError.domain
        else
          match nodes.findIdx? (fun q => q.id == source.id) with
          | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
          | none => throw LayoutError.domain
        pure ({ id := source.id, role := source.role.id, rect := r,
                parent := source.parent, exclusive := source.exclusive } : _root_.Box)) =
            (Except.ok target : Except LayoutError _root_.Box) →
        target.id = source.id := by
    intro source _ target decoded
    split at decoded <;> split at decoded <;>
      dsimp only [pure, Except.pure, Bind.bind, Except.bind] at decoded <;>
      cases decoded <;> rfl
  have endpointBox : ∀ (n : Nat) (hn : n < nodes.length)
      (hfind : nodes.findIdx? (fun b => b.id == nodes[n].id) = some n),
      ∃ box, scene.layoutDump.box? nodes[n].id = some box ∧
        box.rect.x = (geometry.boxes.getD n default).x0 + dx ∧
        box.rect.y = (geometry.boxes.getD n default).y0 + dy ∧
        box.rect.w = (geometry.boxes.getD n default).x1 -
          (geometry.boxes.getD n default).x0 ∧
        box.rect.h = (geometry.boxes.getD n default).y1 -
          (geometry.boxes.getD n default).y0 := by
    intro n hn hfind
    have filtered : nodes[n] ∈ m.boxes.filter (fun b => b.role != .group) :=
      Eq.mp (congrArg (fun xs : List ModelBox => nodes[n] ∈ xs) hnodes)
        (List.getElem_mem hn)
    have member : nodes[n] ∈ m.boxes := (List.mem_filter.mp filtered).1
    have nongroup : (nodes[n].role == .group) = false := by
      simpa using (List.mem_filter.mp filtered).2
    have hng : n < nodeInput.length := by omega
    have hgeomLength : n < geometry.boxes.length := by
      rw [hgeometry]
      simpa only [Grid.Architecture.geometry, List.length_map,
        List.length_zipIdx] using hng
    obtain ⟨hboxLength, hbox⟩ := mapM_index geometry.boxes boxes hboxes n hgeomLength
    have hsource : geometry.boxes[n] = geometry.boxes.getD n default := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgeomLength,
        Option.getD_some]
    rw [hsource] at hbox
    have getBox : boxes.getD n ⟨0, 0, 0, 0⟩ = boxes[n] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hboxLength,
        Option.getD_some]
    let box : _root_.Box :=
      { id := nodes[n].id, role := nodes[n].role.id, rect := boxes[n],
        parent := nodes[n].parent, exclusive := nodes[n].exclusive }
    have lookup : dumpBoxes.find? (fun b => b.id == nodes[n].id) = some box := by
      apply mapped_box_find m.boxes dumpBoxes _ hdumpBoxes dumpIds
        (Model.boxIds_nodup wellFormed) nodes[n] member box
      simp only [nongroup, Bool.false_eq_true, ↓reduceIte, hfind,
        pure, Except.pure, getBox]
      rfl
    have size := nodeSizes (nodeInput.getD n default) (by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hng,
        Option.getD_some] using List.getElem_mem hng)
    have positive := geometry_box_positive_height p pitch nodeInput groupInput resolved n
      hng size.2.1 size.2.2 hthickness0
    rw [← hgeometry] at positive
    rcases translateRect_shape dx dy _ _ hbox with degenerate | shape
    · exact False.elim (by omega)
    · refine ⟨box, ?_, shape⟩
      rw [hscene]
      exact lookup
  intro route member
  have routeMember := member
  rw [hscene] at routeMember
  change route ∈ dumpRoutes at routeMember
  rw [hdumpRoutes] at routeMember
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp routeMember
  obtain ⟨hi, hget⟩ :=
    List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)
  obtain ⟨he, hfindA, hfindB, ha, hb, hidA, hidB⟩ := decodedEdges q.2 hi
  obtain ⟨first, last, hfirst, hlast, firstBoundary, lastBoundary⟩ :=
    routes_index_endpoints p pitch nodeInput groupInput edges resolved
      (fun node member => let s := nodeSizes node member; ⟨by omega, by omega, s.2.2⟩)
      edgeBounds hthickness0 q.2 he
  rw [← hgeometry, ← hrawRoutes] at hfirst hlast
  rw [← hgeometry] at firstBoundary lastBoundary
  have rawLength : q.2 < rawRoutes.length := by
    rw [hrawRoutes]
    simp only [Grid.Architecture.routes, Grid.Architecture.assignPorts,
      List.length_map, List.length_zipIdx]
    exact he
  obtain ⟨routeLength, translated⟩ := mapM_index rawRoutes routes hroutes q.2 rawLength
  have pointMap := mapM_ok_pointwise dx dy rawRoutes[q.2] routes[q.2] translated
  have rawAt : rawRoutes.getD q.2 [] = rawRoutes[q.2] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem rawLength,
      Option.getD_some]
  rw [rawAt] at hfirst hlast
  have routeAt : routes.getD q.2 [] = routes[q.2] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem routeLength,
      Option.getD_some]
  obtain ⟨fb, hfb, hfx, hfy, hfw, hfh⟩ :=
    endpointBox edges[q.2].a ha (by rw [hidA]; exact hfindA)
  obtain ⟨tb, htb, htx, hty, htw, hth⟩ :=
    endpointBox edges[q.2].b hb (by rw [hidB]; exact hfindB)
  refine ⟨⟨first.x + dx, first.y + dy⟩, ⟨last.x + dx, last.y + dy⟩,
    fb, tb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (routes.getD q.2 []).head? = _
    rw [routeAt, pointMap, List.head?_map, hfirst]
    rfl
  · change (routes.getD q.2 []).getLast? = _
    rw [routeAt, pointMap, List.getLast?_map, hlast]
    rfl
  · change scene.layoutDump.box? q.1.fromId = some fb
    rw [← hget, ← hidA]
    exact hfb
  · change scene.layoutDump.box? q.1.toId = some tb
    rw [← hget, ← hidB]
    exact htb
  · exact spanBoundary_onBoundary dx dy _ _ _ _ hfx hfy hfw hfh rfl rfl firstBoundary
  · exact spanBoundary_onBoundary dx dy _ _ _ _ htx hty htw hth rfl rfl lastBoundary

theorem layout_scene_C5 (m : Model) (result : Layered.FamilyResult)
    (wellFormed : WellFormed m)
    (success : Elegant.Kinds.Architecture.layout m = .ok result) :
    _root_.Validator.C5 result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := public_layout_dump m result success
  rw [dump]
  exact build_scene_C5 m scene capped wellFormed built

theorem translateRect_parent_contains (dx dy : Int) (outer inner : Span)
    (parent child : Rect)
    (outerNonempty : outer.x0 ≠ outer.x1 ∨ outer.y0 ≠ outer.y1)
    (innerNonempty : inner.x0 ≠ inner.x1 ∨ inner.y0 ≠ inner.y1)
    (contains : outer.contains inner)
    (parentTranslated : translateRect dx dy outer = .ok parent)
    (childTranslated : translateRect dx dy inner = .ok child) :
    parent.Contained child := by
  rcases translateRect_shape dx dy outer parent parentTranslated with degenerate | shape
  · rcases outerNonempty with horizontal | vertical
    · exact False.elim (horizontal degenerate.1)
    · exact False.elim (vertical degenerate.2.1)
  · rcases translateRect_shape dx dy inner child childTranslated with degenerate | childShape
    · rcases innerNonempty with horizontal | vertical
      · exact False.elim (horizontal degenerate.1)
      · exact False.elim (vertical degenerate.2.1)
    · unfold Span.contains at contains
      simp only [Rect.Contained]
      rcases shape with ⟨px, py, pw, ph⟩
      rcases childShape with ⟨cx, cy, cw, ch⟩
      rw [px, py, pw, ph, cx, cy, cw, ch]
      omega

private theorem mapped_box_source_metadata
    (xs : List ModelBox) (ys : List _root_.Box)
    (f : ModelBox → Except LayoutError _root_.Box)
    (mapped : xs.mapM f = .ok ys)
    (metadata : ∀ source ∈ xs, ∀ target, f source = .ok target →
      target.id = source.id ∧ target.parent = source.parent)
    (target : _root_.Box) (member : target ∈ ys) :
    ∃ source ∈ xs, f source = .ok target ∧
      target.id = source.id ∧ target.parent = source.parent := by
  obtain ⟨source, sourceMember, decoded⟩ := mapM_output_origin mapped member
  exact ⟨source, sourceMember, decoded, metadata source sourceMember target decoded⟩

private theorem fold_max_source_bounds {α : Type} (value : α → Int)
    (xs : List α) (initial : Int) :
    initial ≤ xs.foldl (fun acc x => max acc (value x)) initial ∧
      ∀ x ∈ xs, value x ≤ xs.foldl (fun acc x => max acc (value x)) initial := by
  induction xs generalizing initial with
  | nil => exact ⟨Int.le_refl _, by simp⟩
  | cons first rest ih =>
    obtain ⟨accumulator, members⟩ := ih (max initial (value first))
    constructor
    · exact Int.le_trans (Int.le_max_left _ _) accumulator
    · intro x member
      rcases List.mem_cons.mp member with rfl | member
      · exact Int.le_trans (Int.le_max_right _ _) accumulator
      · exact members x member

theorem pitch_horizontal_source_bounds (p : GeometryParams) (nodes : List Node)
    (edgeLabels : List Size) :
    p.pitchX ≤ (pitch p nodes edgeLabels).x ∧
      p.iconW + p.gutter ≤ (pitch p nodes edgeLabels).x := by
  unfold pitch
  dsimp only
  split
  · constructor
    · exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
    · exact Int.le_trans
        (Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _))
        (Int.le_max_left _ _)
  · constructor
    · exact Int.le_max_left _ _
    · exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)

theorem pitch_vertical_source_budget (p : GeometryParams) (nodes : List Node)
    (edgeLabels : List Size) (node : Node) (member : node ∈ nodes)
    (labelNonnegative : 0 ≤ node.label.h)
    (thicknessNonnegative : 0 ≤ p.thickness) (gutterNonnegative : 0 ≤ p.gutter) :
    0 ≤ (pitch p nodes edgeLabels).top ∧
      p.pitchY ≤ (pitch p nodes edgeLabels).y ∧
      (pitch p nodes edgeLabels).top + p.iconH + node.label.h +
        (if node.label.h > 0 then p.thickness else 0) ≤
          (pitch p nodes edgeLabels).y := by
  let maximum := nodes.foldl (fun acc n => max acc n.label.h) 0
  let edgeMaximum := edgeLabels.foldl (fun acc s => max acc s.h) 0
  let top0 := max 0 (Int.fdiv (p.pitchY - p.iconH) 2)
  let top := if edgeMaximum > 0 then
    max top0 (p.thickness + p.labelGap + edgeMaximum) else top0
  let tail := if maximum > 0 then maximum + p.thickness +
    max p.gutter (max 0 (p.pitchY - top0 - p.iconH - p.lineHeight))
    else max 0 (p.pitchY - top0 - p.iconH)
  have labelBound : node.label.h ≤ maximum :=
    (fold_max_source_bounds (fun n : Node => n.label.h) nodes 0).2 node member
  have top0Nonnegative : 0 ≤ top0 := Int.le_max_left _ _
  have topNonnegative : 0 ≤ top := by
    dsimp only [top]
    split
    · exact Int.le_trans top0Nonnegative (Int.le_max_left _ _)
    · exact top0Nonnegative
  have tailBudget :
      node.label.h + (if node.label.h > 0 then p.thickness else 0) ≤ tail := by
    dsimp only [tail]
    split
    · have reserve : 0 ≤ max p.gutter
          (max 0 (p.pitchY - top0 - p.iconH - p.lineHeight)) :=
        Int.le_trans gutterNonnegative (Int.le_max_left _ _)
      split <;> omega
    · have reserve : 0 ≤ max 0 (p.pitchY - top0 - p.iconH) := Int.le_max_left _ _
      split <;> omega
  change 0 ≤ top ∧ p.pitchY ≤ max p.pitchY (top + p.iconH + tail) ∧
    top + p.iconH + node.label.h +
      (if node.label.h > 0 then p.thickness else 0) ≤
        max p.pitchY (top + p.iconH + tail)
  refine ⟨topNonnegative, Int.le_max_left _ _, ?_⟩
  have upper := Int.le_max_right p.pitchY (top + p.iconH + tail)
  omega

theorem geometry_ordinary_box_inside_native_tile
    (p : GeometryParams) (nodes : List Node) (edgeLabels : List Size)
    (groups : List Group) (resolved : Resolved) (n : Nat) (bound : n < nodes.length)
    (ordinary : (nodes.getD n default).junction = false)
    (iconWidth : (nodes.getD n default).icon.w = p.iconW)
    (iconHeight : (nodes.getD n default).icon.h = p.iconH)
    (labelNonnegative : 0 ≤ (nodes.getD n default).label.h)
    (thicknessNonnegative : 0 ≤ p.thickness) (gutterNonnegative : 0 ≤ p.gutter) :
    let nativePitch := pitch p nodes edgeLabels
    let position := resolved.nodes.getD n default
    (⟨position.x * nativePitch.x, position.y * nativePitch.y,
      (position.x + 1) * nativePitch.x,
      (position.y + 1) * nativePitch.y⟩ : Span).contains
        ((geometry p nativePitch nodes groups resolved).boxes.getD n default) := by
  have member : nodes.getD n default ∈ nodes := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
      Option.getD_some] using List.getElem_mem bound
  have horizontal := pitch_horizontal_source_bounds p nodes edgeLabels
  have vertical := pitch_vertical_source_budget p nodes edgeLabels
    (nodes.getD n default) member labelNonnegative thicknessNonnegative gutterNonnegative
  have difference : 0 ≤ (pitch p nodes edgeLabels).x - p.iconW := by omega
  have centered :
      0 ≤ Int.fdiv ((pitch p nodes edgeLabels).x - p.iconW) 2 ∧
      Int.fdiv ((pitch p nodes edgeLabels).x - p.iconW) 2 ≤
        (pitch p nodes edgeLabels).x - p.iconW := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    constructor
    · exact Int.ediv_nonneg difference (by decide)
    · apply Int.ediv_le_of_le_mul (by decide : (0 : Int) < 2)
      omega
  dsimp only
  rw [geometry_box_at p (pitch p nodes edgeLabels) nodes groups resolved n bound,
    geometry_icon_at p (pitch p nodes edgeLabels) nodes groups resolved n bound]
  simp only [ordinary, Bool.false_eq_true, ↓reduceIte, iconWidth, iconHeight, sized,
    Span.contains]
  constructor
  · omega
  constructor
  · simp only [Int.add_mul]
    omega
  constructor
  · omega
  · simp only [Int.add_mul]
    omega

theorem architecture_loaded_pixel_constants (profile : Profile) :
    0 < LayoutConst.architecture_pitch_x.get profile ∧
    0 < LayoutConst.architecture_pitch_y.get profile ∧
    0 < LayoutConst.architecture_junction_size.get profile ∧
    LayoutConst.architecture_junction_size.get profile ≤
      LayoutConst.architecture_pitch_x.get profile ∧
    LayoutConst.architecture_junction_size.get profile ≤
      LayoutConst.architecture_pitch_y.get profile ∧
    0 ≤ LayoutConst.architecture_line_thickness.get profile := by
  cases profile <;> decide

theorem geometry_box_horizontal_inside_native_tile
    (p : GeometryParams) (nodes : List Node) (edgeLabels : List Size)
    (groups : List Group) (resolved : Resolved) (n : Nat) (bound : n < nodes.length)
    (sourceWidth : (nodes.getD n default).icon.w ≤
      max p.pitchX (p.iconW + p.gutter)) :
    let nativePitch := pitch p nodes edgeLabels
    let position := resolved.nodes.getD n default
    let box := (geometry p nativePitch nodes groups resolved).boxes.getD n default
    position.x * nativePitch.x ≤ box.x0 ∧
      box.x1 ≤ (position.x + 1) * nativePitch.x := by
  have horizontal := pitch_horizontal_source_bounds p nodes edgeLabels
  have iconBound : (nodes.getD n default).icon.w ≤ (pitch p nodes edgeLabels).x := by
    have upper : max p.pitchX (p.iconW + p.gutter) ≤ (pitch p nodes edgeLabels).x :=
      Int.max_le.mpr horizontal
    exact Int.le_trans sourceWidth upper
  have difference :
      0 ≤ (pitch p nodes edgeLabels).x - (nodes.getD n default).icon.w := by omega
  have centered :
      0 ≤ Int.fdiv ((pitch p nodes edgeLabels).x - (nodes.getD n default).icon.w) 2 ∧
      Int.fdiv ((pitch p nodes edgeLabels).x - (nodes.getD n default).icon.w) 2 ≤
        (pitch p nodes edgeLabels).x - (nodes.getD n default).icon.w := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    constructor
    · exact Int.ediv_nonneg difference (by decide)
    · apply Int.ediv_le_of_le_mul (by decide : (0 : Int) < 2)
      omega
  dsimp only
  rw [geometry_box_at p (pitch p nodes edgeLabels) nodes groups resolved n bound,
    geometry_icon_at p (pitch p nodes edgeLabels) nodes groups resolved n bound]
  simp only [sized]
  constructor
  · omega
  · simp only [Int.add_mul]
    omega

theorem decoded_icon_source_bounds (profile : Profile) (iw ih gutter : Int)
    (junction : Bool) (widthPositive : 0 < iw) (heightPositive : 0 < ih)
    (gutterNonnegative : 0 ≤ gutter) :
    let size := if junction then LayoutConst.architecture_junction_size.get profile else iw
    let height := if junction then size else ih
    0 < size ∧ 0 < height ∧
      size ≤ max (LayoutConst.architecture_pitch_x.get profile) (iw + gutter) := by
  have constants := architecture_loaded_pixel_constants profile
  cases junction with
  | false =>
    dsimp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨widthPositive, heightPositive, ?_⟩
    exact Int.le_trans (by omega : iw ≤ iw + gutter) (Int.le_max_right _ _)
  | true =>
    dsimp only [↓reduceIte]
    exact ⟨constants.2.2.1, constants.2.2.1,
      Int.le_trans constants.2.2.2.1 (Int.le_max_left _ _)⟩

theorem configured_frame_padding_nonnegative (profile : Profile) (px : Int)
    (sourceNonnegative : 0 ≤ px) :
    0 ≤ (if profile == .cell then Int.fdiv (2 * px + 20) 40 else px * 64) := by
  cases profile with
  | vector =>
    change 0 ≤ px * 64
    exact Int.mul_nonneg sourceNonnegative (by decide)
  | cell =>
    change 0 ≤ Int.fdiv (2 * px + 20) 40
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    exact Int.ediv_nonneg (by omega) (by decide)

end Elegant.Grid.Architecture


