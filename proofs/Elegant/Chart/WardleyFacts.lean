import Elegant.Kinds.Wardley

set_option autoImplicit false

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Elegant.Chart.Wardley

/-- The exact clamped projection used before pipelines are placed. -/
theorem wardley_points_in_plot (plot : Rect) (x y : Int)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) :
    plot.x ≤ (project plot x y).x ∧ (project plot x y).x ≤ plot.x + plot.w ∧
    plot.y ≤ (project plot x y).y ∧ (project plot x y).y ≤ plot.y + plot.h := by
  have hx := clamp_between x 0 100000
  have hy := clamp_between y 0 100000
  have hx0 : 0 ≤ clamp x 0 100000 := by omega
  have hx1 : clamp x 0 100000 ≤ 100000 := by omega
  have hy0 : 0 ≤ clamp y 0 100000 := by omega
  have hy1 : clamp y 0 100000 ≤ 100000 := by omega
  have px := fdiv_scaled_between (clamp x 0 100000) 100000 plot.w (by decide) hx0 hx1
  have py := fdiv_scaled_between (clamp y 0 100000) 100000 plot.h (by decide) hy0 hy1
  simp only [project]
  omega

/-- Canonical Wardley links attach to the centre-point boxes at both ends. -/
theorem linkPoints_endpoints (g : Geometry) (source target : Nat) :
    (linkPoints g source target).head? = some ((g.positions[source]?).getD ⟨0, 0⟩) ∧
    (linkPoints g source target).getLast? = some ((g.positions[target]?).getD ⟨0, 0⟩) := by
  simp [linkPoints]

theorem wardley_links_join_nodes (g : Geometry) (model : ModelRoute) (route : Route)
    (h : routeGeometry g model = .ok route) :
    ∃ source target,
      endpoint g model.fromId = .ok source ∧ endpoint g model.toId = .ok target ∧
      route.points.head? = some source ∧ route.points.getLast? = some target := by
  cases hs : endpoint g model.fromId with
  | error e => simp [routeGeometry, hs, Bind.bind, Except.bind] at h
  | ok source =>
      cases ht : endpoint g model.toId with
      | error e => simp [routeGeometry, hs, ht, Bind.bind, Except.bind] at h
      | ok target =>
          cases hc : XY.checkMagnitude [source.x, source.y, target.x, target.y] with
          | error e => simp [routeGeometry, hs, ht, hc, Bind.bind, Except.bind] at h
          | ok value =>
              cases value
              simp [routeGeometry, hs, ht, hc, Bind.bind, Except.bind] at h
              cases h
              exact ⟨source, target, rfl, rfl, rfl, rfl⟩

/-- Both ends of an executed route come from canonical declarations. In particular,
numeric suffix parsing cannot turn an undeclared alias into a route endpoint. -/
theorem wardley_route_endpoint_declarations (c : GeometryConstants) (input : Input)
    (model : ModelRoute) (route : Route)
    (h : routeGeometry (arrange c input) model = .ok route) :
    ∃ source target,
      route.points.head? = some source ∧ route.points.getLast? = some target ∧
      ((∃ entry ∈ (input.nodes.zip (arrange c input).positions).zipIdx,
          model.fromId = "n" ++ toString entry.2 ∧ source = entry.1.2) ∨
        (∃ entry ∈ (arrange c input).ghosts.zipIdx,
          model.fromId = "tg" ++ toString entry.2 ∧ source = entry.1)) ∧
      ((∃ entry ∈ (input.nodes.zip (arrange c input).positions).zipIdx,
          model.toId = "n" ++ toString entry.2 ∧ target = entry.1.2) ∨
        (∃ entry ∈ (arrange c input).ghosts.zipIdx,
          model.toId = "tg" ++ toString entry.2 ∧ target = entry.1)) := by
  obtain ⟨source, target, hs, ht, hfirst, hlast⟩ :=
    wardley_links_join_nodes (arrange c input) model route h
  exact ⟨source, target, hfirst, hlast,
    endpoint_declaration c input model.fromId source hs,
    endpoint_declaration c input model.toId target ht⟩

/-- Point boxes make the canonical centre attachment a boundary attachment. -/
theorem nodeRect_boundary (p : Point) :
    Validator.onBoundary p (nodeRect p) := by
  simp [Validator.onBoundary, nodeRect]

theorem clampPlot_in_plot (plot : Rect) (p : Point)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) :
    plot.x ≤ (clampPlot plot p).x ∧ (clampPlot plot p).x ≤ plot.x + plot.w ∧
    plot.y ≤ (clampPlot plot p).y ∧ (clampPlot plot p).y ≤ plot.y + plot.h := by
  have hx := clamp_between p.x plot.x (plot.x + plot.w)
  have hy := clamp_between p.y plot.y (plot.y + plot.h)
  simp only [clampPlot]
  omega

theorem clipPlot_inside (plot r : Rect)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h)
    (hx : r.x ≤ plot.x + plot.w) (hy : r.y ≤ plot.y + plot.h) :
    plot.Contained (clipPlot plot r) := by
  simp only [clipPlot, Rect.Contained]
  omega

theorem fitPlot_inside (plot r : Rect)
    (hw : r.w ≤ plot.w) (hh : r.h ≤ plot.h) :
    plot.Contained (fitPlot plot r) := by
  have hx := clamp_between r.x plot.x (max (plot.x + plot.w - r.w) plot.x)
  have hy := clamp_between r.y plot.y (max (plot.y + plot.h - r.h) plot.y)
  simp only [fitPlot, Rect.Contained]
  omega

theorem projected_node_inside (plot : Rect) (x y : Int)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) :
    plot.Contained (nodeRect (project plot x y)) := by
  have h := wardley_points_in_plot plot x y hw hh
  simpa [Rect.Contained, nodeRect] using h

theorem clamped_node_inside (plot : Rect) (p : Point)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) :
    plot.Contained (nodeRect (clampPlot plot p)) := by
  have h := clampPlot_in_plot plot p hw hh
  simpa [Rect.Contained, nodeRect] using h

theorem pipeline_parent_inside (c : GeometryConstants) (plot : Rect)
    (base : List Point) (pipeline : Pipeline)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) :
    plot.Contained (nodeRect (pipelineGeometry c plot base pipeline).2) := by
  unfold pipelineGeometry
  exact clamped_node_inside plot _ hw hh


private def extendBounds (base : List Point) (bounds : Point × Point) (i : Nat) :
    Point × Point :=
  let q := (base[i]?).getD ⟨0, 0⟩
  (⟨min bounds.1.x q.x, min bounds.1.y q.y⟩,
   ⟨max bounds.2.x q.x, max bounds.2.y q.y⟩)

private def BoundsPoint (bounds : Point × Point) (p : Point) : Prop :=
  bounds.1.x ≤ p.x ∧ p.x ≤ bounds.2.x ∧ bounds.1.y ≤ p.y ∧ p.y ≤ bounds.2.y

private theorem extendBounds_preserves (base : List Point) (bounds : Point × Point)
    (i : Nat) (p : Point) (h : BoundsPoint bounds p) :
    BoundsPoint (extendBounds base bounds i) p := by
  simp only [extendBounds, BoundsPoint] at *
  omega

private theorem extendBounds_contains (base : List Point) (bounds : Point × Point) (i : Nat) :
    BoundsPoint (extendBounds base bounds i) ((base[i]?).getD ⟨0, 0⟩) := by
  simp only [extendBounds, BoundsPoint]
  omega

private theorem fold_bounds_preserves (base : List Point) (indices : List Nat)
    (bounds : Point × Point) (p : Point) (h : BoundsPoint bounds p) :
    BoundsPoint (indices.foldl (extendBounds base) bounds) p := by
  induction indices generalizing bounds with
  | nil => exact h
  | cons i rest ih =>
      exact ih (extendBounds base bounds i) (extendBounds_preserves base bounds i p h)

private theorem fold_bounds_contains (base : List Point) (indices : List Nat)
    (bounds : Point × Point) (i : Nat) (hi : i ∈ indices) :
    BoundsPoint (indices.foldl (extendBounds base) bounds) ((base[i]?).getD ⟨0, 0⟩) := by
  induction indices generalizing bounds with
  | nil => simp at hi
  | cons j rest ih =>
      rcases List.mem_cons.mp hi with rfl | hi
      · exact fold_bounds_preserves base rest (extendBounds base bounds i) _
          (extendBounds_contains base bounds i)
      · exact ih (extendBounds base bounds j) hi

theorem pipeline_frame_contains_base_child (c : GeometryConstants) (plot : Rect)
    (base : List Point) (pipeline : Pipeline) (i : Nat)
    (hi : i ∈ pipeline.children)
    (hplot : plot.Contained (nodeRect ((base[i]?).getD ⟨0, 0⟩)))
    (hpad : 0 ≤ c.pipelinePad) (hheight : 0 ≤ c.pipelineHeight)
    (hedge : 0 ≤ c.edge) :
    (pipelineGeometry c plot base pipeline).1.Contained
      (nodeRect ((base[i]?).getD ⟨0, 0⟩)) := by
  cases hc : pipeline.children with
  | nil => simp [hc] at hi
  | cons first rest =>
      let p := (base[first]?).getD ⟨0, 0⟩
      have hp : BoundsPoint (rest.foldl (extendBounds base) (p, p))
          ((base[i]?).getD ⟨0, 0⟩) := by
        rw [hc] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact fold_bounds_preserves base rest (p, p) p (by simp [BoundsPoint])
        · exact fold_bounds_contains base rest (p, p) i hi
      have half := fdiv_mono (D := 2) (t := 0) (t' := c.pipelineHeight) (by decide) hheight
      change 0 ≤ Int.fdiv c.pipelineHeight 2 at half
      simp only [pipelineGeometry, hc, List.headD, List.drop_succ_cons, List.drop_zero]
      change (clipPlot plot _).Contained _
      simp only [clipPlot, nodeRect, Rect.Contained] at *
      unfold BoundsPoint at hp
      unfold extendBounds at hp
      dsimp only [p] at hp
      omega

theorem pipeline_frame_inside_plot (c : GeometryConstants) (plot : Rect)
    (base : List Point) (pipeline : Pipeline)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h)
    (hfirst : plot.Contained
      (nodeRect ((base[pipeline.children.headD 0]?).getD ⟨0, 0⟩)))
    (hpad : 0 ≤ c.pipelinePad) (hheight : 0 ≤ c.pipelineHeight) :
    plot.Contained (pipelineGeometry c plot base pipeline).1 := by
  let first := (base[pipeline.children.headD 0]?).getD ⟨0, 0⟩
  let b := (pipeline.children.drop 1).foldl (extendBounds base) (first, first)
  have hbound : BoundsPoint b first :=
    fold_bounds_preserves base _ (first, first) first (by simp [BoundsPoint])
  have hhalf := fdiv_mono (D := 2) (t := 0) (t' := c.pipelineHeight)
    (by decide) hheight
  change 0 ≤ Int.fdiv c.pipelineHeight 2 at hhalf
  change plot.Contained (clipPlot plot
    ⟨b.1.x - c.pipelinePad, b.1.y - Int.fdiv c.pipelineHeight 2,
      b.2.x - b.1.x + 2 * c.pipelinePad + c.edge,
      b.2.y - b.1.y + 2 * Int.fdiv c.pipelineHeight 2 + c.edge⟩)
  apply clipPlot_inside plot _ hw hh
  all_goals
    simp only [BoundsPoint, nodeRect, Rect.Contained, Int.add_zero] at hbound hfirst
    dsimp only at hfirst ⊢
    dsimp only [first] at hbound
    omega

theorem projected_pipeline_frame_inside_plot (c : GeometryConstants) (plot : Rect)
    (nodes : List Node) (pipeline : Pipeline)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h)
    (hindex : pipeline.children.headD 0 < nodes.length)
    (hpad : 0 ≤ c.pipelinePad) (hheight : 0 ≤ c.pipelineHeight) :
    plot.Contained
      (pipelineGeometry c plot (nodes.map (fun n => project plot n.x n.y)) pipeline).1 := by
  apply pipeline_frame_inside_plot c plot _ pipeline hw hh _ hpad hheight
  have hnode : nodes[pipeline.children.headD 0]? =
      some nodes[pipeline.children.headD 0] :=
    List.getElem?_eq_some_iff.mpr ⟨hindex, rfl⟩
  simp only [List.getElem?_map, hnode, Option.map_some, Option.getD_some]
  exact projected_node_inside plot _ _ hw hh

theorem arranged_frames_inside_plot (c : GeometryConstants) (input : Input)
    (hw : 0 ≤ (arrange c input).plot.w) (hh : 0 ≤ (arrange c input).plot.h)
    (hindex : ∀ pipeline ∈ input.pipelines,
      pipeline.children.headD 0 < input.nodes.length)
    (hpad : 0 ≤ c.pipelinePad) (hheight : 0 ≤ c.pipelineHeight) :
    ∀ frame ∈ (arrange c input).frames, (arrange c input).plot.Contained frame := by
  intro frame hframe
  change frame ∈ (input.pipelines.map
    (pipelineGeometry c (arrange c input).plot (arrange c input).base)).map Prod.fst at hframe
  obtain ⟨pair, hpair, hframe⟩ := List.mem_map.mp hframe
  obtain ⟨pipeline, hpipeline, hpair⟩ := List.mem_map.mp hpair
  rw [← hframe, ← hpair]
  exact projected_pipeline_frame_inside_plot c (arrange c input).plot input.nodes
    pipeline hw hh (hindex pipeline hpipeline) hpad hheight
private theorem getElem?_set_other {α : Type} (xs : List α) (i j : Nat) (value : α)
    (hne : i ≠ j) : (xs.set i value)[j]? = xs[j]? := by
  induction xs generalizing i j with
  | nil => simp
  | cons head rest ih =>
      cases i <;> cases j <;> simp_all [List.set]

private theorem fold_set_other (pairs : List (Pipeline × (Rect × Point))) (ps : List Point)
    (i : Nat) (h : ∀ pair ∈ pairs, pair.1.parent ≠ i) :
    (pairs.foldl (fun points pair => points.set pair.1.parent pair.2.2) ps)[i]? = ps[i]? := by
  induction pairs generalizing ps with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun p hp => h p (List.mem_cons_of_mem pair hp))]
      exact getElem?_set_other ps pair.1.parent i pair.2.2 (h pair (by simp))

theorem arranged_position_unchanged (c : GeometryConstants) (input : Input) (i : Nat)
    (h : ∀ pipeline ∈ input.pipelines, pipeline.parent ≠ i) :
    (arrange c input).positions[i]? = (arrange c input).base[i]? := by
  unfold arrange
  apply fold_set_other
  intro pair hp
  exact h pair.1 (List.of_mem_zip hp).1


private theorem set_preserves {α : Type} (P : α → Prop)
    (ps : List α) (index : Nat) (p : α)
    (h : ∀ q ∈ ps, P q) (hp : P p) : ∀ q ∈ ps.set index p, P q := by
  induction ps generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero =>
          intro q hq
          simp only [List.set, List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hp
          · exact h q (List.mem_cons_of_mem head hq)
      | succ index =>
          intro q hq
          simp only [List.set, List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact h q (by simp)
          · exact ih index (fun q hq => h q (List.mem_cons_of_mem head hq)) q hq

private theorem fold_set_preserves (plot : Rect) (pairs : List (Pipeline × (Rect × Point)))
    (ps : List Point)
    (hs : ∀ p ∈ ps, plot.Contained (nodeRect p))
    (hp : ∀ pair ∈ pairs, plot.Contained (nodeRect pair.2.2)) :
    ∀ p ∈ pairs.foldl (fun ps pair => ps.set pair.1.parent pair.2.2) ps,
      plot.Contained (nodeRect p) := by
  induction pairs generalizing ps with
  | nil => exact hs
  | cons pair rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact set_preserves _ ps pair.1.parent pair.2.2 hs (hp pair (by simp))
      · intro q hq
        exact hp q (List.mem_cons_of_mem pair hq)

theorem arranged_positions_inside (c : GeometryConstants) (input : Input)
    (hw : 0 ≤ (arrange c input).plot.w) (hh : 0 ≤ (arrange c input).plot.h) :
    ∀ p ∈ (arrange c input).positions, (arrange c input).plot.Contained (nodeRect p) := by
  let plot := (arrange c input).plot
  let base := input.nodes.map (fun n => project plot n.x n.y)
  have hs : ∀ p ∈ base, plot.Contained (nodeRect p) := by
    intro p hp
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hp
    exact projected_node_inside plot n.x n.y hw hh
  have hp : ∀ pair ∈ input.pipelines.zip (input.pipelines.map (pipelineGeometry c plot base)),
      plot.Contained (nodeRect pair.2.2) := by
    intro pair hpair
    obtain ⟨pipeline, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hpair).2
    rw [← heq]
    exact pipeline_parent_inside c plot base pipeline hw hh
  exact fold_set_preserves plot _ base hs hp

theorem endpoint_inside_plot (c : GeometryConstants) (input : Input)
    (id : String) (point : Point)
    (hw : 0 ≤ (arrange c input).plot.w) (hh : 0 ≤ (arrange c input).plot.h)
    (h : endpoint (arrange c input) id = .ok point) :
    (arrange c input).plot.Contained (nodeRect point) := by
  rcases endpoint_declaration c input id point h with hn | hg
  · obtain ⟨entry, he, _, hp⟩ := hn
    rw [hp]
    exact arranged_positions_inside c input hw hh entry.1.2
      (List.of_mem_zip (List.fst_mem_of_mem_zipIdx he)).2
  · obtain ⟨entry, he, _, hp⟩ := hg
    rw [hp]
    have hmem := List.fst_mem_of_mem_zipIdx he
    obtain ⟨trend, _, hpoint⟩ := List.mem_map.mp hmem
    rw [← hpoint]
    exact projected_node_inside (arrange c input).plot trend.x trend.y hw hh

theorem routeGeometry_points_inside_plot (c : GeometryConstants) (input : Input)
    (model : ModelRoute) (route : Route)
    (hw : 0 ≤ (arrange c input).plot.w) (hh : 0 ≤ (arrange c input).plot.h)
    (h : routeGeometry (arrange c input) model = .ok route) :
    ∀ point ∈ route.points, (arrange c input).plot.Contained (nodeRect point) := by
  cases ha : endpoint (arrange c input) model.fromId with
  | error e => simp [routeGeometry, ha, Bind.bind, Except.bind] at h
  | ok a =>
      cases hb : endpoint (arrange c input) model.toId with
      | error e => simp [routeGeometry, ha, hb, Bind.bind, Except.bind] at h
      | ok b =>
          cases hc : XY.checkMagnitude [a.x, a.y, b.x, b.y] with
          | error e => simp [routeGeometry, ha, hb, hc, Bind.bind, Except.bind] at h
          | ok value =>
              cases value
              simp [routeGeometry, ha, hb, hc, Bind.bind, Except.bind] at h
              cases h
              intro point hp
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl
              · exact endpoint_inside_plot c input model.fromId point hw hh ha
              · exact endpoint_inside_plot c input model.toId point hw hh hb

theorem fitCanvas_nonnegative (canvas : Size) (r : Rect) :
    0 ≤ (fitCanvas canvas r).x ∧ 0 ≤ (fitCanvas canvas r).y := by
  have hx := clamp_between r.x 0 (max (canvas.w - r.w) 0)
  have hy := clamp_between r.y 0 (max (canvas.h - r.h) 0)
  simp only [fitCanvas]
  omega

theorem fitCanvas_sizes (canvas : Size) (r : Rect) :
    (fitCanvas canvas r).w = r.w ∧ (fitCanvas canvas r).h = r.h := by
  exact ⟨rfl, rfl⟩

theorem all_nonexclusive_clauses (d : LayoutDump)
    (h : ∀ b ∈ d.boxes, b.exclusive = false ∧ b.role = "node") :
    Validator.C2 d ∧ Validator.C6 d ∧ Validator.C7 d ∧ Validator.C8 d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb c hc _ he
    have hf := (h b hb).1
    simp [hf] at he
  · intro r hr b hb he
    have hf := (h b hb).1
    simp [hf] at he
  · intro l hl b hb he
    have hf := (h b hb).1
    simp [hf] at he
  · constructor
    · intro b hb hg
      have hf := (h b hb).2
      simp [hf] at hg
    · intro b hb hg
      have hf := (h b hb).2
      simp [hf] at hg


theorem orthogonal_metadata_clause (d : LayoutDump)
    (h : ∀ r ∈ d.routes, r.orthogonal = false) : Validator.C4 d := by
  intro r hr he
  have hf := h r hr
  simp [hf] at he

theorem point_box_boundary_iff (p q : Point) :
    Validator.onBoundary p (nodeRect q) ↔ p = q := by
  constructor
  · intro h
    simp only [Validator.onBoundary, nodeRect] at h
    cases p; cases q; simp_all; omega
  · intro h
    subst p
    exact nodeRect_boundary q

theorem plot_canvas_inside (c : GeometryConstants) (input : Input)
    (hx : 0 ≤ c.padX) (hy : 0 ≤ c.padY) :
    (Validator.canvasRect {
      canvas := (arrange c input).canvas
      boxes := [], routes := [], labels := [] }).Contained (arrange c input).plot := by
  simp only [Validator.canvasRect, arrange, Rect.Contained]
  omega

theorem point_rect_disjoint (p : Point) (r : Rect) : Disjoint (nodeRect p) r := by
  simp only [Disjoint, Rect.meetsInterior, nodeRect]
  omega

theorem point_rect_containment_iff (plot : Rect) (p : Point) :
    plot.Contained (nodeRect p) ↔
      plot.x ≤ p.x ∧ p.x ≤ plot.x + plot.w ∧
      plot.y ≤ p.y ∧ p.y ≤ plot.y + plot.h := by
  simp [Rect.Contained, nodeRect]

theorem grown_canvas_keeps_plot (canvas grown : Size) (plot : Rect)
    (hw : canvas.w ≤ grown.w) (hh : canvas.h ≤ grown.h)
    (h : (Validator.canvasRect { canvas, boxes := [], routes := [], labels := [] }).Contained plot) :
    (Validator.canvasRect { canvas := grown, boxes := [], routes := [], labels := [] }).Contained plot := by
  simp only [Validator.canvasRect, Rect.Contained] at *
  omega

theorem hardConstraints_of_wardley_clauses (d : LayoutDump)
    (flags : ∀ b ∈ d.boxes, b.exclusive = false ∧ b.role = "node")
    (orthogonal : ∀ r ∈ d.routes, r.orthogonal = false)
    (canvas : Validator.C1 d) (parent : Validator.C3 d) (ports : Validator.C5 d) :
    HardConstraints d := by
  obtain ⟨siblings, routes, labels, frames⟩ := all_nonexclusive_clauses d flags
  exact ⟨canvas, siblings, parent, orthogonal_metadata_clause d orthogonal,
    ports, routes, labels, frames⟩

theorem grow_labels_monotone (labels : List PlacedLabel) (canvas : Size) :
    let grown := labels.foldl (fun size l => if l.shown then
      ⟨max size.w (l.rect.x + l.rect.w), max size.h (l.rect.y + l.rect.h)⟩ else size) canvas
    canvas.w ≤ grown.w ∧ canvas.h ≤ grown.h := by
  induction labels generalizing canvas with
  | nil => exact ⟨Int.le_refl _, Int.le_refl _⟩
  | cons l rest ih =>
      simp only [List.foldl_cons]
      cases hs : l.shown with
      | false => simpa [hs] using ih canvas
      | true =>
          simp only [ite_true]
          have h := ih ⟨max canvas.w (l.rect.x + l.rect.w),
            max canvas.h (l.rect.y + l.rect.h)⟩
          exact ⟨Int.le_trans (Int.le_max_left _ _) h.1,
            Int.le_trans (Int.le_max_left _ _) h.2⟩

theorem arrange_plot_nonnegative (c : GeometryConstants) (input : Input)
    (hwidth : 0 ≤ c.arrowWidth + c.edge)
    (hheight : 0 ≤ 2 * (c.arrowShaft + c.arrowHead) + c.edge) :
    0 ≤ (arrange c input).plot.w ∧ 0 ≤ (arrange c input).plot.h := by
  simp only [arrange]
  omega

theorem arrange_canvas_nonnegative (c : GeometryConstants) (input : Input)
    (hx : 0 ≤ c.padX) (hy : 0 ≤ c.padY)
    (hwidth : 0 ≤ c.arrowWidth + c.edge)
    (hheight : 0 ≤ 2 * (c.arrowShaft + c.arrowHead) + c.edge) :
    0 ≤ (arrange c input).canvas.w ∧ 0 ≤ (arrange c input).canvas.h := by
  simp only [arrange]
  omega

theorem clampPlot_idempotent (plot : Rect) (p : Point)
    (_hw : 0 ≤ plot.w) (_hh : 0 ≤ plot.h) :
    clampPlot plot (clampPlot plot p) = clampPlot plot p := by
  have hx := clamp_between p.x plot.x (plot.x + plot.w)
  have hy := clamp_between p.y plot.y (plot.y + plot.h)
  have ex : clamp (clamp p.x plot.x (plot.x + plot.w)) plot.x (plot.x + plot.w) =
      clamp p.x plot.x (plot.x + plot.w) := by
    apply clamp_of_between <;> omega
  have ey : clamp (clamp p.y plot.y (plot.y + plot.h)) plot.y (plot.y + plot.h) =
      clamp p.y plot.y (plot.y + plot.h) := by
    apply clamp_of_between <;> omega
  simp only [clampPlot, ex, ey]

theorem centre_link_ports (a b : Point) :
    ([a, b] : List Point).head? = some a ∧
    ([a, b] : List Point).getLast? = some b ∧
    Validator.onBoundary a (nodeRect a) ∧ Validator.onBoundary b (nodeRect b) := by
  exact ⟨rfl, rfl, nodeRect_boundary a, nodeRect_boundary b⟩


theorem adapter_success_consistent (m : Model) (s : Scene)
    (h : Elegant.Kinds.Wardley.scene m = .ok s) :
    ∃ input, Elegant.Kinds.Wardley.decode m = .ok input ∧
      Elegant.Kinds.Wardley.modelConsistent input m = true ∧
      Elegant.Kinds.Wardley.metadataConsistent m = true ∧
      Elegant.Kinds.Wardley.noSelfMembership input = true ∧
      Elegant.Kinds.Wardley.parentsMarked input = true ∧
      layoutWith (constants m) input m = .ok s := by
  unfold Elegant.Kinds.Wardley.scene at h
  cases hd : Elegant.Kinds.Wardley.decode m with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok input =>
      cases hc : Elegant.Kinds.Wardley.modelConsistent input m with
      | false => simp [hd, hc, Bind.bind, Except.bind] at h
      | true =>
          cases hm : Elegant.Kinds.Wardley.metadataConsistent m with
          | false => simp [hd, hc, hm, Bind.bind, Except.bind] at h
          | true =>
              cases hn : Elegant.Kinds.Wardley.noSelfMembership input with
              | false => simp [hd, hc, hm, hn, Bind.bind, Except.bind] at h
              | true =>
                  cases hp : Elegant.Kinds.Wardley.parentsMarked input with
                  | false => simp [hd, hc, hm, hn, hp, Bind.bind, Except.bind] at h
                  | true =>
                      refine ⟨input, rfl, hc, rfl, hn, hp, ?_⟩
                      simpa [hd, hc, hm, hn, hp, Bind.bind, Except.bind] using h

theorem unmarked_node_not_pipeline_parent (input : Input) (i : Nat) (node : Node)
    (hmarked : Elegant.Kinds.Wardley.parentsMarked input = true)
    (hnode : input.nodes[i]? = some node) (hflag : node.flags &&& 4 = 0) :
    ∀ pipeline ∈ input.pipelines, pipeline.parent ≠ i := by
  intro pipeline hp heq
  unfold Elegant.Kinds.Wardley.parentsMarked at hmarked
  have h := List.all_eq_true.mp hmarked pipeline hp
  simp [heq, hnode, hflag] at h

theorem unmarked_node_position (c : GeometryConstants) (input : Input) (i : Nat) (node : Node)
    (hmarked : Elegant.Kinds.Wardley.parentsMarked input = true)
    (hnode : input.nodes[i]? = some node) (hflag : node.flags &&& 4 = 0) :
    (arrange c input).positions[i]? = (arrange c input).base[i]? := by
  apply arranged_position_unchanged
  exact unmarked_node_not_pipeline_parent input i node hmarked hnode hflag

theorem layout_success_scene (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    Elegant.Kinds.Wardley.scene m = .ok result.scene ∧ result.budgetExhausted = false := by
  unfold Elegant.Kinds.Wardley.layout at h
  cases hp : Elegant.Kinds.Wardley.annotationParentsValid m with
  | false => simp [hp] at h
  | true =>
    simp [hp] at h
    cases hs : Elegant.Kinds.Wardley.scene m with
    | error e => simp [hs] at h
    | ok s =>
        simp only [hs, Except.ok.injEq] at h
        cases h
        exact ⟨rfl, rfl⟩


theorem metadataConsistent_flags (m : Model)
    (h : Elegant.Kinds.Wardley.metadataConsistent m = true) :
    (∀ b ∈ m.boxes, b.exclusive = false ∧ b.role = .node) ∧
    (∀ r ∈ m.routes, r.orthogonal = false) := by
  unfold Elegant.Kinds.Wardley.metadataConsistent at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hboxes, hroutes⟩, _⟩ := h
  constructor
  · intro b hb
    have hbox := List.all_eq_true.mp hboxes b hb
    simpa using hbox
  · intro r hr
    have hroute := List.all_eq_true.mp hroutes r hr
    simpa using hroute

theorem metadataConsistent_padding (m : Model)
    (h : Elegant.Kinds.Wardley.metadataConsistent m = true) :
    ∀ n, configured m "padding" = some n → 0 ≤ n := by
  unfold Elegant.Kinds.Wardley.metadataConsistent at h
  simp only [Bool.and_eq_true] at h
  have hpadding := h.2
  intro n hn
  simpa [hn] using hpadding

private theorem mapM_preserves {α β : Type} (f : α → Except LayoutError β)
    (P : α → Prop) (Q : β → Prop)
    (hf : ∀ a b, P a → f a = .ok b → Q b)
    (xs : List α) (ys : List β) (hx : ∀ a ∈ xs, P a)
    (h : xs.mapM f = .ok ys) : ∀ b ∈ ys, Q b := by
  induction xs generalizing ys with
  | nil =>
      simp [List.mapM_nil, Pure.pure, Except.pure] at h
      subst ys
      simp
  | cons a rest ih =>
      cases ha : f a with
      | error e => simp [List.mapM_cons, ha, Bind.bind, Except.bind] at h
      | ok b =>
          cases ht : rest.mapM f with
          | error e => simp [List.mapM_cons, ha, ht, Bind.bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, ha, ht, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              subst ys
              intro out hout
              rcases List.mem_cons.mp hout with rfl | hout
              · exact hf a out (hx a (by simp)) ha
              · exact ih tail (fun x hx' => hx x (List.mem_cons_of_mem a hx')) ht out hout

theorem modelConsistent_parent (input : Input) (m : Model) (b expected : ModelBox)
    (h : Elegant.Kinds.Wardley.modelConsistent input m = true)
    (hb : b ∈ m.boxes)
    (he : (Elegant.Kinds.Wardley.expectedBoxes input m).find?
      (fun candidate => candidate.id == b.id) = some expected) :
    b.parent = expected.parent := by
  unfold Elegant.Kinds.Wardley.modelConsistent at h
  have hp := List.all_eq_true.mp h b hb
  simpa [he] using hp

private def boxFunction (g : Geometry) (annotationBox : Rect) (b : ModelBox) :
    Except LayoutError Box := do
  let rect ← boxRect g annotationBox b.id
  XY.checkRect rect
  return ⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩

private def finalCanvas (input : Input) (g : Geometry) (measured : List MeasuredLabel)
    (annotationBox : Rect) (labels : List PlacedLabel) : Size :=
  let grown := labels.foldl (fun size l => if l.shown then
    ⟨max size.w (l.rect.x + l.rect.w), max size.h (l.rect.y + l.rect.h)⟩ else size) g.canvas
  if input.box.isSome && !(boxedAnnotations measured).isEmpty then
    ⟨max grown.w (annotationBox.x + annotationBox.w), max grown.h (annotationBox.y + annotationBox.h)⟩
  else grown

private theorem finalCanvas_ge_base (input : Input) (g : Geometry)
    (measured : List MeasuredLabel) (annotationBox : Rect) (labels : List PlacedLabel) :
    g.canvas.w ≤ (finalCanvas input g measured annotationBox labels).w ∧
      g.canvas.h ≤ (finalCanvas input g measured annotationBox labels).h := by
  have h := grow_labels_monotone labels g.canvas
  unfold finalCanvas
  split <;> simp only <;> omega

private theorem finalCanvas_contains_plot (c : Constants) (input : Input)
    (measured : List MeasuredLabel) (annotationBox : Rect) (labels : List PlacedLabel)
    (hx : 0 ≤ c.geometry.padX) (hy : 0 ≤ c.geometry.padY) :
    (⟨0, 0, (finalCanvas input (arrange c.geometry input) measured annotationBox labels).w,
      (finalCanvas input (arrange c.geometry input) measured annotationBox labels).h⟩ : Rect).Contained
      (arrange c.geometry input).plot := by
  have hplot := plot_canvas_inside c.geometry input hx hy
  have hcanvas := finalCanvas_ge_base input (arrange c.geometry input) measured annotationBox labels
  simp only [Validator.canvasRect, Rect.Contained] at *
  omega

private theorem grow_labels_contains_shown (labels : List PlacedLabel) (canvas : Size)
    (label : PlacedLabel) (hmem : label ∈ labels) (hshown : label.shown = true) :
    label.rect.x + label.rect.w ≤
        (labels.foldl (fun size l => if l.shown then
          ⟨max size.w (l.rect.x + l.rect.w),
            max size.h (l.rect.y + l.rect.h)⟩ else size) canvas).w ∧
      label.rect.y + label.rect.h ≤
        (labels.foldl (fun size l => if l.shown then
          ⟨max size.w (l.rect.x + l.rect.w),
            max size.h (l.rect.y + l.rect.h)⟩ else size) canvas).h := by
  induction labels generalizing canvas with
  | nil => cases hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp only [List.foldl_cons]
        rw [hshown]
        simp only [↓reduceIte]
        have hg := grow_labels_monotone tail
          (⟨max canvas.w (label.rect.x + label.rect.w),
            max canvas.h (label.rect.y + label.rect.h)⟩ : Size)
        exact ⟨Int.le_trans (Int.le_max_right _ _) hg.1,
          Int.le_trans (Int.le_max_right _ _) hg.2⟩
      · simp only [List.foldl_cons]
        exact ih _ htail

theorem finalCanvas_contains_shown_label_extents (input : Input) (g : Geometry)
    (measured : List MeasuredLabel) (annotationBox : Rect) (labels : List PlacedLabel)
    (label : PlacedLabel) (hmem : label ∈ labels) (hshown : label.shown = true) :
    label.rect.x + label.rect.w ≤
        (finalCanvas input g measured annotationBox labels).w ∧
      label.rect.y + label.rect.h ≤
        (finalCanvas input g measured annotationBox labels).h := by
  have hg := grow_labels_contains_shown labels g.canvas label hmem hshown
  unfold finalCanvas
  split <;> simp only <;> omega

theorem finalCanvas_contains_pipeline_frames (c : Constants) (input : Input)
    (measured : List MeasuredLabel) (annotationBox : Rect) (labels : List PlacedLabel)
    (hx : 0 ≤ c.geometry.padX) (hy : 0 ≤ c.geometry.padY)
    (hw : 0 ≤ (arrange c.geometry input).plot.w)
    (hh : 0 ≤ (arrange c.geometry input).plot.h)
    (hindex : ∀ pipeline ∈ input.pipelines,
      pipeline.children.headD 0 < input.nodes.length)
    (hpad : 0 ≤ c.geometry.pipelinePad) (hheight : 0 ≤ c.geometry.pipelineHeight) :
    ∀ frame ∈ (arrange c.geometry input).frames,
      (⟨0, 0, (finalCanvas input (arrange c.geometry input) measured annotationBox labels).w,
        (finalCanvas input (arrange c.geometry input) measured annotationBox labels).h⟩ : Rect).Contained
        frame := by
  intro frame hframe
  have hplot := finalCanvas_contains_plot c input measured annotationBox labels hx hy
  have hf := arranged_frames_inside_plot c.geometry input hw hh hindex hpad hheight frame hframe
  simp only [Rect.Contained] at *
  omega

theorem arranged_force_inside_plot (c : GeometryConstants) (input : Input) (point : Point) :
    (arrange c input).plot.Contained (forceRect c (arrange c input).plot point) := by
  unfold forceRect
  apply fitPlot_inside
  · simp only [arrange]
    omega
  · simp only [arrange]
    omega

theorem arranged_accelerators_inside_plot (c : GeometryConstants) (input : Input) :
    ∀ r ∈ (arrange c input).accelerators, (arrange c input).plot.Contained r := by
  intro r hr
  obtain ⟨point, _, rfl⟩ := List.mem_map.mp hr
  exact arranged_force_inside_plot c input point

theorem arranged_deaccelerators_inside_plot (c : GeometryConstants) (input : Input) :
    ∀ r ∈ (arrange c input).deaccelerators, (arrange c input).plot.Contained r := by
  intro r hr
  obtain ⟨point, _, rfl⟩ := List.mem_map.mp hr
  exact arranged_force_inside_plot c input point

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem layoutWith_decompose (c : Constants) (input : Input) (m : Model) (s : Scene)
    (h : layoutWith c input m = .ok s) :
    ∃ measured annotationBox labels boxes routes,
      measureLabels c.fonts (m.profile == .cell) m.labels m.options.fontFamily = .ok measured ∧
      placeLabels c.labels (m.profile == .cell) input (arrange c.geometry input)
        m.routes measured = .ok (annotationBox, labels) ∧
      m.boxes.mapM (boxFunction (arrange c.geometry input) annotationBox) = .ok boxes ∧
      m.routes.mapM (routeGeometry (arrange c.geometry input)) = .ok routes ∧
      s.boxes = boxes ∧ s.routes = routes ∧ s.labels = labels.map PlacedLabel.dump ∧
      s.canvas = finalCanvas input (arrange c.geometry input) measured annotationBox labels := by
  unfold layoutWith at h
  obtain ⟨measured, hm, h⟩ := bind_ok h
  obtain ⟨pair, hp, h⟩ := bind_ok h
  rcases pair with ⟨annotationBox, labels⟩
  obtain ⟨boxes, hb, h⟩ := bind_ok h
  obtain ⟨routes, hr, h⟩ := bind_ok h
  obtain ⟨magnitude, _, h⟩ := bind_ok h
  cases magnitude
  obtain ⟨checked, _, h⟩ := bind_ok h
  cases checked
  obtain ⟨items, _, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst s
  exact ⟨measured, annotationBox, labels, boxes, routes,
    hm, hp, hb, hr, rfl, rfl, rfl, rfl⟩
private theorem boxFunction_flags (g : Geometry) (annotationBox : Rect)
    (b : ModelBox) (out : Box) (hb : b.exclusive = false ∧ b.role = .node)
    (h : boxFunction g annotationBox b = .ok out) :
    out.exclusive = false ∧ out.role = "node" := by
  unfold boxFunction at h
  cases hr : boxRect g annotationBox b.id with
  | error e => simp [hr, Bind.bind, Except.bind] at h
  | ok rect =>
      cases hc : XY.checkRect rect with
      | error e => simp [hr, hc, Bind.bind, Except.bind] at h
      | ok value =>
          cases value
          simp [hr, hc, Bind.bind, Except.bind] at h
          cases h
          exact ⟨hb.1, by simp [hb.2, BoxRole.id]⟩

private theorem routeGeometry_orthogonal (g : Geometry) (r : ModelRoute) (out : Route)
    (hr : r.orthogonal = false) (h : routeGeometry g r = .ok out) :
    out.orthogonal = false := by
  unfold routeGeometry at h
  cases ha : endpoint g r.fromId with
  | error e => simp [ha, Bind.bind, Except.bind] at h
  | ok a =>
      cases hb : endpoint g r.toId with
      | error e => simp [ha, hb, Bind.bind, Except.bind] at h
      | ok b =>
          cases hc : XY.checkMagnitude [a.x, a.y, b.x, b.y] with
          | error e => simp [ha, hb, hc, Bind.bind, Except.bind] at h
          | ok value =>
              cases value
              simp [ha, hb, hc, Bind.bind, Except.bind] at h
              cases h
              exact hr

theorem routeGeometry_metadata (g : Geometry) (model : ModelRoute) (route : Route)
    (h : routeGeometry g model = .ok route) :
    route.id = model.id ∧ route.fromId = model.fromId ∧ route.toId = model.toId := by
  unfold routeGeometry at h
  obtain ⟨source, _, h⟩ := bind_ok h
  obtain ⟨target, _, h⟩ := bind_ok h
  obtain ⟨checked, _, h⟩ := bind_ok h
  cases checked
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst route
  exact ⟨rfl, rfl, rfl⟩

private theorem mapM_provenance {α β : Type} (f : α → Except LayoutError β)
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys) :
    ∀ b ∈ ys, ∃ a ∈ xs, f a = .ok b := by
  induction xs generalizing ys with
  | nil =>
      simp [List.mapM_nil, Pure.pure, Except.pure] at h
      subst ys
      simp
  | cons a rest ih =>
      cases ha : f a with
      | error e => simp [List.mapM_cons, ha, Bind.bind, Except.bind] at h
      | ok b =>
          cases ht : rest.mapM f with
          | error e => simp [List.mapM_cons, ha, ht, Bind.bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, ha, ht, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
              subst ys
              intro out hout
              rcases List.mem_cons.mp hout with rfl | hout
              · exact ⟨a, by simp, ha⟩
              · obtain ⟨original, hmem, horiginal⟩ := ih tail ht out hout
                exact ⟨original, List.mem_cons_of_mem a hmem, horiginal⟩

theorem layoutWith_route_endpoints (c : Constants) (input : Input) (m : Model)
    (s : Scene) (h : layoutWith c input m = .ok s) :
    ∀ route ∈ s.routes, ∃ model ∈ m.routes,
      route.id = model.id ∧ route.fromId = model.fromId ∧ route.toId = model.toId ∧
      ∃ source target,
        endpoint (arrange c.geometry input) route.fromId = .ok source ∧
        endpoint (arrange c.geometry input) route.toId = .ok target ∧
        route.points.head? = some source ∧ route.points.getLast? = some target := by
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, _, _, hr, _, hsroute, _, _⟩ := layoutWith_decompose c input m s h
  intro route hroute
  rw [hsroute] at hroute
  obtain ⟨model, hmodel, hexecuted⟩ :=
    mapM_provenance (routeGeometry (arrange c.geometry input)) m.routes routes hr route hroute
  obtain ⟨hid, hfrom, hto⟩ := routeGeometry_metadata _ model route hexecuted
  obtain ⟨source, target, hs, ht, hfirst, hlast⟩ :=
    wardley_links_join_nodes _ model route hexecuted
  exact ⟨model, hmodel, hid, hfrom, hto, source, target,
    hfrom.symm ▸ hs, hto.symm ▸ ht, hfirst, hlast⟩

theorem layoutWith_routes_inside_canvas (c : Constants) (input : Input) (m : Model)
    (s : Scene) (h : layoutWith c input m = .ok s)
    (hx : 0 ≤ c.geometry.padX) (hy : 0 ≤ c.geometry.padY)
    (hw : 0 ≤ (arrange c.geometry input).plot.w)
    (hh : 0 ≤ (arrange c.geometry input).plot.h) :
    ∀ route ∈ s.routes, ∀ point ∈ route.points,
      (Validator.canvasRect s.layoutDump).Contained (nodeRect point) := by
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, _, _, hr, _, hsroute, _, hcanvas⟩ := layoutWith_decompose c input m s h
  have hplot := finalCanvas_contains_plot c input measured annotationBox labels hx hy
  intro route hroute point hpoint
  rw [hsroute] at hroute
  obtain ⟨model, _, hexecuted⟩ :=
    mapM_provenance (routeGeometry (arrange c.geometry input)) m.routes routes hr route hroute
  have hp := routeGeometry_points_inside_plot c.geometry input model route hw hh
    hexecuted point hpoint
  change (⟨0, 0, s.canvas.w, s.canvas.h⟩ : Rect).Contained (nodeRect point)
  rw [hcanvas]
  simp only [Rect.Contained] at hplot hp ⊢
  omega

theorem layoutWith_structural_clauses (c : Constants) (input : Input) (m : Model) (s : Scene)
    (hmeta : Elegant.Kinds.Wardley.metadataConsistent m = true)
    (h : layoutWith c input m = .ok s) :
    Validator.C2 s.layoutDump ∧ Validator.C4 s.layoutDump ∧ Validator.C6 s.layoutDump ∧
      Validator.C7 s.layoutDump ∧ Validator.C8 s.layoutDump := by
  obtain ⟨measured, annotationBox, labels, boxes, routes, _, _, hb, hr, hsbox, hsroute, _⟩ :=
    layoutWith_decompose c input m s h
  have hm := metadataConsistent_flags m hmeta
  have hflags : ∀ b ∈ s.boxes, b.exclusive = false ∧ b.role = "node" := by
    rw [hsbox]
    exact mapM_preserves _ _ _ (boxFunction_flags (arrange c.geometry input) annotationBox)
      m.boxes boxes hm.1 hb
  have horth : ∀ r ∈ s.routes, r.orthogonal = false := by
    rw [hsroute]
    exact mapM_preserves _ _ _ (routeGeometry_orthogonal (arrange c.geometry input))
      m.routes routes hm.2 hr
  have hc := all_nonexclusive_clauses s.layoutDump hflags
  exact ⟨hc.1, orthogonal_metadata_clause s.layoutDump horth, hc.2.1, hc.2.2.1, hc.2.2.2⟩

theorem wardley_valid_of_remaining_clauses (m : Model) (result : Layered.FamilyResult)
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (canvas : Validator.C1 result.scene.layoutDump)
    (parents : Validator.C3 result.scene.layoutDump)
    (ports : Validator.C5 result.scene.layoutDump) :
    HardConstraints result.scene.layoutDump := by
  have hs := (layout_success_scene m result h).1
  obtain ⟨input, _, _, hmetadata, _, _, hgeometry⟩ :=
    adapter_success_consistent m result.scene hs
  obtain ⟨c2, c4, c6, c7, c8⟩ :=
    layoutWith_structural_clauses (constants m) input m result.scene hmetadata hgeometry
  exact ⟨canvas, c2, parents, c4, ports, c6, c7, c8⟩

/-- A developer model admitted by the shared model predicate but inconsistent with the
Wardley codec's declared containment. This is not a parser-produced model. -/
def inconsistentParentModel : Model :=
  { kind := "wardley"
    boxes := [{ id := "plot", exclusive := false },
      { id := "n0", parent := "n1", exclusive := false },
      { id := "n1", parent := "plot", exclusive := false }]
    regionSets := [{ parent := -1, regions := [0, 4, 0] },
      { parent := -1, regions := [1, 0, 0, 0, 0, 0, 0] },
      { parent := -1, regions := [1, 0, 0, 100000, 100000, 0, 0] }] }

/-- Canonical two-component control for the numeric-alias regression probe. -/
def canonicalLookupModel : Model :=
  { inconsistentParentModel with
    boxes := [{ id := "plot", exclusive := false },
      { id := "n0", parent := "plot", exclusive := false },
      { id := "n1", parent := "plot", exclusive := false }] }

/-- This must be rejected by the public adapter: `n00` is not a declaration ID. -/
def numericAliasModel : Model :=
  { canonicalLookupModel with
    boxes := canonicalLookupModel.boxes ++
      [{ id := "n00", parent := "n1", exclusive := false }] }

theorem canonicalLookupModel_wellFormed : WellFormed canonicalLookupModel := by
  decide

theorem canonicalLookupModel_withinLimits : WithinLimits canonicalLookupModel := by
  decide

theorem numericAliasModel_wellFormed : WellFormed numericAliasModel := by
  decide

theorem numericAliasModel_withinLimits : WithinLimits numericAliasModel := by
  decide

/-- Probe for the unbacked annotation-box case: the codec has no annotation box,
but the model supplies the reserved ID with a node parent. -/
def unbackedAnnotationParentModel : Model :=
  { canonicalLookupModel with
    boxes := canonicalLookupModel.boxes ++
      [{ id := "ab", parent := "n0", exclusive := false }] }

theorem unbackedAnnotationParentModel_wellFormed :
    WellFormed unbackedAnnotationParentModel := by
  decide

theorem unbackedAnnotationParentModel_withinLimits :
    WithinLimits unbackedAnnotationParentModel := by
  decide

/-- The unbacked reserved ID passes the existing metadata-independent parent test:
the `none` branch of `modelConsistent` does not constrain its parent. -/
theorem unbackedAnnotationParentModel_parent_check :
    Elegant.Kinds.Wardley.modelConsistent
      { stageCount := 4,
        nodes := [⟨0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 100000, 100000, 0, 0⟩] }
      unbackedAnnotationParentModel = true := by
  decide


theorem unbackedAnnotationParentModel_rejected :
    Elegant.Kinds.Wardley.layout unbackedAnnotationParentModel =
      .error (.geometry .domain) := by
  have hp : Elegant.Kinds.Wardley.annotationParentsValid
      unbackedAnnotationParentModel = false := by decide
  simp [Elegant.Kinds.Wardley.layout, hp]

theorem successful_annotation_parent (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (b : ModelBox) (hb : b ∈ m.boxes) (hid : b.id = "ab") :
    b.parent = "" := by
  have hp : Elegant.Kinds.Wardley.annotationParentsValid m = true := by
    cases hc : Elegant.Kinds.Wardley.annotationParentsValid m with
    | false => simp [Elegant.Kinds.Wardley.layout, hc] at h
    | true => rfl
  have hbox := List.all_eq_true.mp hp b hb
  simpa [hid] using hbox

theorem wardley_structural_clauses (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    Validator.C2 result.scene.layoutDump ∧ Validator.C4 result.scene.layoutDump ∧
      Validator.C6 result.scene.layoutDump ∧ Validator.C7 result.scene.layoutDump ∧
      Validator.C8 result.scene.layoutDump := by
  obtain ⟨input, _, _, hmetadata, _, _, hgeometry⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  exact layoutWith_structural_clauses (constants m) input m result.scene hmetadata hgeometry

theorem wardley_route_endpoints (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    ∃ input, Elegant.Kinds.Wardley.decode m = .ok input ∧
      ∀ route ∈ result.scene.routes, ∃ model ∈ m.routes,
        route.id = model.id ∧ route.fromId = model.fromId ∧ route.toId = model.toId ∧
        ∃ source target,
          endpoint (arrange (constants m).geometry input) route.fromId = .ok source ∧
          endpoint (arrange (constants m).geometry input) route.toId = .ok target ∧
          route.points.head? = some source ∧ route.points.getLast? = some target := by
  obtain ⟨input, hd, _, _, _, _, hgeometry⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  exact ⟨input, hd, layoutWith_route_endpoints (constants m) input m result.scene hgeometry⟩

def inconsistentParentDump : LayoutDump :=
  { canvas := ⟨57600, 38400⟩
    boxes := [⟨"plot", "node", ⟨3072, 3072, 51456, 32256⟩, "", false⟩,
      ⟨"n0", "node", nodeRect (project ⟨3072, 3072, 51456, 32256⟩ 0 0), "n1", false⟩,
      ⟨"n1", "node", nodeRect (project ⟨3072, 3072, 51456, 32256⟩ 100000 100000),
        "plot", false⟩]
    routes := [], labels := [] }

theorem inconsistentParentModel_wellFormed : WellFormed inconsistentParentModel := by
  decide

theorem inconsistentParentModel_withinLimits : WithinLimits inconsistentParentModel := by
  decide

theorem inconsistentParentDump_rejected : Validator.check inconsistentParentDump = false := by
  decide
theorem constants_plot_nonnegative (m : Model) (input : Input) :
    0 ≤ (arrange (constants m).geometry input).plot.w ∧
      0 ≤ (arrange (constants m).geometry input).plot.h := by
  apply arrange_plot_nonnegative
  · cases hp : m.profile <;>
      simp [constants, hp, LayoutConst.Pair.get, LayoutConst.wardley_arrow_width]
  · cases hp : m.profile <;>
      simp [constants, hp, LayoutConst.Pair.get,
        LayoutConst.wardley_arrow_shaft, LayoutConst.wardley_arrow_head]

theorem wardley_plot_in_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    ∃ input, Elegant.Kinds.Wardley.decode m = .ok input ∧
      (Validator.canvasRect result.scene.layoutDump).Contained
        (arrange (constants m).geometry input).plot := by
  obtain ⟨input, hd, _, hmeta, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, _, _, _, _, _, _, hcanvas⟩ :=
    layoutWith_decompose (constants m) input m result.scene hs
  have hp := constants_padding_nonnegative m (metadataConsistent_padding m hmeta)
  refine ⟨input, hd, ?_⟩
  change (⟨0, 0, result.scene.canvas.w, result.scene.canvas.h⟩ : Rect).Contained _
  rw [hcanvas]
  exact finalCanvas_contains_plot (constants m) input measured annotationBox labels hp.1 hp.2

theorem wardley_route_points_in_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    ∀ route ∈ result.scene.routes, ∀ point ∈ route.points,
      (Validator.canvasRect result.scene.layoutDump).Contained (nodeRect point) := by
  obtain ⟨input, _, _, hmeta, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  have hp := constants_padding_nonnegative m (metadataConsistent_padding m hmeta)
  have hplot := constants_plot_nonnegative m input
  exact layoutWith_routes_inside_canvas (constants m) input m result.scene hs
    hp.1 hp.2 hplot.1 hplot.2

private theorem boxFunction_geometry (g : Geometry) (annotationBox : Rect)
    (model : ModelBox) (box : Box)
    (h : boxFunction g annotationBox model = .ok box) :
    box.id = model.id ∧ box.parent = model.parent ∧
      boxRect g annotationBox model.id = .ok box.rect := by
  unfold boxFunction at h
  obtain ⟨rect, hr, h⟩ := bind_ok h
  obtain ⟨checked, _, h⟩ := bind_ok h
  cases checked
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst box
  exact ⟨rfl, rfl, hr⟩

theorem layoutWith_box_geometry (c : Constants) (input : Input) (m : Model)
    (s : Scene) (h : layoutWith c input m = .ok s) :
    ∃ annotationBox, ∀ box ∈ s.boxes, ∃ model ∈ m.boxes,
      box.id = model.id ∧ box.parent = model.parent ∧
        boxRect (arrange c.geometry input) annotationBox model.id = .ok box.rect := by
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, _, hb, _, hsbox, _, _, _⟩ := layoutWith_decompose c input m s h
  refine ⟨annotationBox, ?_⟩
  intro box hbox
  rw [hsbox] at hbox
  obtain ⟨model, hm, hexecuted⟩ :=
    mapM_provenance (boxFunction (arrange c.geometry input) annotationBox)
      m.boxes boxes hb box hbox
  exact ⟨model, hm, boxFunction_geometry _ annotationBox model box hexecuted⟩

private theorem mapM_complete {α β : Type} (f : α → Except LayoutError β)
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys) :
    ∀ a ∈ xs, ∃ b ∈ ys, f a = .ok b := by
  induction xs generalizing ys with
  | nil => simp
  | cons a rest ih =>
      cases ha : f a with
      | error e => simp [List.mapM_cons, ha, Bind.bind, Except.bind] at h
      | ok b =>
          cases ht : rest.mapM f with
          | error e => simp [List.mapM_cons, ha, ht, Bind.bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, ha, ht, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
              subst ys
              intro model hm
              rcases List.mem_cons.mp hm with rfl | hm
              · exact ⟨b, List.mem_cons_self, ha⟩
              · obtain ⟨out, hout, hexecuted⟩ := ih tail ht model hm
                exact ⟨out, List.mem_cons_of_mem b hout, hexecuted⟩

theorem layoutWith_model_box_geometry (c : Constants) (input : Input) (m : Model)
    (s : Scene) (h : layoutWith c input m = .ok s) :
    ∃ annotationBox, ∀ model ∈ m.boxes, ∃ box ∈ s.boxes,
      box.id = model.id ∧ box.parent = model.parent ∧
        boxRect (arrange c.geometry input) annotationBox model.id = .ok box.rect := by
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, _, hb, _, hsbox, _, _, _⟩ := layoutWith_decompose c input m s h
  refine ⟨annotationBox, ?_⟩
  intro model hm
  obtain ⟨box, hbox, hexecuted⟩ :=
    mapM_complete (boxFunction (arrange c.geometry input) annotationBox)
      m.boxes boxes hb model hm
  refine ⟨box, ?_, boxFunction_geometry _ annotationBox model box hexecuted⟩
  rw [hsbox]
  exact hbox

theorem wardley_plot_box_in_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (box : Box) (hb : box ∈ result.scene.boxes) (hid : box.id = "plot") :
    (Validator.canvasRect result.scene.layoutDump).Contained box.rect := by
  obtain ⟨input, hd, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_box_geometry (constants m) input m result.scene hs
  obtain ⟨model, _, hmodel, _, hr⟩ := hboxes box hb
  have hmplot : model.id = "plot" := hmodel.symm.trans hid
  have hrect : (arrange (constants m).geometry input).plot = box.rect := by
    simpa [boxRect, hmplot] using hr
  obtain ⟨decoded, hdecoded, hplot⟩ := wardley_plot_in_canvas m result h
  have hinput : decoded = input := by
    rw [hd] at hdecoded
    exact Except.ok.inj hdecoded.symm
  subst decoded
  rw [← hrect]
  exact hplot

theorem constants_pipeline_nonnegative (m : Model) :
    0 ≤ (constants m).geometry.pipelinePad ∧
      0 ≤ (constants m).geometry.pipelineHeight := by
  cases hp : m.profile <;>
    simp [constants, hp, LayoutConst.Pair.get,
      LayoutConst.wardley_pipeline_pad, LayoutConst.wardley_pipeline_height]

theorem wardley_pipeline_frames_in_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    ∃ input, Elegant.Kinds.Wardley.decode m = .ok input ∧
      ∀ frame ∈ (arrange (constants m).geometry input).frames,
        (Validator.canvasRect result.scene.layoutDump).Contained frame := by
  obtain ⟨input, hd, _, hmeta, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, _, _, _, _, _, _, hcanvas⟩ :=
    layoutWith_decompose (constants m) input m result.scene hs
  have hp := constants_padding_nonnegative m (metadataConsistent_padding m hmeta)
  have hplot := constants_plot_nonnegative m input
  have hpipe := constants_pipeline_nonnegative m
  refine ⟨input, hd, ?_⟩
  intro frame hf
  change (⟨0, 0, result.scene.canvas.w, result.scene.canvas.h⟩ : Rect).Contained frame
  rw [hcanvas]
  exact finalCanvas_contains_pipeline_frames (constants m) input measured annotationBox labels
    hp.1 hp.2 hplot.1 hplot.2
    (Elegant.Kinds.Wardley.decode_pipeline_first_index m input hd)
    hpipe.1 hpipe.2 frame hf

/-- Rectangle provenance through the executed insertion folds of `arrange`, stated
on the six declaration stems with their exact generated keys. No numeric suffix is
ever parsed: each hit carries the zipIdx witness that produced it. -/
def RectEntry (nodes : List Node) (positions ghosts : List Point)
    (frames accelerators deaccelerators : List Rect) (annotations : List Point)
    (id : String) (r : Rect) : Prop :=
  (∃ e ∈ (nodes.zip positions).zipIdx, id = "n" ++ toString e.2 ∧ r = nodeRect e.1.2) ∨
  (∃ e ∈ ghosts.zipIdx, id = "tg" ++ toString e.2 ∧ r = nodeRect e.1) ∨
  (∃ e ∈ frames.zipIdx, id = "pl" ++ toString e.2 ∧ r = e.1) ∨
  (∃ e ∈ accelerators.zipIdx, id = "ac" ++ toString e.2 ∧ r = e.1) ∨
  (∃ e ∈ deaccelerators.zipIdx, id = "de" ++ toString e.2 ∧ r = e.1) ∨
  (∃ e ∈ annotations.zipIdx, id = "an" ++ toString e.2 ∧ r = nodeRect e.1)

/-- The rectangle-only shadow of the private index folds inside `arrange`. Each step
inserts exactly the key and rectangle the corresponding private constructor inserts. -/
def mirrorRects (nodes : List Node) (positions ghosts : List Point)
    (frames accelerators deaccelerators : List Rect) (annotations : List Point) :
    Std.HashMap String Rect :=
  (annotations.zipIdx).foldl
    (fun rs e => rs.insert ("an" ++ toString e.2) (nodeRect e.1))
    ((deaccelerators.zipIdx).foldl
      (fun rs e => rs.insert ("de" ++ toString e.2) e.1)
      ((accelerators.zipIdx).foldl
        (fun rs e => rs.insert ("ac" ++ toString e.2) e.1)
        ((frames.zipIdx).foldl
          (fun rs e => rs.insert ("pl" ++ toString e.2) e.1)
          ((ghosts.zipIdx).foldl
            (fun rs e => rs.insert ("tg" ++ toString e.2) (nodeRect e.1))
            (((nodes.zip positions).zipIdx).foldl
              (fun rs e => rs.insert ("n" ++ toString e.2) (nodeRect e.1.2)) {})))))

private theorem fold_rect_preserves {α σ : Type} (step : σ → α → σ)
    (P : σ → Prop) (entries : List α) (initial : σ)
    (hinit : P initial)
    (hstep : ∀ state entry, P state → entry ∈ entries → P (step state entry)) :
    P (entries.foldl step initial) := by
  induction entries generalizing initial with
  | nil => exact hinit
  | cons entry rest ih =>
      apply ih (step initial entry)
      · exact hstep initial entry hinit (by simp)
      · intro state next hs hn
        exact hstep state next hs (List.mem_cons_of_mem entry hn)

private theorem insert_rect_sound (rs : Std.HashMap String Rect)
    (P : String → Rect → Prop) (id : String) (rect : Rect)
    (h : ∀ key value, rs[key]? = some value → P key value) (hp : P id rect) :
    ∀ key value, (rs.insert id rect)[key]? = some value → P key value := by
  intro key value hv
  rw [Std.HashMap.getElem?_insert] at hv
  split at hv
  · rename_i heq
    have hid : id = key := by simpa using heq
    subst key
    cases hv
    exact hp
  · exact h key value hv

private theorem empty_rects_sound (P : String → Rect → Prop) :
    ∀ k v, (({} : Std.HashMap String Rect))[k]? = some v → P k v := by
  intro k v hv
  have hnone : (({} : Std.HashMap String Rect))[k]? = none :=
    Std.HashMap.getElem?_empty
  rw [hnone] at hv
  cases hv

private theorem foldl_insert_rects_sound {α : Type} {init : Std.HashMap String Rect}
    (entries : List α)
    (step : Std.HashMap String Rect → α → Std.HashMap String Rect)
    (key : α → String) (val : α → Rect) (P : String → Rect → Prop)
    (hstep : ∀ e ∈ entries, P (key e) (val e))
    (hform : ∀ rs e, step rs e = rs.insert (key e) (val e))
    (hsound : ∀ k v, init[k]? = some v → P k v) :
    ∀ k v, (entries.foldl step init)[k]? = some v → P k v := by
  have hQ := fold_rect_preserves step
    (fun rs => ∀ k v, rs[k]? = some v → P k v) entries init hsound
    (fun rs e hs he => by
      rw [hform rs e]
      exact insert_rect_sound rs P (key e) (val e) hs (hstep e he))
  exact hQ

private theorem foldl_lookup_rectangles {α : Type} (entries : List α)
    (step : GeometryLookup → α → GeometryLookup)
    (key : α → String) (val : α → Rect)
    (hstep : ∀ l e, (step l e).rectangles =
      l.rectangles.insert (key e) (val e))
    (init : GeometryLookup) :
    (entries.foldl step init).rectangles =
      entries.foldl (fun rs e => rs.insert (key e) (val e)) init.rectangles := by
  induction entries generalizing init with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih (step init a), hstep]

/-- The executed rectangle lookup of `arrange` is exactly the public mirror: each
private index fold contributes only its rectangle insertions, in order. -/
theorem arrange_lookup_rectangles (c : GeometryConstants) (input : Input) :
    (arrange c input).lookup.rectangles = mirrorRects input.nodes
      (arrange c input).positions (arrange c input).ghosts
      (arrange c input).frames (arrange c input).accelerators
      (arrange c input).deaccelerators (arrange c input).annotations := by
  unfold arrange
  dsimp
  run_tac do
    for name in [`Elegant.Chart.Wardley.indexNodes,
        `Elegant.Chart.Wardley.indexPoints, `Elegant.Chart.Wardley.indexRectangles] do
      Lean.Elab.Tactic.unfoldTarget (Lean.mkPrivateNameCore `Elegant.Chart.Wardley name)
  rw [foldl_lookup_rectangles _ _
    (fun e => "an" ++ toString e.2) (fun e => nodeRect e.1)
    (by intro l e; rfl)]
  rw [foldl_lookup_rectangles _ _
    (fun e => "de" ++ toString e.2) (fun e => e.1)
    (by intro l e; rfl)]
  rw [foldl_lookup_rectangles _ _
    (fun e => "ac" ++ toString e.2) (fun e => e.1)
    (by intro l e; rfl)]
  rw [foldl_lookup_rectangles _ _
    (fun e => "pl" ++ toString e.2) (fun e => e.1)
    (by intro l e; rfl)]
  rw [foldl_lookup_rectangles _ _
    (fun e => "tg" ++ toString e.2) (fun e => nodeRect e.1)
    (by intro l e; rfl)]
  rw [foldl_lookup_rectangles _ _
    (fun e => "n" ++ toString e.2) (fun e => nodeRect e.1.2)
    (by intro l e; rfl)]
  rfl

/-- Every rectangle in the executed lookup comes from one of the six declaration
folds, with the exact key and stored value that fold inserted. -/
theorem mirrorRects_sound (nodes : List Node) (positions ghosts : List Point)
    (frames accelerators deaccelerators : List Rect) (annotations : List Point)
    (id : String) (r : Rect)
    (h : (mirrorRects nodes positions ghosts frames accelerators deaccelerators
      annotations)[id]? = some r) :
    RectEntry nodes positions ghosts frames accelerators deaccelerators
      annotations id r := by
  unfold mirrorRects at h
  exact foldl_insert_rects_sound (annotations.zipIdx)
    (fun rs e => rs.insert ("an" ++ toString e.2) (nodeRect e.1))
    (fun e => "an" ++ toString e.2) (fun e => nodeRect e.1)
    (RectEntry nodes positions ghosts frames accelerators deaccelerators annotations)
    (fun e he => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e, he, rfl, rfl⟩)))))
    (fun rs e => rfl)
    (foldl_insert_rects_sound (deaccelerators.zipIdx)
      (fun rs e => rs.insert ("de" ++ toString e.2) e.1)
      (fun e => "de" ++ toString e.2) (fun e => e.1)
      (RectEntry nodes positions ghosts frames accelerators deaccelerators annotations)
      (fun e he => Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨e, he, rfl, rfl⟩)))))
      (fun rs e => rfl)
      (foldl_insert_rects_sound (accelerators.zipIdx)
        (fun rs e => rs.insert ("ac" ++ toString e.2) e.1)
        (fun e => "ac" ++ toString e.2) (fun e => e.1)
        (RectEntry nodes positions ghosts frames accelerators deaccelerators annotations)
        (fun e he => Or.inr (Or.inr (Or.inr
          (Or.inl ⟨e, he, rfl, rfl⟩))))
        (fun rs e => rfl)
        (foldl_insert_rects_sound (frames.zipIdx)
          (fun rs e => rs.insert ("pl" ++ toString e.2) e.1)
          (fun e => "pl" ++ toString e.2) (fun e => e.1)
          (RectEntry nodes positions ghosts frames accelerators deaccelerators annotations)
          (fun e he => Or.inr (Or.inr
            (Or.inl ⟨e, he, rfl, rfl⟩)))
          (fun rs e => rfl)
          (foldl_insert_rects_sound (ghosts.zipIdx)
            (fun rs e => rs.insert ("tg" ++ toString e.2) (nodeRect e.1))
            (fun e => "tg" ++ toString e.2) (fun e => nodeRect e.1)
            (RectEntry nodes positions ghosts frames accelerators deaccelerators annotations)
            (fun e he => Or.inr (Or.inl ⟨e, he, rfl, rfl⟩))
            (fun rs e => rfl)
            (foldl_insert_rects_sound ((nodes.zip positions).zipIdx)
              (fun rs e => rs.insert ("n" ++ toString e.2) (nodeRect e.1.2))
              (fun e => "n" ++ toString e.2) (fun e => nodeRect e.1.2)
              (RectEntry nodes positions ghosts frames accelerators deaccelerators annotations)
              (fun e he => Or.inl ⟨e, he, rfl, rfl⟩)
              (fun rs e => rfl)
              (empty_rects_sound
                (RectEntry nodes positions ghosts frames accelerators
                  deaccelerators annotations))))))) id r h

/-- Public rectangle-lookup soundness for `arrange`: every hit is produced by one
of the six declaration folds with its exact generated key. -/
theorem arrange_rectangles_sound (c : GeometryConstants) (input : Input)
    (id : String) (r : Rect)
    (h : (arrange c input).lookup.rectangles[id]? = some r) :
    RectEntry input.nodes (arrange c input).positions (arrange c input).ghosts
      (arrange c input).frames (arrange c input).accelerators
      (arrange c input).deaccelerators (arrange c input).annotations id r := by
  rw [arrange_lookup_rectangles c input] at h
  exact mirrorRects_sound input.nodes (arrange c input).positions
    (arrange c input).ghosts (arrange c input).frames
    (arrange c input).accelerators (arrange c input).deaccelerators
    (arrange c input).annotations id r h

theorem arrange_rectangles_inside_plot (c : GeometryConstants) (input : Input)
    (hw : 0 ≤ (arrange c input).plot.w) (hh : 0 ≤ (arrange c input).plot.h)
    (hindex : ∀ pipeline ∈ input.pipelines,
      pipeline.children.headD 0 < input.nodes.length)
    (hpad : 0 ≤ c.pipelinePad) (hheight : 0 ≤ c.pipelineHeight)
    (id : String) (r : Rect)
    (h : (arrange c input).lookup.rectangles[id]? = some r) :
    (arrange c input).plot.Contained r := by
  rcases arrange_rectangles_sound c input id r h with
    hn | hg | hf | ha | hd | ht
  · obtain ⟨entry, he, _, rfl⟩ := hn
    exact arranged_positions_inside c input hw hh entry.1.2
      (List.of_mem_zip (List.fst_mem_of_mem_zipIdx he)).2
  · obtain ⟨entry, he, _, rfl⟩ := hg
    have hmem := List.fst_mem_of_mem_zipIdx he
    obtain ⟨trend, _, hpoint⟩ := List.mem_map.mp hmem
    rw [← hpoint]
    exact projected_node_inside (arrange c input).plot trend.x trend.y hw hh
  · obtain ⟨entry, he, _, rfl⟩ := hf
    exact arranged_frames_inside_plot c input hw hh hindex hpad hheight entry.1
      (List.fst_mem_of_mem_zipIdx he)
  · obtain ⟨entry, he, _, rfl⟩ := ha
    exact arranged_accelerators_inside_plot c input entry.1
      (List.fst_mem_of_mem_zipIdx he)
  · obtain ⟨entry, he, _, rfl⟩ := hd
    exact arranged_deaccelerators_inside_plot c input entry.1
      (List.fst_mem_of_mem_zipIdx he)
  · obtain ⟨entry, he, _, rfl⟩ := ht
    have hmem := List.fst_mem_of_mem_zipIdx he
    obtain ⟨annotation, _, hpoint⟩ := List.mem_map.mp hmem
    rw [← hpoint]
    exact projected_node_inside (arrange c input).plot annotation.x annotation.y hw hh

theorem boxRect_inside_plot (c : GeometryConstants) (input : Input)
    (annotationBox : Rect) (id : String) (r : Rect)
    (hw : 0 ≤ (arrange c input).plot.w) (hh : 0 ≤ (arrange c input).plot.h)
    (hindex : ∀ pipeline ∈ input.pipelines,
      pipeline.children.headD 0 < input.nodes.length)
    (hpad : 0 ≤ c.pipelinePad) (hheight : 0 ≤ c.pipelineHeight)
    (hab : id ≠ "ab")
    (h : boxRect (arrange c input) annotationBox id = .ok r) :
    (arrange c input).plot.Contained r := by
  by_cases hp : id = "plot"
  · have hr : (arrange c input).plot = r := by
      simpa [boxRect, hp] using h
    rw [← hr]
    simp [Rect.Contained]
  · unfold boxRect at h
    simp only [hp, hab, ↓reduceIte] at h
    cases hr : (arrange c input).lookup.rectangles[id]? with
    | none => simp [hr] at h
    | some rect =>
        simp only [hr, Except.ok.injEq] at h
        subst rect
        exact arrange_rectangles_inside_plot c input hw hh hindex hpad hheight id r hr

theorem wardley_nonannotation_boxes_in_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    ∀ box ∈ result.scene.boxes, box.id ≠ "ab" →
      (Validator.canvasRect result.scene.layoutDump).Contained box.rect := by
  obtain ⟨input, hd, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_box_geometry (constants m) input m result.scene hs
  obtain ⟨decoded, hdecoded, hcanvas⟩ := wardley_plot_in_canvas m result h
  have heq : decoded = input := by
    rw [hd] at hdecoded
    exact Except.ok.inj hdecoded.symm
  subst decoded
  have hplot := constants_plot_nonnegative m input
  have hpipeline := constants_pipeline_nonnegative m
  intro box hb hab
  obtain ⟨model, _, hid, _, hr⟩ := hboxes box hb
  have hinside := boxRect_inside_plot (constants m).geometry input annotationBox
    model.id box.rect hplot.1 hplot.2
    (Elegant.Kinds.Wardley.decode_pipeline_first_index m input hd)
    hpipeline.1 hpipeline.2 (fun hm => hab (hid.trans hm)) hr
  simp only [Rect.Contained] at hcanvas hinside ⊢
  omega

theorem placeLabels_annotationBox_eq (c : LabelConstants) (cell : Bool)
    (input : Input) (g : Geometry) (routes : List ModelRoute)
    (measured : List MeasuredLabel) (box : Rect) (labels : List PlacedLabel)
    (h : placeLabels c cell input g routes measured = .ok (box, labels)) :
    box = match input.box with
      | some pos => annotationBox c g.plot pos ((boxedAnnotations measured).map (·.extent))
      | none => ⟨0, 0, 0, 0⟩ := by
  unfold placeLabels at h
  obtain ⟨placed, _, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1.symm

theorem constants_empty_annotation_fits (m : Model) (input : Input) :
    2 * (constants m).labels.boxPad ≤ (arrange (constants m).geometry input).plot.w ∧
      2 * (constants m).labels.boxPad ≤ (arrange (constants m).geometry input).plot.h := by
  cases hp : m.profile <;>
    simp only [arrange, constants, hp, LayoutConst.Pair.get,
      LayoutConst.wardley_box_pad, LayoutConst.wardley_arrow_width,
      LayoutConst.wardley_arrow_shaft, LayoutConst.wardley_arrow_head] <;>
    omega

theorem wardley_c1 (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump := by
  obtain ⟨input, hd, _, hm, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, hplaced, hb, _, hsbox, _, _, hcanvas⟩ :=
    layoutWith_decompose (constants m) input m result.scene hs
  have hpadding := constants_padding_nonnegative m (metadataConsistent_padding m hm)
  have hp := constants_plot_nonnegative m input
  have hplot := finalCanvas_contains_plot (constants m) input measured annotationBox labels
    hpadding.1 hpadding.2
  have hab := placeLabels_annotationBox_eq (constants m).labels
    (m.profile == .cell) input (arrange (constants m).geometry input)
    m.routes measured annotationBox labels hplaced
  intro box hbox
  by_cases hid : box.id = "ab"
  · have hmem : box ∈ boxes := by
      change box ∈ result.scene.boxes at hbox
      rw [hsbox] at hbox
      exact hbox
    obtain ⟨model, _, hexecuted⟩ :=
      mapM_provenance (boxFunction (arrange (constants m).geometry input) annotationBox)
        m.boxes boxes hb box hmem
    obtain ⟨hmodel, _, hr⟩ :=
      boxFunction_geometry (arrange (constants m).geometry input)
        annotationBox model box hexecuted
    have hrect : annotationBox = box.rect := by
      simpa [boxRect, hmodel.symm.trans hid] using hr
    rw [← hrect]
    change (⟨0, 0, result.scene.canvas.w, result.scene.canvas.h⟩ : Rect).Contained _
    rw [hcanvas]
    cases hpos : input.box with
    | none =>
        have hz : annotationBox = ⟨0, 0, 0, 0⟩ := by simpa [hpos] using hab
        rw [hz] at hplot ⊢
        dsimp [Rect.Contained] at hplot ⊢
        omega
    | some pos =>
        have heq : annotationBox = Elegant.Chart.Wardley.annotationBox
            (constants m).labels (arrange (constants m).geometry input).plot pos
            ((boxedAnnotations measured).map (·.extent)) := by
          simpa [hpos] using hab
        by_cases hempty : boxedAnnotations measured = []
        · have hsmall := constants_empty_annotation_fits m input
          have hi : (arrange (constants m).geometry input).plot.Contained annotationBox := by
            rw [heq]
            unfold Elegant.Chart.Wardley.annotationBox
            apply fitPlot_inside
            · simpa [hempty] using hsmall.1
            · simpa [hempty] using hsmall.2
          simp only [Rect.Contained] at hplot hi ⊢
          omega
        · have hx0 : 0 ≤ annotationBox.x := by
            rw [heq]
            simp only [Elegant.Chart.Wardley.annotationBox, fitPlot]
            unfold clamp
            simp only [arrange]
            omega
          have hy0 : 0 ≤ annotationBox.y := by
            rw [heq]
            simp only [Elegant.Chart.Wardley.annotationBox, fitPlot]
            unfold clamp
            simp only [arrange]
            omega
          have hemptyBool : (boxedAnnotations measured).isEmpty = false := by
            cases he : boxedAnnotations measured with
            | nil => exact False.elim (hempty he)
            | cons a rest => rfl
          unfold finalCanvas
          simp only [hpos, Option.isSome_some, hemptyBool,
            Bool.not_false, Bool.and_self, ↓reduceIte]
          simp only [Rect.Contained]
          omega
  · exact wardley_nonannotation_boxes_in_canvas m result h box hbox hid

theorem wardley_annotation_box_parent (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (box : Box) (hb : box ∈ result.scene.boxes) (hid : box.id = "ab") :
    box.parent = "" := by
  obtain ⟨input, _, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_box_geometry (constants m) input m result.scene hs
  obtain ⟨model, hm, heq, hparent, _⟩ := hboxes box hb
  exact hparent.trans
    (successful_annotation_parent m result h model hm (heq.symm.trans hid))

theorem placeLabels_nonnegative (c : LabelConstants) (cell : Bool)
    (input : Input) (g : Geometry) (routes : List ModelRoute)
    (measured : List MeasuredLabel) (box : Rect) (labels : List PlacedLabel)
    (h : placeLabels c cell input g routes measured = .ok (box, labels)) :
    ∀ label ∈ labels, 0 ≤ label.rect.x ∧ 0 ≤ label.rect.y := by
  unfold placeLabels at h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  have hlabels : placed = labels := h.2
  subst placed
  intro label hl
  obtain ⟨original, _, hexecuted⟩ := mapM_provenance _ _ _ hp label hl
  split at hexecuted
  · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hexecuted
    subst label
    change (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 0
    exact ⟨Int.le_refl 0, Int.le_refl 0⟩
  · obtain ⟨pair, _, hexecuted⟩ := bind_ok hexecuted
    rcases pair with ⟨rect, align⟩
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hexecuted
    subst label
    simp only [fitCanvas]
    unfold clamp
    omega

theorem wardley_shown_labels_in_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    ∃ (input : Input) (measured : List MeasuredLabel) (annotationBox : Rect)
        (labels : List PlacedLabel),
      placeLabels (constants m).labels (m.profile == .cell) input
        (arrange (constants m).geometry input) m.routes measured =
          .ok (annotationBox, labels) ∧
      result.scene.labels = labels.map PlacedLabel.dump ∧
      ∀ label ∈ labels, label.shown = true →
        (Validator.canvasRect result.scene.layoutDump).Contained label.rect := by
  obtain ⟨input, _, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨measured, annotationBox, labels, boxes, routes,
      _, hp, _, _, _, _, hlabels, hcanvas⟩ :=
    layoutWith_decompose (constants m) input m result.scene hs
  refine ⟨input, measured, annotationBox, labels, hp, hlabels, ?_⟩
  intro label hl hshown
  have hlo := placeLabels_nonnegative (constants m).labels (m.profile == .cell)
    input (arrange (constants m).geometry input) m.routes measured annotationBox labels
    hp label hl
  have hhi := finalCanvas_contains_shown_label_extents input
    (arrange (constants m).geometry input) measured annotationBox labels label hl hshown
  change (⟨0, 0, result.scene.canvas.w, result.scene.canvas.h⟩ : Rect).Contained _
  rw [hcanvas]
  simp only [Rect.Contained]
  omega

theorem wellFormed_route_boxes (m : Model) (hwf : WellFormed m)
    (route : ModelRoute) (hr : route ∈ m.routes) :
    (∃ box ∈ m.boxes, box.id = route.fromId) ∧
      (∃ box ∈ m.boxes, box.id = route.toId) := by
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  have hroutes := hwf.1.1.2
  have hendpoints := List.all_eq_true.mp hroutes route hr
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hendpoints
  constructor
  · obtain ⟨box, hb, hid⟩ := List.mem_map.mp hendpoints.1
    exact ⟨box, hb, hid⟩
  · obtain ⟨box, hb, hid⟩ := List.mem_map.mp hendpoints.2
    exact ⟨box, hb, hid⟩

theorem wardley_route_boxes (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (route : Route) (hr : route ∈ result.scene.routes) :
    (∃ box ∈ result.scene.boxes, box.id = route.fromId) ∧
      (∃ box ∈ result.scene.boxes, box.id = route.toId) := by
  obtain ⟨input, _, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨model, hm, _, hfrom, hto, _⟩ :=
    layoutWith_route_endpoints (constants m) input m result.scene hs route hr
  obtain ⟨source, target⟩ := wellFormed_route_boxes m hwf model hm
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_model_box_geometry (constants m) input m result.scene hs
  constructor
  · obtain ⟨source, hsource, hid⟩ := source
    obtain ⟨box, hb, heq, _⟩ := hboxes source hsource
    exact ⟨box, hb, heq.trans (hid.trans hfrom.symm)⟩
  · obtain ⟨target, htarget, hid⟩ := target
    obtain ⟨box, hb, heq, _⟩ := hboxes target htarget
    exact ⟨box, hb, heq.trans (hid.trans hto.symm)⟩

private theorem box_lookup_exists (boxes : List Box) (id : String)
    (h : ∃ box ∈ boxes, box.id = id) :
    ∃ box, boxes.find? (fun candidate => candidate.id == id) = some box := by
  induction boxes with
  | nil => simp at h
  | cons first rest ih =>
      by_cases heq : first.id = id
      · exact ⟨first, by simp [heq]⟩
      · obtain ⟨box, hb, hid⟩ := h
        have hrest : box ∈ rest := by
          rcases List.mem_cons.mp hb with hfirst | hrest
          · subst box
            exact False.elim (heq hid)
          · exact hrest
        obtain ⟨found, hf⟩ := ih ⟨box, hrest, hid⟩
        exact ⟨found, by simp [heq, hf]⟩

theorem wardley_route_box_lookups (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (route : Route) (hr : route ∈ result.scene.routes) :
    (∃ box, result.scene.layoutDump.box? route.fromId = some box) ∧
      (∃ box, result.scene.layoutDump.box? route.toId = some box) := by
  obtain ⟨source, target⟩ := wardley_route_boxes m result hwf h route hr
  exact ⟨box_lookup_exists result.scene.boxes route.fromId source,
    box_lookup_exists result.scene.boxes route.toId target⟩

theorem arranged_pipeline_contains_unmarked_child (m : Model) (input : Input)
    (pipeline : Pipeline) (i : Nat) (node : Node)
    (hmarked : Elegant.Kinds.Wardley.parentsMarked input = true)
    (hnode : input.nodes[i]? = some node)
    (hflag : node.flags &&& 4 = 0)
    (hi : i ∈ pipeline.children) :
    (pipelineGeometry (constants m).geometry (arrange (constants m).geometry input).plot
      (arrange (constants m).geometry input).base pipeline).1.Contained
      (nodeRect (((arrange (constants m).geometry input).positions[i]?).getD ⟨0, 0⟩)) := by
  rw [unmarked_node_position (constants m).geometry input i node hmarked hnode hflag]
  apply pipeline_frame_contains_base_child
    (constants m).geometry (arrange (constants m).geometry input).plot
    (arrange (constants m).geometry input).base pipeline i hi
  · have hplot := constants_plot_nonnegative m input
    have hbase : (arrange (constants m).geometry input).base[i]? =
        some (project (arrange (constants m).geometry input).plot node.x node.y) := by
      change (input.nodes.map _)[i]? = _
      simp only [List.getElem?_map, hnode, Option.map_some]
      rfl
    rw [hbase]
    exact projected_node_inside _ node.x node.y hplot.1 hplot.2
  · exact (constants_pipeline_nonnegative m).1
  · exact (constants_pipeline_nonnegative m).2
  · cases hp : m.profile <;>
      simp [constants, hp, LayoutConst.Pair.get]

theorem arranged_endpoint_boxRect (c : GeometryConstants) (input : Input)
    (annotationBox : Rect) (id : String) (point : Point)
    (h : endpoint (arrange c input) id = .ok point) :
    boxRect (arrange c input) annotationBox id = .ok (nodeRect point) := by
  have hp := endpoint_lookup _ _ _ h
  have hr := arrange_point_rectangle c input id point hp
  obtain ⟨hplot, hab⟩ := arrange_point_not_reserved c input id point hp
  simp only [boxRect, hplot, hab, ↓reduceIte, hr]

theorem wardley_c5 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    Validator.C5 result.scene.layoutDump := by
  obtain ⟨input, _, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_box_geometry (constants m) input m result.scene hs
  intro route hr
  obtain ⟨model, _, _, _, _, source, target, hsource, htarget, hfirst, hlast⟩ :=
    layoutWith_route_endpoints (constants m) input m result.scene hs route hr
  obtain ⟨⟨fromBox, hfromBox⟩, ⟨toBox, htoBox⟩⟩ :=
    wardley_route_box_lookups m result hwf h route hr
  have fromMem : fromBox ∈ result.scene.boxes :=
    List.mem_of_find?_eq_some hfromBox
  have toMem : toBox ∈ result.scene.boxes :=
    List.mem_of_find?_eq_some htoBox
  have fromId : fromBox.id = route.fromId := by
    have hid := List.find?_some (p := fun (b : Box) => b.id == route.fromId) hfromBox
    exact beq_iff_eq.mp hid
  have toId : toBox.id = route.toId := by
    have hid := List.find?_some (p := fun (b : Box) => b.id == route.toId) htoBox
    exact beq_iff_eq.mp hid
  obtain ⟨fromModel, _, hfromId, _, hfromRect⟩ := hboxes fromBox fromMem
  obtain ⟨toModel, _, htoId, _, htoRect⟩ := hboxes toBox toMem
  have fromRect : fromBox.rect = nodeRect source := by
    have hid : fromModel.id = route.fromId := hfromId.symm.trans fromId
    rw [hid, arranged_endpoint_boxRect (constants m).geometry input
      annotationBox route.fromId source hsource] at hfromRect
    exact (Except.ok.inj hfromRect).symm
  have toRect : toBox.rect = nodeRect target := by
    have hid : toModel.id = route.toId := htoId.symm.trans toId
    rw [hid, arranged_endpoint_boxRect (constants m).geometry input
      annotationBox route.toId target htarget] at htoRect
    exact (Except.ok.inj htoRect).symm
  refine ⟨source, target, fromBox, toBox, hfirst, hlast, hfromBox, htoBox, ?_, ?_⟩
  · rw [fromRect]
    exact nodeRect_boundary source
  · rw [toRect]
    exact nodeRect_boundary target

theorem wardley_plot_parent_contains (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result)
    (box parent : Box) (hb : box ∈ result.scene.boxes)
    (hparent : box.parent = "plot")
    (hp : result.scene.layoutDump.box? box.parent = some parent) :
    parent.rect.Contained box.rect := by
  obtain ⟨input, hd, _, _, _, _, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_box_geometry (constants m) input m result.scene hs
  have hp' : result.scene.boxes.find? (fun b => b.id == "plot") = some parent := by
    simpa only [hparent, LayoutDump.box?, Scene.layoutDump] using hp
  have hpmem : parent ∈ result.scene.boxes := List.mem_of_find?_eq_some hp'
  have hpid : parent.id = "plot" := by
    have hid := List.find?_some (p := fun (b : Box) => b.id == "plot") hp'
    exact beq_iff_eq.mp hid
  obtain ⟨parentModel, _, hparentId, _, hparentRect⟩ := hboxes parent hpmem
  have hmodelPlot : parentModel.id = "plot" := hparentId.symm.trans hpid
  have hrect : parent.rect = (arrange (constants m).geometry input).plot := by
    have heq : (arrange (constants m).geometry input).plot = parent.rect := by
      simpa only [boxRect, hmodelPlot, ↓reduceIte, Except.ok.injEq] using hparentRect
    exact heq.symm
  rw [hrect]
  obtain ⟨model, hm, hid, _, hr⟩ := hboxes box hb
  have hab : model.id ≠ "ab" := by
    intro heq
    have hboxId : box.id = "ab" := hid.trans heq
    have hempty := wardley_annotation_box_parent m result h box hb hboxId
    rw [hparent] at hempty
    contradiction
  have hplot := constants_plot_nonnegative m input
  have hpipe := constants_pipeline_nonnegative m
  exact boxRect_inside_plot (constants m).geometry input annotationBox model.id box.rect
    hplot.1 hplot.2 (Elegant.Kinds.Wardley.decode_pipeline_first_index m input hd)
    hpipe.1 hpipe.2 hab hr

theorem expected_nonplot_parent (input : Input) (m : Model) (b : ModelBox)
    (hb : b ∈ Elegant.Kinds.Wardley.expectedBoxes input m)
    (hempty : b.parent ≠ "") (hplot : b.parent ≠ "plot") :
    ∃ (i : Nat) (node : Node) (k : Nat) (pipeline : Pipeline),
      input.nodes[i]? = some node ∧ node.flags &&& 4 = 0 ∧
      input.pipelines[k]? = some pipeline ∧ i ∈ pipeline.children ∧
      b.id = "n" ++ toString i ∧ b.parent = "pl" ++ toString k := by
  unfold Elegant.Kinds.Wardley.expectedBoxes at hb
  simp only [List.mem_append, or_assoc] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb
  · simp only [List.mem_singleton] at hb
    subst b
    exact False.elim (hempty rfl)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact False.elim (hplot rfl)
  · obtain ⟨⟨node, i⟩, hn, rfl⟩ := List.mem_map.mp hb
    have hnode : input.nodes[i]? = some node :=
      List.mk_mem_zipIdx_iff_getElem?.mp hn
    change (if node.flags &&& 4 != 0 then "plot" else
      match input.pipelines.zipIdx.find? (fun entry => entry.1.children.contains i) with
      | some (_, k) => "pl" ++ toString k
      | none => "plot") ≠ "plot" at hplot
    by_cases hflag : node.flags &&& 4 = 0
    · simp only [hflag, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hplot ⊢
      cases hf : input.pipelines.zipIdx.find?
          (fun entry => entry.1.children.contains i) with
      | none => simp only [hf] at hplot; exact False.elim (hplot rfl)
      | some entry =>
          rcases entry with ⟨pipeline, k⟩
          have hp := List.mem_of_find?_eq_some hf
          have hc := List.find?_some
            (p := fun entry : Pipeline × Nat => entry.1.children.contains i) hf
          refine ⟨i, node, k, pipeline, hnode, hflag,
            List.mk_mem_zipIdx_iff_getElem?.mp hp, List.contains_iff_mem.mp hc, rfl, ?_⟩
          rfl
    · have hne : (node.flags &&& 4 != 0) = true := by simp [hflag]
      simp only [hne, ↓reduceIte] at hplot
      exact False.elim (hplot rfl)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact False.elim (hplot rfl)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact False.elim (hempty rfl)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact False.elim (hempty rfl)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact False.elim (hplot rfl)
  · split at hb
    · simp only [List.mem_singleton] at hb
      subst b
      exact False.elim (hempty rfl)
    · simp at hb

theorem rectangle_expected_id (input : Input) (m : Model) (c : GeometryConstants)
    (id : String) (rect : Rect)
    (hr : (arrange c input).lookup.rectangles[id]? = some rect) :
    ∃ expected ∈ Elegant.Kinds.Wardley.expectedBoxes input m, expected.id = id := by
  rcases arrange_rectangles_sound c input id rect hr with hn | hg | hp | ha | hd | han
  · obtain ⟨⟨⟨node, point⟩, i⟩, he, hid, _⟩ := hn
    have hi := List.snd_lt_of_mem_zipIdx he
    simp only [List.length_zip, Nat.add_zero] at hi
    have hin : i < input.nodes.length := by omega
    let node := input.nodes[i]
    have hn : (node, i) ∈ input.nodes.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [node])
    let parent := if node.flags &&& 4 != 0 then "plot" else
      match input.pipelines.zipIdx.find? (fun entry => entry.1.children.contains i) with
      | some (_, k) => "pl" ++ toString k
      | none => "plot"
    refine ⟨{ id := "n" ++ toString i, parent, exclusive := false }, ?_, hid.symm⟩
    unfold Elegant.Kinds.Wardley.expectedBoxes
    simp only [List.mem_append, or_assoc]
    exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨(node, i), hn, rfl⟩)))
  · obtain ⟨⟨point, i⟩, he, hid, _⟩ := hg
    have hi := List.snd_lt_of_mem_zipIdx he
    have hlen : (arrange c input).ghosts.length = input.trends.length := by
      simp [arrange]
    have hi' : i ∈ List.range input.trends.length := by
      simp only [List.mem_range]
      omega
    refine ⟨{ id := "tg" ++ toString i, parent := "plot", exclusive := false }, ?_, hid.symm⟩
    unfold Elegant.Kinds.Wardley.expectedBoxes
    simp only [List.mem_append, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨i, hi', rfl⟩))))
  · obtain ⟨⟨frame, i⟩, he, hid, _⟩ := hp
    have hi := List.snd_lt_of_mem_zipIdx he
    have hlen : (arrange c input).frames.length = input.pipelines.length := by
      simp [arrange]
    have hi' : i ∈ List.range input.pipelines.length := by
      simp only [List.mem_range]
      omega
    refine ⟨{ id := "pl" ++ toString i, parent := "plot", exclusive := false }, ?_, hid.symm⟩
    unfold Elegant.Kinds.Wardley.expectedBoxes
    simp only [List.mem_append, or_assoc]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨i, hi', rfl⟩))
  · obtain ⟨⟨force, i⟩, he, hid, _⟩ := ha
    have hi := List.snd_lt_of_mem_zipIdx he
    have hlen : (arrange c input).accelerators.length = input.accelerators.length := by
      simp [arrange]
    have hi' : i ∈ List.range input.accelerators.length := by
      simp only [List.mem_range]
      omega
    refine ⟨{ id := "ac" ++ toString i, exclusive := false }, ?_, hid.symm⟩
    unfold Elegant.Kinds.Wardley.expectedBoxes
    simp only [List.mem_append, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨i, hi', rfl⟩)))))
  · obtain ⟨⟨force, i⟩, he, hid, _⟩ := hd
    have hi := List.snd_lt_of_mem_zipIdx he
    have hlen : (arrange c input).deaccelerators.length = input.deaccelerators.length := by
      simp [arrange]
    have hi' : i ∈ List.range input.deaccelerators.length := by
      simp only [List.mem_range]
      omega
    refine ⟨{ id := "de" ++ toString i, exclusive := false }, ?_, hid.symm⟩
    unfold Elegant.Kinds.Wardley.expectedBoxes
    simp only [List.mem_append, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.mem_map.mpr ⟨i, hi', rfl⟩))))))
  · obtain ⟨⟨point, i⟩, he, hid, _⟩ := han
    have hi := List.snd_lt_of_mem_zipIdx he
    have hlen : (arrange c input).annotations.length = input.annotations.length := by
      simp [arrange]
    have hi' : i ∈ List.range input.annotations.length := by
      simp only [List.mem_range]
      omega
    refine ⟨{ id := "an" ++ toString i, parent := "plot", exclusive := false }, ?_, hid.symm⟩
    unfold Elegant.Kinds.Wardley.expectedBoxes
    simp only [List.mem_append, or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.mem_map.mpr ⟨i, hi', rfl⟩)))))))

theorem wardley_c3 (m : Model) (result : Layered.FamilyResult)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    Validator.C3 result.scene.layoutDump := by
  obtain ⟨input, hd, hcons, _, _, hmarked, hs⟩ :=
    adapter_success_consistent m result.scene (layout_success_scene m result h).1
  obtain ⟨annotationBox, hboxes⟩ :=
    layoutWith_box_geometry (constants m) input m result.scene hs
  intro box hb hempty parent hp
  by_cases hplot : box.parent = "plot"
  · exact wardley_plot_parent_contains m result h box parent hb hplot hp
  obtain ⟨model, hm, hid, hparent, hr⟩ := hboxes box hb
  have hab : model.id ≠ "ab" := by
    intro heq
    exact hempty (wardley_annotation_box_parent m result h box hb (hid.trans heq))
  have hmodelPlot : model.id ≠ "plot" := by
    intro heq
    have hcheck := List.all_eq_true.mp hcons model hm
    have hroot : model.parent = "" := by
      have hfind : (Elegant.Kinds.Wardley.expectedBoxes input m).find?
          (fun b => b.id == model.id) =
          some ({ id := "plot", parent := "", exclusive := false } : ModelBox) := by
        unfold Elegant.Kinds.Wardley.expectedBoxes
        simp only [List.cons_append, List.nil_append, heq, List.find?_cons]
        rfl
      rw [hfind] at hcheck
      exact beq_iff_eq.mp hcheck
    exact hempty (hparent.trans hroot)
  have hlookup : (arrange (constants m).geometry input).lookup.rectangles[model.id]? =
      some box.rect := by
    unfold boxRect at hr
    simp only [hmodelPlot, hab, ↓reduceIte] at hr
    cases hl : (arrange (constants m).geometry input).lookup.rectangles[model.id]? with
    | none => simp [hl] at hr
    | some rect =>
        simp only [hl, Except.ok.injEq] at hr
        subst rect
        rfl
  obtain ⟨candidate, hc, hcid⟩ :=
    rectangle_expected_id input m (constants m).geometry model.id box.rect hlookup
  have hexpected : ∃ expected,
      (Elegant.Kinds.Wardley.expectedBoxes input m).find?
        (fun b => b.id == model.id) = some expected := by
    cases hf : (Elegant.Kinds.Wardley.expectedBoxes input m).find?
        (fun b => b.id == model.id) with
    | none =>
        have hnone := List.find?_eq_none.mp hf candidate hc
        exact False.elim (hnone (by simp [hcid]))
    | some expected => exact ⟨expected, rfl⟩
  obtain ⟨expected, he⟩ := hexpected
  have heMem := List.mem_of_find?_eq_some he
  have heId : expected.id = model.id := by
    have heq := List.find?_some (p := fun b : ModelBox => b.id == model.id) he
    exact beq_iff_eq.mp heq
  have heParent := modelConsistent_parent input m model expected hcons hm he
  have heEmpty : expected.parent ≠ "" := by
    intro heq
    exact hempty (hparent.trans (heParent.trans heq))
  have hePlot : expected.parent ≠ "plot" := by
    intro heq
    exact hplot (hparent.trans (heParent.trans heq))
  obtain ⟨i, node, k, pipeline, hn, hflag, hk, hi, hni, hpk⟩ :=
    expected_nonplot_parent input m expected heMem heEmpty hePlot
  have hnodeId : model.id = "n" ++ toString i := heId.symm.trans hni
  have hparentId : box.parent = "pl" ++ toString k :=
    hparent.trans (heParent.trans hpk)
  have hnodeRect : box.rect =
      nodeRect (((arrange (constants m).geometry input).positions[i]?).getD ⟨0, 0⟩) := by
    rw [hnodeId, arrange_node_rectangle (constants m).geometry input i node hn] at hlookup
    exact (Option.some.inj hlookup).symm
  have hpmem : parent ∈ result.scene.boxes := List.mem_of_find?_eq_some hp
  have hpId : parent.id = box.parent := by
    have heq := List.find?_some (p := fun b : Box => b.id == box.parent) hp
    exact beq_iff_eq.mp heq
  obtain ⟨pm, _, hpmid, _, hpr⟩ := hboxes parent hpmem
  have hpm : pm.id = "pl" ++ toString k :=
    hpmid.symm.trans (hpId.trans hparentId)
  have hplPlot : "pl" ++ toString k ≠ "plot" :=
    Elegant.Kinds.Wardley.pl_toString_ne_plot
  have hplAb : "pl" ++ toString k ≠ "ab" := by
    intro heq
    have hh := congrArg (fun s : String => s.toList.head?) heq
    simp at hh
  have hpRect : parent.rect =
      (pipelineGeometry (constants m).geometry (arrange (constants m).geometry input).plot
        (arrange (constants m).geometry input).base pipeline).1 := by
    simp only [boxRect, hpm, hplPlot, hplAb, ↓reduceIte,
      arrange_pipeline_rectangle (constants m).geometry input k pipeline hk,
      Except.ok.injEq] at hpr
    exact hpr.symm
  rw [hpRect, hnodeRect]
  exact arranged_pipeline_contains_unmarked_child m input pipeline i node
    hmarked hn hflag hi

theorem wardley_valid (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : Elegant.Kinds.Wardley.layout m = .ok result) :
    HardConstraints result.scene.layoutDump := by
  exact wardley_valid_of_remaining_clauses m result hwf hlimits h
    (wardley_c1 m result h) (wardley_c3 m result h) (wardley_c5 m result hwf h)

end Elegant.Chart.Wardley
