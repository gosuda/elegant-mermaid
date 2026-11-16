theorem endpoint_lookup (g : Geometry) (id : String) (point : Point)
    (h : endpoint g id = .ok point) : g.lookup.points[id]? = some point := by
  unfold endpoint at h
  cases hp : g.lookup.points[id]? with
  | none => simp [hp] at h
  | some value =>
      simp only [hp, Except.ok.injEq] at h
      subst value
      rfl

theorem endpoint_declaration (c : GeometryConstants) (input : Input)
    (id : String) (point : Point)
    (h : endpoint (arrange c input) id = .ok point) :
    (∃ entry ∈ (input.nodes.zip (arrange c input).positions).zipIdx,
      id = "n" ++ toString entry.2 ∧ point = entry.1.2) ∨
    (∃ entry ∈ (arrange c input).ghosts.zipIdx,
      id = "tg" ++ toString entry.2 ∧ point = entry.1) :=
  arrange_lookup_points_sound c input id point (endpoint_lookup _ _ _ h)
