import Elegant.Treeview
import Elegant.Kinds.Common

namespace Elegant.Kinds.Treeview

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if m.boxes.length > m.options.limits.maxNodes then
    throw (.tooLarge m.options.limits.maxNodes m.boxes.length)
  let bytes := m.labels.foldl (fun n l => n + l.text.utf8ByteSize) 0
  if bytes > m.options.limits.maxTextBytes then
    throw (.tooLarge m.options.limits.maxTextBytes bytes)
  match Elegant.Treeview.layout m with
  | .error error => throw (.geometry error)
  | .ok scene => pure { scene := scene, budgetExhausted := false }

/-- Public success is success of the same native scene, not of a replacement
    tree or a scene with rewritten containment metadata. -/
theorem successful_native_layout {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    Elegant.Treeview.layout m = .ok result.scene := by
  by_cases hnodes : m.boxes.length > m.options.limits.maxNodes
  · simp [layout, hnodes, throw, Bind.bind, Except.bind] at h
  · by_cases htext :
        m.labels.foldl (fun n l => n + l.text.utf8ByteSize) 0 >
          m.options.limits.maxTextBytes
    · simp [layout, hnodes, htext, throw, Bind.bind, Except.bind] at h
    · simp only [layout, hnodes, htext, ↓reduceIte] at h
      cases hn : Elegant.Treeview.layout m with
      | error e => simp [hn] at h
      | ok scene =>
        simp only [hn, pure, Except.pure, Except.ok.injEq] at h
        subst result
        rfl

theorem successful_empty_parents {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    m.boxes.any (fun b => b.parent != "") = false :=
  Elegant.Treeview.successful_layout_empty_parents (successful_native_layout h)

/-- The public adapter exposes exactly the metrics and rows admitted by the
    executed geometry kernel. -/
theorem successful_rows {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∃ p rs, Elegant.Treeview.metrics m = .ok p ∧
      Elegant.Treeview.rows m = .ok rs ∧
      1 ≤ p.textHeight ∧ 0 ≤ p.paddingX ∧ 0 ≤ p.paddingY ∧
      0 ≤ p.rowIndent :=
  Elegant.Treeview.successful_layout_rows (successful_native_layout h)

theorem successful_row_invariants {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∃ p rs, Elegant.Treeview.metrics m = .ok p ∧
      Elegant.Treeview.rows m = .ok rs ∧
      Elegant.Treeview.RowsInvariant rs.toArray ∧
      1 ≤ p.textHeight ∧ 0 ≤ p.paddingX ∧ 0 ≤ p.paddingY ∧
      0 ≤ p.rowIndent := by
  obtain ⟨p, rs, hp, hr, ht, hx, hy, hi⟩ := successful_rows h
  exact ⟨p, rs, hp, hr, Elegant.Treeview.successful_rows_invariant hr,
    ht, hx, hy, hi⟩

theorem treeview_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump :=
  Elegant.Treeview.treeview_valid hwf hlimits (successful_native_layout h)


end Elegant.Kinds.Treeview
