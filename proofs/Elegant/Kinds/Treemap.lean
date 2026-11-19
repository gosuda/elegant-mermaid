import Elegant.Kinds.Common
import Elegant.Chart.TreemapAdapter

namespace Elegant.Kinds.Treemap

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if m.boxes.length > m.options.limits.maxNodes then
    throw (.tooLarge m.options.limits.maxNodes m.boxes.length)
  let bytes := m.labels.foldl (fun n l => n + l.text.utf8ByteSize) 0
  if bytes > m.options.limits.maxTextBytes then
    throw (.tooLarge m.options.limits.maxTextBytes bytes)
  if (Elegant.Treemap.constants m).width < 0 then
    throw (.geometry .domain)
  if (Elegant.Treemap.constants m).height < 0 then
    throw (.geometry .domain)
  if m.boxes.any (fun box => box.id == "") then
    throw (.geometry .domain)
  if !(Elegant.Treemap.labelIdsNameOwner m) then
    throw (.geometry .domain)
  match Elegant.Treemap.layout m with
  | .error e => throw (.geometry e)
  | .ok scene => pure { scene, budgetExhausted := false }

theorem layout_adapter_success (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    Elegant.Treemap.layout m = .ok result.scene := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok (Common.guarded_ok
    (Common.guarded_ok (Common.guarded_ok (Common.guarded_ok h)))))
  cases hs : Elegant.Treemap.layout m with
  | error e => simp [hs] at h
  | ok scene =>
    simp only [hs, pure, Except.pure, Except.ok.injEq] at h
    cases h
    rfl

theorem layout_width_nonnegative (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : 0 ≤ (Elegant.Treemap.constants m).width := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok h)
  by_cases hw : (Elegant.Treemap.constants m).width < 0
  · exact (Common.guarded_error hw h).elim
  · omega

theorem layout_height_nonnegative (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : 0 ≤ (Elegant.Treemap.constants m).height := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok (Common.guarded_ok h))
  by_cases hh : (Elegant.Treemap.constants m).height < 0
  · exact (Common.guarded_error hh h).elim
  · omega

theorem layout_box_ids_nonempty (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : ∀ box ∈ m.boxes, box.id ≠ "" := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok (Common.guarded_ok
    (Common.guarded_ok h)))
  by_cases hany : m.boxes.any (fun box => box.id == "") = true
  · exact (Common.guarded_error hany h).elim
  · intro box hbox hid
    exact hany (List.any_eq_true.mpr ⟨box, hbox, by simp [hid]⟩)


theorem layout_label_ids_name_owner (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    ∀ label ∈ m.labels,
      label.id = label.owner ++ ".name" ∨ label.id = label.owner ++ ".value" ∨
        (label.id = "title" ∧ label.owner = "root") := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok (Common.guarded_ok
    (Common.guarded_ok (Common.guarded_ok h))))
  by_cases hbad : (!(Elegant.Treemap.labelIdsNameOwner m)) = true
  · rw [ite_eq_left hbad] at h
    cases h
  · have hx : Elegant.Treemap.labelIdsNameOwner m = true := by
      cases hb : Elegant.Treemap.labelIdsNameOwner m with
      | true => rfl
      | false => exact absurd (by simp [hb]) hbad
    intro label hlabel
    have hl := List.all_eq_true.mp hx label hlabel
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hl
    rcases hl with (hname | hvalue) | htitle
    · exact Or.inl hname
    · exact Or.inr (Or.inl hvalue)
    · exact Or.inr (Or.inr htitle)

theorem layout_routes_eq_nil (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : result.scene.layoutDump.routes = [] := by
  exact Elegant.Treemap.layout_routes_eq_nil m result.scene
    (layout_adapter_success m result h)

theorem treemap_c4 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C4 result.scene.layoutDump := by
  intro route hr
  rw [layout_routes_eq_nil m result h] at hr
  simp at hr

theorem treemap_c5 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C5 result.scene.layoutDump := by
  intro route hr
  rw [layout_routes_eq_nil m result h] at hr
  simp at hr

theorem treemap_c6 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C6 result.scene.layoutDump := by
  intro route hr
  rw [layout_routes_eq_nil m result h] at hr
  simp at hr

end Elegant.Kinds.Treemap
