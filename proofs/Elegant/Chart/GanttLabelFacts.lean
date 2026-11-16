import Elegant.Chart.GanttFacts
import Elegant.Kinds.Gantt

set_option autoImplicit false

namespace Elegant.Chart.Gantt

private theorem labelFacts_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem labelFacts_mapM_mem {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (bs : List β), l.mapM f = .ok bs → ∀ b ∈ bs, ∃ a ∈ l, f a = .ok b := by
  intro l
  induction l with
  | nil =>
    intro bs h b hb
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hb
  | cons a as ih =>
    intro bs h b hb
    rw [List.mapM_cons] at h
    obtain ⟨b1, hfa, h⟩ := labelFacts_bind_ok h
    obtain ⟨bs1, hrest, h⟩ := labelFacts_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), hfa⟩
    · obtain ⟨x, hx, hfx⟩ := ih bs1 hrest b hb'
      exact ⟨x, List.mem_cons.mpr (Or.inr hx), hfx⟩

/-- Every dumped box of a successful Gantt layout comes from a model box with the same
exclusivity flag and role token. -/
theorem gantt_scene_boxes_origin (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) :
    ∀ box ∈ result.scene.layoutDump.boxes, ∃ b ∈ m.boxes,
      box.exclusive = b.exclusive ∧ box.role = b.role.id := by
  rcases Kinds.Gantt.successful_scene m result h with
    ⟨p, boxes, labels, excluded, _, hb, _, _, hs, _, _⟩
  have hbox : result.scene.layoutDump.boxes = boxes := by
    rw [hs]
    rfl
  rw [hbox]
  intro box hmem
  obtain ⟨a, ha, hfa⟩ := labelFacts_mapM_mem _ _ _ hb box hmem
  obtain ⟨_, _, hp⟩ := labelFacts_bind_ok hfa
  simp only [pure, Except.pure, Except.ok.injEq] at hp
  subst hp
  exact ⟨a, ha, rfl, rfl⟩

/-- C7 for a successful Gantt layout whose model boxes are all non-exclusive. The Go and Rust
frontends emit Gantt boxes with `Exclusive` unset (`internal/layout/chart/gantt.go`,
`dumpBoxes`), so this is a frontend invariant. Without it C7 fails: a task label sits inside
its own exclusive owner box. -/
theorem gantt_c7 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result)
    (hne : ∀ b ∈ m.boxes, b.exclusive = false) :
    Validator.C7 result.scene.layoutDump := by
  intro l _ b hb hex
  obtain ⟨a, ha, he, _⟩ := gantt_scene_boxes_origin m result h b hb
  cases (hex.symm.trans (he.trans (hne a ha)))

/-- C8 for a successful Gantt layout whose model boxes all have role `node`. The frontends emit
every Gantt box with role node (`internal/layout/chart/gantt.go`, `dumpBoxes`), so no group
frame exists and both C8 conditions are vacuous. -/
theorem gantt_c8 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result)
    (hnode : ∀ b ∈ m.boxes, b.role = BoxRole.node) :
    Validator.C8 result.scene.layoutDump := by
  have hrole : ∀ g ∈ result.scene.layoutDump.boxes, g.role ≠ "group" := by
    intro g hg hgr
    obtain ⟨a, ha, _, hr⟩ := gantt_scene_boxes_origin m result h g hg
    have hn : g.role = "node" := hr.trans (congrArg BoxRole.id (hnode a ha))
    exact absurd (hn.symm.trans hgr) (by simp)
  refine ⟨?_, ?_⟩
  · intro g hg hgr
    exact absurd hgr (hrole g hg)
  · intro g hg hgr
    exact absurd hgr (hrole g hg)

end Elegant.Chart.Gantt
