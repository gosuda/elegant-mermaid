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

theorem gantt_scene_boxes_origin (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) :
    ∃ p : Plan, prepare m = .ok p ∧
      result.scene.canvas = ⟨p.c.width, p.height⟩ ∧
      ∀ box ∈ result.scene.layoutDump.boxes, ∃ b ∈ m.boxes,
        p.boxRect b = .ok box.rect ∧ box.id = b.id ∧ box.parent = b.parent ∧
        box.exclusive = b.exclusive ∧ box.role = b.role.id := by
  rcases Kinds.Gantt.successful_scene m result h with
    ⟨p, boxes, labels, excluded, hp, hb, _, _, hs, _, _⟩
  refine ⟨p, hp, ?_, ?_⟩
  · rw [hs]
    rfl
  · have hbox : result.scene.layoutDump.boxes = boxes := by rw [hs]; rfl
    rw [hbox]
    intro box hmem
    obtain ⟨a, ha, hfa⟩ := labelFacts_mapM_mem _ _ _ hb box hmem
    obtain ⟨r, hr, hpure⟩ := labelFacts_bind_ok hfa
    simp only [pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    exact ⟨a, ha, hr, rfl, rfl, rfl, rfl⟩

theorem gantt_c1 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) : Validator.C1 result.scene.layoutDump := by
  obtain ⟨p, hp, hcanvas, horigin⟩ := gantt_scene_boxes_origin m result h
  obtain ⟨c, hload, hpc, _⟩ := prepare_decompose m p hp
  have hc := Kinds.Gantt.successful_constants m result h
  rw [hload] at hc
  rw [← hpc] at hc
  have hplot : (Validator.canvasRect result.scene.layoutDump).Contained p.plot := by
    simp only [Validator.canvasRect, Scene.layoutDump, hcanvas, Plan.plot,
      Plan.height, Plan.axisY, Rect.Contained]
    omega
  intro box hb
  obtain ⟨b, hbm, hr, _⟩ := horigin box hb
  exact hplot.trans (successful_box_inside_plot m result h p hp b hbm box.rect hr)

theorem gantt_c3 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) : Validator.C3 result.scene.layoutDump := by
  obtain ⟨p, hp, _, horigin⟩ := gantt_scene_boxes_origin m result h
  intro box hb hnon parent hlookup
  obtain ⟨b, hbm, hr, _, hpar, _⟩ := horigin box hb
  have hparent := Kinds.Gantt.successful_box_parent m result h b hbm
  have hparentplot : box.parent = "plot" := by
    rcases hparent with ⟨_, hempty⟩ | ⟨_, hplot⟩
    · exact False.elim (hnon (hpar.trans hempty))
    · exact hpar.trans hplot
  unfold LayoutDump.box? at hlookup
  have hpmem := List.mem_of_find?_eq_some hlookup
  have hpid : parent.id = box.parent := by
    simpa only [beq_iff_eq] using List.find?_some hlookup
  obtain ⟨pb, hpb, hrect, hsourceid, _⟩ := horigin parent hpmem
  have hpbid : pb.id = "plot" := hsourceid.symm.trans (hpid.trans hparentplot)
  have hplotrect : parent.rect = p.plot := by
    unfold Plan.boxRect at hrect
    simp only [hpbid, beq_self_eq_true, ite_true, Bind.bind, Except.bind,
      pure, Except.pure] at hrect
    split at hrect
    · exact (Except.ok.inj hrect).symm
    · cases hrect
  rw [hplotrect]
  exact successful_box_inside_plot m result h p hp b hbm box.rect hr

theorem gantt_c7 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) :
    Validator.C7 result.scene.layoutDump := by
  obtain ⟨_, _, _, horigin⟩ := gantt_scene_boxes_origin m result h
  intro l _ b hb hex
  obtain ⟨a, ha, _, _, _, he, _⟩ := horigin b hb
  have hfalse := (Kinds.Gantt.successful_supported_box m result h a ha).2
  cases (hex.symm.trans (he.trans hfalse))

theorem gantt_c8 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) :
    Validator.C8 result.scene.layoutDump := by
  obtain ⟨_, _, _, horigin⟩ := gantt_scene_boxes_origin m result h
  have hrole : ∀ g ∈ result.scene.layoutDump.boxes, g.role ≠ "group" := by
    intro g hg hgr
    obtain ⟨a, ha, _, _, _, _, hr⟩ := horigin g hg
    have hn : g.role = "node" := hr.trans (congrArg BoxRole.id
      (Kinds.Gantt.successful_supported_box m result h a ha).1)
    exact absurd (hn.symm.trans hgr) (by simp)
  refine ⟨?_, ?_⟩
  · intro g hg hgr
    exact absurd hgr (hrole g hg)
  · intro g hg hgr
    exact absurd hgr (hrole g hg)

theorem gantt_valid (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) : HardConstraints result.scene.layoutDump :=
  ⟨gantt_c1 m result h, gantt_c2 m result h, gantt_c3 m result h,
    Kinds.Gantt.gantt_c4 m result h, Kinds.Gantt.gantt_c5 m result h,
    Kinds.Gantt.gantt_c6 m result h, gantt_c7 m result h, gantt_c8 m result h⟩

end Elegant.Chart.Gantt
