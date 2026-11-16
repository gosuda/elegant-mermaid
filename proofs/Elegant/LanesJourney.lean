theorem admitted_section_interval (g : Input) (band first last : Nat)
    (h : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first ≤ k ∧ k ≤ last) == (t.band == (band : Int))) = true)
    {t : Task} {i : Nat} (hi : (t, i) ∈ g.tasks.zipIdx) :
    (first ≤ i ∧ i ≤ last) ↔ t.band = (band : Int) := by
  have ht := (List.all_eq_true.mp h) (t, i) hi
  have he : decide (first ≤ i ∧ i ≤ last) = (t.band == (band : Int)) :=
    beq_iff_eq.mp ht
  constructor
  · intro hin
    have hd : decide (first ≤ i ∧ i ≤ last) = true := by simp [hin]
    rw [he] at hd
    exact beq_iff_eq.mp hd
  · intro hb
    have hd : (t.band == (band : Int)) = true := beq_iff_eq.mpr hb
    rw [← he] at hd
    exact of_decide_eq_true hd

theorem admitted_section_contains_task (g : Input) (c : Constants)
    (band first last : Nat) (top taskTop height dx dy : Int)
    (h : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first ≤ k ∧ k ≤ last) == (t.band == (band : Int))) = true)
    (hc : 0 ≤ c.taskWidth + c.columnGap) (htop : top ≤ taskTop)
    {t : Task} {i : Nat} (hi : (t, i) ∈ g.tasks.zipIdx)
    (hb : t.band = (band : Int)) :
    (shiftRect dx dy (sectionRect c top (taskTop + height - top) first last)).Contained
      (shiftRect dx dy (taskRect c taskTop height i)) := by
  obtain ⟨hf, hl⟩ := (admitted_section_interval g band first last h hi).mpr hb
  exact journey_origin_preserves_containment _ _ dx dy
    (journey_frame_contains_task c top taskTop height first last i hc hf hl htop)

theorem journey_shifted_tasks_disjoint (c : Constants) (top height dx dy : Int)
    (i j : Nat) (hp : 0 ≤ c.taskWidth + c.columnGap)
    (hg : 0 ≤ c.columnGap) (hij : i < j) :
    Disjoint (shiftRect dx dy (taskRect c top height i))
      (shiftRect dx dy (taskRect c top height j)) := by
  have h := journey_tasks_disjoint c top height i j hp hg hij
  unfold Disjoint Rect.meetsInterior shiftRect at *
  dsimp only at *
  omega

/-- The task array constructed by the adapter carries its source task index. -/
theorem journey_task_rect_mem (g : Input) (c : Constants) (top height : Int)
    {t : Task} {i : Nat} (hi : (t, i) ∈ g.tasks.zipIdx) :
    taskRect c top height i ∈
      (g.tasks.zipIdx.map fun (_, k) => taskRect c top height k) := by
  exact List.mem_map.mpr ⟨(t, i), hi, rfl⟩

theorem journey_task_faces_score_order (c : Constants) (bottom dy : Int)
    (a b : Int) (hp : 0 ≤ c.scoreStep) (hab : a ≤ b) :
    faceY c bottom b + dy ≤ faceY c bottom a + dy := by
  have h := journey_score_antitone c bottom a b hp hab
  omega

theorem journey_card_contains_people (c : Constants) (card : Rect)
    (captionHeight peopleHeight : Int)
    (hpad : 0 ≤ c.padX) (hcaption : 0 ≤ captionHeight)
    (hheight : captionHeight + peopleHeight ≤ card.h) :
    let block := centred c card (captionHeight + peopleHeight)
    card.Contained { block with y := block.y + captionHeight, h := peopleHeight } := by
  have hhalf : 0 ≤ half (card.h - (captionHeight + peopleHeight)) ∧
      half (card.h - (captionHeight + peopleHeight)) ≤
        card.h - (captionHeight + peopleHeight) := by
    unfold half
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
    omega
  dsimp only [centred, Rect.Contained]
  omega

theorem journey_task_disjoint_foreign_section (c : Constants)
    (top frameHeight taskTop taskHeight : Int) (first last i : Nat)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hg : 0 ≤ c.columnGap)
    (hout : i < first ∨ last < i) :
    Disjoint (sectionRect c top frameHeight first last)
      (taskRect c taskTop taskHeight i) := by
  rcases hout with hi | hi
  · have hm := Int.mul_le_mul_of_nonneg_right
      (show (i : Int) + 1 ≤ first by omega) hp
    unfold sectionRect taskRect column Disjoint Rect.meetsInterior
    simp only [Int.add_mul, Int.one_mul] at hm
    dsimp only
    omega
  · have hm := Int.mul_le_mul_of_nonneg_right
      (show (last : Int) + 1 ≤ i by omega) hp
    unfold sectionRect taskRect column Disjoint Rect.meetsInterior
    simp only [Int.sub_mul, Int.add_mul, Int.one_mul] at *
    omega

theorem journey_shifted_task_disjoint_foreign_section (c : Constants)
    (top frameHeight taskTop taskHeight dx dy : Int) (first last i : Nat)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hg : 0 ≤ c.columnGap)
    (hout : i < first ∨ last < i) :
    Disjoint (shiftRect dx dy (sectionRect c top frameHeight first last))
      (shiftRect dx dy (taskRect c taskTop taskHeight i)) := by
  have h := journey_task_disjoint_foreign_section c top frameHeight taskTop
    taskHeight first last i hp hg hout
  unfold Disjoint Rect.meetsInterior shiftRect at *
  dsimp only at *
  omega

theorem admitted_section_disjoint_foreign_task (g : Input) (c : Constants)
    (band first last : Nat) (top frameHeight taskTop taskHeight dx dy : Int)
    (h : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first ≤ k ∧ k ≤ last) == (t.band == (band : Int))) = true)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hg : 0 ≤ c.columnGap)
    {t : Task} {i : Nat} (hi : (t, i) ∈ g.tasks.zipIdx)
    (hb : t.band ≠ (band : Int)) :
    Disjoint (shiftRect dx dy (sectionRect c top frameHeight first last))
      (shiftRect dx dy (taskRect c taskTop taskHeight i)) := by
  have hout : ¬ (first ≤ i ∧ i ≤ last) := by
    intro hin
    exact hb ((admitted_section_interval g band first last h hi).mp hin)
  exact journey_shifted_task_disjoint_foreign_section c top frameHeight taskTop
    taskHeight dx dy first last i hp hg (by omega)

theorem journey_union_contains_left (a b : Rect) :
    (Rect.unionRaw a b).Contained a := by
  unfold Rect.unionRaw Rect.Contained
  dsimp only
  omega

theorem journey_union_contains_right (a b : Rect) :
    (Rect.unionRaw a b).Contained b := by
  unfold Rect.unionRaw Rect.Contained
  dsimp only
  omega

theorem journey_extent_contains (rs : List Rect) (seed : Rect) :
    (rs.foldl Rect.unionRaw seed).Contained seed ∧
      ∀ r ∈ rs, (rs.foldl Rect.unionRaw seed).Contained r := by
  induction rs generalizing seed with
  | nil =>
    exact ⟨Rect.Contained.refl seed, by simp⟩
  | cons a rest ih =>
    obtain ⟨hseed, hrest⟩ := ih (Rect.unionRaw seed a)
    constructor
    · exact hseed.trans (journey_union_contains_left seed a)
    · intro r hr
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact hseed.trans (journey_union_contains_right seed a)
      · exact hrest r hr

theorem journey_shifted_extent_contains (ext r : Rect) (margin : Int)
    (hm : 0 ≤ margin) (hr : ext.Contained r) :
    (⟨0, 0, ext.w + 2 * margin, ext.h + 2 * margin⟩ : Rect).Contained
      (shiftRect (margin - ext.x) (margin - ext.y) r) := by
  unfold Rect.Contained shiftRect at *
  dsimp only at *
  omega

theorem journey_shifted_extent_member (seed : Rect) (rs : List Rect)
    (r : Rect) (margin : Int) (hm : 0 ≤ margin)
    (hr : r ∈ seed :: rs) :
    let ext := rs.foldl Rect.unionRaw seed
    (⟨0, 0, ext.w + 2 * margin, ext.h + 2 * margin⟩ : Rect).Contained
      (shiftRect (margin - ext.x) (margin - ext.y) r) := by
  apply journey_shifted_extent_contains _ _ margin hm
  rcases List.mem_cons.mp hr with hr | hr
  · subst r
    exact (journey_extent_contains rs seed).1
  · exact (journey_extent_contains rs seed).2 r hr

theorem journey_shifted_people_inside_extent (c : Constants)
    (ext card : Rect) (captionHeight peopleHeight : Int)
    (hext : ext.Contained card) (hm : 0 ≤ c.margin)
    (hpad : 0 ≤ c.padX) (hcaption : 0 ≤ captionHeight)
    (hheight : captionHeight + peopleHeight ≤ card.h) :
    let block := centred c card (captionHeight + peopleHeight)
    (⟨0, 0, ext.w + 2 * c.margin, ext.h + 2 * c.margin⟩ : Rect).Contained
      (shiftRect (c.margin - ext.x) (c.margin - ext.y)
        { block with y := block.y + captionHeight, h := peopleHeight }) := by
  apply journey_shifted_extent_contains ext _ c.margin hm
  exact hext.trans
    (journey_card_contains_people c card captionHeight peopleHeight
      hpad hcaption hheight)

theorem journey_contained_disjoint_right (frame card people : Rect)
    (hc : card.Contained people) (hd : Disjoint frame card) :
    Disjoint frame people := by
  unfold Rect.Contained at hc
  unfold Disjoint Rect.meetsInterior at *
  omega

theorem journey_people_disjoint_foreign_section (g : Input) (c : Constants)
    (band first last : Nat) (top frameHeight taskTop taskHeight dx dy : Int)
    (h : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first ≤ k ∧ k ≤ last) == (t.band == (band : Int))) = true)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hg : 0 ≤ c.columnGap)
    {t : Task} {i : Nat} (hi : (t, i) ∈ g.tasks.zipIdx)
    (hb : t.band ≠ (band : Int)) (people : Rect)
    (hc : (taskRect c taskTop taskHeight i).Contained people) :
    Disjoint (shiftRect dx dy (sectionRect c top frameHeight first last))
      (shiftRect dx dy people) := by
  exact journey_contained_disjoint_right _ _ _
    (journey_origin_preserves_containment _ _ dx dy hc)
    (admitted_section_disjoint_foreign_task g c band first last
      top frameHeight taskTop taskHeight dx dy h hp hg hi hb)

theorem journey_people_inside_section (g : Input) (c : Constants)
    (band first last : Nat) (top taskTop taskHeight dx dy : Int)
    (h : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first ≤ k ∧ k ≤ last) == (t.band == (band : Int))) = true)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (htop : top ≤ taskTop)
    {t : Task} {i : Nat} (hi : (t, i) ∈ g.tasks.zipIdx)
    (hb : t.band = (band : Int)) (people : Rect)
    (hc : (taskRect c taskTop taskHeight i).Contained people) :
    (shiftRect dx dy (sectionRect c top (taskTop + taskHeight - top) first last)).Contained
      (shiftRect dx dy people) := by
  exact (admitted_section_contains_task g c band first last
    top taskTop taskHeight dx dy h hp htop hi hb).trans
      (journey_origin_preserves_containment _ _ dx dy hc)
