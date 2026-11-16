import Elegant.Lanes

set_option autoImplicit false
namespace Elegant.Lanes.Journey

structure Constants where
  taskWidth : Int
  taskHeight : Int
  bandHeight : Int
  columnGap : Int
  scoreStep : Int
  radius : Int
  padX : Int
  padY : Int
  corner : Int
  margin : Int

def constants (p : Profile) : Constants :=
  { taskWidth := LayoutConst.journey_task_width.get p
    taskHeight := LayoutConst.journey_task_height.get p
    bandHeight := LayoutConst.journey_band_height.get p
    columnGap := LayoutConst.journey_column_gap.get p
    scoreStep := LayoutConst.journey_score_step.get p
    radius := LayoutConst.journey_face_radius.get p
    padX := LayoutConst.node_pad_x.get p + LayoutConst.node_border.get p
    padY := LayoutConst.node_pad_y.get p + LayoutConst.node_border.get p
    corner := LayoutConst.corner_radius.get p
    margin := LayoutConst.canvas_margin.get p }

structure Card where
  id : String
  caption : Caption

structure Task extends Card where
  band : Int
  score : Int
  people : Option Caption := none

structure Input where
  title : Option Card := none
  sections : List Card := []
  tasks : List Task := []

def column (c : Constants) (i : Int) : Int := i * (c.taskWidth + c.columnGap)
def faceY (c : Constants) (bottom score : Int) : Int :=
  bottom + (5 - score) * c.scoreStep + c.scoreStep

theorem journey_task_columns_ordered (c : Constants) (i j : Int)
    (hp : 0 < c.taskWidth + c.columnGap) (h : i < j) : column c i < column c j := by
  unfold column
  exact Int.mul_lt_mul_of_pos_right h hp

theorem journey_score_antitone (c : Constants) (bottom a b : Int)
    (hp : 0 ≤ c.scoreStep) (h : a ≤ b) : faceY c bottom b ≤ faceY c bottom a := by
  unfold faceY
  have hm := Int.mul_le_mul_of_nonneg_right (show 5 - b ≤ 5 - a by omega) hp
  omega

def taskRect (c : Constants) (top height : Int) (i : Nat) : Rect :=
  ⟨column c i, top, c.taskWidth, height⟩
def sectionRect (c : Constants) (top height : Int) (first last : Nat) : Rect :=
  ⟨column c first, top, column c (last - first : Int) + c.taskWidth, height⟩

theorem journey_task_inside_section (c : Constants) (top height : Int) (first last i : Nat)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hf : first ≤ i) (hl : i ≤ last) :
    (sectionRect c top height first last).Contained (taskRect c top height i) := by
  have h₁ := Int.mul_le_mul_of_nonneg_right (show (first : Int) ≤ i by omega) hp
  have h₂ := Int.mul_le_mul_of_nonneg_right (show (i : Int) ≤ last by omega) hp
  unfold sectionRect taskRect column Rect.Contained
  simp only [Int.sub_mul]
  omega

theorem journey_frame_contains_task (c : Constants) (top taskTop height : Int)
    (first last i : Nat) (hp : 0 ≤ c.taskWidth + c.columnGap)
    (hf : first ≤ i) (hl : i ≤ last) (ht : top ≤ taskTop) :
    (sectionRect c top (taskTop + height - top) first last).Contained
      (taskRect c taskTop height i) := by
  have h₁ := Int.mul_le_mul_of_nonneg_right (show (first : Int) ≤ i by omega) hp
  have h₂ := Int.mul_le_mul_of_nonneg_right (show (i : Int) ≤ last by omega) hp
  unfold sectionRect taskRect column Rect.Contained
  simp only [Int.sub_mul]
  omega

theorem journey_origin_preserves_containment (outer inner : Rect) (dx dy : Int)
    (h : outer.Contained inner) :
    (shiftRect dx dy outer).Contained (shiftRect dx dy inner) := by
  unfold shiftRect Rect.Contained at *
  dsimp only at *
  omega

theorem journey_section_bands_disjoint (c : Constants) (top h : Int) (a b d e : Nat)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hg : 0 ≤ c.columnGap) (_hab : a ≤ b)
    (hbd : b < d) :
    Disjoint (sectionRect c top h a b) (sectionRect c top h d e) := by
  have hm := Int.mul_le_mul_of_nonneg_right (show (b : Int) + 1 ≤ d by omega) hp
  unfold sectionRect column Disjoint Rect.meetsInterior
  simp only [Int.sub_mul, Int.add_mul] at *
  omega

theorem journey_tasks_disjoint (c : Constants) (top height : Int) (i j : Nat)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hg : 0 ≤ c.columnGap) (hij : i < j) :
    Disjoint (taskRect c top height i) (taskRect c top height j) := by
  have hm := Int.mul_le_mul_of_nonneg_right (show (i : Int) + 1 ≤ j by omega) hp
  unfold taskRect column Disjoint Rect.meetsInterior
  simp only [Int.add_mul] at *
  omega

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

def centred (c : Constants) (r : Rect) (h : Int) : Rect :=
  ⟨r.x + c.padX, r.y + half (r.h - h), r.w - 2 * c.padX, h⟩

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

def face (p : Profile) (c : Constants) (pos : Point) (score : Int) : List Primitive :=
  if p == .cell then [.symbolRef "ring" pos "ink-line"] else
  let third := Int.fdiv c.radius 3
  let eye := max (Int.fdiv c.radius 6) 1
  let y := pos.y + Int.fdiv (7 * c.radius) 15
  let mouth := if score == 3 then
      Primitive.polyline [⟨pos.x - third, y⟩, ⟨pos.x + third, y⟩] 0 (plain "ink-line")
    else
      let cy := pos.y + Int.fdiv ((if score > 3 then 2 else 7) * c.radius) 15
      let r := Int.fdiv c.radius 2
      Primitive.path [.M ⟨pos.x + r, cy⟩,
        .A ⟨pos.x, cy⟩ r 0 (if score > 3 then 32768 else -32768)] (plain "ink-line")
  [.ellipse pos.x pos.y c.radius c.radius (plain "ink-line"),
   .ellipse (pos.x - third) (pos.y - third) eye eye (plain "ink"),
   .ellipse (pos.x + third) (pos.y - third) eye eye (plain "ink"), mouth]

end Elegant.Lanes.Journey
