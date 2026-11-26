import Elegant.Railroad
import Elegant.Chart.Scale

set_option autoImplicit false

namespace Elegant.Railroad

/-- The geometry used by placement and wrapper sizing has an exact baseline split. -/
theorem railroad_box_height_split (s : Shape) : s.up + s.down = s.height := rfl


/-- Choice placement centres a child in the maximum-width interior between the two rails. -/
theorem railroad_choice_inside (radius widest y : Int) (kid : Shape)
    (hw : kid.w ≤ widest) :
    2 * radius ≤ (choiceOffset radius widest y kid).x ∧
      (choiceOffset radius widest y kid).x + kid.w ≤ widest + 4 * radius - 2 * radius := by
  have h := Chart.fdiv_between (widest - kid.w) 2 0 (widest - kid.w)
    (by decide) (by omega) (by omega)
  simp only [choiceOffset]
  omega

/-- The offsets emitted by the sequence sizing fold put both child baselines on `up`.
The same fold advances the next child by exactly its predecessor's width plus the rail gap. -/
theorem railroad_rail_join (up gap x : Int) (left right : Shape) :
    (sequenceOffset up x left).y + left.up = up ∧
    (sequenceOffset up (sequenceAdvance gap x left) right).y + right.up = up ∧
    (sequenceOffset up (sequenceAdvance gap x left) right).x -
      ((sequenceOffset up x left).x + left.w) = gap := by
  simp only [sequenceOffset, sequenceAdvance]
  omega

theorem sequence_end_ge (up gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (x : Int),
      (∀ k ∈ kids, 0 ≤ k.w) → x ≤ (sequenceLayout up gap x kids).1 := by
  intro kids
  induction kids with
  | nil => intro x _; simp [sequenceLayout]
  | cons k ks ih =>
    intro x hk
    have hw := hk k (by simp)
    have ht := ih (sequenceAdvance gap x k) (fun a ha => hk a (by simp [ha]))
    simp only [sequenceLayout]
    simp only [sequenceAdvance] at *
    omega

/-- Every child emitted by the sequence sizing traversal fits vertically between the
common ascent and descent, and horizontally before the traversal's final rail gap. -/
theorem railroad_sequence_inside (up down gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (x : Int),
      (∀ k ∈ kids, 0 ≤ k.w ∧ k.up ≤ up ∧ k.down ≤ down) →
      ∀ pair ∈ kids.zip (sequenceLayout up gap x kids).2,
        0 ≤ pair.2.y ∧ pair.2.y + pair.1.height ≤ up + down ∧
          pair.2.x + pair.1.w ≤ (sequenceLayout up gap x kids).1 - gap := by
  intro kids
  induction kids with
  | nil => intro x _ pair hp; simp [sequenceLayout] at hp
  | cons k ks ih =>
    intro x hk pair hp
    have hhead := hk k (by simp)
    have htail : ∀ a ∈ ks, 0 ≤ a.w ∧ a.up ≤ up ∧ a.down ≤ down :=
      fun a ha => hk a (by simp [ha])
    simp only [sequenceLayout, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hend := sequence_end_ge up gap hg ks (sequenceAdvance gap x k)
        (fun a ha => (htail a ha).1)
      simp only [sequenceOffset, sequenceLayout, Shape.height]
      simp only [sequenceAdvance] at *
      omega
    · exact ih (sequenceAdvance gap x k) htail pair hp

theorem sequence_offsets_length (up gap : Int) :
    ∀ (kids : List Shape) (x : Int),
      (sequenceLayout up gap x kids).2.length = kids.length := by
  intro kids
  induction kids with
  | nil => intro x; rfl
  | cons k ks ih =>
    intro x
    simp only [sequenceLayout, List.length_cons]
    rw [ih]

theorem fold_max_bounds (value : Shape → Int) :
    ∀ (kids : List Shape) (initial : Int),
      initial ≤ kids.foldl (fun a k => max a (value k)) initial ∧
        ∀ k ∈ kids, value k ≤ kids.foldl (fun a k => max a (value k)) initial := by
  intro kids
  induction kids with
  | nil => intro initial; simp
  | cons k ks ih =>
    intro initial
    obtain ⟨hinit, htail⟩ := ih (max initial (value k))
    simp only [List.foldl_cons]
    refine ⟨Int.le_trans (Int.le_max_left _ _) hinit, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Int.le_trans (Int.le_max_right _ _) hinit
    · exact htail a ha

def Nonnegative (s : Shape) : Prop := 0 ≤ s.w ∧ 0 ≤ s.up ∧ 0 ≤ s.down

theorem spacing_nonnegative (p : Profile) :
    0 ≤ constant p "pad_x" ∧ 0 ≤ constant p "pad_y" ∧
    0 ≤ constant p "line_height" ∧ 0 ≤ constant p "arc_radius" ∧
    0 ≤ constant p "hsep" ∧ 0 ≤ constant p "vsep" := by
  cases p <;> decide

theorem half_split_nonnegative (height : Int) (hh : 0 ≤ height) :
    0 ≤ Int.fdiv height 2 ∧ 0 ≤ height - Int.fdiv height 2 := by
  have := Chart.fdiv_between height 2 0 height (by decide) (by omega) (by omega)
  omega

theorem leafShape_nonnegative (p : Profile) (n : Node) (width : Int) (hw : 0 ≤ width) :
    Nonnegative (leafShape p n width) := by
  obtain ⟨hx,hy,hl,_,_,_⟩ := spacing_nonnegative p
  have h := half_split_nonnegative (constant p "line_height" + 2 * constant p "pad_y")
    (by omega)
  simp only [Nonnegative, leafShape]
  exact ⟨by omega,h.1,h.2⟩

theorem sequenceShape_nonnegative (p : Profile) (n : Node) (kids : List Shape)
    (hne : kids ≠ []) (hk : ∀ k ∈ kids, Nonnegative k) :
    Nonnegative (sequenceShape p n kids) := by
  have hg := (spacing_nonnegative p).2.2.2.2.1
  have hup := (fold_max_bounds (fun k => k.up) kids 0).1
  have hdown := (fold_max_bounds (fun k => k.down) kids 0).1
  cases kids with
  | nil => exact False.elim (hne rfl)
  | cons k ks =>
    have hw := (hk k (by simp)).1
    have hend := sequence_end_ge
      ((k::ks).foldl (fun a k => max a k.up) 0) (constant p "hsep") hg ks
      (sequenceAdvance (constant p "hsep") 0 k)
      (fun a ha => (hk a (by simp [ha])).1)
    simp only [Nonnegative, sequenceShape, sequenceLayout]
    simp only [sequenceAdvance] at *
    exact ⟨by omega,hup,hdown⟩

theorem choice_end_ge (radius widest gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (y : Int),
      (∀ k ∈ kids, 0 ≤ k.height) → y ≤ (choiceLayout radius widest gap y kids).1 := by
  intro kids
  induction kids with
  | nil => intro y _; simp [choiceLayout]
  | cons k ks ih =>
    intro y hk
    have hh := hk k (by simp)
    have ht := ih (y+k.height+gap) (fun a ha => hk a (by simp [ha]))
    simp only [choiceLayout]
    omega

theorem choiceShape_nonnegative (p : Profile) (n : Node) (kids : List Shape)
    (hne : kids ≠ []) (hk : ∀ k ∈ kids, Nonnegative k) :
    Nonnegative (choiceShape p n kids) := by
  have hr := (spacing_nonnegative p).2.2.2.1
  have hg := (spacing_nonnegative p).2.2.2.2.2
  have hwidest := (fold_max_bounds (fun k => k.w) kids 0).1
  have hh : 0 ≤ (choiceLayout (constant p "arc_radius")
      (kids.foldl (fun a k => max a k.w) 0) (constant p "vsep") 0 kids).1 -
        constant p "vsep" := by
    cases kids with
    | nil => exact False.elim (hne rfl)
    | cons k ks =>
      have hhead := hk k (by simp)
      have hheight : 0 ≤ k.height := Int.add_nonneg hhead.2.1 hhead.2.2
      have hend := choice_end_ge (constant p "arc_radius")
        ((k::ks).foldl (fun a k => max a k.w) 0) (constant p "vsep") hg ks
        (0+k.height+constant p "vsep") (fun a ha => by
          have h := hk a (by simp [ha])
          exact Int.add_nonneg h.2.1 h.2.2)
      simp only [choiceLayout]
      omega
  have hsplit := half_split_nonnegative _ hh
  simp only [Nonnegative, choiceShape]
  exact ⟨by omega,hsplit.1,hsplit.2⟩

theorem wrapperShape_nonnegative (p : Profile) (n : Node) (kid : Shape)
    (hk : Nonnegative kid) : Nonnegative (wrapperShape p n kid) := by
  have hr := (spacing_nonnegative p).2.2.2.1
  unfold Nonnegative wrapperShape Shape.height at *
  split <;> split <;> simp only <;> omega

theorem sizeRaw_nonnegative (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (hk : ∀ k ∈ kids, Nonnegative k)
    (h : sizeRaw p metric n kids = .ok s) : Nonnegative s := by
  unfold sizeRaw at h
  split at h
  · split at h
    · cases h
    · cases hw : Measure.textWidth metric n.text.toList with
      | error e => simp [hw, bind, Except.bind] at h
      | ok width =>
        have hn := Measure.textWidth_nonneg hw
        simp only [hw, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst s
        exact leafShape_nonnegative p n width hn
  · split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst s
        apply sequenceShape_nonnegative p n kids
        · intro he
          subst kids
          simp_all
        · exact hk
    · split at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s
          apply choiceShape_nonnegative p n kids
          · intro he
            subst kids
            simp_all
          · exact hk
      · split at h
        · cases kids with
          | nil => cases h
          | cons kid tail =>
            cases tail with
            | nil =>
              simp only [Except.ok.injEq] at h
              subst s
              exact wrapperShape_nonnegative p n kid (hk kid (by simp))
            | cons second rest => cases h
        · cases h

theorem size_nonnegative (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (hk : ∀ k ∈ kids, Nonnegative k)
    (h : size p metric n kids = .ok s) : Nonnegative s := by
  unfold size at h
  cases hs : sizeRaw p metric n kids with
  | error e => simp [hs, bind, Except.bind] at h
  | ok raw =>
    have hn := sizeRaw_nonnegative p metric n kids raw hk hs
    simp only [hs, bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst s
      exact hn

theorem mapM_nonnegative {α : Type} (f : α → Except LayoutError Shape)
    (hf : ∀ a s, f a = .ok s → Nonnegative s) :
    ∀ (xs : List α) (ys : List Shape), xs.mapM f = .ok ys → ∀ s ∈ ys, Nonnegative s := by
  intro xs
  induction xs with
  | nil =>
    intro ys h s hs
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst ys
    simp at hs
  | cons a rest ih =>
    intro ys h s hs
    cases ha : f a with
    | error e => simp [List.mapM_cons,ha,bind,Except.bind] at h
    | ok first =>
      cases ht : rest.mapM f with
      | error e => simp [List.mapM_cons,ha,ht,bind,Except.bind] at h
      | ok tail =>
        have he : first :: tail = ys := by
          simpa [List.mapM_cons,ha,ht,bind,Except.bind,pure,Except.pure] using h
        subst ys
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hf a _ ha
        · exact ih tail ht s hs

/-- Every successful recursive sizing result has non-negative width, ascent and descent. -/
theorem railroad_box_nonneg :
    ∀ (fuel : Nat) (p : Profile) (metric : Measure.Metric) (n : Node) (s : Shape),
      measure fuel p metric n = .ok s → Nonnegative s := by
  intro fuel
  induction fuel with
  | zero => intro p metric n s h; cases h
  | succ fuel ih =>
    intro p metric n s h
    simp only [measure] at h
    cases hk : n.children.mapM (measure fuel p metric) with
    | error e => simp [hk,bind,Except.bind] at h
    | ok kids =>
      have hn := mapM_nonnegative (measure fuel p metric)
        (fun a s ha => ih p metric a s ha) n.children kids hk
      simp only [hk,bind,Except.bind] at h
      exact size_nonnegative p metric n kids s hn h

theorem sequenceShape_inside (p : Profile) (n : Node) (kids : List Shape)
    (hk : ∀ k ∈ kids, Nonnegative k) :
    ∀ pair ∈ kids.zip (sequenceShape p n kids).offsets,
      0 ≤ pair.2.y ∧
      pair.2.y + pair.1.height ≤ (sequenceShape p n kids).height ∧
      pair.2.x + pair.1.w ≤ (sequenceShape p n kids).w := by
  have hu := (fold_max_bounds (fun k => k.up) kids 0).2
  have hd := (fold_max_bounds (fun k => k.down) kids 0).2
  have hh := (spacing_nonnegative p).2.2.2.2.1
  simpa only [sequenceShape, Shape.height] using
    railroad_sequence_inside
      (kids.foldl (fun a k => max a k.up) 0)
      (kids.foldl (fun a k => max a k.down) 0)
      (constant p "hsep") hh kids 0
      (fun k hmem => ⟨(hk k hmem).1,hu k hmem,hd k hmem⟩)

theorem choice_offsets_horizontal (radius widest gap : Int) :
    ∀ (kids : List Shape) (y : Int),
      (∀ k ∈ kids, k.w ≤ widest) →
      ∀ pair ∈ kids.zip (choiceLayout radius widest gap y kids).2,
        2 * radius ≤ pair.2.x ∧ pair.2.x + pair.1.w ≤ widest + 2 * radius := by
  intro kids
  induction kids with
  | nil => intro y _ pair hp; simp [choiceLayout] at hp
  | cons k ks ih =>
    intro y hk pair hp
    simp only [choiceLayout,List.zip_cons_cons,List.mem_cons] at hp
    rcases hp with rfl | hp
    · have h := railroad_choice_inside radius widest y k (hk k (by simp))
      dsimp only
      exact ⟨h.1,by omega⟩
    · exact ih (y+k.height+gap) (fun a ha => hk a (by simp [ha])) pair hp

theorem choiceShape_inside (p : Profile) (n : Node) (kids : List Shape) :
    ∀ pair ∈ kids.zip (choiceShape p n kids).offsets,
      2 * constant p "arc_radius" ≤ pair.2.x ∧
      pair.2.x + pair.1.w ≤ (choiceShape p n kids).w - 2 * constant p "arc_radius" := by
  have h := choice_offsets_horizontal (constant p "arc_radius")
    (kids.foldl (fun a k => max a k.w) 0) (constant p "vsep") kids 0
    (fold_max_bounds (fun k => k.w) kids 0).2
  simpa only [choiceShape,show ∀ a b : Int, a + 4*b - 2*b = a+2*b by intros; omega] using h

theorem sequence_first_two (up gap x : Int) (left right : Shape) (rest : List Shape) :
    (sequenceLayout up gap x (left :: right :: rest)).2 =
      sequenceOffset up x left ::
        sequenceOffset up (sequenceAdvance gap x left) right ::
          (sequenceLayout up gap (sequenceAdvance gap (sequenceAdvance gap x left) right) rest).2 := by
  rfl

def Joined (up gap : Int) (a b : Shape × Point) : Prop :=
  a.2.y + a.1.up = up ∧ b.2.y + b.1.up = up ∧
    b.2.x - (a.2.x + a.1.w) = gap

def ConsecutiveJoins (up gap : Int) : List (Shape × Point) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Joined up gap a b ∧ ConsecutiveJoins up gap (b :: rest)

theorem sequence_all_rail_joins (up gap : Int) :
    ∀ (kids : List Shape) (x : Int),
      ConsecutiveJoins up gap (kids.zip (sequenceLayout up gap x kids).2) := by
  intro kids
  induction kids with
  | nil => intro x; trivial
  | cons left tail ih =>
    intro x
    cases tail with
    | nil => trivial
    | cons right rest =>
      constructor
      · exact railroad_rail_join up gap x left right
      · exact ih (sequenceAdvance gap x left)

theorem sequence_start_ge (up gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (x : Int),
      (∀ k ∈ kids, 0 ≤ k.w) →
      ∀ pair ∈ kids.zip (sequenceLayout up gap x kids).2, x ≤ pair.2.x := by
  intro kids
  induction kids with
  | nil => intro x _ pair hp; simp [sequenceLayout] at hp
  | cons k ks ih =>
    intro x hk pair hp
    simp only [sequenceLayout,List.zip_cons_cons,List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [sequenceOffset]
    · have ht := ih (sequenceAdvance gap x k)
        (fun a ha => hk a (by simp [ha])) pair hp
      have hw := hk k (by simp)
      simp only [sequenceAdvance] at *
      omega

theorem sequence_children_disjoint (up gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (x : Int),
      (∀ k ∈ kids, 0 ≤ k.w) →
      List.Pairwise (fun a b : Shape × Point => a.2.x+a.1.w ≤ b.2.x)
        (kids.zip (sequenceLayout up gap x kids).2) := by
  intro kids
  induction kids with
  | nil => intro x _; simp [sequenceLayout]
  | cons k ks ih =>
    intro x hk
    simp only [sequenceLayout,List.zip_cons_cons,List.pairwise_cons]
    constructor
    · intro pair hp
      have h := sequence_start_ge up gap hg ks (sequenceAdvance gap x k)
        (fun a ha => hk a (by simp [ha])) pair hp
      simp only [sequenceOffset]
      unfold sequenceAdvance at h
      omega
    · exact ih (sequenceAdvance gap x k) (fun a ha => hk a (by simp [ha]))

theorem choice_start_ge (radius widest gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (y : Int),
      (∀ k ∈ kids, 0 ≤ k.height) →
      ∀ pair ∈ kids.zip (choiceLayout radius widest gap y kids).2, y ≤ pair.2.y := by
  intro kids
  induction kids with
  | nil => intro y _ pair hp; simp [choiceLayout] at hp
  | cons k ks ih =>
    intro y hk pair hp
    simp only [choiceLayout,List.zip_cons_cons,List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [choiceOffset]
    · have ht := ih (y+k.height+gap) (fun a ha => hk a (by simp [ha])) pair hp
      have hh := hk k (by simp)
      omega

theorem choice_children_disjoint (radius widest gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (y : Int),
      (∀ k ∈ kids, 0 ≤ k.height) →
      List.Pairwise (fun a b : Shape × Point => a.2.y+a.1.height ≤ b.2.y)
        (kids.zip (choiceLayout radius widest gap y kids).2) := by
  intro kids
  induction kids with
  | nil => intro y _; simp [choiceLayout]
  | cons k ks ih =>
    intro y hk
    simp only [choiceLayout,List.zip_cons_cons,List.pairwise_cons]
    constructor
    · intro pair hp
      have h := choice_start_ge radius widest gap hg ks (y+k.height+gap)
        (fun a ha => hk a (by simp [ha])) pair hp
      simp only [choiceOffset]
      omega
    · exact ih (y+k.height+gap) (fun a ha => hk a (by simp [ha]))

theorem choice_child_bottom (radius widest gap : Int) (hg : 0 ≤ gap) :
    ∀ (kids : List Shape) (y : Int),
      (∀ k ∈ kids, 0 ≤ k.height) →
      ∀ pair ∈ kids.zip (choiceLayout radius widest gap y kids).2,
        pair.2.y + pair.1.height ≤ (choiceLayout radius widest gap y kids).1-gap := by
  intro kids
  induction kids with
  | nil => intro y _ pair hp; simp [choiceLayout] at hp
  | cons k ks ih =>
    intro y hk pair hp
    simp only [choiceLayout,List.zip_cons_cons,List.mem_cons] at hp
    rcases hp with rfl | hp
    · have h := choice_end_ge radius widest gap hg ks (y+k.height+gap)
        (fun a ha => hk a (by simp [ha]))
      simp only [choiceOffset,choiceLayout]
      omega
    · exact ih (y+k.height+gap) (fun a ha => hk a (by simp [ha])) pair hp

theorem choiceShape_vertical_inside (p : Profile) (n : Node) (kids : List Shape)
    (hk : ∀ k ∈ kids, Nonnegative k) :
    ∀ pair ∈ kids.zip (choiceShape p n kids).offsets,
      0 ≤ pair.2.y ∧
      pair.2.y + pair.1.height ≤ (choiceShape p n kids).height := by
  have hheight : ∀ k ∈ kids, 0 ≤ k.height :=
    fun k h => Int.add_nonneg (hk k h).2.1 (hk k h).2.2
  have hg := (spacing_nonnegative p).2.2.2.2.2
  have ht := choice_start_ge (constant p "arc_radius")
    (kids.foldl (fun a k => max a k.w) 0) (constant p "vsep") hg kids 0 hheight
  have hb := choice_child_bottom (constant p "arc_radius")
    (kids.foldl (fun a k => max a k.w) 0) (constant p "vsep") hg kids 0 hheight
  intro pair hp
  have htop := ht pair hp
  have hbottom := hb pair hp
  simp only [choiceShape,Shape.height]
  exact ⟨htop,by unfold Shape.height at hbottom; omega⟩

def ChildrenInside (s : Shape) : Prop :=
  ∀ pair ∈ s.children.zip s.offsets,
    0 ≤ pair.2.x ∧ 0 ≤ pair.2.y ∧
      pair.2.x + pair.1.w ≤ s.w ∧ pair.2.y + pair.1.height ≤ s.height

theorem sequenceShape_children_inside (p : Profile) (n : Node) (kids : List Shape)
    (hk : ∀ k ∈ kids, Nonnegative k) : ChildrenInside (sequenceShape p n kids) := by
  intro pair hp
  have h := sequenceShape_inside p n kids hk pair hp
  have hx := sequence_start_ge
    (kids.foldl (fun a k => max a k.up) 0) (constant p "hsep")
    (spacing_nonnegative p).2.2.2.2.1 kids 0 (fun k h => (hk k h).1) pair
    (by simpa only [sequenceShape] using hp)
  exact ⟨hx,h.1,h.2.2,h.2.1⟩

theorem choiceShape_children_inside (p : Profile) (n : Node) (kids : List Shape)
    (hk : ∀ k ∈ kids, Nonnegative k) : ChildrenInside (choiceShape p n kids) := by
  intro pair hp
  have hx := choiceShape_inside p n kids pair hp
  have hy := choiceShape_vertical_inside p n kids hk pair hp
  have hr := (spacing_nonnegative p).2.2.2.1
  exact ⟨by omega,hy.1,by omega,hy.2⟩

theorem wrapperShape_children_inside (p : Profile) (n : Node) (kid : Shape) :
    ChildrenInside (wrapperShape p n kid) := by
  intro pair hp
  simp only [wrapperShape,List.zip_cons_cons,List.zip_nil_left,List.mem_singleton] at hp
  subst pair
  have hr := (spacing_nonnegative p).2.2.2.1
  unfold wrapperShape Shape.height
  split <;> split <;> simp only <;> omega

theorem sizeRaw_children_inside (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (hk : ∀ k ∈ kids, Nonnegative k)
    (h : sizeRaw p metric n kids = .ok s) : ChildrenInside s := by
  unfold sizeRaw at h
  split at h
  · split at h
    · cases h
    · cases hw : Measure.textWidth metric n.text.toList with
      | error e => simp [hw,bind,Except.bind] at h
      | ok width =>
        simp only [hw,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
        subst s
        intro pair hp
        simp [leafShape] at hp
  · split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst s
        exact sequenceShape_children_inside p n kids hk
    · split at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s
          exact choiceShape_children_inside p n kids hk
      · split at h
        · cases kids with
          | nil => cases h
          | cons kid tail =>
            cases tail with
            | nil =>
              simp only [Except.ok.injEq] at h
              subst s
              exact wrapperShape_children_inside p n kid
            | cons second rest => cases h
        · cases h

theorem choice_offsets_length (radius widest gap : Int) :
    ∀ (kids : List Shape) (y : Int),
      (choiceLayout radius widest gap y kids).2.length = kids.length := by
  intro kids
  induction kids with
  | nil => intro y; rfl
  | cons k ks ih =>
    intro y
    simp only [choiceLayout,List.length_cons]
    rw [ih]

theorem sizeRaw_offsets_length (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (h : sizeRaw p metric n kids = .ok s) :
    s.offsets.length = s.children.length := by
  unfold sizeRaw at h
  split at h
  · split at h
    · cases h
    · cases hw : Measure.textWidth metric n.text.toList with
      | error e => simp [hw,bind,Except.bind] at h
      | ok width =>
        simp only [hw,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
        subst s
        rfl
  · split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst s
        exact sequence_offsets_length _ _ kids 0
    · split at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s
          exact choice_offsets_length _ _ _ kids 0
      · split at h
        · cases kids with
          | nil => cases h
          | cons kid tail =>
            cases tail with
            | nil =>
              simp only [Except.ok.injEq] at h
              subst s
              rfl
            | cons second rest => cases h
        · cases h

theorem child_rect_contained (s : Shape) (hs : ChildrenInside s) (x y : Int)
    (pair : Shape × Point) (hp : pair ∈ s.children.zip s.offsets) :
    (shapeRect s x y).Contained (shapeRect pair.1 (x+pair.2.x) (y+pair.2.y)) := by
  have h := hs pair hp
  unfold shapeRect Rect.Contained
  dsimp only at *
  omega

theorem horizontal_rects_disjoint (a b : Shape × Point) (x y : Int)
    (h : a.2.x+a.1.w ≤ b.2.x) :
    Disjoint (shapeRect a.1 (x+a.2.x) (y+a.2.y))
      (shapeRect b.1 (x+b.2.x) (y+b.2.y)) := by
  unfold Disjoint Rect.meetsInterior shapeRect
  dsimp only at *
  omega

theorem vertical_rects_disjoint (a b : Shape × Point) (x y : Int)
    (h : a.2.y+a.1.height ≤ b.2.y) :
    Disjoint (shapeRect a.1 (x+a.2.x) (y+a.2.y))
      (shapeRect b.1 (x+b.2.x) (y+b.2.y)) := by
  unfold Disjoint Rect.meetsInterior shapeRect
  dsimp only at *
  omega

theorem horizontal_route_orthogonal (left right y : Int) :
    Polyline.isOrthogonal [⟨left,y⟩,⟨right,y⟩] = true := by
  simp [Polyline.isOrthogonal]

theorem horizontal_route_avoids (left right y : Int) (r : Rect)
    (h : max left right ≤ r.x ∨ r.x+r.w ≤ min left right ∨ y ≤ r.y ∨ r.y+r.h ≤ y) :
    ¬ Polyline.hitsRect [⟨left,y⟩,⟨right,y⟩] r := by
  intro hit
  apply hit.2.2
  refine ⟨?_, trivial⟩
  unfold Polyline.segMisses
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using h))))

theorem sizeRaw_metadata (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (h : sizeRaw p metric n kids = .ok s) :
    s.id = n.id ∧ s.kind = n.kind ∧ s.children = kids := by
  unfold sizeRaw at h
  split at h
  · split at h
    · cases h
    · cases hw : Measure.textWidth metric n.text.toList with
      | error e => simp [hw,bind,Except.bind] at h
      | ok width =>
        simp only [hw,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
        subst s
        refine ⟨rfl,rfl,?_⟩
        cases kids <;> simp_all [leafShape]
  · split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst s
        exact ⟨rfl,rfl,rfl⟩
    · split at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s
          exact ⟨rfl,rfl,rfl⟩
      · split at h
        · cases kids with
          | nil => cases h
          | cons kid tail =>
            cases tail with
            | nil =>
              simp only [Except.ok.injEq] at h
              subst s
              exact ⟨rfl,rfl,rfl⟩
            | cons second rest => cases h
        · cases h

theorem size_metadata (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (h : size p metric n kids = .ok s) :
    s.id = n.id ∧ s.kind = n.kind ∧ s.children = kids := by
  unfold size at h
  cases hs : sizeRaw p metric n kids with
  | error e => simp [hs,bind,Except.bind] at h
  | ok raw =>
    have hm := sizeRaw_metadata p metric n kids raw hs
    simp only [hs,bind,Except.bind] at h
    split at h
    · cases h
    · simp only [pure,Except.pure,Except.ok.injEq] at h
      subst s
      exact hm

theorem size_raw_of_ok (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (h : size p metric n kids = .ok s) :
    sizeRaw p metric n kids = .ok s := by
  unfold size at h
  cases hs : sizeRaw p metric n kids with
  | error e => simp [hs,bind,Except.bind] at h
  | ok raw =>
    simp only [hs,bind,Except.bind] at h
    split at h
    · cases h
    · simp only [pure,Except.pure,Except.ok.injEq] at h
      subst s
      rfl

def ChildrenSeparated (s : Shape) : Prop :=
  List.Pairwise (fun a b : Shape × Point =>
    Disjoint (shapeRect a.1 a.2.x a.2.y) (shapeRect b.1 b.2.x b.2.y))
    (s.children.zip s.offsets)

theorem sequenceShape_children_separated (p : Profile) (n : Node) (kids : List Shape)
    (hk : ∀ k ∈ kids, Nonnegative k) : ChildrenSeparated (sequenceShape p n kids) := by
  have h := sequence_children_disjoint
    (kids.foldl (fun a k => max a k.up) 0) (constant p "hsep")
    (spacing_nonnegative p).2.2.2.2.1 kids 0 (fun k hmem => (hk k hmem).1)
  refine List.Pairwise.imp ?_ h
  intro a b hab
  simpa using horizontal_rects_disjoint a b 0 0 hab

theorem choiceShape_children_separated (p : Profile) (n : Node) (kids : List Shape)
    (hk : ∀ k ∈ kids, Nonnegative k) : ChildrenSeparated (choiceShape p n kids) := by
  have h := choice_children_disjoint (constant p "arc_radius")
    (kids.foldl (fun a k => max a k.w) 0) (constant p "vsep")
    (spacing_nonnegative p).2.2.2.2.2 kids 0
    (fun k hmem => Int.add_nonneg (hk k hmem).2.1 (hk k hmem).2.2)
  refine List.Pairwise.imp ?_ h
  intro a b hab
  simpa using vertical_rects_disjoint a b 0 0 hab

theorem sizeRaw_children_separated (p : Profile) (metric : Measure.Metric) (n : Node)
    (kids : List Shape) (s : Shape) (hk : ∀ k ∈ kids, Nonnegative k)
    (h : sizeRaw p metric n kids = .ok s) : ChildrenSeparated s := by
  unfold sizeRaw at h
  split at h
  · split at h
    · cases h
    · cases hw : Measure.textWidth metric n.text.toList with
      | error e => simp [hw,bind,Except.bind] at h
      | ok width =>
        simp only [hw,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
        subst s
        simp [ChildrenSeparated,leafShape]
  · split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst s
        exact sequenceShape_children_separated p n kids hk
    · split at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s
          exact choiceShape_children_separated p n kids hk
      · split at h
        · cases kids with
          | nil => cases h
          | cons kid tail =>
            cases tail with
            | nil =>
              simp only [Except.ok.injEq] at h
              subst s
              simp [ChildrenSeparated,wrapperShape]
            | cons second rest => cases h
        · cases h

inductive Geometry : Shape → Prop where
  | node (s : Shape) (nonnegative : Nonnegative s) (inside : ChildrenInside s)
      (lengths : s.offsets.length = s.children.length)
      (separated : ChildrenSeparated s)
      (descendants : ∀ child ∈ s.children, Geometry child) : Geometry s

theorem mapM_property {α β : Type} (f : α → Except LayoutError β) (P : β → Prop)
    (hf : ∀ a b, f a = .ok b → P b) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ b ∈ ys, P b := by
  intro xs
  induction xs with
  | nil =>
    intro ys h b hb
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at h
    subst ys
    simp at hb
  | cons a rest ih =>
    intro ys h b hb
    cases ha : f a with
    | error e => simp [List.mapM_cons,ha,bind,Except.bind] at h
    | ok head =>
      cases ht : rest.mapM f with
      | error e => simp [List.mapM_cons,ha,ht,bind,Except.bind] at h
      | ok tail =>
        have he : head :: tail = ys := by
          simpa [List.mapM_cons,ha,ht,bind,Except.bind,pure,Except.pure] using h
        subst ys
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hf a _ ha
        · exact ih tail ht b hb

theorem Geometry.nonnegative {s : Shape} (h : Geometry s) : Nonnegative s := by
  cases h with
  | node _ hn _ _ _ _ => exact hn

theorem measure_geometry :
    ∀ (fuel : Nat) (p : Profile) (metric : Measure.Metric) (n : Node) (s : Shape),
      measure fuel p metric n = .ok s → Geometry s := by
  intro fuel
  induction fuel with
  | zero => intro p metric n s h; cases h
  | succ fuel ih =>
    intro p metric n s h
    simp only [measure] at h
    cases hk : n.children.mapM (measure fuel p metric) with
    | error e => simp [hk,bind,Except.bind] at h
    | ok kids =>
      have hgeom := mapM_property (measure fuel p metric) Geometry
        (fun a s ha => ih p metric a s ha) n.children kids hk
      have hn : ∀ k ∈ kids, Nonnegative k :=
        fun k hmem => (hgeom k hmem).nonnegative
      simp only [hk,bind,Except.bind] at h
      have hraw := size_raw_of_ok p metric n kids s h
      have hmeta := sizeRaw_metadata p metric n kids s hraw
      refine Geometry.node s (sizeRaw_nonnegative p metric n kids s hn hraw)
        (sizeRaw_children_inside p metric n kids s hn hraw)
        (sizeRaw_offsets_length p metric n kids s hraw)
        (sizeRaw_children_separated p metric n kids s hn hraw) ?_
      simpa only [hmeta.2.2] using hgeom

theorem Geometry.child {s : Shape} (h : Geometry s) (pair : Shape × Point)
    (hp : pair ∈ s.children.zip s.offsets) : Geometry pair.1 := by
  cases h with
  | node _ _ _ _ _ children => exact children pair.1 (List.of_mem_zip hp).1

theorem Geometry.inside {s : Shape} (h : Geometry s) : ChildrenInside s := by
  cases h with
  | node _ _ inside _ _ _ => exact inside

inductive DescendantFrame : Shape → Int → Int → Rect → Prop where
  | self (s : Shape) (x y : Int) : DescendantFrame s x y (shapeRect s x y)
  | child (s : Shape) (x y : Int) (pair : Shape × Point) (r : Rect)
      (member : pair ∈ s.children.zip s.offsets)
      (below : DescendantFrame pair.1 (x+pair.2.x) (y+pair.2.y) r) :
      DescendantFrame s x y r

theorem descendant_contained {s : Shape} {x y : Int} {r : Rect}
    (hd : DescendantFrame s x y r) : Geometry s → (shapeRect s x y).Contained r := by
  induction hd with
  | self s x y =>
    intro _
    unfold Rect.Contained
    omega
  | child s x y pair r hp hd ih =>
    intro hs
    exact Rect.Contained.trans (child_rect_contained s hs.inside x y pair hp)
      (ih (hs.child pair hp))

theorem contained_disjoint {outerA outerB a b : Rect}
    (ha : outerA.Contained a) (hb : outerB.Contained b) (h : Disjoint outerA outerB) :
    Disjoint a b := by
  unfold Rect.Contained at ha hb
  unfold Disjoint Rect.meetsInterior at h ⊢
  omega

theorem descendant_siblings_disjoint {s : Shape} (hs : Geometry s) (x y : Int)
    (a b : Shape × Point) (ha : a ∈ s.children.zip s.offsets)
    (hb : b ∈ s.children.zip s.offsets) (ra rb : Rect)
    (hsep : Disjoint (shapeRect a.1 (x+a.2.x) (y+a.2.y))
      (shapeRect b.1 (x+b.2.x) (y+b.2.y)))
    (hda : DescendantFrame a.1 (x+a.2.x) (y+a.2.y) ra)
    (hdb : DescendantFrame b.1 (x+b.2.x) (y+b.2.y) rb) : Disjoint ra rb :=
  contained_disjoint (descendant_contained hda (hs.child a ha))
    (descendant_contained hdb (hs.child b hb)) hsep

def RoutesOrthogonal (state : State) : Prop :=
  ∀ route ∈ state.routes, Polyline.isOrthogonal route.points = true

theorem joinStep_orthogonal (s : Shape) (x y : Int) (state : State) (i : Nat)
    (h : RoutesOrthogonal state) : RoutesOrthogonal (joinStep s x y state i) := by
  intro route hr
  simp only [joinStep,List.mem_append,List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact h route hr
  · exact horizontal_route_orthogonal _ _ _

theorem foldl_preserves {α β : Type} (f : β → α → β) (P : β → Prop)
    (hf : ∀ a b, P b → P (f b a)) :
    ∀ (xs : List α) (initial : β), P initial → P (xs.foldl f initial) := by
  intro xs
  induction xs with
  | nil => intro initial h; exact h
  | cons a rest ih =>
    intro initial h
    exact ih (f initial a) (hf a initial h)

theorem sequenceJoins_orthogonal (s : Shape) (x y : Int) (state : State)
    (h : RoutesOrthogonal state) : RoutesOrthogonal (sequenceJoins s x y state) :=
  foldl_preserves (joinStep s x y) RoutesOrthogonal
    (fun i acc ha => joinStep_orthogonal s x y acc i ha) _ state h

theorem foldlM_preserves {α β : Type} (f : β → α → Except LayoutError β) (P : β → Prop)
    (hf : ∀ a before after, P before → f before a = .ok after → P after) :
    ∀ (xs : List α) (initial final : β), P initial →
      xs.foldlM f initial = .ok final → P final := by
  intro xs
  induction xs with
  | nil =>
    intro initial final hi h
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at h
    subst final
    exact hi
  | cons a rest ih =>
    intro initial final hi h
    cases ha : f initial a with
    | error e => simp [List.foldlM_cons,ha,bind,Except.bind] at h
    | ok next =>
      have hn := hf a initial next hi ha
      simp only [List.foldlM_cons,ha,bind,Except.bind] at h
      exact ih next final hn h

theorem placeNode_orthogonal :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), RoutesOrthogonal initial →
      placeNode fuel p s x y parent initial = .ok final → RoutesOrthogonal final := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final _ h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final hi h
    simp only [placeNode] at h
    split at h
    · simp only [pure,Except.pure,Except.ok.injEq] at h
      subst final
      exact hi
    · apply foldlM_preserves _ RoutesOrthogonal
        (fun pair before after hb he => ih p pair.1 _ _ s.id before after hb he)
        _ _ final ?_ h
      split
      · exact sequenceJoins_orthogonal s x y _ hi
      · exact hi

theorem addRule_orthogonal (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State) (h : RoutesOrthogonal state) :
    RoutesOrthogonal (addRule p rule s g y state) := by
  unfold addRule
  split <;> exact h

theorem placeRule_orthogonal (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule) (hi : RoutesOrthogonal before.state)
    (h : placeRule m metric before rule = .ok after) : RoutesOrthogonal after.state := by
  unfold placeRule at h
  cases hs : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hs,bind,Except.bind] at h
  | ok s =>
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hs,ht,bind,Except.bind] at h
    | ok title =>
      simp only [hs,ht,bind,Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+(ruleGeometry m.profile s title).defX)
          (before.y+(ruleGeometry m.profile s title).defY) rule.id
          (addRule m.profile rule s (ruleGeometry m.profile s title) before.y before.state) with
        | error e => simp [hp] at h
        | ok state =>
          have hn := placeNode_orthogonal _ _ _ _ _ _ _ _ (addRule_orthogonal _ _ _ _ _ _ hi) hp
          simp only [hp,pure,Except.pure,Except.ok.injEq] at h
          subst after
          exact hn

theorem layout_orthogonal (m : Model) (rules : List Rule) (s : Scene)
    (h : layout m rules = .ok s) : Validator.C4 s.layoutDump := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm,bind,Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric) {y := constant m.profile "margin"} with
    | error e => simp [hm,hf,bind,Except.bind] at h
    | ok result =>
      have hi : RoutesOrthogonal ({} : State) := by intro r hr; cases hr
      have ho := foldlM_preserves (placeRule m metric)
        (fun state => RoutesOrthogonal state.state)
        (fun rule before after hb he => placeRule_orthogonal m metric before after rule hb he)
        rules {y := constant m.profile "margin"} result hi hf
      simp only [hm,hf,bind,Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (intro route hr _; exact ho route hr)
        | (try simp only [pure,Except.pure,Except.ok.injEq] at h
           subst s
           intro route hr _
           exact ho route hr)

def BoxesInside (outer : Rect) (state : State) : Prop :=
  ∀ box ∈ state.boxes, outer.Contained box.rect

theorem joinStep_boxes_inside (outer : Rect) (s : Shape) (x y : Int)
    (state : State) (i : Nat) (h : BoxesInside outer state) :
    BoxesInside outer (joinStep s x y state i) := h

theorem sequenceJoins_boxes_inside (outer : Rect) (s : Shape) (x y : Int)
    (state : State) (h : BoxesInside outer state) :
    BoxesInside outer (sequenceJoins s x y state) :=
  foldl_preserves (joinStep s x y) (BoxesInside outer)
    (fun i acc ha => joinStep_boxes_inside outer s x y acc i ha) _ state h

theorem foldlM_preserves_mem {α β : Type} (f : β → α → Except LayoutError β) (P : β → Prop) :
    ∀ (xs : List α),
      (∀ a ∈ xs, ∀ before after, P before → f before a = .ok after → P after) →
      ∀ initial final, P initial → xs.foldlM f initial = .ok final → P final := by
  intro xs
  induction xs with
  | nil =>
    intro _ initial final hi h
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at h
    subst final
    exact hi
  | cons a rest ih =>
    intro hf initial final hi h
    cases ha : f initial a with
    | error e => simp [List.foldlM_cons,ha,bind,Except.bind] at h
    | ok next =>
      have hn := hf a (by simp) initial next hi ha
      simp only [List.foldlM_cons,ha,bind,Except.bind] at h
      exact ih (fun b hb => hf b (by simp [hb])) next final hn h

theorem placeNode_boxes_inside (outer : Rect) :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), Geometry s → outer.Contained (shapeRect s x y) →
      BoxesInside outer initial → placeNode fuel p s x y parent initial = .ok final →
      BoxesInside outer final := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final _ _ _ h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final hs hrect hi h
    have hbase : BoxesInside outer
        {initial with boxes := initial.boxes ++
          [⟨s.id,if leaf s.kind then "node" else "group",shapeRect s x y,parent,leaf s.kind⟩]} := by
      intro box hb
      simp only [List.mem_append,List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hi box hb
      · exact hrect
    simp only [placeNode] at h
    split at h
    · simp only [pure,Except.pure,Except.ok.injEq] at h
      subst final
      simpa [BoxesInside, *] using hbase
    · refine foldlM_preserves_mem _ (BoxesInside outer) _ ?_ _ final ?_ h
      · intro pair hp before after hb he
        exact ih p pair.1 _ _ s.id before after (hs.child pair hp)
          (Rect.Contained.trans hrect (child_rect_contained s hs.inside x y pair hp)) hb he
      · split
        · apply sequenceJoins_boxes_inside outer s x y
          simpa [BoxesInside, *] using hbase
        · simpa [BoxesInside, *] using hbase

theorem rule_spacing_nonnegative (p : Profile) :
    0 ≤ constant p "margin" ∧ 0 ≤ constant p "rule_name_gap" ∧
    0 ≤ constant p "rule_end_gap" ∧ 0 ≤ constant p "marker_radius" ∧
    0 ≤ constant p "rule_min_height" := by
  cases p <;> decide

theorem ruleGeometry_nonnegative (p : Profile) (s : Shape) (title : Int)
    (hs : Nonnegative s) (ht : 0 ≤ title) :
    0 ≤ (ruleGeometry p s title).width ∧ 0 ≤ (ruleGeometry p s title).height := by
  obtain ⟨hm,hn,he,hmark,hh⟩ := rule_spacing_nonnegative p
  have hheight := Int.le_max_left (constant p "rule_min_height")
    ((ruleGeometry p s title).defY+s.height+2*constant p "margin")
  dsimp only [ruleGeometry] at hheight ⊢
  exact ⟨by have hw := hs.1; omega,by omega⟩

theorem rule_contains_definition (p : Profile) (s : Shape) (title y : Int)
    (ht : 0 ≤ title) :
    (ruleFrame p (ruleGeometry p s title) y).Contained
      (shapeRect s (constant p "margin"+(ruleGeometry p s title).defX)
        (y+(ruleGeometry p s title).defY)) := by
  obtain ⟨hm,hn,he,hmark,_⟩ := rule_spacing_nonnegative p
  have hb := Int.le_max_right (constant p "rule_min_baseline") s.up
  have hh := Int.le_max_right (constant p "rule_min_height")
    ((max (constant p "rule_min_baseline") s.up-s.up)+s.height+2*constant p "margin")
  dsimp only [ruleGeometry,ruleFrame,shapeRect,Rect.Contained]
  omega

def StageFrame (p : Profile) (state : RuleState) : Rect :=
  ⟨0,0,state.widest+2*constant p "margin",state.y⟩

def StageBounds (p : Profile) (state : RuleState) : Prop :=
  0 ≤ state.y ∧ 0 ≤ state.widest ∧ BoxesInside (StageFrame p state) state.state

theorem boxes_inside_mono {small large : Rect} {state : State}
    (hc : large.Contained small) (h : BoxesInside small state) : BoxesInside large state :=
  fun box hb => Rect.Contained.trans hc (h box hb)
theorem rule_stage_bounds (p : Profile) (s : Shape) (title : Int) (before : RuleState)
    (hs : Nonnegative s) (ht : 0 ≤ title) (hi : StageBounds p before) :
    let g := ruleGeometry p s title
    let after : RuleState := ⟨before.state,before.y+g.height+constant p "vsep",
      max before.widest g.width⟩
    0 ≤ after.y ∧ 0 ≤ after.widest ∧
      (StageFrame p after).Contained (StageFrame p before) ∧
      (StageFrame p after).Contained (ruleFrame p g before.y) := by
  have hg := ruleGeometry_nonnegative p s title hs ht
  have hm := (rule_spacing_nonnegative p).1
  have hv := (spacing_nonnegative p).2.2.2.2.2
  have hw1 := Int.le_max_left before.widest (ruleGeometry p s title).width
  have hw2 := Int.le_max_right before.widest (ruleGeometry p s title).width
  dsimp only [StageFrame,ruleFrame,Rect.Contained]
  obtain ⟨hy,hw,_⟩ := hi
  omega

theorem addRule_boxes_inside (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State) (outer : Rect)
    (hi : BoxesInside outer state) (hf : outer.Contained (ruleFrame p g y)) :
    BoxesInside outer (addRule p rule s g y state) := by
  unfold addRule
  split
  · exact hi
  · intro box hb
    simp only [List.mem_append,List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hi box hb
    · exact hf


theorem placeRule_stage_bounds (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule) (hi : StageBounds m.profile before)
    (h : placeRule m metric before rule = .ok after) : StageBounds m.profile after := by
  unfold placeRule at h
  cases hs : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hs,bind,Except.bind] at h
  | ok s =>
    have hg := measure_geometry _ _ _ _ _ hs
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hs,ht,bind,Except.bind] at h
    | ok title =>
      have hn := Measure.textWidth_nonneg ht
      have hb := rule_stage_bounds m.profile s title before hg.nonnegative hn hi
      let g := ruleGeometry m.profile s title
      let target : RuleState :=
        ⟨before.state,before.y+g.height+constant m.profile "vsep",max before.widest g.width⟩
      have ho : BoxesInside (StageFrame m.profile target) before.state :=
        boxes_inside_mono hb.2.2.1 hi.2.2
      have ha := addRule_boxes_inside m.profile rule s g before.y before.state
        (StageFrame m.profile target) ho hb.2.2.2
      have hd := Rect.Contained.trans hb.2.2.2
        (rule_contains_definition m.profile s title before.y hn)
      simp only [hs,ht,bind,Except.bind] at h
      split at h
      · cases h
      · dsimp only [g] at *
        cases hp : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          have hf := placeNode_boxes_inside (StageFrame m.profile target)
            _ _ _ _ _ _ _ _ hg hd ha hp
          dsimp only [g] at hp
          simp only [hp,pure,Except.pure,Except.ok.injEq] at h
          subst after
          exact ⟨hb.1,hb.2.1,hf⟩

end Elegant.Railroad
