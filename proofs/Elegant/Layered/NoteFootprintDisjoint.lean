import Elegant.Layered.AttachPipeline
import ElegantGeometry.Disjoint

set_option autoImplicit false

/-! The footprint of an attached-note bundle places the target box and its note fragments
side by side inside one reserved size. With a positive gap, a nonnegative target width, and
nonnegative note sizes the target does not meet any note interior, the notes are pairwise
disjoint, and every placed rect lies inside the footprint size. -/

namespace Elegant
namespace Layered

namespace PipelineImpl

/-- Left-side width accumulation of `footprint`. -/
def leftSum (gap : Int) (notes : List (Size × Bool)) : Int :=
  notes.foldl (fun l n => if n.2 then l else l + n.1.w + gap) 0

/-- Right-side width accumulation of `footprint`. -/
def rightSum (gap : Int) (notes : List (Size × Bool)) : Int :=
  notes.foldl (fun r n => if n.2 then r + n.1.w + gap else r) 0

/-- Height accumulation of `footprint`. -/
def heightSum (h0 : Int) (notes : List (Size × Bool)) : Int :=
  notes.foldl (fun h n => max h n.1.h) h0

/-- The `i`-th placed note rect: `a` is the left cursor start, `b` the right cursor start,
`gap` the spacing added per note, `total` the reserved height. -/
def noteRect (a b gap total : Int) (notes : List (Size × Bool)) (i : Nat)
    (n : Size × Bool) : Rect :=
  ⟨if n.2 then b + rightSum gap (notes.take i) else a + leftSum gap (notes.take i),
   Int.fdiv (total - n.1.h) 2, n.1.w, n.1.h⟩

theorem leftSum_add (gap : Int) (s : Int) (notes : List (Size × Bool)) :
    List.foldl (fun l n => if n.2 then l else l + n.1.w + gap) s notes =
      s + leftSum gap notes := by
  induction notes generalizing s with
  | nil => simp [leftSum]
  | cons n ns ih =>
    show List.foldl _ ((fun l m => if m.2 then l else l + m.1.w + gap) s n) ns = _
    rw [ih]
    show _ = s + List.foldl _ 0 (n :: ns)
    rw [List.foldl_cons, ih]
    show (if n.2 = true then s else s + n.1.w + gap) + leftSum gap ns =
         s + ((if n.2 = true then (0 : Int) else 0 + n.1.w + gap) + leftSum gap ns)
    split <;> omega

theorem rightSum_add (gap : Int) (s : Int) (notes : List (Size × Bool)) :
    List.foldl (fun r n => if n.2 then r + n.1.w + gap else r) s notes =
      s + rightSum gap notes := by
  induction notes generalizing s with
  | nil => simp [rightSum]
  | cons n ns ih =>
    show List.foldl _ ((fun r m => if m.2 then r + m.1.w + gap else r) s n) ns = _
    rw [ih]
    show _ = s + List.foldl _ 0 (n :: ns)
    rw [List.foldl_cons, ih]
    show (if n.2 = true then s + n.1.w + gap else s) + rightSum gap ns =
         s + ((if n.2 = true then 0 + n.1.w + gap else (0 : Int)) + rightSum gap ns)
    split <;> omega

theorem leftSum_cons (gap : Int) (n : Size × Bool) (ns : List (Size × Bool)) :
    leftSum gap (n :: ns) =
      (if n.2 = true then (0 : Int) else 0 + n.1.w + gap) + leftSum gap ns := by
  show List.foldl _ 0 (n :: ns) = _
  rw [List.foldl_cons, leftSum_add]

theorem rightSum_cons (gap : Int) (n : Size × Bool) (ns : List (Size × Bool)) :
    rightSum gap (n :: ns) =
      (if n.2 = true then 0 + n.1.w + gap else (0 : Int)) + rightSum gap ns := by
  show List.foldl _ 0 (n :: ns) = _
  rw [List.foldl_cons, rightSum_add]

theorem leftSum_append (gap : Int) (as_ bs : List (Size × Bool)) :
    leftSum gap (as_ ++ bs) = leftSum gap as_ + leftSum gap bs := by
  show List.foldl _ 0 (as_ ++ bs) = _
  rw [List.foldl_append]
  show List.foldl _ (List.foldl _ 0 as_) bs = List.foldl _ 0 as_ + leftSum gap bs
  rw [leftSum_add]

theorem rightSum_append (gap : Int) (as_ bs : List (Size × Bool)) :
    rightSum gap (as_ ++ bs) = rightSum gap as_ + rightSum gap bs := by
  show List.foldl _ 0 (as_ ++ bs) = _
  rw [List.foldl_append]
  show List.foldl _ (List.foldl _ 0 as_) bs = List.foldl _ 0 as_ + rightSum gap bs
  rw [rightSum_add]

theorem leftSum_nonneg (gap : Int) (hgap : 0 ≤ gap) (notes : List (Size × Bool))
    (hpos : ∀ n ∈ notes, 0 ≤ n.1.w) :
    0 ≤ leftSum gap notes := by
  revert hpos
  induction notes with
  | nil => intro hpos; simp [leftSum]
  | cons n ns ih =>
    intro hpos
    rw [leftSum_cons]
    have hw := hpos n (List.mem_cons_self)
    have hle := ih (fun m hm => hpos m (List.mem_cons_of_mem _ hm))
    split <;> omega

theorem rightSum_nonneg (gap : Int) (hgap : 0 ≤ gap) (notes : List (Size × Bool))
    (hpos : ∀ n ∈ notes, 0 ≤ n.1.w) :
    0 ≤ rightSum gap notes := by
  revert hpos
  induction notes with
  | nil => intro hpos; simp [rightSum]
  | cons n ns ih =>
    intro hpos
    rw [rightSum_cons]
    have hw := hpos n (List.mem_cons_self)
    have hle := ih (fun m hm => hpos m (List.mem_cons_of_mem _ hm))
    split <;> omega

theorem leftSum_ge_take (gap : Int) (hgap : 0 ≤ gap) (notes : List (Size × Bool))
    (hpos : ∀ n ∈ notes, 0 ≤ n.1.w) {i j : Nat} (hij : i ≤ j) :
    leftSum gap (notes.take i) ≤ leftSum gap (notes.take j) := by
  have key : notes.take j = notes.take i ++ (notes.take j).drop i := by
    have h1 := List.take_append_drop i (notes.take j)
    rw [List.take_take, Nat.min_eq_left hij] at h1
    exact h1.symm
  rw [key, leftSum_append]
  have hle := leftSum_nonneg gap hgap ((notes.take j).drop i) (fun n hn =>
    hpos n (List.mem_of_mem_take (List.mem_of_mem_drop hn)))
  omega

theorem rightSum_ge_take (gap : Int) (hgap : 0 ≤ gap) (notes : List (Size × Bool))
    (hpos : ∀ n ∈ notes, 0 ≤ n.1.w) {i j : Nat} (hij : i ≤ j) :
    rightSum gap (notes.take i) ≤ rightSum gap (notes.take j) := by
  have key : notes.take j = notes.take i ++ (notes.take j).drop i := by
    have h1 := List.take_append_drop i (notes.take j)
    rw [List.take_take, Nat.min_eq_left hij] at h1
    exact h1.symm
  rw [key, rightSum_append]
  have hle := rightSum_nonneg gap hgap ((notes.take j).drop i) (fun n hn =>
    hpos n (List.mem_of_mem_take (List.mem_of_mem_drop hn)))
  omega

theorem heightSum_ge_start (h0 : Int) (notes : List (Size × Bool)) :
    h0 ≤ heightSum h0 notes := by
  induction notes generalizing h0 with
  | nil => simp [heightSum]
  | cons n ns ih =>
    show h0 ≤ heightSum (max h0 n.1.h) ns
    exact Int.le_trans (Int.le_max_left _ _) (ih (max h0 n.1.h))

theorem heightSum_ge (h0 : Int) (notes : List (Size × Bool)) :
    ∀ n ∈ notes, n.1.h ≤ heightSum h0 notes := by
  induction notes generalizing h0 with
  | nil => simp
  | cons m ms ih =>
    intro n hn
    by_cases hnm : n = m
    · subst hnm
      show n.1.h ≤ heightSum (max h0 n.1.h) ms
      exact Int.le_trans (Int.le_max_right _ _) (heightSum_ge_start _ ms)
    · have hn' : n ∈ ms := by
        rcases List.mem_cons.mp hn with h | h
        · exact absurd h hnm
        · exact h
      show n.1.h ≤ heightSum (max h0 m.1.h) ms
      exact ih (max h0 m.1.h) n hn'

private theorem fdiv_two_bounds {d : Int} (hd : 0 ≤ d) :
    0 ≤ Int.fdiv d 2 ∧ Int.fdiv d 2 ≤ d := by
  rw [Int.fdiv_eq_ediv_of_nonneg d (by omega : (0 : Int) ≤ 2)]
  omega

private theorem leftSum_take_succ (gap : Int) (notes : List (Size × Bool)) (i : Nat)
    (x : Size × Bool) (hx : notes[i]? = some x) :
    leftSum gap (notes.take (i + 1)) =
      leftSum gap (notes.take i) + (if x.2 then 0 else x.1.w + gap) := by
  have htake : notes.take (i + 1) = notes.take i ++ [x] := by
    induction notes generalizing i with
    | nil => cases i <;> simp at hx
    | cons a as ih =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hx
        injection hx with h1
        subst h1
        simp [List.take_succ_cons, List.take_zero, List.nil_append]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        rw [List.take_succ_cons, List.take_succ_cons, ih i hx, List.cons_append]
  rw [htake, leftSum_append]
  have hsing : leftSum gap [x] = if x.2 then (0 : Int) else x.1.w + gap := by
    rw [leftSum_cons]
    simp only [leftSum, List.foldl_nil]
    split <;> omega
  rw [hsing]

private theorem rightSum_take_succ (gap : Int) (notes : List (Size × Bool)) (i : Nat)
    (x : Size × Bool) (hx : notes[i]? = some x) :
    rightSum gap (notes.take (i + 1)) =
      rightSum gap (notes.take i) + (if x.2 then x.1.w + gap else 0) := by
  have htake : notes.take (i + 1) = notes.take i ++ [x] := by
    induction notes generalizing i with
    | nil => cases i <;> simp at hx
    | cons a as ih =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hx
        injection hx with h1
        subst h1
        simp [List.take_succ_cons, List.take_zero, List.nil_append]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        rw [List.take_succ_cons, List.take_succ_cons, ih i hx, List.cons_append]
  rw [htake, rightSum_append]
  have hsing : rightSum gap [x] = if x.2 then x.1.w + gap else (0 : Int) := by
    rw [rightSum_cons]
    simp only [rightSum, List.foldl_nil]
    split <;> omega
  rw [hsing]

private theorem disjoint_by_x_le {p q : Rect} (h : q.x + q.w ≤ p.x) : Disjoint p q := by
  unfold Disjoint Rect.meetsInterior
  intro hmeet
  obtain ⟨h1, -⟩ := hmeet
  omega

private theorem disjoint_by_x_ge {p q : Rect} (h : p.x + p.w ≤ q.x) : Disjoint p q := by
  unfold Disjoint Rect.meetsInterior
  intro hmeet
  obtain ⟨h1, -⟩ := hmeet
  omega

private theorem leftSum_cons_of_true {gap : Int} {n : Size × Bool}
    {ns : List (Size × Bool)} (hn : n.2 = true) :
    leftSum gap (n :: ns) = (0 : Int) + leftSum gap ns := by
  rw [leftSum_cons, hn]; simp

private theorem leftSum_cons_of_false {gap : Int} {n : Size × Bool}
    {ns : List (Size × Bool)} (hn : n.2 = false) :
    leftSum gap (n :: ns) = (0 + n.1.w + gap) + leftSum gap ns := by
  rw [leftSum_cons, hn]; simp

private theorem rightSum_cons_of_true {gap : Int} {n : Size × Bool}
    {ns : List (Size × Bool)} (hn : n.2 = true) :
    rightSum gap (n :: ns) = (0 + n.1.w + gap) + rightSum gap ns := by
  rw [rightSum_cons, hn]; simp

private theorem rightSum_cons_of_false {gap : Int} {n : Size × Bool}
    {ns : List (Size × Bool)} (hn : n.2 = false) :
    rightSum gap (n :: ns) = (0 : Int) + rightSum gap ns := by
  rw [rightSum_cons, hn]; simp

private theorem leftSum_nil (gap : Int) : leftSum gap [] = 0 := by
  simp [leftSum]

private theorem rightSum_nil (gap : Int) : rightSum gap [] = 0 := by
  simp [rightSum]

private theorem noteRect_left {a b gap total : Int} {notes : List (Size × Bool)} {i : Nat}
    {x : Size × Bool} (hx2 : x.2 = false) :
    noteRect a b gap total notes i x =
      ⟨a + leftSum gap (notes.take i), Int.fdiv (total - x.1.h) 2, x.1.w, x.1.h⟩ := by
  simp [noteRect, hx2]

private theorem noteRect_right {a b gap total : Int} {notes : List (Size × Bool)} {i : Nat}
    {x : Size × Bool} (hx2 : x.2 = true) :
    noteRect a b gap total notes i x =
      ⟨b + rightSum gap (notes.take i), Int.fdiv (total - x.1.h) 2, x.1.w, x.1.h⟩ := by
  simp [noteRect, hx2]

private theorem mem_mapIdx {α β : Type} (f : Nat → α → β) (l : List α) (y : β) :
    y ∈ l.mapIdx f ↔ ∃ i x, l[i]? = some x ∧ f i x = y := by
  induction l generalizing f y with
  | nil => simp [List.mapIdx_nil]
  | cons a as ih =>
    simp only [List.mapIdx_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, x, hx, hf⟩)
      · exact ⟨0, a, List.getElem?_cons_zero, rfl⟩
      · exact ⟨i + 1, x, by simp only [List.getElem?_cons_succ]; exact hx, hf⟩
    · rintro ⟨i, x, hx, hf⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hx
        injection hx with hxa
        subst hxa
        subst hf
        exact Or.inl rfl
      | succ i =>
        refine Or.inr ⟨i, x, ?_, hf⟩
        simp only [List.getElem?_cons_succ] at hx
        exact hx

private theorem mapIdx_congr {α β : Type} (f g : Nat → α → β) (l : List α)
    (h : ∀ i x, l[i]? = some x → f i x = g i x) : l.mapIdx f = l.mapIdx g := by
  induction l generalizing f g with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons]
    rw [ih (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun i x hx => h (i + 1) x (by simp only [List.getElem?_cons_succ]; exact hx))]
    rw [h 0 a List.getElem?_cons_zero]

private theorem pairwise_mapIdx {α β : Type} (R : β → β → Prop) (f : Nat → α → β) (l : List α)
    (h : ∀ i j x y, i < j → l[i]? = some x → l[j]? = some y → R (f i x) (f j y)) :
    (l.mapIdx f).Pairwise R := by
  induction l generalizing f with
  | nil => simp [List.mapIdx_nil]
  | cons a as ih =>
    simp only [List.mapIdx_cons]
    refine List.pairwise_cons.mpr ⟨?_, ih (fun i x => f (i + 1) x) ?_⟩
    · intro y hy
      obtain ⟨i, x, hx, rfl⟩ := (mem_mapIdx _ _ _).mp hy
      have key := h 0 (i + 1) a x (by omega) List.getElem?_cons_zero
        (by simp only [List.getElem?_cons_succ]; exact hx)
      exact key
    · intro i j x y hij hgi hgj
      exact h (i + 1) (j + 1) x y (by omega)
        (by simp only [List.getElem?_cons_succ]; exact hgi)
        (by simp only [List.getElem?_cons_succ]; exact hgj)

/-- The `placed` fold of `footprint`: cursor sums plus the appended fragment list. -/
theorem placed_fold_gen (gap total a b : Int) (out0 : List Rect)
    (notes : List (Size × Bool)) :
    notes.foldl
      (fun (acc : Int × Int × List Rect) n =>
        let rect : Rect :=
          ⟨if n.2 then acc.2.1 else acc.1, Int.fdiv (total - n.1.h) 2, n.1.w, n.1.h⟩
        if n.2 then (acc.1, acc.2.1 + n.1.w + gap, acc.2.2 ++ [rect])
        else (acc.1 + n.1.w + gap, acc.2.1, acc.2.2 ++ [rect]))
      (a, b, out0) =
    (a + leftSum gap notes, b + rightSum gap notes,
      out0 ++ notes.mapIdx (noteRect a b gap total notes)) := by
  induction notes generalizing a b out0 with
  | nil => simp [leftSum, rightSum, List.mapIdx_nil]
  | cons n ns ih =>
    simp only [List.foldl_cons]
    cases hn : n.2 with
    | true =>
      have htail : ns.mapIdx (noteRect a (b + n.1.w + gap) gap total ns) =
          ns.mapIdx (fun i => noteRect a b gap total (n :: ns) (i + 1)) := by
        refine mapIdx_congr _ _ ns ?_
        intro i x hx
        cases hx2 : x.2
        · rw [noteRect_left hx2, noteRect_left hx2, List.take_succ_cons,
            leftSum_cons_of_true hn]
          congr 1 <;> omega
        · rw [noteRect_right hx2, noteRect_right hx2, List.take_succ_cons,
            rightSum_cons_of_true hn]
          congr 1 <;> omega
      show List.foldl _ (a, b + n.1.w + gap,
          out0 ++ [⟨b, Int.fdiv (total - n.1.h) 2, n.1.w, n.1.h⟩]) ns = _
      rw [ih, htail, leftSum_cons_of_true hn, rightSum_cons_of_true hn]
      simp only [List.mapIdx_cons, List.cons_append, List.append_assoc,
        List.take_zero, List.nil_append, noteRect, hn,
        leftSum_nil, rightSum_nil, Int.add_zero, Int.zero_add, reduceIte,
        Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · trivial
      · omega
      · trivial
    | false =>
      have htail : ns.mapIdx (noteRect (a + n.1.w + gap) b gap total ns) =
          ns.mapIdx (fun i => noteRect a b gap total (n :: ns) (i + 1)) := by
        refine mapIdx_congr _ _ ns ?_
        intro i x hx
        cases hx2 : x.2
        · rw [noteRect_left hx2, noteRect_left hx2, List.take_succ_cons,
            leftSum_cons_of_false hn]
          congr 1 <;> omega
        · rw [noteRect_right hx2, noteRect_right hx2, List.take_succ_cons,
            rightSum_cons_of_false hn]
          congr 1 <;> omega
      show List.foldl _ (a + n.1.w + gap, b,
          out0 ++ [⟨a, Int.fdiv (total - n.1.h) 2, n.1.w, n.1.h⟩]) ns = _
      rw [ih, htail, leftSum_cons_of_false hn, rightSum_cons_of_false hn]
      simp only [List.mapIdx_cons, List.cons_append, List.append_assoc,
        List.take_zero, List.nil_append, noteRect, hn,
        leftSum_nil, rightSum_nil, Int.add_zero, Int.zero_add, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega

/-- The size field of `footprint` in terms of the cursor sums. -/
theorem footprint_size (gap : Int) (target : Size) (notes : List (Size × Bool)) :
    (footprint gap target notes).size =
      ⟨gap + leftSum gap notes + target.w + (gap + rightSum gap notes),
        heightSum target.h notes + 2 * gap⟩ := by
  have hleft := leftSum_add gap gap notes
  have hright := rightSum_add gap gap notes
  simp only [footprint, hleft, hright, heightSum]

/-- The target rect of `footprint` in terms of the cursor sums. -/
theorem footprint_target (gap : Int) (target : Size) (notes : List (Size × Bool)) :
    (footprint gap target notes).target =
      ⟨gap + leftSum gap notes,
        Int.fdiv (heightSum target.h notes + 2 * gap - target.h) 2, target.w, target.h⟩ := by
  have hleft := leftSum_add gap gap notes
  have hright := rightSum_add gap gap notes
  simp only [footprint, hleft, hright, heightSum]

/-- The placed note rects of `footprint`. -/
theorem footprint_notes (gap : Int) (target : Size) (notes : List (Size × Bool)) :
    (footprint gap target notes).notes =
      notes.mapIdx (noteRect gap
        (gap + leftSum gap notes + target.w + gap) gap
        (heightSum target.h notes + 2 * gap) notes) := by
  have hleft := leftSum_add gap gap notes
  have hright := rightSum_add gap gap notes
  have hfold := placed_fold_gen gap
    ((notes.foldl (fun h n => max h n.1.h) target.h) + 2 * gap) gap
    ((notes.foldl (fun l n => if n.2 then l else l + n.1.w + gap) gap) + target.w + gap) [] notes
  simp only [footprint]
  rw [hfold]
  simp only [hleft, heightSum, List.nil_append]

/-- The placed fragments of a footprint are pairwise disjoint, disjoint from the target
box, and contained in the footprint size. -/
theorem footprint_notes_disjoint_target (gap : Int) (hgap : 0 < gap)
    (target : Size) (notes : List (Size × Bool)) (htar : 0 ≤ target.w)
    (hpos : ∀ n ∈ notes, 0 ≤ n.1.w ∧ 0 ≤ n.1.h) :
    (∀ r ∈ (footprint gap target notes).notes, Disjoint (footprint gap target notes).target r) ∧
    (footprint gap target notes).notes.Pairwise Disjoint ∧
    ∀ r ∈ (footprint gap target notes).target :: (footprint gap target notes).notes,
      (Rect.mk 0 0 (footprint gap target notes).size.w
        (footprint gap target notes).size.h).Contained r := by
  have hg : 0 ≤ gap := Int.le_of_lt hgap
  have hw : ∀ n ∈ notes, 0 ≤ n.1.w := fun n hn => (hpos n hn).1
  have hh : ∀ n ∈ notes, 0 ≤ n.1.h := fun n hn => (hpos n hn).2
  have hL0 : 0 ≤ leftSum gap notes := leftSum_nonneg gap hg notes hw
  have hR0 : 0 ≤ rightSum gap notes := rightSum_nonneg gap hg notes hw
  have hHt : target.h ≤ heightSum target.h notes := heightSum_ge_start target.h notes
  have hHge : ∀ n ∈ notes, n.1.h ≤ heightSum target.h notes := heightSum_ge target.h notes
  have htakeL : ∀ i, 0 ≤ leftSum gap (notes.take i) := fun i =>
    leftSum_nonneg gap hg _ (fun n hn => hw n (List.mem_of_mem_take hn))
  have htakeR : ∀ i, 0 ≤ rightSum gap (notes.take i) := fun i =>
    rightSum_nonneg gap hg _ (fun n hn => hw n (List.mem_of_mem_take hn))
  have hszw : (footprint gap target notes).size.w
      = gap + leftSum gap notes + target.w + (gap + rightSum gap notes) := by
    rw [footprint_size]
  have hszh : (footprint gap target notes).size.h = heightSum target.h notes + 2 * gap := by
    rw [footprint_size]
  rw [footprint_notes, footprint_target, hszw, hszh]
  have hmem : ∀ (i : Nat) (x : Size × Bool), notes[i]? = some x → x ∈ notes :=
    fun i x hx => List.mem_of_getElem? hx
  have hy : ∀ (i : Nat) (x : Size × Bool), notes[i]? = some x →
      0 ≤ Int.fdiv (heightSum target.h notes + 2 * gap - x.1.h) 2 ∧
        Int.fdiv (heightSum target.h notes + 2 * gap - x.1.h) 2 + x.1.h ≤
          heightSum target.h notes + 2 * gap := by
    intro i x hx
    have hm : x ∈ notes := hmem i x hx
    have h2 : 0 ≤ heightSum target.h notes + 2 * gap - x.1.h := by
      have := hHge x hm; omega
    obtain ⟨h3, h4⟩ := fdiv_two_bounds h2
    have hh' := hh x hm
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, x, hx, hgx⟩ := (mem_mapIdx _ _ _).mp hr
    subst hgx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hx
    cases hx2 : x.2
    · rw [noteRect_left hx2]
      refine disjoint_by_x_le ?_
      have h1 := leftSum_take_succ gap notes i x hx
      have h2 := leftSum_ge_take gap hg notes hw (show i + 1 ≤ notes.length from by omega)
      simp only [List.take_length] at h2
      simp [hx2] at h1
      dsimp only
      omega
    · rw [noteRect_right hx2]
      refine disjoint_by_x_ge ?_
      have hRi := htakeR i
      dsimp only
      omega
  · refine pairwise_mapIdx Disjoint
      (noteRect gap (gap + leftSum gap notes + target.w + gap) gap
        (heightSum target.h notes + 2 * gap) notes) notes ?_
    intro i j x y hij hxi hxj
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hxi
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hxj
    cases hx2 : x.2 <;> cases hy2 : y.2
    · rw [noteRect_left hx2, noteRect_left hy2]
      refine disjoint_by_x_ge ?_
      have h1 := leftSum_take_succ gap notes i x hxi
      have h2 := leftSum_ge_take gap hg notes hw (show i + 1 ≤ j from by omega)
      simp [hx2] at h1
      dsimp only
      omega
    · rw [noteRect_left hx2, noteRect_right hy2]
      refine disjoint_by_x_ge ?_
      have h1 := leftSum_take_succ gap notes i x hxi
      have h2 := leftSum_ge_take gap hg notes hw (show i + 1 ≤ notes.length from by omega)
      simp only [List.take_length] at h2
      have h3 := rightSum_nonneg gap hg (notes.take j)
        (fun n hn => hw n (List.mem_of_mem_take hn))
      simp [hx2] at h1
      dsimp only
      omega
    · rw [noteRect_right hx2, noteRect_left hy2]
      refine disjoint_by_x_le ?_
      have h1 := leftSum_take_succ gap notes j y hxj
      have h2 := leftSum_ge_take gap hg notes hw (show j + 1 ≤ notes.length from by omega)
      simp only [List.take_length] at h2
      have h3 := rightSum_nonneg gap hg (notes.take i)
        (fun n hn => hw n (List.mem_of_mem_take hn))
      simp [hy2] at h1
      dsimp only
      omega
    · rw [noteRect_right hx2, noteRect_right hy2]
      refine disjoint_by_x_ge ?_
      have h1 := rightSum_take_succ gap notes i x hxi
      have h2 := rightSum_ge_take gap hg notes hw (show i + 1 ≤ j from by omega)
      simp [hx2] at h1
      dsimp only
      omega
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr2
    · have h2 : 0 ≤ heightSum target.h notes + 2 * gap - target.h := by omega
      obtain ⟨h3, h4⟩ := fdiv_two_bounds h2
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · obtain ⟨i, x, hx, hgx⟩ := (mem_mapIdx _ _ _).mp hr2
      subst hgx
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hx
      obtain ⟨hy0, hy1⟩ := hy i x hx
      cases hx2 : x.2
      · rw [noteRect_left hx2]
        refine ⟨?_, ?_, ?_, ?_⟩
        · have hLi := htakeL i
          dsimp only
          omega
        · have h1 := leftSum_take_succ gap notes i x hx
          have h2 := leftSum_ge_take gap hg notes hw (show i + 1 ≤ notes.length from by omega)
          simp only [List.take_length] at h2
          simp [hx2] at h1
          dsimp only
          omega
        · dsimp only
          omega
        · dsimp only
          omega
      · rw [noteRect_right hx2]
        refine ⟨?_, ?_, ?_, ?_⟩
        · have hRi := htakeR i
          dsimp only
          omega
        · have h1 := rightSum_take_succ gap notes i x hx
          have h2 := rightSum_ge_take gap hg notes hw (show i + 1 ≤ notes.length from by omega)
          simp only [List.take_length] at h2
          simp [hx2] at h1
          dsimp only
          omega
        · dsimp only
          omega
        · dsimp only
          omega

end PipelineImpl
end Layered
end Elegant
