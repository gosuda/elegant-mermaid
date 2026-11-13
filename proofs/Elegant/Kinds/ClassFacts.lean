import Elegant.Kinds.Class
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

/-! Facts about the class adapter that do not depend on the family's validity theorem:
the label text is recovered exactly (class-051 input), the size is the compartment table of
class-051 and class-052, the drawing stays inside the placed box, and the adapter preserves the
family's dump, its ids, and its budget flag. -/

namespace Elegant
namespace Kinds
namespace Class

/-! ### Label text recovery -/

/-- No two adjacent line breaks. -/
def NoBlank : List Char → Prop
  | [] => True
  | [_] => True
  | c :: d :: rest => ¬(c = '\n' ∧ d = '\n') ∧ NoBlank (d :: rest)

theorem noBlank_cons {c : Char} {x : List Char} (hc : c ≠ '\n') (hx : NoBlank x) :
    NoBlank (c :: x) := by
  cases x with
  | nil => trivial
  | cons d rest => exact ⟨fun h => hc h.1, hx⟩

theorem noBlank_cons_newline {x : List Char} (hx : NoBlank x) (hh : x.head? ≠ some '\n') :
    NoBlank ('\n' :: x) := by
  cases x with
  | nil => trivial
  | cons d rest =>
    refine ⟨fun h => hh (by simp [h.2]), hx⟩

theorem noBlank_noNewline {l : List Char} (h : '\n' ∉ l) : NoBlank l := by
  induction l with
  | nil => trivial
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at h
    exact noBlank_cons (fun e => h.1 e.symm) (ih h.2)

theorem noBlank_append_newline {l t : List Char} (hl : '\n' ∉ l) (ht : NoBlank t)
    (hh : t.head? ≠ some '\n') : NoBlank (l ++ '\n' :: t) := by
  induction l with
  | nil => exact noBlank_cons_newline ht hh
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at hl
    exact noBlank_cons (fun e => hl.1 e.symm) (ih hl.2)

theorem splitLastBlank_cons (c : Char) (rest : List Char) :
    splitLastBlank (c :: rest) =
      match splitLastBlank rest with
      | some q => some (c :: q.1, q.2)
      | none =>
        match c :: rest with
        | '\n' :: '\n' :: r => some ([], r)
        | _ => none := rfl

theorem splitLastBlank_cons_none {c : Char} {rest : List Char}
    (hn : splitLastBlank rest = none) (hb : ∀ r, c :: rest ≠ '\n' :: '\n' :: r) :
    splitLastBlank (c :: rest) = none := by
  rw [splitLastBlank_cons, hn]
  dsimp only
  split
  · rename_i r e
    exact absurd e (hb r)
  · rfl

theorem splitLastBlank_of_noBlank {cs : List Char} (h : NoBlank cs) :
    splitLastBlank cs = none := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hr : NoBlank rest := by
      cases rest with
      | nil => trivial
      | cons d r => exact h.2
    refine splitLastBlank_cons_none (ih hr) ?_
    cases rest with
    | nil => intro r e; simp at e
    | cons d r =>
      have hne : ¬(c = '\n' ∧ d = '\n') := h.1
      intro r' e
      simp only [List.cons.injEq] at e
      exact hne ⟨e.1, e.2.1⟩

theorem splitLastBlank_append (x : List Char) {r : List Char} (hr : NoBlank r)
    (hh : r.head? ≠ some '\n') :
    splitLastBlank (x ++ '\n' :: '\n' :: r) = some (x, r) := by
  induction x with
  | nil =>
    have h1 : splitLastBlank ('\n' :: r) = none :=
      splitLastBlank_of_noBlank (noBlank_cons_newline hr hh)
    rw [List.nil_append, splitLastBlank_cons, h1]
    rfl
  | cons c rest ih =>
    rw [List.cons_append, splitLastBlank_cons, ih]

theorem splitLines_cons (c : Char) (rest : List Char) :
    splitLines (c :: rest) =
      match splitLines rest with
      | [] => [[c]]
      | l :: ls => if c = '\n' then [] :: l :: ls else (c :: l) :: ls := rfl

theorem splitLines_ne_nil (l : List Char) : splitLines l ≠ [] := by
  induction l with
  | nil => simp [splitLines]
  | cons c rest ih =>
    rw [splitLines_cons]
    cases hs : splitLines rest with
    | nil => exact absurd hs ih
    | cons x xs => simp only []; split <;> simp

theorem splitLines_noNewline {l : List Char} (h : '\n' ∉ l) : splitLines l = [l] := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at h
    rw [splitLines_cons, ih h.2]
    simp [Ne.symm h.1]

theorem splitLines_append {l : List Char} (rest : List Char) (h : '\n' ∉ l) :
    splitLines (l ++ '\n' :: rest) = l :: splitLines rest := by
  induction l with
  | nil =>
    rw [List.nil_append, splitLines_cons]
    cases hs : splitLines rest with
    | nil => exact absurd hs (splitLines_ne_nil rest)
    | cons x xs => simp
  | cons c l ih =>
    simp only [List.mem_cons, not_or] at h
    rw [List.cons_append, splitLines_cons, ih h.2]
    simp [Ne.symm h.1]

theorem splitLines_joinLines : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, '\n' ∉ l) → splitLines (joinLines ls) = ls
  | [], h, _ => absurd rfl h
  | [l], _, hl => by
    simp [joinLines, splitLines_noNewline (hl l (by simp))]
  | l :: l' :: ls, _, hl => by
    have h1 : '\n' ∉ l := hl l (by simp)
    have h2 := splitLines_joinLines (ls := l' :: ls) (by simp)
      (fun x hx => hl x (by simp [hx]))
    simp only [joinLines]
    rw [splitLines_append _ h1, h2]

theorem joinLines_head_ne : ∀ {ls : List (List Char)}, (∀ l ∈ ls, l ≠ [] ∧ '\n' ∉ l) →
    NoBlank (joinLines ls) ∧ (joinLines ls).head? ≠ some '\n'
  | [], _ => ⟨trivial, by simp [joinLines]⟩
  | [l], h => by
    have := h l (by simp)
    exact ⟨noBlank_noNewline this.2, by
      cases l with
      | nil => exact absurd rfl this.1
      | cons c rest =>
        simp only [joinLines, List.head?_cons, ne_eq, Option.some.injEq]
        intro e; exact this.2 (by simp [e])⟩
  | l :: l' :: ls, h => by
    have h1 := h l (by simp)
    have ih := joinLines_head_ne (ls := l' :: ls) (fun x hx => h x (by simp [hx]))
    refine ⟨?_, ?_⟩
    · simp only [joinLines]
      exact noBlank_append_newline h1.2 ih.1 ih.2
    · cases l with
      | nil => exact absurd rfl h1.1
      | cons c rest =>
        simp only [joinLines, List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
        intro e; exact h1.2 (by simp [e])

theorem compartmentLines_chars {rows : List String}
    (h : ∀ s ∈ rows, s ≠ "" ∧ '\n' ∉ s.toList) : compartmentLines (compartmentChars rows) = rows := by
  cases rows with
  | nil => simp [compartmentLines, compartmentChars, joinLines]
  | cons r rs =>
    have hr := h r (by simp)
    have hne : compartmentChars (r :: rs) ≠ [] := by
      have hr' : r.toList ≠ [] := fun e => hr.1 (String.toList_eq_nil_iff.mp e)
      cases hl : r.toList with
      | nil => exact absurd hl hr'
      | cons c rest =>
        cases rs <;> simp [compartmentChars, joinLines, hl]
    have hrows : ∀ l ∈ (r :: rs).map String.toList, '\n' ∉ l := by
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨s, hs, rfl⟩ := hl
      exact (h s hs).2
    have hsplit := splitLines_joinLines (ls := (r :: rs).map String.toList) (by simp) hrows
    have hempty : (compartmentChars (r :: rs)).isEmpty = false := by
      cases hc : compartmentChars (r :: rs) with
      | nil => exact absurd hc hne
      | cons _ _ => rfl
    unfold compartmentLines
    rw [hempty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold compartmentChars
    rw [hsplit]
    simp [List.map_map, Function.comp_def]

/-- A label's compartments: the heading is any nonempty list of lines; members are nonempty
single lines. -/
structure Table.WellFormed (t : Table) : Prop where
  head_ne : t.head ≠ []
  head_lines : ∀ s ∈ t.head, '\n' ∉ s.toList
  attribute_rows : ∀ s ∈ t.attributes, s ≠ "" ∧ '\n' ∉ s.toList
  method_rows : ∀ s ∈ t.methods, s ≠ "" ∧ '\n' ∉ s.toList

/-- The recovery of the compartments is exact on every label that the model writes. -/
theorem tableOfChars_chars {t : Table} (h : t.WellFormed) : tableOfChars t.chars = some t := by
  have hm : NoBlank (compartmentChars t.methods) ∧
      (compartmentChars t.methods).head? ≠ some '\n' := joinLines_head_ne (ls := t.methods.map String.toList) (by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    exact ⟨fun e => (h.method_rows s hs).1 (String.toList_eq_nil_iff.mp e),
      (h.method_rows s hs).2⟩)
  have ha : NoBlank (compartmentChars t.attributes) ∧
      (compartmentChars t.attributes).head? ≠ some '\n' := joinLines_head_ne (ls := t.attributes.map String.toList) (by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    exact ⟨fun e => (h.attribute_rows s hs).1 (String.toList_eq_nil_iff.mp e),
      (h.attribute_rows s hs).2⟩)
  have e1 : t.chars = (compartmentChars t.head ++ '\n' :: '\n' :: compartmentChars t.attributes) ++
      '\n' :: '\n' :: compartmentChars t.methods := by
    simp [Table.chars, List.append_assoc]
  have s1 := splitLastBlank_append (compartmentChars t.head ++ '\n' :: '\n' ::
    compartmentChars t.attributes) hm.1 hm.2
  have s2 := splitLastBlank_append (compartmentChars t.head) ha.1 ha.2
  have hhead : (splitLines (compartmentChars t.head)).map String.ofList = t.head := by
    have hrows : ∀ l ∈ t.head.map String.toList, '\n' ∉ l := by
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨s, hs, rfl⟩ := hl
      exact h.head_lines s hs
    unfold compartmentChars
    rw [splitLines_joinLines (by simpa using h.head_ne) hrows]
    simp [List.map_map, Function.comp_def]
  have hatt := compartmentLines_chars h.attribute_rows
  have hmet := compartmentLines_chars h.method_rows
  unfold tableOfChars
  rw [e1, s1]
  simp [s2, hhead, hatt, hmet]

/-! ### Size (class-051, class-052) -/

theorem maxWidthM_spec {α : Type} (f : α → Except LayoutError Int) :
    ∀ (xs : List α) (w0 w : Int), maxWidthM f xs w0 = .ok w →
      w0 ≤ w ∧ ∀ a ∈ xs, ∃ x, f a = .ok x ∧ x ≤ w
  | [], w0, w, h => by
    simp only [maxWidthM, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨Int.le_refl _, by simp⟩
  | a :: xs, w0, w, h => by
    simp only [maxWidthM, List.foldlM_cons, bind, Except.bind] at h
    cases hfa : f a with
    | error e => simp [hfa] at h
    | ok x =>
      simp only [hfa, pure, Except.pure] at h
      have ih := maxWidthM_spec f xs (max w0 x) w h
      refine ⟨by omega, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨x, hfa, by omega⟩
      · exact ih.2 b hb

theorem compartmentWidth_spec {m : Measure.Metric} {rows : List String} {w : Int}
    (h : compartmentWidth m rows = .ok w) :
    0 ≤ w ∧ ∀ row ∈ rows, ∃ x, Measure.textWidth m row.toList = .ok x ∧ x ≤ w :=
  maxWidthM_spec (fun row : String => Measure.textWidth m row.toList) rows 0 w h

theorem tableWidth_spec {m : Measure.Metric} {cs : List (List String)} {w : Int}
    (h : tableWidth m cs = .ok w) :
    0 ≤ w ∧ ∀ c ∈ cs, ∀ row ∈ c, ∃ x, Measure.textWidth m row.toList = .ok x ∧ x ≤ w := by
  obtain ⟨h0, h1⟩ := maxWidthM_spec (compartmentWidth m) cs 0 w h
  refine ⟨h0, fun c hc row hr => ?_⟩
  obtain ⟨x, hx, hxw⟩ := h1 c hc
  obtain ⟨_, hrow⟩ := compartmentWidth_spec hx
  obtain ⟨y, hy, hyx⟩ := hrow row hr
  exact ⟨y, hy, by omega⟩

theorem checkSize_spec {w h : Int} {s : Size} (hs : checkSize w h = .ok s) :
    s.w = w ∧ s.h = h := by
  unfold checkSize at hs
  split at hs
  · simp at hs
  · simp only [Except.ok.injEq] at hs
    subst hs
    exact ⟨rfl, rfl⟩

/-- class-051 and class-052 as a closed form: the width is the widest row plus twice the padding;
the height is the compartment heights, one separator between neighbouring compartments (two for
three compartments), and two border rows in the cell profile. -/
theorem classSize_spec {p : Profile} {t : Table} {s : Size} (h : classSize p t = .ok s) :
    ∃ m widest, metricOf p = .ok m ∧ tableWidth m t.compartments = .ok widest ∧
      s.w = widest + 2 * constant p "class.padding" ∧
      s.h = tableHeight (constant p "line_h") t.compartments +
        2 * constant p "class.separator" + (if p = .cell then 2 else 0) := by
  unfold classSize at h
  cases hm : metricOf p with
  | error e => rw [hm] at h; simp at h
  | ok m =>
    rw [hm] at h
    dsimp only at h
    cases hw : tableWidth m t.compartments with
    | error e => rw [hw] at h; simp at h
    | ok widest =>
      rw [hw] at h
      dsimp only at h
      obtain ⟨hs1, hs2⟩ := checkSize_spec h
      refine ⟨m, widest, rfl, hw, hs1, ?_⟩
      rw [hs2]
      simp only [Table.compartments, List.length_cons, List.length_nil]
      omega

theorem compartmentHeight_nonneg {lineH : Int} (hl : 0 ≤ lineH) (c : List String) :
    0 ≤ compartmentHeight lineH c :=
  Int.mul_nonneg (by omega) hl

/-- An empty compartment retains one row. -/
theorem compartmentHeight_empty (lineH : Int) : compartmentHeight lineH [] = lineH := by
  have : (max 1 ([] : List String).length : Int) = 1 := rfl
  unfold compartmentHeight
  rw [this, Int.one_mul]

theorem compartmentHeight_ge {lineH : Int} (hl : 0 ≤ lineH) (c : List String) :
    lineH ≤ compartmentHeight lineH c := by
  unfold compartmentHeight
  have : (1 : Int) ≤ (max 1 c.length : Int) := by omega
  calc lineH = 1 * lineH := (Int.one_mul _).symm
    _ ≤ _ := Int.mul_le_mul_of_nonneg_right this hl

theorem tableHeight_nonneg {lineH : Int} (hl : 0 ≤ lineH) :
    ∀ cs : List (List String), 0 ≤ tableHeight lineH cs
  | [] => Int.le_refl _
  | c :: cs => by
    have := tableHeight_nonneg hl cs
    have := compartmentHeight_nonneg hl c
    simp only [tableHeight]
    omega

/-- Every compartment takes at least one row. -/
theorem tableHeight_ge {lineH : Int} (hl : 0 ≤ lineH) :
    ∀ cs : List (List String), (cs.length : Int) * lineH ≤ tableHeight lineH cs
  | [] => by simp [tableHeight]
  | c :: cs => by
    have ih := tableHeight_ge hl cs
    have hc := compartmentHeight_ge hl c
    have e : (((c :: cs).length : Nat) : Int) * lineH = (cs.length : Int) * lineH + lineH := by
      simp [Int.add_mul]
    simp only [tableHeight]
    omega

/-- Every row of every compartment fits in the table between its paddings. -/
theorem classSize_covers_rows {p : Profile} {t : Table} {s : Size} (h : classSize p t = .ok s) :
    ∀ c ∈ t.compartments, ∀ row ∈ c, ∃ m x, metricOf p = .ok m ∧
      Measure.textWidth m row.toList = .ok x ∧ x + 2 * constant p "class.padding" ≤ s.w := by
  obtain ⟨m, widest, hm, hw, hsw, _⟩ := classSize_spec h
  intro c hc row hr
  obtain ⟨x, hx, hxw⟩ := (tableWidth_spec hw).2 c hc row hr
  exact ⟨m, x, hm, hx, by omega⟩

/-! ### Drawing stays inside the placed box (class-052) -/

theorem tops_ge {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep) :
    ∀ (cs : List (List String)) (y : Int), ∀ y' ∈ tops lineH sep y cs, y ≤ y'
  | [], y, y', h => by simp [tops] at h
  | c :: cs, y, y', h => by
    have hc := compartmentHeight_nonneg hl c
    simp only [tops, List.mem_cons] at h
    rcases h with rfl | h
    · exact Int.le_refl _
    · have := tops_ge hl hs cs (y + compartmentHeight lineH c + sep) y' h
      omega

theorem tops_tail_ge {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep)
    (cs : List (List String)) (y : Int) : ∀ y' ∈ (tops lineH sep y cs).tail, y + sep ≤ y' := by
  cases cs with
  | nil => simp [tops]
  | cons c cs =>
    intro y' h
    have hc := compartmentHeight_nonneg hl c
    have := tops_ge hl hs cs (y + compartmentHeight lineH c + sep) y' h
    omega

theorem tops_le {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep) :
    ∀ (cs : List (List String)) (y : Int), ∀ y' ∈ tops lineH sep y cs,
      y' ≤ y + tableHeight lineH cs + ((cs.length : Int) - 1) * sep
  | [], y, y', h => by simp [tops] at h
  | c :: cs, y, y', h => by
    have hc := compartmentHeight_nonneg hl c
    have ht := tableHeight_nonneg hl cs
    have hn : (0 : Int) ≤ (cs.length : Int) * sep := Int.mul_nonneg (by omega) hs
    have e1 : (((c :: cs).length : Int) - 1) * sep = (cs.length : Int) * sep := by simp
    simp only [tops, List.mem_cons] at h
    rcases h with rfl | h
    · simp only [tableHeight, e1]
      omega
    · have ih := tops_le hl hs cs (y + compartmentHeight lineH c + sep) y' h
      have e2 : ((cs.length : Int) - 1) * sep = (cs.length : Int) * sep - sep := by
        rw [Int.sub_mul, Int.one_mul]
      simp only [tableHeight, e1]
      omega

theorem tops_bound {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep) :
    ∀ (cs : List (List String)) (y : Int), ∀ q ∈ (tops lineH sep y cs).zip cs,
      y ≤ q.1 ∧ q.1 + compartmentHeight lineH q.2 ≤
        y + tableHeight lineH cs + ((cs.length : Int) - 1) * sep
  | [], y, q, h => by simp [tops] at h
  | c :: cs, y, q, h => by
    have hc := compartmentHeight_nonneg hl c
    have ht := tableHeight_nonneg hl cs
    have hn : (0 : Int) ≤ (cs.length : Int) * sep := Int.mul_nonneg (by omega) hs
    have e1 : (((c :: cs).length : Int) - 1) * sep = (cs.length : Int) * sep := by simp
    simp only [tops, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp only [tableHeight, e1]
      omega
    · have ih := tops_bound hl hs cs (y + compartmentHeight lineH c + sep) q h
      have e2 : ((cs.length : Int) - 1) * sep = (cs.length : Int) * sep - sep := by
        rw [Int.sub_mul, Int.one_mul]
      simp only [tableHeight, e1]
      omega

/-- A drawing primitive lies inside a box of the profile's border width `b`: one cell on the
right and bottom edges of the cell profile, none in the vector profile. -/
def _root_.Elegant.Primitive.insideBox (b : Int) (r : Rect) : Primitive → Prop
  | .rect q _ => q = r
  | .polyline pts _ _ =>
    ∀ pt ∈ pts, r.x ≤ pt.x ∧ pt.x ≤ r.x + r.w - b ∧ r.y ≤ pt.y ∧ pt.y ≤ r.y + r.h - b
  | .text tx =>
    r.x ≤ tx.rect.x ∧ tx.rect.x + tx.rect.w ≤ r.x + r.w ∧
      r.y ≤ tx.rect.y ∧ tx.rect.y + tx.rect.h ≤ r.y + r.h - b
  | _ => False

/-- class-052: for a box at least as large as its table, every frame, rule, and text of the
class drawing lies inside the box; rules span from the left to the right border. -/
theorem classPrimitives_inside {p : Profile} {rect : Rect} {t : Table} {s : Size}
    (hs : classSize p t = .ok s)
    (hpad : 1 ≤ constant p "class.padding") (hsep : 0 ≤ constant p "class.separator")
    (hline : 0 ≤ constant p "line_h") (hw : s.w ≤ rect.w) (hh : s.h ≤ rect.h) :
    ∀ item ∈ classPrimitives p rect t, item.insideBox (if p = .cell then 1 else 0) rect := by
  obtain ⟨m, widest, _, htw, hsw, hsh⟩ := classSize_spec hs
  have hwidest := (tableWidth_spec htw).1
  obtain ⟨b, hb⟩ : ∃ b : Int, b = if p = .cell then 1 else 0 := ⟨_, rfl⟩
  have hb2 : (if p = .cell then (2 : Int) else 0) = 2 * b := by
    rw [hb]; split <;> simp
  have hb0 : 0 ≤ b ∧ b ≤ 1 := by rw [hb]; split <;> omega
  rw [← hb]
  rw [hb2] at hsh
  generalize hP : constant p "class.padding" = pad at *
  generalize hS : constant p "class.separator" = sep at *
  generalize hL : constant p "line_h" = lineH at *
  have htop : (if p = .cell then rect.y + 1 else rect.y) = rect.y + b := by
    rw [hb]; split <;> simp
  have hright : (if p = .cell then rect.x + rect.w - 1 else rect.x + rect.w) =
      rect.x + rect.w - b := by
    rw [hb]; split <;> simp
  have hbound := tops_bound hline hsep t.compartments (rect.y + b)
  have hle := tops_le hline hsep t.compartments (rect.y + b)
  have hge := tops_tail_ge hline hsep t.compartments (rect.y + b)
  have hcomp : t.compartments.length = 3 := rfl
  have hlen : ((t.compartments.length : Int) - 1) = 2 := by rw [hcomp]; rfl
  rw [hlen] at hbound hle
  intro item hi
  unfold classPrimitives at hi
  simp only [htop, hright, hP, hS, hL, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | ⟨y, hy, rfl⟩) | ⟨q, hq, rfl⟩
  · rfl
  · intro pt hpt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt
    have h1 := hge y hy
    have h2 := hle y (List.mem_of_mem_tail hy)
    rcases hpt with rfl | rfl <;> simp only [] <;> omega
  · have h := hbound q hq
    simp only [Primitive.insideBox]
    omega

/-! ### Adapter facts -/

theorem decorate_layoutDump (m : Model) (s : Scene) :
    (decorate m s).layoutDump = s.layoutDump := rfl

/-- The adapter's scene has the family's dump and budget flag; only the display list differs. -/
theorem layout_spec {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    ∃ sizes res, classSizes m = .ok sizes ∧
      Layered.layoutFamily (input m sizes) m.options = .ok res ∧
      r.scene.layoutDump = res.scene.layoutDump ∧ r.budgetExhausted = res.budgetExhausted := by
  unfold layout at h
  cases hs : classSizes m with
  | error e => rw [hs] at h; simp at h
  | ok sizes =>
    rw [hs] at h
    dsimp only at h
    cases hr : Layered.layoutFamily (input m sizes) m.options with
    | error e => rw [hr] at h; simp at h
    | ok res =>
      rw [hr] at h
      dsimp only at h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨sizes, res, rfl, hr, ?_, rfl⟩
      show (decorate m _).layoutDump = _
      rw [decorate_layoutDump]
      exact Scene.projectCellAttachments_layoutDump _ _

/-- Box and route ids keep the model's declaration order. -/
theorem layout_ids {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    r.scene.boxes.map (·.id) = m.boxes.map (·.id) ∧
      r.scene.routes.map (·.id) = m.routes.map (·.id) := by
  obtain ⟨sizes, res, _, hf, hd, _⟩ := layout_spec h
  have hid := Layered.layoutFamily_ids hf
  have hb : r.scene.boxes = res.scene.boxes := congrArg LayoutDump.boxes hd
  have hr : r.scene.routes = res.scene.routes := congrArg LayoutDump.routes hd
  rw [hb, hr]
  exact hid

/-- Class validity reduces to the family's: the adapter changes sizes and the display list only. -/
theorem layout_valid_of_family
    (hfam : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      Layered.layoutFamily inp o = .ok res → Validator.check res.scene.layoutDump = true)
    {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    Validator.check r.scene.layoutDump = true := by
  obtain ⟨sizes, res, _, hf, hd, _⟩ := layout_spec h
  rw [hd]
  exact hfam _ _ _ hf

end Class
end Kinds
end Elegant
