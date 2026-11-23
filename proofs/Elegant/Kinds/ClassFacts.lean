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

theorem foldl_max_spec {α : Type} (f : α → Int) :
    ∀ (xs : List α) (w0 : Int), w0 ≤ xs.foldl (fun w a => max w (f a)) w0 ∧
      ∀ a ∈ xs, f a ≤ xs.foldl (fun w a => max w (f a)) w0
  | [], w0 => ⟨Int.le_refl _, fun a ha => by simp at ha⟩
  | a :: xs, w0 => by
    obtain ⟨h1, h2⟩ := foldl_max_spec f xs (max w0 (f a))
    simp only [List.foldl_cons]
    refine ⟨by omega, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · exact h2 b hb

theorem compartmentWidth_spec (lines : List Measure.Line) :
    0 ≤ compartmentWidth lines ∧ ∀ l ∈ lines, l.width ≤ compartmentWidth lines :=
  foldl_max_spec (fun l : Measure.Line => l.width) lines 0

theorem tableWidth_spec (cs : List (List Measure.Line)) :
    0 ≤ tableWidth cs ∧ ∀ c ∈ cs, ∀ l ∈ c, l.width ≤ tableWidth cs := by
  unfold tableWidth
  obtain ⟨h0, h1⟩ := foldl_max_spec compartmentWidth cs 0
  refine ⟨h0, fun c hc l hl => ?_⟩
  have h2 := (compartmentWidth_spec c).2 l hl
  have h3 := h1 c hc
  omega

theorem checkSize_spec {w h : Int} {s : Size} (hs : checkSize w h = .ok s) :
    s.w = w ∧ s.h = h := by
  unfold checkSize at hs
  split at hs
  · simp at hs
  · simp only [Except.ok.injEq] at hs
    subst hs
    exact ⟨rfl, rfl⟩

theorem tableSize_spec {p : Profile} {cs : List (List Measure.Line)} {s : Size}
    (h : tableSize p cs = .ok s) :
    s.w = tableWidth cs + 2 * LayoutConst.class_padding.get p ∧
      s.h = tableHeight (LayoutConst.line_h.get p) cs +
        ((cs.length : Int) - 1) * LayoutConst.class_separator.get p + (if p = .cell then 2 else 0) := by
  unfold tableSize at h
  exact checkSize_spec h

/-- The three compartments are measured in order, each under the metric of its index. -/
theorem measureTable_spec {fontFamily : Bool} {p : Profile} {t : Table} {cs : List (List Measure.Line)}
    (h : measureTable p t fontFamily = .ok cs) :
    ∃ m0 m1 m2 head attributes methods,
      compartmentMetric p 0 fontFamily = .ok m0 ∧ compartmentMetric p 1 fontFamily = .ok m1 ∧
      compartmentMetric p 2 fontFamily = .ok m2 ∧ measureCompartment m0 t.head = .ok head ∧
      measureCompartment m1 t.attributes = .ok attributes ∧
      measureCompartment m2 t.methods = .ok methods ∧ cs = [head, attributes, methods] := by
  unfold measureTable at h
  split at h
  · simp at h
  · rename_i m0 h0
    split at h
    · simp at h
    · rename_i head hh
      split at h
      · simp at h
      · rename_i m1 h1
        split at h
        · simp at h
        · rename_i attributes ha
          split at h
          · simp at h
          · rename_i m2 h2
            split at h
            · simp at h
            · rename_i methods hm
              simp only [Except.ok.injEq] at h
              exact ⟨m0, m1, m2, head, attributes, methods, h0, h1, h2, hh, ha, hm, h.symm⟩

/-- Every row of a compartment contributes its lines to the compartment. -/
theorem measureCompartment_covers (metric : Measure.Metric) :
    ∀ (rows : List String) (out : List Measure.Line), measureCompartment metric rows = .ok out →
      ∀ row ∈ rows, ∃ ls, rowLines metric row = .ok ls ∧ ∀ l ∈ ls, l ∈ out
  | [], _, _, row, hr => by simp at hr
  | r :: rs, out, h, row, hr => by
    simp only [measureCompartment] at h
    split at h
    · simp at h
    · rename_i ls hls
      split at h
      · simp at h
      · rename_i rest hrest
        simp only [Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨ls, hls, fun l hl => List.mem_append_left _ hl⟩
        · obtain ⟨ls', h1, h2⟩ := measureCompartment_covers metric rs rest hrest row hr
          exact ⟨ls', h1, fun l hl => List.mem_append_right _ (h2 l hl)⟩

/-- class-051 and class-052 as a closed form: the width is the widest line plus twice the padding;
the height is the compartment heights, one separator between neighbouring compartments (two for
three compartments), and two border rows in the cell profile. -/
theorem classSize_spec {fontFamily : Bool} {p : Profile} {t : Table} {s : Size} (h : classSize p t fontFamily = .ok s) :
    ∃ cs, measureTable p t fontFamily = .ok cs ∧ cs.length = 3 ∧
      s.w = tableWidth cs + 2 * LayoutConst.class_padding.get p ∧
      s.h = tableHeight (LayoutConst.line_h.get p) cs + 2 * LayoutConst.class_separator.get p +
        (if p = .cell then 2 else 0) := by
  unfold classSize at h
  cases hm : measureTable p t fontFamily with
  | error e => rw [hm] at h; simp at h
  | ok cs =>
    rw [hm] at h
    dsimp only at h
    obtain ⟨hw, hh⟩ := tableSize_spec h
    obtain ⟨_, _, _, head, attributes, methods, _, _, _, _, _, _, hcs⟩ := measureTable_spec hm
    have hlen : cs.length = 3 := by rw [hcs]; rfl
    refine ⟨cs, rfl, hlen, hw, ?_⟩
    rw [hh, hlen]
    omega

theorem compartmentHeight_nonneg {α : Type} {lineH : Int} (hl : 0 ≤ lineH) (c : List α) :
    0 ≤ compartmentHeight lineH c :=
  Int.mul_nonneg (by omega) hl

/-- An empty compartment retains one row. -/
theorem compartmentHeight_empty {α : Type} (lineH : Int) :
    compartmentHeight lineH ([] : List α) = lineH := by
  have : (max 1 ([] : List α).length : Int) = 1 := rfl
  unfold compartmentHeight
  rw [this, Int.one_mul]

theorem compartmentHeight_ge {α : Type} {lineH : Int} (hl : 0 ≤ lineH) (c : List α) :
    lineH ≤ compartmentHeight lineH c := by
  unfold compartmentHeight
  have : (1 : Int) ≤ (max 1 c.length : Int) := by omega
  calc lineH = 1 * lineH := (Int.one_mul _).symm
    _ ≤ _ := Int.mul_le_mul_of_nonneg_right this hl

theorem tableHeight_nonneg {α : Type} {lineH : Int} (hl : 0 ≤ lineH) :
    ∀ cs : List (List α), 0 ≤ tableHeight lineH cs
  | [] => Int.le_refl _
  | c :: cs => by
    have := tableHeight_nonneg hl cs
    have := compartmentHeight_nonneg hl c
    simp only [tableHeight]
    omega

/-- Every compartment takes at least one row. -/
theorem tableHeight_ge {α : Type} {lineH : Int} (hl : 0 ≤ lineH) :
    ∀ cs : List (List α), (cs.length : Int) * lineH ≤ tableHeight lineH cs
  | [] => by simp [tableHeight]
  | c :: cs => by
    have ih := tableHeight_ge hl cs
    have hc := compartmentHeight_ge hl c
    have e : (((c :: cs).length : Nat) : Int) * lineH = (cs.length : Int) * lineH + lineH := by
      simp [Int.add_mul]
    simp only [tableHeight]
    omega

/-- Every line of every row of every compartment fits in the table between its paddings. -/
theorem classSize_covers_rows {fontFamily : Bool} {p : Profile} {t : Table} {s : Size} (h : classSize p t fontFamily = .ok s) :
    ∀ index c, t.compartments[index]? = some c → ∀ row ∈ c, ∃ m ls,
      compartmentMetric p index fontFamily = .ok m ∧ rowLines m row = .ok ls ∧
      ∀ l ∈ ls, l.width + 2 * LayoutConst.class_padding.get p ≤ s.w := by
  obtain ⟨cs, hm, _, hw, _⟩ := classSize_spec h
  obtain ⟨m0, m1, m2, head, attributes, methods, hm0, hm1, hm2, hh, ha, hme, hcs⟩ :=
    measureTable_spec hm
  have hmax := tableWidth_spec cs
  subst hcs
  intro index c hc row hr
  match index, hc with
  | 0, hc =>
    simp only [Table.compartments, List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    obtain ⟨ls, hl, hls⟩ := measureCompartment_covers m0 t.head head hh row hr
    refine ⟨m0, ls, hm0, hl, fun l hl' => ?_⟩
    have := hmax.2 head (by simp) l (hls l hl')
    omega
  | 1, hc =>
    simp only [Table.compartments, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hc
    subst hc
    obtain ⟨ls, hl, hls⟩ := measureCompartment_covers m1 t.attributes attributes ha row hr
    refine ⟨m1, ls, hm1, hl, fun l hl' => ?_⟩
    have := hmax.2 attributes (by simp) l (hls l hl')
    omega
  | 2, hc =>
    simp only [Table.compartments, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hc
    subst hc
    obtain ⟨ls, hl, hls⟩ := measureCompartment_covers m2 t.methods methods hme row hr
    refine ⟨m2, ls, hm2, hl, fun l hl' => ?_⟩
    have := hmax.2 methods (by simp) l (hls l hl')
    omega
  | n + 3, hc => simp [Table.compartments] at hc

/-! ### Drawing stays inside the placed box (class-052) -/

theorem tops_ge {α : Type} {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep) :
    ∀ (cs : List (List α)) (y : Int), ∀ y' ∈ tops lineH sep y cs, y ≤ y'
  | [], y, y', h => by simp [tops] at h
  | c :: cs, y, y', h => by
    have hc := compartmentHeight_nonneg hl c
    simp only [tops, List.mem_cons] at h
    rcases h with rfl | h
    · exact Int.le_refl _
    · have := tops_ge hl hs cs (y + compartmentHeight lineH c + sep) y' h
      omega

theorem tops_tail_ge {α : Type} {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep)
    (cs : List (List α)) (y : Int) : ∀ y' ∈ (tops lineH sep y cs).tail, y + sep ≤ y' := by
  cases cs with
  | nil => simp [tops]
  | cons c cs =>
    intro y' h
    have hc := compartmentHeight_nonneg hl c
    have := tops_ge hl hs cs (y + compartmentHeight lineH c + sep) y' h
    omega

theorem tops_le {α : Type} {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep) :
    ∀ (cs : List (List α)) (y : Int), ∀ y' ∈ tops lineH sep y cs,
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

theorem tops_bound {α : Type} {lineH sep : Int} (hl : 0 ≤ lineH) (hs : 0 ≤ sep) :
    ∀ (cs : List (List α)) (y : Int), ∀ q ∈ (tops lineH sep y cs).zip cs,
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
theorem classPrimitives_inside {p : Profile} {rect : Rect} {cs : List (List Measure.Line)}
    {s : Size} (hs : tableSize p cs = .ok s)
    (hpad : 1 ≤ LayoutConst.class_padding.get p) (hsep : 0 ≤ LayoutConst.class_separator.get p)
    (hline : 0 ≤ LayoutConst.line_h.get p) (hw : s.w ≤ rect.w) (hh : s.h ≤ rect.h) :
    ∀ item ∈ classPrimitives p rect cs, item.insideBox (if p = .cell then 1 else 0) rect := by
  obtain ⟨hsw, hsh⟩ := tableSize_spec hs
  have hwidest := (tableWidth_spec cs).1
  obtain ⟨b, hb⟩ : ∃ b : Int, b = if p = .cell then 1 else 0 := ⟨_, rfl⟩
  have hb2 : (if p = .cell then (2 : Int) else 0) = 2 * b := by
    rw [hb]; split <;> simp
  have hb0 : 0 ≤ b ∧ b ≤ 1 := by rw [hb]; split <;> omega
  rw [← hb]
  rw [hb2] at hsh
  generalize hP : LayoutConst.class_padding.get p = pad at *
  generalize hS : LayoutConst.class_separator.get p = sep at *
  generalize hL : LayoutConst.line_h.get p = lineH at *
  have htop : (if p = .cell then rect.y + 1 else rect.y) = rect.y + b := by
    rw [hb]; split <;> simp
  have hright : (if p = .cell then rect.x + rect.w - 1 else rect.x + rect.w) =
      rect.x + rect.w - b := by
    rw [hb]; split <;> simp
  have hbound := tops_bound hline hsep cs (rect.y + b)
  have hle := tops_le hline hsep cs (rect.y + b)
  have hge := tops_tail_ge hline hsep cs (rect.y + b)
  intro item hi
  unfold classPrimitives at hi
  simp only [htop, hright, hP, hS, hL, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · rfl
  · intro pt hpt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt
    have h1 := hge y hy
    have h2 := hle y (List.mem_of_mem_tail hy)
    rcases hpt with rfl | rfl <;> simp only [] <;> omega
  · have h := hbound x.1 (List.fst_mem_of_mem_zipIdx hx)
    simp only [compartmentText, Primitive.insideBox]
    omega

/-! ### Adapter facts -/

/-- The drawing replacement changes the display list only. -/
theorem decorate_layoutDump {m : Model} {s s' : Scene} (h : decorate m s = .ok s') :
    s'.layoutDump = s.layoutDump := by
  unfold decorate at h
  cases hm : s.items.mapM (decorateGroup m s) with
  | error e => rw [hm] at h; simp at h
  | ok items =>
    rw [hm] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl

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
      cases hd : decorate m (res.scene.projectCellAttachments (routeMarkers m)) with
      | error e => rw [hd] at h; simp at h
      | ok scene =>
        rw [hd] at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨sizes, res, rfl, hr,
          (decorate_layoutDump hd).trans (Scene.projectCellAttachments_layoutDump _ _), rfl⟩

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
