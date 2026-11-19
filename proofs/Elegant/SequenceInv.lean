import Elegant.SequenceFacts
import Elegant.SequenceAnc

set_option autoImplicit false

/-! The walk invariant of the sequence family: what holds of the boxes, labels, and open fragments after
every event, enough to show that the frames of the fragments keep clear of foreign boxes and labels
and hold their own (`spec/layout/sequence.md`, sequence-54). The ghost list `E` records every settled
box and label rectangle with the id of the fragment that hosts it. -/

namespace Elegant
namespace Sequence

/-- A settled rectangle of the walk: a box (`self`) or a label, with the id of its hosting fragment
(`""` when none). -/
structure Ent where
  r : Rect
  host : String
  self : Option Nat

def entId (m : Model) (e : Ent) : String := (e.self.map (boxId m)).getD ""

/-- The row at which the walk starts, below the headers. -/
def B0 (pl : Plan) : Int := pl.bandTop + pl.bandHeight + 2 * pl.c.boxMargin

/-- The rows that a fragment header takes. -/
def adv (pl : Plan) (f : FragRun) : Int := fragmentAdvance pl f.kind f.box

/-- The rows that a divider takes. -/
def hgt (pl : Plan) (d : Divider) : Int := sectionHeight pl.c (pl.linesAt d.label).length

/-- The row bands that a fragment holds for its header and its dividers. -/
def bandsOf (pl : Plan) (f : FragRun) : List (Int × Int) :=
  (f.top, f.top + adv pl f) :: f.dividers.map fun d => (d.row, d.row + hgt pl d)

/-- The rectangle stays out of the band. -/
def Avoids (r : Rect) (b : Int × Int) : Prop := r.y + r.h ≤ b.1 ∨ b.2 ≤ r.y

/-- Two settled rectangles are apart, or one hosts the other through a chain of fragments. -/
def Sep (m : Model) (e e' : Ent) : Prop :=
  Disjoint e.r e'.r ∨ ChainS m e'.host (entId m e) ∨ ChainS m e.host (entId m e')

/-- Box `i` of the model is a group. -/
def IsGroupAt (m : Model) (i : Nat) : Prop := ∃ b, m.boxes[i]? = some b ∧ b.role = BoxRole.group

/-- The frame list `fs` after members `ms` joined its innermost fragment. -/
def fragsAddAll (fs : List FragRun) (ms : List Rect) : List FragRun :=
  match fs with
  | [] => []
  | f :: rest => { f with members := f.members ++ ms } :: rest

theorem foldl_fragsAdd (ms : List Rect) : ∀ (fs : List FragRun),
    ms.foldl fragsAdd fs = fragsAddAll fs ms := by
  induction ms with
  | nil =>
    intro fs
    cases fs <;> simp [fragsAddAll]
  | cons r t ih =>
    intro fs
    cases fs with
    | nil => simp [fragsAdd, fragsAddAll, ih]
    | cons f rest =>
      simp only [List.foldl_cons, fragsAdd]
      rw [ih]
      simp [fragsAddAll, List.append_assoc]

theorem getD_set_gen {α : Type} (l : List α) (i j : Nat) (v d : α) :
    (l.set i v).getD j d = if i = j ∧ i < l.length then v else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < l.length <;> simp [h2]
  · simp [h]

structure Inv (pl : Plan) (hdr lab0 : List Rect) (stack placed : List Nat) (w : Walk)
    (E : List Ent) : Prop where
  stack_eq : w.fragments.map (·.box) = stack
  chain : ChainOK pl.m stack
  stack_lt : ∀ s ∈ stack, s < pl.m.boxes.length
  stack_len : stack.length ≤ pl.m.boxes.length
  stack_nodup : stack.Nodup
  placed_lt : ∀ i ∈ placed, i < pl.m.boxes.length
  stack_placed : ∀ s ∈ stack, s ∈ placed
  lenR : w.boxRects.length = pl.m.boxes.length
  lenL : w.labelRects.length = pl.m.labels.length
  unplaced : ∀ i, i ∉ placed → w.boxRects.getD i rectZero = hdr.getD i rectZero
  frag : FragInv w.fragments w.cursor
  cursor : B0 pl ≤ w.cursor
  frag_top : ∀ f ∈ w.fragments, B0 pl ≤ f.top
  frag_adv : ∀ f ∈ w.fragments, f.top + adv pl f ≤ w.cursor ∧
    ∀ d ∈ f.dividers, f.top + adv pl f ≤ d.row ∧ d.row + hgt pl d ≤ w.cursor
  frag_members : ∀ f ∈ w.fragments, ∀ r ∈ f.members, f.top + adv pl f ≤ r.y
  frag_nested : w.fragments.Pairwise fun g f =>
    f.top + adv pl f ≤ g.top ∧ ∀ d ∈ f.dividers, d.row + hgt pl d ≤ g.top
  ent_ok : ∀ e ∈ E, B0 pl ≤ e.r.y ∧ 0 ≤ e.r.w ∧ 0 ≤ e.r.h ∧ e.r.y + e.r.h ≤ w.cursor
  ent_host : ∀ e ∈ E, e.host = "" ∨ ∃ t ∈ placed, e.host = boxId pl.m t
  ent_j1 : ∀ e ∈ E, ∀ f ∈ w.fragments, e.r.y + e.r.h ≤ f.top ∨
    (ChainS pl.m e.host (boxId pl.m f.box) ∧ ∀ b ∈ bandsOf pl f, Avoids e.r b)
  ent_cover : ∀ e ∈ E, ∀ f ∈ w.fragments, e.host = boxId pl.m f.box →
    ∃ r ∈ f.members, r.Contained e.r
  ent_sep : ∀ e ∈ E, ∀ e' ∈ E, (∃ i, e.self = some i ∧ IsGroupAt pl.m i) → e ≠ e' → Sep pl.m e e'
  ent_strict : ∀ e ∈ E, ∀ g, g ∈ placed → g ∉ stack → e.host = boxId pl.m g →
    (w.boxRects.getD g rectZero).StrictInside e.r
  link_box : ∀ i, i ∈ placed → i ∉ stack →
    ∃ e ∈ E, e.self = some i ∧ e.r = w.boxRects.getD i rectZero ∧ e.host = boxParent pl.m i
  link_lab : ∀ p, w.labelRects.getD p rectZero = lab0.getD p rectZero ∨
    ∃ e ∈ E, e.self = none ∧ e.r = w.labelRects.getD p rectZero

/-- The facts about the model that the invariant steps use. -/
structure ModelFacts (m : Model) : Prop where
  nodup : (m.boxes.map (·.id)).Nodup
  nonempty : ∀ i, i < m.boxes.length → boxId m i ≠ ""

theorem boxId_inj {m : Model} (hf : ModelFacts m) {i j : Nat} (hi : i < m.boxes.length)
    (hj : j < m.boxes.length) (h : boxId m i = boxId m j) : i = j := by
  have hLi : i < (m.boxes.map (·.id)).length := by simpa using hi
  have hLj : j < (m.boxes.map (·.id)).length := by simpa using hj
  refine hf.nodup.eq_of_getElem_eq hLi hLj ?_
  simpa [boxId, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using h

theorem initWalk_lenR (pl : Plan) (cs : List Int) :
    (initWalk pl cs).boxRects.length = pl.m.boxes.length := by
  simp [initWalk, placeHeaders, headerRects]

theorem centreLabel_length (pl : Plan) (ls : List Rect) (label : Option Nat) (frame : Rect) (top : Int) :
    (centreLabel pl ls label frame top).length = ls.length := by
  unfold centreLabel
  split
  · rfl
  · split <;> simp

theorem headerLabels_length (pl : Plan) (rects : List Rect) :
    (headerLabels pl rects).length = pl.m.labels.length := by
  unfold headerLabels
  have key : ∀ (l : List (ModelBox × Nat)) (ls : List Rect), ls.length = pl.m.labels.length →
      (l.foldl (fun ls (bi : ModelBox × Nat) =>
        if isParticipantBox bi.1 then
          centreLabel pl ls (labelPosById pl.m (bi.1.id ++ ".label")) (rects.getD bi.2 rectZero)
            ((rects.getD bi.2 rectZero).y + pl.c.boxTextMargin)
        else ls) ls).length = pl.m.labels.length := by
    intro l
    induction l with
    | nil => intro ls h; exact h
    | cons b t ih =>
      intro ls h
      simp only [List.foldl_cons]
      apply ih
      split
      · rw [centreLabel_length]; exact h
      · exact h
  exact key _ _ (by simp)

theorem inv_init {pl : Plan} {cs : List Int} :
    Inv pl (headerRects pl cs) (headerLabels pl (headerRects pl cs)) [] [] (initWalk pl cs) [] := by
  refine { stack_eq := ?_, chain := ?_, stack_lt := ?_, stack_len := ?_, stack_nodup := ?_,
           placed_lt := ?_, stack_placed := ?_, lenR := ?_, lenL := ?_, unplaced := ?_, frag := ?_,
           cursor := ?_, frag_top := ?_, frag_adv := ?_, frag_members := ?_, frag_nested := ?_,
           ent_ok := ?_, ent_host := ?_, ent_j1 := ?_, ent_cover := ?_, ent_sep := ?_,
           ent_strict := ?_, link_box := ?_, link_lab := ?_ }
  · rfl
  · exact trivial
  · intro s hs; simp at hs
  · simp
  · exact List.nodup_nil
  · intro i hi; simp at hi
  · intro s hs; simp at hs
  · exact initWalk_lenR pl cs
  · show (headerLabels pl (headerRects pl cs)).length = _
    exact headerLabels_length pl _
  · intro i _; rfl
  · exact initWalk_inv pl cs
  · exact Int.le_refl _
  · intro f hf; simp [initWalk] at hf
  · intro f hf; simp [initWalk] at hf
  · intro f hf; simp [initWalk] at hf
  · exact List.Pairwise.nil
  · intro e he; simp at he
  · intro e he; simp at he
  · intro e he; simp at he
  · intro e he; simp at he
  · intro e he; simp at he
  · intro e he; simp at he
  · intro i hi; simp at hi
  · intro p; exact Or.inl rfl

theorem host_not_new {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E) {n : Nat}
    (hn : n < pl.m.boxes.length) (hnp : n ∉ placed) {e : Ent} (he : e ∈ E)
    (h : e.host = boxId pl.m n) : False := by
  rcases hI.ent_host e he with h0 | ⟨t, ht, h0⟩
  · exact hfm.nonempty n hn (h ▸ h0 ▸ rfl)
  · have := boxId_inj hfm (hI.placed_lt t ht) hn (h0 ▸ h ▸ rfl)
    exact hnp (this ▸ ht)

theorem inv_push {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hpl : pl.Wf) (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E)
    (kind box : Nat) (hbox : box < pl.m.boxes.length) (hnp : box ∉ placed)
    (hpar : boxParent pl.m box = topId pl.m stack) (hlen : stack.length + 1 ≤ pl.m.boxes.length) :
    Inv pl hdr lab0 (box :: stack) (box :: placed) (stepFragmentStart pl w kind box) E := by
  have hadv := fragmentAdvance_pos pl hpl kind box
  have hF : (stepFragmentStart pl w kind box).fragments =
      ⟨box, kind, w.cursor, [], []⟩ :: w.fragments := rfl
  have hCur : (stepFragmentStart pl w kind box).cursor = w.cursor + fragmentAdvance pl kind box := rfl
  have hB := hI.cursor
  refine { stack_eq := ?_, chain := ?_, stack_lt := ?_, stack_len := ?_, stack_nodup := ?_,
           placed_lt := ?_, stack_placed := ?_, lenR := ?_, lenL := ?_, unplaced := ?_, frag := ?_,
           cursor := ?_, frag_top := ?_, frag_adv := ?_, frag_members := ?_, frag_nested := ?_,
           ent_ok := ?_, ent_host := ?_, ent_j1 := ?_, ent_cover := ?_, ent_sep := ?_,
           ent_strict := ?_, link_box := ?_, link_lab := ?_ }
  · rw [hF]; show box :: w.fragments.map (·.box) = box :: stack; rw [hI.stack_eq]
  · exact ⟨hpar, hI.chain⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hbox
    · exact hI.stack_lt s hs
  · simp only [List.length_cons]; exact hlen
  · exact List.nodup_cons.mpr ⟨fun h => hnp (hI.stack_placed box h), hI.stack_nodup⟩
  · intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hbox
    · exact hI.placed_lt i hi
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hI.stack_placed s hs)
  · exact hI.lenR
  · exact hI.lenL
  · intro i hi
    exact hI.unplaced i (fun h => hi (List.mem_cons_of_mem _ h))
  · exact stepFragmentStart_inv pl hpl w kind box hI.frag
  · rw [hCur]; omega
  · intro f hf
    rw [hF] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hB
    · exact hI.frag_top f hf
  · intro f hf
    rw [hF] at hf
    rw [hCur]
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨by show w.cursor + fragmentAdvance pl kind box ≤ _; omega, ?_⟩
      intro d hd; simp at hd
    · have h1 := hI.frag_adv f hf
      refine ⟨by omega, fun d hd => ?_⟩
      have := h1.2 d hd
      exact ⟨this.1, by omega⟩
  · intro f hf r hr
    rw [hF] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · simp at hr
    · exact hI.frag_members f hf r hr
  · rw [hF]
    refine List.pairwise_cons.mpr ⟨fun f hf => ?_, hI.frag_nested⟩
    have h1 := hI.frag_adv f hf
    exact ⟨h1.1, fun d hd => (h1.2 d hd).2⟩
  · intro e he
    have h := hI.ent_ok e he
    rw [hCur]
    exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩
  · intro e he
    exact (hI.ent_host e he).imp_right fun ⟨t, ht, h⟩ => ⟨t, List.mem_cons_of_mem _ ht, h⟩
  · intro e he f hf
    rw [hF] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Or.inl (by have := hI.ent_ok e he; show e.r.y + e.r.h ≤ w.cursor; omega)
    · exact hI.ent_j1 e he f hf
  · intro e he f hf hh
    rw [hF] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (host_not_new hfm hI hbox hnp he hh).elim
    · exact hI.ent_cover e he f hf hh
  · exact hI.ent_sep
  · intro e he g hg hgs hh
    have hg' : g ∈ placed := by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact absurd List.mem_cons_self hgs
      · exact hg
    exact hI.ent_strict e he g hg' (fun h => hgs (List.mem_cons_of_mem _ h)) hh
  · intro i hi his
    have hi' : i ∈ placed := by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact absurd List.mem_cons_self his
      · exact hi
    exact hI.link_box i hi' (fun h => his (List.mem_cons_of_mem _ h))
  · exact hI.link_lab

theorem inv_else {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hpl : pl.Wf) (hI : Inv pl hdr lab0 stack placed w E) (box sect : Nat)
    (hne : w.fragments ≠ []) :
    Inv pl hdr lab0 stack placed (stepFragmentElse pl w box sect) E := by
  obtain ⟨f, rest, hS⟩ : ∃ f rest, w.fragments = f :: rest := by
    cases h : w.fragments with
    | nil => exact absurd h hne
    | cons f rest => exact ⟨f, rest, rfl⟩
  have hpos := sectionHeight_pos pl hpl (pl.linesAt (sectionLabel pl box sect)).length
  have hF : (stepFragmentElse pl w box sect).fragments =
      { f with dividers := f.dividers ++ [⟨w.cursor, sectionLabel pl box sect⟩] } :: rest := by
    unfold stepFragmentElse; rw [hS]
  have hCur : (stepFragmentElse pl w box sect).cursor =
      w.cursor + sectionHeight pl.c (pl.linesAt (sectionLabel pl box sect)).length := rfl
  have hf0 := hI.frag_adv f (by rw [hS]; exact List.mem_cons_self)
  refine { stack_eq := ?_, chain := hI.chain, stack_lt := hI.stack_lt, stack_len := hI.stack_len,
           stack_nodup := hI.stack_nodup, placed_lt := hI.placed_lt, stack_placed := hI.stack_placed,
           lenR := hI.lenR, lenL := hI.lenL, unplaced := hI.unplaced, frag := ?_,
           cursor := ?_, frag_top := ?_, frag_adv := ?_, frag_members := ?_, frag_nested := ?_,
           ent_ok := ?_, ent_host := hI.ent_host, ent_j1 := ?_, ent_cover := ?_, ent_sep := hI.ent_sep,
           ent_strict := hI.ent_strict, link_box := hI.link_box, link_lab := hI.link_lab }
  · rw [hF]; have := hI.stack_eq; rw [hS] at this; simpa using this
  · exact stepFragmentElse_inv pl hpl w box sect hI.frag
  · rw [hCur]; have := hI.cursor; omega
  · intro g hg
    rw [hF] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hI.frag_top f (by rw [hS]; exact List.mem_cons_self)
    · exact hI.frag_top g (by rw [hS]; exact List.mem_cons_of_mem _ hg)
  · intro g hg
    rw [hF] at hg
    rw [hCur]
    rcases List.mem_cons.mp hg with rfl | hg
    · refine ⟨by show f.top + adv pl f ≤ _; omega, fun d hd => ?_⟩
      rcases List.mem_append.mp hd with hd | hd
      · have := hf0.2 d hd
        exact ⟨this.1, by omega⟩
      · have hd' : d = ⟨w.cursor, sectionLabel pl box sect⟩ := by simpa using hd
        subst hd'
        refine ⟨hf0.1, ?_⟩
        show w.cursor + sectionHeight pl.c (pl.linesAt (sectionLabel pl box sect)).length ≤ _
        omega
    · have h1 := hI.frag_adv g (by rw [hS]; exact List.mem_cons_of_mem _ hg)
      exact ⟨by omega, fun d hd => ⟨(h1.2 d hd).1, by have := (h1.2 d hd).2; omega⟩⟩
  · intro g hg r hr
    rw [hF] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hI.frag_members f (by rw [hS]; exact List.mem_cons_self) r hr
    · exact hI.frag_members g (by rw [hS]; exact List.mem_cons_of_mem _ hg) r hr
  · rw [hF]
    have h := hI.frag_nested
    rw [hS] at h
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp h
    exact List.pairwise_cons.mpr ⟨h1, h2⟩
  · intro e he
    have h := hI.ent_ok e he
    rw [hCur]
    exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩
  · intro e he g hg
    rw [hF] at hg
    have hok := hI.ent_ok e he
    have hbands : bandsOf pl { f with dividers := f.dividers ++ [⟨w.cursor, sectionLabel pl box sect⟩] } =
        bandsOf pl f ++ [(w.cursor, w.cursor + sectionHeight pl.c (pl.linesAt (sectionLabel pl box sect)).length)] := by
      simp [bandsOf, adv, hgt, List.map_append]
    rcases List.mem_cons.mp hg with h0 | hg
    · rw [h0]
      rcases hI.ent_j1 e he f (by rw [hS]; exact List.mem_cons_self) with h | ⟨hc, hb⟩
      · exact Or.inl h
      · right
        refine ⟨hc, ?_⟩
        intro b hb'
        rw [hbands] at hb'
        rcases List.mem_append.mp hb' with hb' | hb'
        · exact hb b hb'
        · have : b = (w.cursor, w.cursor + sectionHeight pl.c (pl.linesAt (sectionLabel pl box sect)).length) := by
            simpa using hb'
          rw [this]
          exact Or.inl hok.2.2.2
    · exact hI.ent_j1 e he g (by rw [hS]; exact List.mem_cons_of_mem _ hg)
  · intro e he g hg hh
    rw [hF] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hI.ent_cover e he f (by rw [hS]; exact List.mem_cons_self) hh
    · exact hI.ent_cover e he g (by rw [hS]; exact List.mem_cons_of_mem _ hg) hh

end Sequence
end Elegant
