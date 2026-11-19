import Elegant.SequenceValid3

set_option autoImplicit false

/-! The ancestors of the dump boxes, and the strict containment of a settled box in its parent and
in each of its ancestors (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem box?_eq_none {pl : Plan} {cs : List Int} {w : Walk} {s : String}
    (h : pl.m.boxes.find? (fun b => b.id == s) = none) : (dumpOf pl cs w).box? s = none := by
  unfold LayoutDump.box?
  rw [List.find?_eq_none]
  intro x hx
  obtain ⟨i, b, hb, rfl⟩ := mem_dump_boxes.mp hx
  have := List.find?_eq_none.mp h b (List.mem_of_getElem? hb)
  exact this

theorem box?_eq_some {pl : Plan} {cs : List Int} {w : Walk} (hfm : ModelFacts pl.m) {s : String}
    {b : ModelBox} (h : pl.m.boxes.find? (fun b => b.id == s) = some b) :
    ∃ i, pl.m.boxes[i]? = some b ∧ (dumpOf pl cs w).box? s = some (dbox pl w b i) := by
  have hmem := List.mem_of_find?_eq_some h
  have hs : (b.id == s) = true := List.find?_some (p := fun b => b.id == s) (l := pl.m.boxes) h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  refine ⟨i, hi, ?_⟩
  have := box?_dbox (cs := cs) (w := w) hfm hi
  rw [beq_iff_eq] at hs
  rw [← hs]
  exact this

theorem anc_go_eq {pl : Plan} {cs : List Int} {w : Walk} (hfm : ModelFacts pl.m) :
    ∀ (k : Nat) (s : String), LayoutDump.ancestors.go (dumpOf pl cs w) k s = ancGo pl.m k s := by
  intro k
  induction k with
  | zero => intro s; simp [LayoutDump.ancestors.go, ancGo]
  | succ k ih =>
    intro s
    cases hf : pl.m.boxes.find? (fun b => b.id == s) with
    | none =>
      simp only [LayoutDump.ancestors.go, ancGo, hf, box?_eq_none hf]
    | some b =>
      obtain ⟨i, hi, hd⟩ := box?_eq_some (cs := cs) (w := w) hfm hf
      simp only [LayoutDump.ancestors.go, ancGo, hf, hd]
      show (if b.parent = "" then [] else b.parent :: LayoutDump.ancestors.go (dumpOf pl cs w) k b.parent) = _
      rw [ih]

theorem ancestors_eq {pl : Plan} {cs : List Int} {w : Walk} (hfm : ModelFacts pl.m) (s : String) :
    (dumpOf pl cs w).ancestors s = ancGo pl.m pl.m.boxes.length s := by
  unfold LayoutDump.ancestors
  have hl : (dumpOf pl cs w).boxes.length = pl.m.boxes.length := by
    rw [dump_boxes]
    simp
  rw [hl]
  exact anc_go_eq hfm _ _

theorem parent_placed {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {i : Nat} (hip : i ∈ ck.placed)
    (hne : boxParent pl.m i ≠ "") :
    ∃ t, t ∈ ck.placed ∧ t < pl.m.boxes.length ∧ boxId pl.m t = boxParent pl.m i ∧
      (rr w t).StrictInside (rr w i) := by
  obtain ⟨e, he, hs, hr, hh⟩ := F.inv.link_box i hip (by simp)
  rcases F.inv.ent_host e he with h0 | ⟨t, ht, h0⟩
  · rw [hh] at h0
    exact absurd h0 hne
  · refine ⟨t, ht, F.inv.placed_lt t ht, by rw [← h0, hh], ?_⟩
    have := F.inv.ent_strict e he t ht (by simp) h0
    rw [hr] at this
    exact this

theorem strict_chain {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) :
    ∀ (k i g : Nat), i ∈ ck.placed → g < pl.m.boxes.length →
      boxId pl.m g ∈ ancGo pl.m k (boxId pl.m i) → (rr w g).StrictInside (rr w i) := by
  intro k
  induction k with
  | zero => intro i g _ _ h; simp [ancGo] at h
  | succ k ih =>
    intro i g hip hg hmem
    have hi := F.inv.placed_lt i hip
    obtain ⟨b, hb⟩ : ∃ b, pl.m.boxes[i]? = some b := ⟨pl.m.boxes[i], List.getElem?_eq_getElem hi⟩
    have hfind := find_box_id pl.m F.fm.nodup i hi
    rw [hb] at hfind
    by_cases hp : b.parent = ""
    · simp [ancGo, hfind, hp] at hmem
    · rw [ancGo_found pl.m k _ b hfind hp] at hmem
      have hne : boxParent pl.m i ≠ "" := by rw [boxParent_of_getElem pl.m i b hb]; exact hp
      obtain ⟨t, ht, htl, hid, hst⟩ := parent_placed F hip hne
      rw [boxParent_of_getElem pl.m i b hb] at hid
      rcases List.mem_cons.mp hmem with h | h
      · have : g = t := boxId_inj F.fm hg htl (by rw [h, hid])
        subst this
        exact hst
      · rw [← hid] at h
        exact strictInside_trans (ih t g ht hg h) hst

end Sequence
end Elegant
