import Elegant.Kinds.Mindmap
import Elegant.TreeNormalized

set_option autoImplicit false

namespace Elegant
namespace Kinds
namespace Mindmap

open Common

/-- The adapter's measurement pass preserves declaration indices. -/
theorem measured_record {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      xs.length = ys.length ∧
      ∀ (i : Nat) (y : β), ys[i]? = some y →
        ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    change Except.ok [] = Except.ok ys at h
    have he := Except.ok.inj h
    subst ys
    exact ⟨rfl, by intro i y hy; simp at hy⟩
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hf : f x with
    | error e =>
      rw [hf] at h
      cases h
    | ok y =>
      cases ht : xs.mapM f with
      | error e =>
        rw [hf, ht] at h
        cases h
      | ok tail =>
        rw [hf, ht] at h
        change Except.ok (y :: tail) = Except.ok ys at h
        have he := Except.ok.inj h
        subst ys
        obtain ⟨hlen, hget⟩ := ih tail ht
        refine ⟨by simp [hlen], ?_⟩
        intro i z hz
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
          subst z
          exact ⟨x, rfl, hf⟩
        | succ i =>
          obtain ⟨a, ha, he⟩ := hget i z hz
          exact ⟨a, ha, he⟩

abbrev measuredNodes (m : Model) (measured : List Measured) : List Tree.Node :=
  (measured.zip (parents m)).map fun (s, p) => ⟨p, s.width, s.height⟩

theorem measuredNodes_length {m : Model} {measured : List Measured}
    (hl : measured.length = m.boxes.length) :
    (measuredNodes m measured).length = m.boxes.length := by
  simp only [measuredNodes, List.length_map, List.length_zip, parents_length, hl, Nat.min_self]

theorem measuredNodes_parent {m : Model} {measured : List Measured}
    (hl : measured.length = m.boxes.length) {i p : Nat}
    (hp : (parents m)[i]? = some (some p)) :
    Tree.parentOf (measuredNodes m measured) i = some p := by
  have hi : i < measured.length := by
    have h := (List.getElem?_eq_some_iff.mp hp).1
    rw [parents_length] at h
    omega
  let s := measured[i]
  have hs : measured[i]? = some s := List.getElem?_eq_getElem hi
  have hz : (measured.zip (parents m))[i]? = some (s, some p) :=
    List.getElem?_zip_eq_some.mpr ⟨hs, hp⟩
  simp [Tree.parentOf, measuredNodes, List.getElem?_map, hz]

theorem build_box_origin {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {out : Tree.Layout} {b : Box}
    (hb : b ∈ (build m c measured canvas out).boxes) :
    ∃ (i : Nat) (mb : ModelBox) (r : Rect),
      m.boxes[i]? = some mb ∧ out.boxes[i]? = some r ∧
      b = ⟨mb.id, mb.role.id, r, "", mb.exclusive⟩ := by
  obtain ⟨⟨mb, r⟩, hz, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hpair := List.getElem?_zip_eq_some.mp hi
  exact ⟨i, mb, r, hpair.1, hpair.2, rfl⟩

theorem build_box_at {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {out : Tree.Layout} {i : Nat} {mb : ModelBox} {r : Rect}
    (hm : m.boxes[i]? = some mb) (hr : out.boxes[i]? = some r) :
    (build m c measured canvas out).boxes[i]? =
      some ⟨mb.id, mb.role.id, r, "", mb.exclusive⟩ := by
  have hz : (m.boxes.zip out.boxes)[i]? = some (mb, r) :=
    List.getElem?_zip_eq_some.mpr ⟨hm, hr⟩
  simp only [build, List.getElem?_map, hz, Option.map_some]

theorem model_box_index_unique {m : Model} (hwf : WellFormed m) {i j : Nat}
    {a b : ModelBox} (ha : m.boxes[i]? = some a) (hb : m.boxes[j]? = some b)
    (hid : a.id = b.id) : i = j := by
  apply Tree.nodup_getElem?_inj (Model.boxIds_nodup hwf)
    (c := a.id)
  · simp [List.getElem?_map, ha]
  · simp [List.getElem?_map, hb, hid]

theorem build_box_id_ext {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {out : Tree.Layout} (hwf : WellFormed m) {a b : Box}
    (ha : a ∈ (build m c measured canvas out).boxes)
    (hb : b ∈ (build m c measured canvas out).boxes) (hid : a.id = b.id) : a = b := by
  obtain ⟨i, ma, ra, hma, hra, rfl⟩ := build_box_origin ha
  obtain ⟨j, mb, rb, hmb, hrb, rfl⟩ := build_box_origin hb
  have hij := model_box_index_unique hwf hma hmb hid
  subst j
  have hm := Option.some.inj (hma.symm.trans hmb)
  have hr := Option.some.inj (hra.symm.trans hrb)
  rw [hm, hr]

private theorem find_unique {α : Type} (p : α → Bool) {b : α}
    (hp : p b = true) : ∀ (xs : List α), b ∈ xs →
      (∀ a ∈ xs, p a = true → a = b) → xs.find? p = some b
  | [], h, _ => by simp at h
  | a :: as, h, hu => by
    by_cases ha : p a = true
    · have he := hu a List.mem_cons_self ha
      simp [List.find?, he, hp]
    · have hb : b ∈ as := by
        rcases List.mem_cons.mp h with rfl | hb
        · exact False.elim (ha hp)
        · exact hb
      have ht := find_unique p hp as hb (fun a ha hp => hu a (List.mem_cons_of_mem _ ha) hp)
      simp [List.find?, ha, ht]

theorem build_box_lookup {m : Model} {c : Consts} {measured : List Measured}
    {canvas : Size} {out : Tree.Layout} (hwf : WellFormed m) {i : Nat} {mb : ModelBox} {r : Rect}
    (hm : m.boxes[i]? = some mb) (hr : out.boxes[i]? = some r) :
    (build m c measured canvas out).layoutDump.box? mb.id =
      some ⟨mb.id, mb.role.id, r, "", mb.exclusive⟩ := by
  have hb := List.mem_of_getElem? (build_box_at (c := c) (measured := measured) (canvas := canvas) hm hr)
  apply find_unique (fun b => b.id == mb.id) (by simp) _ hb
  intro b hbm hbid
  exact build_box_id_ext hwf hbm hb (by simpa using hbid)

end Mindmap
end Kinds
end Elegant
