import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant

open Validator LayoutDump

/-- A well-formed dump in which two unrelated exclusive node boxes overlap.

The parent chain is `a -> p1 -> r` and `b -> p2 -> r`.  The two intermediate
boxes are non-exclusive nodes, so clause C2 never compares `a` with `b`, and no
box has role `group`, so clause C8a is vacuous.  Clause C3 only forces each leaf
inside its own parent, and the two parents overlap. -/
def unrelatedOverlapDump : LayoutDump :=
  { canvas := ⟨100, 100⟩
    boxes :=
      [ { id := "r", role := "node", rect := ⟨0, 0, 100, 100⟩, parent := "", exclusive := false }
      , { id := "p1", role := "node", rect := ⟨0, 0, 60, 100⟩, parent := "r", exclusive := false }
      , { id := "p2", role := "node", rect := ⟨40, 0, 60, 100⟩, parent := "r", exclusive := false }
      , { id := "a", role := "node", rect := ⟨45, 10, 10, 10⟩, parent := "p1", exclusive := true }
      , { id := "b", role := "node", rect := ⟨50, 15, 10, 10⟩, parent := "p2", exclusive := true } ]
    routes := []
    labels := [] }

def overlapA : Box :=
  { id := "a", role := "node", rect := ⟨45, 10, 10, 10⟩, parent := "p1", exclusive := true }

def overlapB : Box :=
  { id := "b", role := "node", rect := ⟨50, 15, 10, 10⟩, parent := "p2", exclusive := true }

theorem unrelatedOverlapDump_c2 : Validator.C2 unrelatedOverlapDump := by
  decide

theorem unrelatedOverlapDump_c3 : Validator.C3 unrelatedOverlapDump := by
  decide

theorem unrelatedOverlapDump_c8a : Validator.C8a unrelatedOverlapDump := by
  decide

theorem unrelatedOverlapDump_wellFormed : WellFormed unrelatedOverlapDump := by
  decide

theorem unrelatedOverlapDump_a_mem : overlapA ∈ unrelatedOverlapDump.boxes := by
  decide

theorem unrelatedOverlapDump_b_mem : overlapB ∈ unrelatedOverlapDump.boxes := by
  decide

theorem unrelatedOverlapDump_meets : overlapA.rect.meetsInterior overlapB.rect := by
  decide

theorem unrelatedOverlapDump_unrelated :
    ¬ "a" ∈ unrelatedOverlapDump.ancestors "b" ∧ ¬ "b" ∈ unrelatedOverlapDump.ancestors "a" := by
  decide

/-- The stated lemma is false already for `WellFormed` dumps: the
counterexample satisfies C2, C3, C8a, and every well-formedness condition, yet
the two exclusive boxes meet. -/
theorem exclusive_unrelated_disjoint_false :
    ∃ d : LayoutDump, WellFormed d ∧ Validator.C2 d ∧ Validator.C3 d ∧
      Validator.C8a d ∧
      ∃ a b : Box, a ∈ d.boxes ∧ b ∈ d.boxes ∧ a.exclusive = true ∧
        b.exclusive = true ∧ a.id ≠ b.id ∧ a.id ∉ d.ancestors b.id ∧
        b.id ∉ d.ancestors a.id ∧ a.rect.meetsInterior b.rect := by
  exact ⟨unrelatedOverlapDump, unrelatedOverlapDump_wellFormed,
    unrelatedOverlapDump_c2, unrelatedOverlapDump_c3, unrelatedOverlapDump_c8a,
    overlapA, overlapB, unrelatedOverlapDump_a_mem, unrelatedOverlapDump_b_mem,
    rfl, rfl, by decide, by decide, by decide, unrelatedOverlapDump_meets⟩


/-! ### Rectangle monotonicity and dump lookup helpers -/

/-- A rectangle contained in a frame that is disjoint from `other` is itself
disjoint from `other`. -/
theorem Disjoint.of_contained_left {outer inner other : Rect}
    (h : outer.Contained inner) (hd : Disjoint outer other) : Disjoint inner other := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  intro hm
  apply hd
  obtain ⟨h1, h2⟩ := hm
  obtain ⟨h3, h4, h5, h6⟩ := h
  constructor <;> omega

/-- A rectangle whose interior meets `other` still meets it after enlarging to a
containing frame. -/
theorem meetsInterior_of_contained {outer inner other : Rect}
    (h : outer.Contained inner) (hm : inner.meetsInterior other) :
    outer.meetsInterior other := by
  unfold Rect.Contained Rect.meetsInterior at *
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := hm
  constructor <;> omega

/-- `find?` over a nodup id list returns the unique box with that id. -/
theorem findBox_eq_self {boxes : List Box} (hn : (boxes.map (·.id)).Nodup)
    {x : Box} (hx : x ∈ boxes) : boxes.find? (fun b => b.id == x.id) = some x := by
  induction boxes with
  | nil => simp at hx
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hfresh, hrest⟩ := hn
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hne : first.id ≠ x.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨x, by simp [hx], heq.symm⟩)
      simp [List.find?, beq_eq_false_iff_ne.mpr hne,
        ih hrest hx]

/-- `box?` returns the unique box with the requested id. -/
theorem dumpBox?_eq_self {d : LayoutDump} (hW1 : WF1 d) {x : Box}
    (hx : x ∈ d.boxes) : d.box? x.id = some x :=
  findBox_eq_self hW1 hx

/-- Box ids are injective on the box list. -/
theorem dumpBox_id_inj {d : LayoutDump} (hW1 : WF1 d) {x y : Box}
    (hx : x ∈ d.boxes) (hy : y ∈ d.boxes) (h : x.id = y.id) : x = y := by
  have hx' := dumpBox?_eq_self hW1 hx
  have hy' : d.box? y.id = some y := dumpBox?_eq_self hW1 hy
  have : d.box? x.id = d.box? y.id := by rw [h]
  rw [hx'] at this
  exact Option.some.inj (this.trans hy')

/-! ### `ancestors.go` recursion lemmas -/

/-- Ancestor-list membership only grows with more fuel. -/
theorem go_mono {d : LayoutDump} :
    ∀ (k k' : Nat) (s : String), k ≤ k' →
      LayoutDump.ancestors.go d k s ⊆ LayoutDump.ancestors.go d k' s := by
  intro k
  induction k with
  | zero =>
    intro k' s _ a ha
    simp only [LayoutDump.ancestors.go] at ha
    cases ha
  | succ k ih =>
    intro k' s hk
    cases k' with
    | zero => omega
    | succ k'' =>
      have hkk : k ≤ k'' := by omega
      simp only [LayoutDump.ancestors.go]
      cases hbox : d.box? s with
      | none => intro a ha; exact ha
      | some b =>
        by_cases hpar : b.parent = ""
        · simp only [hpar, ↓reduceIte]
          intro a ha
          exact ha
        · simp only [hpar, ↓reduceIte]
          intro a ha
          simp only [List.mem_cons] at ha ⊢
          rcases ha with rfl | ha
          · exact Or.inl rfl
          · exact Or.inr (ih k'' b.parent hkk ha)

/-- Transitivity of the fuel-bounded ancestor walk. -/
theorem go_trans {d : LayoutDump} :
    ∀ (k₁ k₂ : Nat) (a b c : String),
      a ∈ LayoutDump.ancestors.go d k₁ b →
      b ∈ LayoutDump.ancestors.go d k₂ c →
      a ∈ LayoutDump.ancestors.go d (k₁ + k₂) c := by
  intro k₁ k₂ a b c
  revert c
  revert b
  revert a
  revert k₁
  induction k₂ with
  | zero =>
    intro k₁ a b c ha hb
    simp only [LayoutDump.ancestors.go] at hb
    cases hb
  | succ k₂ ih =>
    intro k₁ a b c ha hb
    cases hbc : d.box? c with
    | none =>
      simp only [LayoutDump.ancestors.go, hbc] at hb
      cases hb
    | some bc =>
      have hgo : LayoutDump.ancestors.go d (k₂ + 1) c =
          if bc.parent = "" then [] else bc.parent ::
            LayoutDump.ancestors.go d k₂ bc.parent := by
        simp only [LayoutDump.ancestors.go, hbc]
      rw [hgo] at hb
      by_cases hpar : bc.parent = ""
      · simp only [hpar, ↓reduceIte] at hb
        cases hb
      · simp only [hpar, ↓reduceIte, List.mem_cons] at hb
        have hgoal : LayoutDump.ancestors.go d (k₁ + (k₂ + 1)) c =
            bc.parent :: LayoutDump.ancestors.go d (k₁ + k₂) bc.parent := by
          have heq : k₁ + (k₂ + 1) = (k₁ + k₂) + 1 := by omega
          rw [heq]
          simp only [LayoutDump.ancestors.go, hbc, hpar, ↓reduceIte]
        rw [hgoal]
        simp only [List.mem_cons]
        rcases hb with rfl | hb'
        · exact Or.inr (go_mono k₁ (k₁ + k₂) _ (by omega) ha)
        · exact Or.inr (ih k₁ a b bc.parent ha hb')

/-- Once the fuel-bounded walk has stopped early, extra fuel does not extend it. -/
theorem go_succ_eq_of_length_lt {d : LayoutDump} :
    ∀ (k : Nat) (s : String), (LayoutDump.ancestors.go d k s).length < k →
      LayoutDump.ancestors.go d (k + 1) s = LayoutDump.ancestors.go d k s := by
  intro k
  induction k with
  | zero => intro s h; simp at h
  | succ k ih =>
    intro s h
    cases hbox : d.box? s with
    | none => simp [LayoutDump.ancestors.go, hbox]
    | some b =>
      by_cases hpar : b.parent = ""
      · simp [LayoutDump.ancestors.go, hbox, hpar]
      · simp only [LayoutDump.ancestors.go, hbox, hpar, ↓reduceIte]
        have hlen : (LayoutDump.ancestors.go d k b.parent).length < k := by
          have : (LayoutDump.ancestors.go d (k + 1) s).length =
              (LayoutDump.ancestors.go d k b.parent).length + 1 := by
            simp [LayoutDump.ancestors.go, hbox, hpar]
          omega
        exact congrArg (fun t => b.parent :: t) (ih b.parent hlen)

/-- Every id on the ancestor walk names a box of the dump. -/
theorem go_elements_box_ids {d : LayoutDump} (hwf : WellFormed d) :
    ∀ (k : Nat) (x : Box), x ∈ d.boxes →
      ∀ y ∈ LayoutDump.ancestors.go d k x.id, ∃ b ∈ d.boxes, b.id = y := by
  have hW1 : WF1 d := hwf.1
  have hW6 : WF6 d := hwf.2.2.2.2.2.1
  intro k
  induction k with
  | zero => intro x hx y hy; simp [LayoutDump.ancestors.go] at hy
  | succ k ih =>
    intro x hx y hy
    have hxbox : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
    by_cases hpar : x.parent = ""
    · simp [LayoutDump.ancestors.go, hxbox, hpar] at hy
    · simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte,
        List.mem_cons] at hy
      rcases hy with rfl | hy
      · have hparent : x.parent ∈ d.boxIds := by
          rcases hW6 x hx with he | hm
          · exact absurd he hpar
          · exact hm
        obtain ⟨b, hb, hbE⟩ := List.mem_map.mp hparent
        exact ⟨b, hb, hbE⟩
      · obtain ⟨px, hpxmem, hpxid⟩ : ∃ px ∈ d.boxes, px.id = x.parent := by
          have hparent : x.parent ∈ d.boxIds := by
            rcases hW6 x hx with he | hm
            · exact absurd he hpar
            · exact hm
          obtain ⟨b, hb, hbE⟩ := List.mem_map.mp hparent
          exact ⟨b, hb, hbE⟩
        have hgo : LayoutDump.ancestors.go d k x.parent =
            LayoutDump.ancestors.go d k px.id := by rw [hpxid]
        rw [hgo] at hy
        exact ih px hpxmem y hy

/-! ### Nodup, length bound, fuel stability, transitivity, containment -/

/-- Membership survives erasing a different element. -/
theorem mem_erase_of_ne {α : Type} [BEq α] [LawfulBEq α] {a b : α} {l : List α}
    (h : b ∈ l) (hne : b ≠ a) : b ∈ l.erase a := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.erase_cons]
    by_cases hx : x == a
    · rw [ite_eq_left hx]
      have hxa : x = a := beq_iff_eq.mp hx
      subst hxa
      rcases List.mem_cons.mp h with rfl | hxs
      · exact absurd hne (by simp)
      · exact hxs
    · rw [ite_eq_right hx]
      rcases List.mem_cons.mp h with rfl | hxs
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih hxs))

theorem nodup_length_le {α : Type} [BEq α] [LawfulBEq α] {l m : List α}
    (hl : l.Nodup) (hm : m.Nodup) (h : ∀ y ∈ l, y ∈ m) : l.length ≤ m.length := by
  induction l generalizing m with
  | nil => simp
  | cons y ys ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hynot, hynodup⟩ := hl
    have hym : y ∈ m := h y (by simp)
    have hsub : ∀ z ∈ ys, z ∈ m.erase y := by
      intro z hz
      have hzm : z ∈ m := h z (List.mem_cons_of_mem y hz)
      have hzy : z ≠ y := by
        intro heq
        subst heq
        exact hynot hz
      exact mem_erase_of_ne hzm hzy
    have hle := ih hynodup (List.Nodup.erase y hm) hsub
    have hlen : (m.erase y).length = m.length - 1 := List.length_erase_of_mem hym
    have hmpos : 0 < m.length := List.length_pos_of_mem hym
    simp only [List.length_cons]
    omega

/-- The ancestor walk has no repeated id within the box-count fuel. -/
theorem go_nodup {d : LayoutDump} (hwf : WellFormed d) :
    ∀ (k : Nat), k ≤ d.boxes.length → ∀ x ∈ d.boxes,
      (LayoutDump.ancestors.go d k x.id).Nodup := by
  have hW1 : WF1 d := hwf.1
  have hW6 : WF6 d := hwf.2.2.2.2.2.1
  have hW7 : WF7 d := hwf.2.2.2.2.2.2.1
  intro k
  induction k with
  | zero => intro hk x hx; simp [LayoutDump.ancestors.go]
  | succ k ih =>
    intro hk x hx
    have hk' : k ≤ d.boxes.length := by omega
    have hxbox : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
    by_cases hpar : x.parent = ""
    · simp [LayoutDump.ancestors.go, hxbox, hpar]
    · obtain ⟨px, hpxmem, hpxid⟩ : ∃ px ∈ d.boxes, px.id = x.parent := by
        have hparent : x.parent ∈ d.boxIds := by
          rcases hW6 x hx with he | hm
          · exact absurd he hpar
          · exact hm
        obtain ⟨b, hb, hbE⟩ := List.mem_map.mp hparent
        exact ⟨b, hb, hbE⟩
      have hgo : LayoutDump.ancestors.go d (k + 1) x.id =
          px.id :: LayoutDump.ancestors.go d k px.id := by
        simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte]
        congr 1
        · exact hpxid.symm
        · rw [hpxid]
      rw [hgo]
      have htail : (LayoutDump.ancestors.go d k px.id).Nodup := ih hk' px hpxmem
      refine List.nodup_cons.mpr ⟨?_, htail⟩
      intro hmem
      have hsub := go_mono (d := d) k d.boxes.length px.id hk'
      have hmem' : px.id ∈ LayoutDump.ancestors.go d d.boxes.length px.id := hsub hmem
      have hanc : px.id ∉ d.ancestors px.id := hW7 px hpxmem
      exact hanc hmem'

/-- The full ancestor walk of a box has length below the box count. -/
theorem go_length_le {d : LayoutDump} (hwf : WellFormed d) {x : Box}
    (hx : x ∈ d.boxes) :
    (LayoutDump.ancestors.go d d.boxes.length x.id).length ≤ d.boxes.length - 1 := by
  have hW1 : WF1 d := hwf.1
  have hW7 : WF7 d := hwf.2.2.2.2.2.2.1
  have hnodup := go_nodup hwf d.boxes.length (Nat.le_refl _) x hx
  have hsub : ∀ y ∈ LayoutDump.ancestors.go d d.boxes.length x.id,
      y ∈ d.boxIds.erase x.id := by
    intro y hy
    obtain ⟨b, hb, hbE⟩ := go_elements_box_ids hwf d.boxes.length x hx y hy
    have hybox : y ∈ d.boxIds := List.mem_map.mpr ⟨b, hb, hbE⟩
    have hyne : y ≠ x.id := by
      intro heq
      subst heq
      have hanc : x.id ∉ d.ancestors x.id := hW7 x hx
      exact hanc hy
    exact mem_erase_of_ne hybox hyne
  have hle := nodup_length_le hnodup (List.Nodup.erase x.id hW1) hsub
  have hxid : x.id ∈ d.boxIds := List.mem_map.mpr ⟨x, hx, rfl⟩
  have hlen : (d.boxIds.erase x.id).length = d.boxIds.length - 1 :=
    List.length_erase_of_mem hxid
  have hmaplen : d.boxIds.length = d.boxes.length := by
    simp [LayoutDump.boxIds]
  omega

/-- Past the box-count fuel the ancestor walk is stable. -/
theorem go_fuel_ge_stable {d : LayoutDump} (hwf : WellFormed d) {x : Box}
    (hx : x ∈ d.boxes) :
    ∀ n, LayoutDump.ancestors.go d (d.boxes.length + n) x.id =
      LayoutDump.ancestors.go d d.boxes.length x.id := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have hL : 1 ≤ d.boxes.length := List.length_pos_of_mem hx
    have hlen : (LayoutDump.ancestors.go d (d.boxes.length + n) x.id).length <
        d.boxes.length + n := by
      rw [ih]
      have := go_length_le hwf hx
      omega
    have heq : d.boxes.length + (n + 1) = (d.boxes.length + n) + 1 := by omega
    rw [heq]
    exact (go_succ_eq_of_length_lt (d.boxes.length + n) x.id hlen).trans ih

/-- Transitivity of the public ancestor relation. -/
theorem ancestors_trans {d : LayoutDump} (hwf : WellFormed d) {a b : String}
    {c : Box} (hc : c ∈ d.boxes) (ha : a ∈ d.ancestors b) (hb : b ∈ d.ancestors c.id) :
    a ∈ d.ancestors c.id := by
  have ha' : a ∈ LayoutDump.ancestors.go d d.boxes.length b := ha
  have hb' : b ∈ LayoutDump.ancestors.go d d.boxes.length c.id := hb
  have h := go_trans d.boxes.length d.boxes.length a b c.id ha' hb'
  have hstable := go_fuel_ge_stable hwf hc d.boxes.length
  rw [hstable] at h
  exact h

/-- An ancestor's frame contains the descendant's frame. -/
theorem contained_of_ancestor {d : LayoutDump} (hwf : WellFormed d)
    (hC3 : Validator.C3 d) {x p : Box} (hx : x ∈ d.boxes) (hp : p ∈ d.boxes)
    (h : p.id ∈ d.ancestors x.id) : p.rect.Contained x.rect := by
  have hW1 : WF1 d := hwf.1
  have hW6 : WF6 d := hwf.2.2.2.2.2.1
  have key : ∀ fuel x, x ∈ d.boxes → ∀ p ∈ d.boxes,
      p.id ∈ LayoutDump.ancestors.go d fuel x.id → p.rect.Contained x.rect := by
    intro fuel
    induction fuel with
    | zero => intro x hx p hp hmem; simp [LayoutDump.ancestors.go] at hmem
    | succ fuel ih =>
      intro x hx p hp hmem
      have hxbox : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
      by_cases hpar : x.parent = ""
      · simp [LayoutDump.ancestors.go, hxbox, hpar] at hmem
      · obtain ⟨pb, hbmem, hbpid⟩ : ∃ pb ∈ d.boxes, pb.id = x.parent := by
          have hparent : x.parent ∈ d.boxIds := by
            rcases hW6 x hx with he | hm
            · exact absurd he hpar
            · exact hm
          obtain ⟨b, hb, hbE⟩ := List.mem_map.mp hparent
          exact ⟨b, hb, hbE⟩
        have hpbbox : d.box? x.parent = some pb := by
          have hfind := findBox_eq_self hW1 hbmem
          have : d.boxes.find? (fun b => b.id == x.parent) = some pb := by
            rw [← hbpid]
            exact hfind
          exact this
        simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte,
          List.mem_cons] at hmem
        rcases hmem with hpid | htail
        · have hpid' : p.id = x.parent := hpid
          have hppb : p = pb := by
            apply dumpBox_id_inj hW1 hp hbmem
            rw [hbpid]; exact hpid'
          rw [hppb]
          exact hC3 x hx hpar pb hpbbox
        · have hgo : LayoutDump.ancestors.go d fuel x.parent =
              LayoutDump.ancestors.go d fuel pb.id := by rw [hbpid]
          rw [hgo] at htail
          have hinner := ih pb hbmem p hp htail
          have houter := hC3 x hx hpar pb hpbbox
          exact Rect.Contained.trans hinner houter
  have hgo : d.ancestors x.id = LayoutDump.ancestors.go d d.boxes.length x.id := rfl
  rw [hgo] at h
  exact key d.boxes.length x hx p hp h

/-! ### Chain helpers for the separation argument -/

/-- A root box has no proper ancestors. -/
theorem ancestors_eq_nil {d : LayoutDump} (hwf : WellFormed d) {x : Box}
    (hx : x ∈ d.boxes) (h : x.parent = "") : d.ancestors x.id = [] := by
  have hW1 : WF1 d := hwf.1
  have hxbox : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
  show LayoutDump.ancestors.go d d.boxes.length x.id = []
  cases hL : d.boxes.length with
  | zero => rfl
  | succ n =>
      simp [LayoutDump.ancestors.go, hxbox, h]

/-- A non-root box's parent is its first proper ancestor. -/
theorem parent_mem_ancestors {d : LayoutDump} (hwf : WellFormed d) {x : Box}
    (hx : x ∈ d.boxes) (h : x.parent ≠ "") : x.parent ∈ d.ancestors x.id := by
  have hW1 : WF1 d := hwf.1
  have hxbox : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
  show x.parent ∈ LayoutDump.ancestors.go d d.boxes.length x.id
  cases hL : d.boxes.length with
  | zero =>
      exact absurd (List.length_pos_of_mem hx) (by omega)
  | succ n =>
      simp [LayoutDump.ancestors.go, hxbox, h]

/-- Equal parents give equal ancestor walks. -/
theorem ancestors_eq_of_parent_eq {d : LayoutDump} (hwf : WellFormed d)
    {x y : Box} (hx : x ∈ d.boxes) (hy : y ∈ d.boxes) (h : x.parent = y.parent) :
    d.ancestors x.id = d.ancestors y.id := by
  have hW1 : WF1 d := hwf.1
  have hxx : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
  have hyy : d.box? y.id = some y := dumpBox?_eq_self hW1 hy
  show LayoutDump.ancestors.go d d.boxes.length x.id =
    LayoutDump.ancestors.go d d.boxes.length y.id
  cases hL : d.boxes.length with
  | zero => rfl
  | succ n =>
      by_cases hxp : x.parent = ""
      · have hyp : y.parent = "" := by
          have : y.parent = x.parent := h.symm
          rw [this, hxp]
        simp [LayoutDump.ancestors.go, hxx, hyy, hxp, hyp]
      · have hyp : y.parent ≠ "" := by
          intro hy0
          apply hxp
          have : x.parent = y.parent := h
          rw [hy0] at this
          exact this
        simp only [LayoutDump.ancestors.go, hxx, hyy, hxp, hyp, ↓reduceIte]
        rw [h]

/-- On the ancestor chain of `x`, the node just below `p` (or `x` itself when
`p` is its parent) has `p` as parent. -/
theorem exists_child_below {d : LayoutDump} (hwf : WellFormed d) :
    ∀ fuel x p, x ∈ d.boxes → p ∈ d.boxes →
      p.id ∈ LayoutDump.ancestors.go d fuel x.id →
      ∃ c, c ∈ d.boxes ∧ c.parent = p.id ∧
        (c.id = x.id ∨ c.id ∈ LayoutDump.ancestors.go d fuel x.id) := by
  have hW1 : WF1 d := hwf.1
  have hW6 : WF6 d := hwf.2.2.2.2.2.1
  intro fuel
  induction fuel with
  | zero => intro x p hx hp hmem; simp [LayoutDump.ancestors.go] at hmem
  | succ fuel ih =>
    intro x p hx hp hmem
    have hxbox : d.box? x.id = some x := dumpBox?_eq_self hW1 hx
    by_cases hpar : x.parent = ""
    · simp [LayoutDump.ancestors.go, hxbox, hpar] at hmem
    · obtain ⟨pb, hbmem, hbpid⟩ : ∃ pb ∈ d.boxes, pb.id = x.parent := by
        have hparent : x.parent ∈ d.boxIds := by
          rcases hW6 x hx with he | hm
          · exact absurd he hpar
          · exact hm
        obtain ⟨b, hb, hbE⟩ := List.mem_map.mp hparent
        exact ⟨b, hb, hbE⟩
      simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte,
        List.mem_cons] at hmem
      rcases hmem with hpid | htail
      · refine ⟨x, hx, ?_, Or.inl rfl⟩
        have : x.parent = p.id := hpid.symm
        exact this
      · have hgo : LayoutDump.ancestors.go d fuel x.parent =
            LayoutDump.ancestors.go d fuel pb.id := by rw [hbpid]
        rw [hgo] at htail
        obtain ⟨c, hcmem, hcpar, hc⟩ := ih pb p hbmem hp htail
        refine ⟨c, hcmem, hcpar, ?_⟩
        rcases hc with hcid | hctail
        · have hcpb : c = pb := dumpBox_id_inj hW1 hcmem hbmem hcid
          subst hcpb
          right
          have hmemhead : x.parent ∈
              LayoutDump.ancestors.go d (fuel + 1) x.id := by
            simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte]
            exact List.mem_cons.mpr (Or.inl rfl)
          rw [hbpid]
          exact hmemhead
        · right
          rw [← hgo] at hctail
          simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte,
            List.mem_cons]
          exact Or.inr hctail

/-- The extra well-formedness that makes the laminar claim true: every proper
ancestor of an exclusive box is a group frame, so clause C8a can separate the
two sides at their divergence. -/
def ExclusiveFrameAncestors (d : LayoutDump) : Prop :=
  ∀ b ∈ d.boxes, b.exclusive = true → ∀ p ∈ d.boxes,
    p.id ∈ d.ancestors b.id → p.role = "group"

/-- With `ExclusiveFrameAncestors`, unrelated exclusive boxes are disjoint:
their ancestor chains diverge at a group frame that clause C8a separates. -/
theorem exclusive_unrelated_disjoint_of_frame_ancestors :
    ∀ d : LayoutDump, WellFormed d → Validator.C2 d → Validator.C3 d →
      Validator.C8a d → ExclusiveFrameAncestors d →
      ∀ a b : Box, a ∈ d.boxes → b ∈ d.boxes → a.exclusive = true →
        b.exclusive = true → a.id ≠ b.id → a.id ∉ d.ancestors b.id →
        b.id ∉ d.ancestors a.id → ¬ a.rect.meetsInterior b.rect := by
  intro d hwf hC2 hC3 hC8a hEFA a b ha hb haex hbex hne ha_nb hb_na
  have hW1 : WF1 d := hwf.1
  have hW6 : WF6 d := hwf.2.2.2.2.2.1
  have hW7 : WF7 d := hwf.2.2.2.2.2.2.1
  by_cases hpar : a.parent = b.parent
  · exact hC2 a ha b hb hne haex hbex hpar
  · by_cases hbroot : b.parent = ""
    · have hap : a.parent ≠ "" := by
        intro h; apply hpar; rw [h, hbroot]
      obtain ⟨pa, hpamem, hpaid⟩ : ∃ pa ∈ d.boxes, pa.id = a.parent := by
        have hparid : a.parent ∈ d.boxIds := by
          rcases hW6 a ha with he | hm
          · exact absurd he hap
          · exact hm
        obtain ⟨p, hp, hpE⟩ := List.mem_map.mp hparid
        exact ⟨p, hp, hpE⟩
      have hapA : pa.id ∈ d.ancestors a.id := by
        rw [hpaid]
        exact parent_mem_ancestors hwf ha hap
      have hpage : pa.role = "group" := hEFA a ha haex pa hpamem hapA
      have hpb_ne : pa.id ≠ b.id := fun heq => hb_na (heq ▸ hapA)
      have hpa_not_ancB : pa.id ∉ d.ancestors b.id := by
        rw [ancestors_eq_nil hwf hb hbroot]
        simp
      have hb_not_anc_pa : b.id ∉ d.ancestors pa.id := by
        intro h
        exact hb_na (ancestors_trans hwf ha h hapA)
      have hdisjoint : Disjoint pa.rect b.rect :=
        hC8a pa hpamem hpage b hb (Ne.symm hpb_ne) hpa_not_ancB hb_not_anc_pa
      have hpaC : pa.rect.Contained a.rect :=
        contained_of_ancestor hwf hC3 ha hpamem hapA
      intro hmeet
      exact hdisjoint (meetsInterior_of_contained hpaC hmeet)
    · obtain ⟨pb, hbmem, hbpid⟩ : ∃ pb ∈ d.boxes, pb.id = b.parent := by
        have hparid : b.parent ∈ d.boxIds := by
          rcases hW6 b hb with he | hm
          · exact absurd he hbroot
          · exact hm
        obtain ⟨p, hp, hpE⟩ := List.mem_map.mp hparid
        exact ⟨p, hp, hpE⟩
      have hbpidB : pb.id ∈ d.ancestors b.id := by
        rw [hbpid]
        exact parent_mem_ancestors hwf hb hbroot
      by_cases hall : ∀ y ∈ d.ancestors b.id, y ∈ d.ancestors a.id
      · have hpbA : pb.id ∈ d.ancestors a.id := hall pb.id hbpidB
        obtain ⟨c, hcmem, hcpar, hc⟩ :=
          exists_child_below hwf d.boxes.length a pb ha hbmem hpbA
        rcases hc with hcid | hctail
        · have hca : c = a := dumpBox_id_inj hW1 hcmem ha hcid
          have hcap : a.parent = b.parent := by
            have h1 : c.parent = b.parent := hcpar.trans hbpid
            rwa [hca] at h1
          exact absurd hcap hpar
        · have hcrole : c.role = "group" := hEFA a ha haex c hcmem hctail
          have hctailB : c.id ∉ d.ancestors b.id := by
            intro hcinB
            have hpbne : pb.id ≠ "" := by rw [hbpid]; exact hbroot
            by_cases hcpb : c.id = pb.id
            · have hcpb' : c = pb := dumpBox_id_inj hW1 hcmem hbmem hcpb
              have hppar : pb.parent = pb.id := by
                have h1 : pb.parent = c.parent := congrArg Box.parent hcpb'.symm
                rw [hcpar] at h1
                exact h1
              have hpmem : pb.parent ∈ d.ancestors pb.id :=
                parent_mem_ancestors hwf hbmem (by rw [hppar]; exact hpbne)
              rw [hppar] at hpmem
              exact hW7 pb hbmem hpmem
            · have hLpos : 0 < d.boxes.length := List.length_pos_of_mem hb
              obtain ⟨n, hn⟩ : ∃ n, d.boxes.length = n + 1 :=
                ⟨d.boxes.length - 1, by omega⟩
              have hcinB' : c.id ∈
                  LayoutDump.ancestors.go d d.boxes.length b.id := hcinB
              rw [hn] at hcinB'
              simp only [LayoutDump.ancestors.go, dumpBox?_eq_self hW1 hb,
                hbroot, ↓reduceIte, List.mem_cons] at hcinB'
              rcases hcinB' with hcb | hctail'
              · have hcidpb : c.id = pb.id := by rw [hbpid]; exact hcb
                exact hcpb hcidpb
              · have hcinpb : c.id ∈ LayoutDump.ancestors.go d n pb.id := by
                  rw [hbpid]
                  exact hctail'
                have hcinanc : c.id ∈ d.ancestors pb.id :=
                  go_mono n d.boxes.length pb.id (by omega) hcinpb
                have hcpne : c.parent ≠ "" := by rw [hcpar, hbpid]; exact hbroot
                have hpb_in_anc_c : pb.id ∈ d.ancestors c.id := by
                  have h1 := parent_mem_ancestors hwf hcmem hcpne
                  rwa [hcpar] at h1
                exact hW7 pb hbmem (ancestors_trans hwf hbmem hpb_in_anc_c hcinanc)
          have hbancC : b.id ∉ d.ancestors c.id := by
            intro hbc
            exact hb_na (ancestors_trans hwf ha hbc hctail)
          have hcb_ne : b.id ≠ c.id := fun heq => hb_na (heq.symm ▸ hctail)
          have hdisjoint : Disjoint c.rect b.rect :=
            hC8a c hcmem hcrole b hb hcb_ne hctailB hbancC
          have hcC : c.rect.Contained a.rect :=
            contained_of_ancestor hwf hC3 ha hcmem hctail
          intro hmeet
          exact hdisjoint (meetsInterior_of_contained hcC hmeet)
      · have hex : ∃ y, y ∈ d.ancestors b.id ∧ y ∉ d.ancestors a.id := by
          obtain ⟨y, hy⟩ := Classical.not_forall.mp hall
          refine ⟨y, ?_, ?_⟩
          · by_cases hyB : y ∈ d.ancestors b.id
            · exact hyB
            · exact False.elim (hy (fun hb => False.elim (hyB hb)))
          · intro hyA
            exact hy (fun _ => hyA)
        obtain ⟨qid, hqB, hqA⟩ := hex
        obtain ⟨Q, hQmem, hQid⟩ :=
          go_elements_box_ids hwf d.boxes.length b hb qid hqB
        have hQB : Q.id ∈ d.ancestors b.id := by rw [hQid]; exact hqB
        have hQA : Q.id ∉ d.ancestors a.id := by rw [hQid]; exact hqA
        have hQrole : Q.role = "group" := hEFA b hb hbex Q hQmem hQB
        have hQne : a.id ≠ Q.id := fun heq => ha_nb (heq.symm ▸ hQB)
        have ha_not_ancQ : a.id ∉ d.ancestors Q.id := by
          intro h
          exact ha_nb (ancestors_trans hwf hb h hQB)
        have hdisjoint : Disjoint Q.rect a.rect :=
          hC8a Q hQmem hQrole a ha hQne hQA ha_not_ancQ
        have hQC : Q.rect.Contained b.rect :=
          contained_of_ancestor hwf hC3 hb hQmem hQB
        intro hmeet
        have hbmeet : b.rect.meetsInterior a.rect :=
          (Rect.meetsInterior_comm a.rect b.rect).mp hmeet
        exact hdisjoint (meetsInterior_of_contained hQC hbmeet)

/-- Label-side corollary: a rect contained in an exclusive box `o` misses the
interior of an exclusive box `b` unrelated to `o`. -/
theorem contained_in_box_misses_unrelated :
    ∀ d : LayoutDump, WellFormed d → Validator.C2 d → Validator.C3 d →
      Validator.C8a d → ExclusiveFrameAncestors d →
      ∀ o b : Box, o ∈ d.boxes → b ∈ d.boxes → o.exclusive = true →
        b.exclusive = true → o.id ≠ b.id → o.id ∉ d.ancestors b.id →
        b.id ∉ d.ancestors o.id → ∀ r : Rect, o.rect.Contained r →
        ¬ r.meetsInterior b.rect := by
  intro d hwf hC2 hC3 hC8a hEFA o b ho hb hoex hbex hone ho_nb hb_no r hor
  have hdisjoint : Disjoint o.rect b.rect :=
    exclusive_unrelated_disjoint_of_frame_ancestors d hwf hC2 hC3 hC8a hEFA
      o b ho hb hoex hbex hone ho_nb hb_no
  intro hr
  exact hdisjoint (meetsInterior_of_contained hor hr)

end Elegant
