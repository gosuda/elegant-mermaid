import ElegantGeometry.Disjoint

/-! One-dimensional compaction: the ordered sweep that keeps minimum gaps between
items.

The plan states the three compaction theorems with an index notation over the input and
output lists. This file states them index-free in the equivalent forms the kernel uses:
`ChainFrom` carries the running end and the ordering, and a `List.zip` membership
carries the per-item identity. The index forms follow because every index below
`length` is a membership and `compactRaw` keeps the length. -/

set_option autoImplicit false

/-- The axis coordinate of a rectangle. -/
def coord (axis : Axis) (r : Rect) : Int :=
  match axis with
  | .X => r.x
  | .Y => r.y

/-- The axis extent of a rectangle. -/
def extent (axis : Axis) (r : Rect) : Int :=
  match axis with
  | .X => r.w
  | .Y => r.h

/-- A rectangle with its axis coordinate replaced. -/
def setCoord (axis : Axis) (r : Rect) (v : Int) : Rect :=
  match axis with
  | .X => ⟨v, r.y, r.w, r.h⟩
  | .Y => ⟨r.x, v, r.w, r.h⟩

theorem coord_setCoord (axis : Axis) (r : Rect) (v : Int) :
    coord axis (setCoord axis r v) = v := by
  cases axis <;> rfl

theorem extent_setCoord (axis : Axis) (r : Rect) (v : Int) :
    extent axis (setCoord axis r v) = extent axis r := by
  cases axis <;> rfl

theorem setCoord_y (r : Rect) (v : Int) : (setCoord .X r v).y = r.y := rfl

theorem setCoord_x (r : Rect) (v : Int) : (setCoord .Y r v).x = r.x := rfl

/-- The compacted list, with no error channel. `e` is the running end of the previous
item; the first item uses its own coordinate. -/
def compactTotal (axis : Axis) (gap : Int) : Int → List Rect → List Rect
  | _, [] => []
  | e, r :: rs =>
    setCoord axis r (max (coord axis r) e) ::
      compactTotal axis gap (max (coord axis r) e + extent axis r + gap) rs

/-- The compacted list of a list of items, before its validity is checked. The first
item keeps its coordinate. -/
def compactRaw (axis : Axis) (gap : Int) (items : List Rect) : List Rect :=
  match items with
  | [] => []
  | r :: rs => compactTotal axis gap (coord axis r) (r :: rs)

/-- Compact a list of rectangles along `axis` with a minimum gap.

The result is `domain` when `gap` is negative or an input rectangle is invalid, and
`overflow` when a placed rectangle would be invalid. -/
def compact (axis : Axis) (gap : Int) (items : List Rect) : Except LayoutError (List Rect) :=
  if 0 ≤ gap ∧ ∀ r ∈ items, r.Valid then
    if ∀ r ∈ compactRaw axis gap items, r.Valid then .ok (compactRaw axis gap items)
    else .error .overflow
  else .error .domain

theorem compact_ok {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) : out = compactRaw axis gap items := by
  unfold compact at h
  split at h
  · split at h
    · exact (Except.ok.inj h).symm
    · simp at h
  · simp at h

theorem compact_ok_gap {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) : 0 ≤ gap := by
  unfold compact at h
  split at h
  · rename_i hv
    exact hv.1
  · simp at h

theorem compact_ok_inputs_valid {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) : ∀ r ∈ items, r.Valid := by
  unfold compact at h
  split at h
  · rename_i hv
    exact hv.2
  · simp at h

theorem compactTotal_head (axis : Axis) (gap e : Int) (r : Rect) (rs : List Rect) :
    compactTotal axis gap e (r :: rs) =
      setCoord axis r (max (coord axis r) e) ::
        compactTotal axis gap (max (coord axis r) e + extent axis r + gap) rs := by
  simp only [compactTotal]

theorem compactTotal_length (axis : Axis) (gap e : Int) (l : List Rect) :
    (compactTotal axis gap e l).length = l.length := by
  induction l generalizing e with
  | nil => rfl
  | cons r rs ih => simp only [compactTotal, List.length_cons, ih]

/-- The separation chain: the running end precedes the head, and the chain continues
from the head's far edge. -/
def ChainFrom (axis : Axis) (gap : Int) : Int → List Rect → Prop
  | _, [] => True
  | e, r :: rs => e ≤ coord axis r ∧ ChainFrom axis gap (coord axis r + extent axis r + gap) rs

/-- The chain gives every later coordinate at or above the running end. -/
theorem chainFrom_le (axis : Axis) (gap : Int) (hgap : 0 ≤ gap) :
    ∀ (e : Int) (l : List Rect), (∀ r ∈ l, 0 ≤ extent axis r) →
      ChainFrom axis gap e l → ∀ r ∈ l, e ≤ coord axis r := by
  intro e l hnn h
  induction l generalizing e with
  | nil => intro r hr; simp at hr
  | cons x xs ih =>
    intro r hr
    obtain ⟨hx, hxs⟩ := h
    have hx_nn : 0 ≤ extent axis x := hnn x (by simp)
    have hstep : e ≤ coord axis x + extent axis x + gap := by omega
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact hx
    · refine Int.le_trans hstep (ih _ ?_ hxs r hr')
      intro r' hr'
      exact hnn r' (by simp [hr'])

/-- The chain orders every pair in list order. -/
theorem chainFrom_pairwise (axis : Axis) (gap : Int) (hgap : 0 ≤ gap) :
    ∀ (e : Int) (l : List Rect), (∀ r ∈ l, 0 ≤ extent axis r) →
      ChainFrom axis gap e l → List.Pairwise (fun a b => coord axis a ≤ coord axis b) l := by
  intro e l hnn h
  induction l generalizing e with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := h
    have hx_nn : 0 ≤ extent axis x := hnn x (by simp)
    have hnn' : ∀ r ∈ xs, 0 ≤ extent axis r := fun r hr => hnn r (by simp [hr])
    have htail : ∀ b ∈ xs, coord axis x + extent axis x + gap ≤ coord axis b :=
      chainFrom_le axis gap hgap _ xs hnn' hxs
    refine List.Pairwise.cons ?_ (ih _ hnn' hxs)
    intro b hb
    have := htail b hb
    omega

/-- A separation on the axis makes the two rectangles disjoint. -/
theorem disjoint_of_axis_sep {axis : Axis} {a b : Rect}
    (h : coord axis a + extent axis a ≤ coord axis b) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  cases axis with
  | X => simp only [coord, extent] at h ⊢; omega
  | Y => simp only [coord, extent] at h ⊢; omega

theorem chainFrom_disjoint (axis : Axis) (gap : Int) (hgap : 0 ≤ gap) :
    ∀ (e : Int) (l : List Rect), (∀ r ∈ l, 0 ≤ extent axis r) →
      ChainFrom axis gap e l → List.Pairwise Disjoint l := by
  intro e l hnn h
  induction l generalizing e with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := h
    have hx_nn : 0 ≤ extent axis x := hnn x (by simp)
    have hnn' : ∀ r ∈ xs, 0 ≤ extent axis r := fun r hr => hnn r (by simp [hr])
    have htail : ∀ b ∈ xs, coord axis x + extent axis x + gap ≤ coord axis b :=
      chainFrom_le axis gap hgap _ xs hnn' hxs
    refine List.Pairwise.cons ?_ (ih _ hnn' hxs)
    intro b hb
    have := htail b hb
    exact disjoint_of_axis_sep (axis := axis) (by omega)

/-- `compactTotal` builds the separation chain from any running end. -/
theorem compactTotal_chain (axis : Axis) (gap e : Int) (l : List Rect) :
    ChainFrom axis gap e (compactTotal axis gap e l) := by
  induction l generalizing e with
  | nil => exact (by simp [compactTotal, ChainFrom])
  | cons r rs ih =>
    rw [compactTotal_head, ChainFrom, coord_setCoord, extent_setCoord]
    exact ⟨by omega, ih (max (coord axis r) e + extent axis r + gap)⟩

/-- The adjacent-pair separation over a list of rectangles. -/
def GapsFrom (axis : Axis) (gap : Int) : List Rect → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    coord axis a + extent axis a + gap ≤ coord axis b ∧ GapsFrom axis gap (b :: rest)

/-- `compactTotal` keeps the adjacent-pair gap. -/
theorem compactTotal_gaps (axis : Axis) (gap e : Int) (l : List Rect) :
    GapsFrom axis gap (compactTotal axis gap e l) := by
  induction l generalizing e with
  | nil => simp [compactTotal, GapsFrom]
  | cons r rs ih =>
    rw [compactTotal_head]
    cases rs with
    | nil => simp [GapsFrom, compactTotal]
    | cons s ss =>
      refine ⟨?_, ih _⟩
      rw [coord_setCoord, coord_setCoord, extent_setCoord]
      omega

/-- An item of `compactTotal` is a placement of an item of its input. -/
theorem compactTotal_mem (axis : Axis) (gap e : Int) (l : List Rect) :
    ∀ q ∈ compactTotal axis gap e l, ∃ r ∈ l, ∃ v, q = setCoord axis r v := by
  induction l generalizing e with
  | nil => simp [compactTotal]
  | cons r rs ih =>
    intro q hq
    rw [compactTotal_head] at hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ⟨r, by simp, max (coord axis r) e, rfl⟩
    · obtain ⟨t, ht, v, hv⟩ := ih _ q hq'
      exact ⟨t, by simp [ht], v, hv⟩

/-- Every output has a non-negative extent when every input is valid. -/
theorem compactTotal_extent_nonneg (axis : Axis) (gap e : Int) (l : List Rect)
    (hv : ∀ r ∈ l, r.Valid) : ∀ q ∈ compactTotal axis gap e l, 0 ≤ extent axis q := by
  intro q hq
  obtain ⟨t, ht, v, rfl⟩ := compactTotal_mem axis gap e l q hq
  rw [extent_setCoord]
  have hval := hv t ht
  cases axis with
  | X => exact hval.1
  | Y => exact hval.2.1

/-- The placement relation: the axis coordinate never moves backwards, and the placed
rectangle is the input rectangle with its axis coordinate replaced. -/
def SameItem (axis : Axis) : Rect → Rect → Prop := fun a b =>
  coord axis a ≤ coord axis b ∧ b = setCoord axis a (coord axis b)

/-- Every item keeps its identity in its placement. -/
theorem compactTotal_sameItem (axis : Axis) (gap e : Int) (l : List Rect) :
    ∀ p ∈ l.zip (compactTotal axis gap e l), SameItem axis p.1 p.2 := by
  induction l generalizing e with
  | nil => simp [compactTotal]
  | cons r rs ih =>
    rw [compactTotal_head, List.zip_cons_cons]
    intro p hp
    rcases List.mem_cons.mp hp with hp0 | hp'
    · have hp0' : p.1 = r ∧ p.2 = setCoord axis r (max (coord axis r) e) :=
        (Prod.mk.injEq p.1 p.2 r (setCoord axis r (max (coord axis r) e))).mp hp0
      rw [hp0'.1, hp0'.2]
      refine ⟨?_, ?_⟩
      · rw [coord_setCoord]; omega
      · rw [coord_setCoord]
    · exact ih _ p hp'

/-- `compact_pairwise_disjoint`: the compacted rectangles are pairwise disjoint. -/
theorem compact_pairwise_disjoint {axis : Axis} {gap : Int} {items out : List Rect}
    (hgap : 0 ≤ gap) (h : compact axis gap items = .ok out) : List.Pairwise Disjoint out := by
  have hout : out = compactRaw axis gap items := compact_ok h
  have hv := compact_ok_inputs_valid h
  cases items with
  | nil => rw [hout]; simp [compactRaw]
  | cons s ss =>
    rw [hout]
    have hnn : ∀ q ∈ compactTotal axis gap (coord axis s) (s :: ss), 0 ≤ extent axis q :=
      compactTotal_extent_nonneg axis gap (coord axis s) (s :: ss) hv
    exact chainFrom_disjoint axis gap hgap (coord axis s)
      (compactTotal axis gap (coord axis s) (s :: ss)) hnn
      (compactTotal_chain axis gap (coord axis s) (s :: ss))

/-- The compacted list has the length of its input. -/
theorem compact_length {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) : out.length = items.length := by
  have hout : out = compactRaw axis gap items := compact_ok h
  cases items with
  | nil => rw [hout]; rfl
  | cons s ss => rw [hout]; exact compactTotal_length axis gap (coord axis s) (s :: ss)

/-- The ordering core of `compact_preserves_order`, in list form. -/
theorem compact_order_core {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) :
    List.Pairwise (fun a b => coord axis a ≤ coord axis b) out ∧
      ∀ p ∈ items.zip out, SameItem axis p.1 p.2 := by
  have hout : out = compactRaw axis gap items := compact_ok h
  have hgap := compact_ok_gap h
  have hv := compact_ok_inputs_valid h
  cases items with
  | nil => rw [hout]; exact ⟨List.Pairwise.nil, by simp [compactRaw]⟩
  | cons s ss =>
    rw [hout]
    have hnn : ∀ q ∈ compactTotal axis gap (coord axis s) (s :: ss), 0 ≤ extent axis q :=
      compactTotal_extent_nonneg axis gap (coord axis s) (s :: ss) hv
    refine ⟨?_, compactTotal_sameItem axis gap (coord axis s) (s :: ss)⟩
    exact chainFrom_pairwise axis gap hgap (coord axis s)
      (compactTotal axis gap (coord axis s) (s :: ss)) hnn
      (compactTotal_chain axis gap (coord axis s) (s :: ss))

/-- Two entries of a pairwise-related list, at indices `i < j`, are related. -/
theorem pairwise_of_getElem? {α : Type} {R : α → α → Prop} {l : List α}
    (h : List.Pairwise R l) {i j : Nat} {a b : α} (hij : i < j)
    (ha : l[i]? = some a) (hb : l[j]? = some b) : R a b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  exact List.pairwise_iff_getElem.mp h i j hi hj hij

/-- Entries at one index of two lists form a member of their zip. -/
theorem mem_zip_of_getElem? {α β : Type} {l₁ : List α} {l₂ : List β} {i : Nat} {a : α}
    {b : β} (ha : l₁[i]? = some a) (hb : l₂[i]? = some b) : (a, b) ∈ l₁.zip l₂ :=
  List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨ha, hb⟩)

/-- `compact_preserves_order`: the output coordinates never decrease in list order, and
each output is its input with only the axis coordinate replaced, so it keeps the cross
coordinates. -/
theorem compact_preserves_order {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) :
    out.length = items.length ∧
      (∀ (i j : Nat) (a b : Rect), i < j → out[i]? = some a → out[j]? = some b →
        coord axis a ≤ coord axis b) ∧
      (∀ (i : Nat) (a b : Rect), items[i]? = some a → out[i]? = some b →
        b = setCoord axis a (coord axis b)) := by
  have hcore := compact_order_core h
  refine ⟨compact_length h, ?_, ?_⟩
  · intro i j a b hij ha hb
    exact pairwise_of_getElem? hcore.1 hij ha hb
  · intro i a b ha hb
    exact (hcore.2 (a, b) (mem_zip_of_getElem? ha hb)).2

/-- Adjacent entries of a list with `GapsFrom` keep the gap. -/
theorem gapsFrom_getElem? (axis : Axis) (gap : Int) :
    ∀ (l : List Rect), GapsFrom axis gap l → ∀ (i : Nat) (a b : Rect),
      l[i]? = some a → l[i + 1]? = some b →
        coord axis a + extent axis a + gap ≤ coord axis b := by
  intro l
  induction l with
  | nil => intro _ i a b ha _; simp at ha
  | cons x xs ih =>
    intro hg i a b ha hb
    cases xs with
    | nil => simp at hb
    | cons y ys =>
      obtain ⟨hxy, hrest⟩ := hg
      cases i with
      | zero =>
        simp at ha hb
        subst ha
        subst hb
        exact hxy
      | succ i => exact ih hrest i a b (by simpa using ha) (by simpa using hb)

/-- `compact_respects_gaps`: each output starts at or after its input, and consecutive
outputs keep the gap. -/
theorem compact_respects_gaps {axis : Axis} {gap : Int} {items out : List Rect}
    (h : compact axis gap items = .ok out) :
    (∀ (i : Nat) (a b : Rect), items[i]? = some a → out[i]? = some b →
        coord axis a ≤ coord axis b) ∧
      (∀ (i : Nat) (a b : Rect), out[i]? = some a → out[i + 1]? = some b →
        coord axis a + extent axis a + gap ≤ coord axis b) := by
  have hout : out = compactRaw axis gap items := compact_ok h
  have hcore := compact_order_core h
  refine ⟨?_, ?_⟩
  · intro i a b ha hb
    exact (hcore.2 (a, b) (mem_zip_of_getElem? ha hb)).1
  · intro i a b ha hb
    have hg : GapsFrom axis gap out := by
      rw [hout]
      cases items with
      | nil => simp [compactRaw, GapsFrom]
      | cons s ss => exact compactTotal_gaps axis gap (coord axis s) (s :: ss)
    exact gapsFrom_getElem? axis gap out hg i a b ha hb
