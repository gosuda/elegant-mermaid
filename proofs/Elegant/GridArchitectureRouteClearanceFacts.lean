import Elegant.GridArchitectureLabels
import Elegant.GridArchitectureRouteFacts
import Elegant.GridArchitectureValidity
import ElegantGeometry.Validator

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Elegant.Grid.Architecture

/-! ### Clause 7: labels stay clear of exclusive node boxes

`placeLabels` only emits a label when `labelClear` accepts it, and `labelClear` rejects
any overlap with a geometry box; the fallback branch spills labels strictly to the right
of the content bounds.  Both branches therefore keep every edge label clear of every node
box, which is clause 7 up to the translation. -/

/-- The per-label step of `placeLabels`: accept a candidate chosen by `labelClear`, or
spill the label to the right of the content bounds, or emit the zero rect for an empty
label size. -/
def labelStep (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (spillX : Int) (state : LabelState)
    (q : Size × Nat) : LabelState :=
  if q.1.w = 0 ∧ q.1.h = 0 then
    { state with output := state.output ++ [⟨0, 0, 0, 0⟩] }
  else
    match (labelCandidates p (routes.getD q.2 []) q.1).find? (labelClear p g routes state) with
    | some r => { state with placed := state.placed ++ [r], output := state.output ++ [r] }
    | none =>
      let r := sized spillX state.spillY q.1
      let nextY := state.spillY + q.1.h + margin
      { region := ⟨state.region.x0, state.region.y0,
          max state.region.x1 (r.x1 + margin),
          max state.region.y1 nextY⟩,
        placed := state.placed ++ [r], output := state.output ++ [r],
        spillY := nextY }

theorem placeLabels_eq (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (sizes : List Size) (bounds : Span) :
    placeLabels p margin g routes sizes bounds =
      (sizes.zipIdx.foldl (labelStep p margin g routes
        ((bounds.inflate margin).x1 + margin))
        (⟨bounds.inflate margin, [], [], (bounds.inflate margin).y0 + margin⟩)).output := by
  unfold placeLabels labelStep
  rfl

namespace ClearanceAux

private theorem getD_append_singleton (xs : List Span) (r : Span) :
    (xs ++ [r]).getD xs.length default = r := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  simp

/-- `List.any` returning `false` decides each prefix predicate to `false`. -/
private theorem any_append_false {α : Type} (xs ys : List α) (f : α → Bool)
    (h : (xs ++ ys).any f = false) : xs.any f = false := by
  by_cases hxb : xs.any f = true
  · exfalso
    rw [List.any_append, hxb] at h
    simp at h
  · exact Bool.eq_false_iff.mpr hxb

/-- Membership-wise form of `any = false`. -/
theorem any_eq_false_iff {α : Type} {xs : List α} {f : α → Bool} :
    xs.any f = false ↔ ∀ x ∈ xs, f x = false := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨hx, hrest⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hrest y hy
    · intro h
      exact ⟨h x (by simp), fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- Every label produced by one `labelStep` is the last element appended to
`state.output`. -/
theorem labelStep_appended (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (spillX : Int) (state : LabelState) (q : Size × Nat) :
    (labelStep p margin g routes spillX state q).output =
      state.output ++
        [(labelStep p margin g routes spillX state q).output.getD
          state.output.length default] := by
  unfold labelStep
  dsimp only
  split
  · rw [getD_append_singleton]
  · split <;> rw [getD_append_singleton]

/-- One `labelStep` either emits the zero rect, or emits a rect that overlaps no
geometry box, or emits a rect starting at `spillX`. -/
theorem labelStep_safe (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (spillX : Int)
    (state : LabelState) (q : Size × Nat) :
    (labelStep p margin g routes spillX state q).output.getD state.output.length default
      = (⟨0, 0, 0, 0⟩ : Span) ∨
      (g.boxes.any ((labelStep p margin g routes spillX state q).output.getD
        state.output.length default).overlaps) = false ∨
      spillX ≤
        ((labelStep p margin g routes spillX state q).output.getD
          state.output.length default).x0 := by
  unfold labelStep
  dsimp only
  split
  · rw [getD_append_singleton]
    exact Or.inl rfl
  · split
    · rename_i r hr
      have hclear : labelClear p g routes state r = true := List.find?_some hr
      unfold labelClear at hclear
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_append,
        Bool.or_eq_false_iff] at hclear
      have hany : g.boxes.any r.overlaps = false := by
        guard_hyp hclear : (((r.strictlyInside state.region = true ∧
            (g.frames.all fun frame => !r.overlaps frame || r.strictlyInside frame) = true) ∧
          (((g.boxes.any r.overlaps = false ∧ g.labels.any r.overlaps = false) ∧
              g.titles.any r.overlaps = false) ∧
            g.badges.any r.overlaps = false) ∧
            state.placed.any r.overlaps = false) ∧
          (routes.any fun route => (segments route).any fun q => r.overlaps
            (widened q.fst q.snd p.thickness)) = false)
        exact hclear.1.2.1.1.1.1
      refine Or.inr (Or.inl ?_)
      rw [getD_append_singleton]
      exact hany
    · refine Or.inr (Or.inr ?_)
      rw [getD_append_singleton]
      simp only [sized]
      omega

/-- The last output of a `labelStep` is safe, for any incoming state. -/
theorem labelStep_output_safe (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (spillX : Int)
    (state : LabelState) (q : Size × Nat) :
    ∃ r, (labelStep p margin g routes spillX state q).output =
        state.output ++ [r] ∧
      (r = (⟨0, 0, 0, 0⟩ : Span) ∨
        (g.boxes.any r.overlaps) = false ∨
        spillX ≤ r.x0) := by
  have hsafe := labelStep_safe p margin g routes spillX state q
  have happ := labelStep_appended p margin g routes spillX state q
  refine ⟨(labelStep p margin g routes spillX state q).output.getD
    state.output.length default, happ, ?_⟩
  rw [happ] at hsafe
  rw [getD_append_singleton] at hsafe
  exact hsafe

/-- One `labelStep` appends exactly one output element. -/
theorem labelStep_output_length (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (spillX : Int) (state : LabelState)
    (q : Size × Nat) :
    (labelStep p margin g routes spillX state q).output.length =
      state.output.length + 1 := by
  obtain ⟨r, heq, _⟩ := labelStep_output_safe p margin g routes spillX state q
  rw [heq, List.length_append, List.length_singleton]

/-- Every element of a `labelStep` fold output satisfies the safety disjunction. -/
theorem labelStep_fold_safe (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (spillX : Int) :
    ∀ (qs : List (Size × Nat)) (state : LabelState),
      (∀ r ∈ state.output,
        r = (⟨0, 0, 0, 0⟩ : Span) ∨
        (g.boxes.any r.overlaps) = false ∨
        spillX ≤ r.x0) →
      ∀ r ∈ (qs.foldl (labelStep p margin g routes spillX) state).output,
        r = (⟨0, 0, 0, 0⟩ : Span) ∨
        (g.boxes.any r.overlaps) = false ∨
        spillX ≤ r.x0 := by
  intro qs
  induction qs with
  | nil => intro state hstate r hr; exact hstate r hr
  | cons q rest ih =>
    intro state hstate r hr
    simp only [List.foldl_cons] at hr
    refine ih _ ?_ r hr
    intro r' hr'
    obtain ⟨r'', heq, hs⟩ := labelStep_output_safe p margin g routes spillX state q
    rw [heq] at hr'
    rcases List.mem_append.mp hr' with hmem | hmem
    · exact hstate r' hmem
    · rw [List.mem_singleton] at hmem
      subst hmem
      exact hs

/-- `placeLabels` output has one span per input size. -/
theorem placeLabels_length (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (sizes : List Size) (bounds : Span) :
    (placeLabels p margin g routes sizes bounds).length = sizes.length := by
  rw [placeLabels_eq]
  have hfold : ∀ (qs : List (Size × Nat)) (state : LabelState),
      (qs.foldl (labelStep p margin g routes
        ((bounds.inflate margin).x1 + margin)) state).output.length =
        state.output.length + qs.length := by
    intro qs
    induction qs with
    | nil => intro state; simp
    | cons q rest ih =>
      intro state
      simp only [List.foldl_cons, List.length_cons, labelStep_output_length, ih]
      omega
  rw [hfold]
  simp [List.length_zipIdx]

/-- Every element of the `placeLabels` output satisfies the safety disjunction. -/
theorem placeLabels_output_safe (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (sizes : List Size) (bounds : Span) :
    ∀ r ∈ placeLabels p margin g routes sizes bounds,
      r = (⟨0, 0, 0, 0⟩ : Span) ∨
      (g.boxes.any r.overlaps) = false ∨
      (bounds.inflate margin).x1 + margin ≤ r.x0 := by
  rw [placeLabels_eq]
  refine labelStep_fold_safe p margin g routes ((bounds.inflate margin).x1 + margin)
    sizes.zipIdx ⟨bounds.inflate margin, [], [], (bounds.inflate margin).y0 + margin⟩ ?_
  exact fun r hr => absurd hr (by simp)

/-- Pointwise form of `mapM` over `Except`, stated with explicit bounds. -/
theorem mapM_pointwise {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (hi : i < xs.length) (hj : i < ys.length) :
    f (xs[i]'hi) = .ok (ys[i]'hj) := by
  revert i hi hj
  induction xs generalizing ys with
  | nil => intro i hi hj; simp at hi
  | cons x rest ih =>
    intro i hi hj
    simp only [List.mapM_cons] at h
    cases hf : f x with
    | error e => rw [hf] at h; cases h
    | ok head =>
      rw [hf] at h
      cases hrest : rest.mapM f with
      | error e => rw [hrest] at h; cases h
      | ok tail =>
        rw [hrest] at h
        have hys : ys = head :: tail := Except.ok.inj h.symm
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero]
          simp only [hys, List.getElem_cons_zero]
          exact hf
        | succ i' =>
          have hi' : i' < rest.length := by
            simp only [List.length_cons] at hi
            omega
          have hj' : i' < tail.length := by
            rw [hys, List.length_cons] at hj
            omega
          have hpoint := ih hrest i' hi' hj'
          simp only [List.getElem_cons_succ]
          simp only [hys, List.getElem_cons_succ]
          exact hpoint

/-- `mapM` correspondence: every output element comes from an input element. -/
theorem mapM_output_origin {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
  obtain ⟨hiy, hxy⟩ := List.getElem?_eq_some_iff.mp hi
  have hlen := (Elegant.Grid.mapM_ok_pairs xs ys h).1
  have hix : i < xs.length := by omega
  have hpoint := mapM_pointwise h i hix hiy
  exact ⟨xs[i]'hix, List.getElem_mem hix, hxy ▸ hpoint⟩

/-- Every input element of a successful `mapM` produces an `.ok` output. -/
theorem mapM_input_origin {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a rest ih =>
    simp only [List.mapM_cons] at h
    cases hf : f a with
    | error e => rw [hf] at h; cases h
    | ok head =>
      rw [hf] at h
      cases hrest : rest.mapM f with
      | error e => rw [hrest] at h; cases h
      | ok tail =>
        rw [hrest] at h
        have hys : ys = head :: tail := Except.ok.inj h.symm
        rcases List.mem_cons.mp hx with rfl | hxr
        · exact ⟨head, by rw [hys]; simp, hf⟩
        · obtain ⟨y, hym, hfy⟩ := ih hrest hxr
          exact ⟨y, by rw [hys]; simp [hym], hfy⟩

/-- A pair in `xs.zip ys` shares an index below both lengths. -/
theorem mem_zip_index {α β : Type} {xs : List α} {ys : List β} {a : α} {b : β}
    (h : (a, b) ∈ xs.zip ys) :
    ∃ i, ∃ hi : i < xs.length, ∃ hj : i < ys.length,
      xs[i]'hi = a ∧ ys[i]'hj = b := by
  induction xs generalizing ys with
  | nil => simp [List.zip] at h
  | cons x rest ih =>
    cases ys with
    | nil => simp [List.zip] at h
    | cons y rest =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with heq | hmem
      · obtain ⟨i1, i2⟩ := Prod.mk.inj heq
        refine ⟨0, by simp, by simp, ?_, ?_⟩
        · simp only [List.getElem_cons_zero]; exact i1.symm
        · simp only [List.getElem_cons_zero]; exact i2.symm
      · obtain ⟨i, h1, h2, h3, h4⟩ := ih hmem
        refine ⟨i + 1, by simp [h1], by simp [h2], ?_, ?_⟩
        · simp only [List.getElem_cons_succ]
          exact h3
        · simp only [List.getElem_cons_succ]
          exact h4

/-- A translated non-degenerate span rectangle does not meet the interior of another
translated rectangle when the source spans do not overlap. -/
theorem translateRect_no_meetInterior (dx dy : Int) (a b : Span) (ra rb : Rect)
    (ha : translateRect dx dy a = .ok ra) (hb : translateRect dx dy b = .ok rb)
    (hno : a.overlaps b = false) :
    ¬ ra.meetsInterior rb := by
  unfold Rect.meetsInterior
  rcases translateRect_shape dx dy a ra ha with dega | shapea
  · rcases translateRect_shape dx dy b rb hb with degb | shapeb
    · simp only [dega.2.2, degb.2.2]
      omega
    · simp only [dega.2.2]
      obtain ⟨bx, byr, bw, bh⟩ := shapeb
      rw [bx, byr, bw, bh]
      omega
  · rcases translateRect_shape dx dy b rb hb with degb | shapeb
    · simp only [degb.2.2]
      obtain ⟨ax, ayr, aw, ah⟩ := shapea
      rw [ax, ayr, aw, ah]
      omega
    · obtain ⟨ax, ayr, aw, ah⟩ := shapea
      obtain ⟨bx, byr, bw, bh⟩ := shapeb
      rw [ax, ayr, aw, ah, bx, byr, bw, bh]
      unfold Span.overlaps at hno
      simp only [decide_eq_false_iff_not] at hno
      omega

/-- A translated span whose `x0` is at least `spillX` does not meet the interior of a
translated span whose `x1` is at most `spillX`. -/
theorem translateRect_no_meetInterior_of_xseparated (dx dy : Int) (a b : Span)
    (ra rb : Rect) (spillX : Int)
    (ha : translateRect dx dy a = .ok ra) (hb : translateRect dx dy b = .ok rb)
    (hbx : b.x1 ≤ spillX) (hax : spillX ≤ a.x0) :
    ¬ ra.meetsInterior rb := by
  unfold Rect.meetsInterior
  rcases translateRect_shape dx dy a ra ha with dega | shapea
  · rcases translateRect_shape dx dy b rb hb with degb | shapeb
    · simp only [dega.2.2, degb.2.2]
      omega
    · simp only [dega.2.2]
      obtain ⟨bx, byr, bw, bh⟩ := shapeb
      rw [bx, byr, bw, bh]
      omega
  · rcases translateRect_shape dx dy b rb hb with degb | shapeb
    · simp only [degb.2.2]
      obtain ⟨ax, ayr, aw, ah⟩ := shapea
      rw [ax, ayr, aw, ah]
      omega
    · obtain ⟨ax, ayr, aw, ah⟩ := shapea
      obtain ⟨bx, byr, bw, bh⟩ := shapeb
      rw [ax, ayr, aw, ah, bx, byr, bw, bh]
      omega

/-- The zero rectangle meets no interior. -/
theorem zeroRect_no_meetsInterior (r : Rect) :
    ¬ (⟨0, 0, 0, 0⟩ : Rect).meetsInterior r := by
  simp only [Rect.meetsInterior]
  omega
end ClearanceAux


namespace RouteClearance

open Polyline

/-- Tile-relative bounds of a placed node box: gutter clearance on every side of the
node's pitch tile. -/
structure BoxBounds (px py g : Int) (rect : Rect) (col row : Int) : Prop where
  pxPos : 0 < px
  pyPos : 0 < py
  gNonneg : 0 ≤ g
  x0ge : col * px + g ≤ rect.x
  x1le : rect.x + rect.w ≤ (col + 1) * px - g
  y0ge : row * py ≤ rect.y
  y1le : rect.y + rect.h ≤ (row + 1) * py - g

/-- A vertical segment on the street `k * px - g` misses every tile-bounded box. -/
theorem vstreet_misses (px py g k : Int) (p q : Point) (rect : Rect) (col row : Int)
    (hx : p.x = q.x) (hX : p.x = k * px - g) (hb : BoxBounds px py g rect col row) :
    segMisses p q rect := by
  have hpx := BoxBounds.pxPos hb
  have hg := BoxBounds.gNonneg hb
  unfold segMisses
  simp only [Point.x, Point.y, Int.min_def, Int.max_def]
  by_cases hlt : col < k
  · refine Or.inr (Or.inl ?_)
    have hA : (col + 1) * px ≤ k * px :=
      Int.mul_le_mul_of_nonneg_right (by omega : ((col + 1) : Int) ≤ k)
        (by omega : (0 : Int) ≤ px)
    have := BoxBounds.x1le hb
    split <;> omega
  · refine Or.inl ?_
    have hA : k * px ≤ col * px :=
      Int.mul_le_mul_of_nonneg_right (by omega : (k : Int) ≤ col)
        (by omega : (0 : Int) ≤ px)
    have := BoxBounds.x0ge hb
    split <;> omega

/-- A horizontal segment on the street `k * py - g` misses every tile-bounded box. -/
theorem hstreet_misses (px py g k : Int) (p q : Point) (rect : Rect) (col row : Int)
    (hy : p.y = q.y) (hY : p.y = k * py - g) (hb : BoxBounds px py g rect col row) :
    segMisses p q rect := by
  have hpy := BoxBounds.pyPos hb
  have hg := BoxBounds.gNonneg hb
  unfold segMisses
  simp only [Point.x, Point.y, Int.min_def, Int.max_def]
  by_cases hlt : row < k
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hA : (row + 1) * py ≤ k * py :=
      Int.mul_le_mul_of_nonneg_right (by omega : ((row + 1) : Int) ≤ k)
        (by omega : (0 : Int) ≤ py)
    have := BoxBounds.y1le hb
    split <;> omega
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hA : k * py ≤ row * py :=
      Int.mul_le_mul_of_nonneg_right (by omega : (k : Int) ≤ row)
        (by omega : (0 : Int) ≤ py)
    have := BoxBounds.y0ge hb
    split <;> omega

/-- A vertical stub segment inside the tile at `(colA, rowA)` misses every foreign
tile-bounded box. -/
theorem tile_vseg_misses (px py g colA rowA : Int) (p q : Point) (rect : Rect)
    (colF rowF : Int)
    (hx : p.x = q.x)
    (hx1 : colA * px - g ≤ p.x) (hx2 : p.x ≤ (colA + 1) * px - g)
    (hy3 : rowA * py - g ≤ min p.y q.y) (hy4 : max p.y q.y ≤ (rowA + 1) * py - g)
    (hdiff : colF ≠ colA ∨ rowF ≠ rowA)
    (hb : BoxBounds px py g rect colF rowF) :
    segMisses p q rect := by
  have hpx := BoxBounds.pxPos hb
  have hpy := BoxBounds.pyPos hb
  have hg := BoxBounds.gNonneg hb
  unfold segMisses
  simp only [Point.x, Point.y, Int.min_def, Int.max_def] at hy3 hy4 ⊢
  by_cases hxo : colF < colA
  · refine Or.inr (Or.inl ?_)
    have hA : (colF + 1) * px ≤ colA * px :=
      Int.mul_le_mul_of_nonneg_right (by omega : ((colF + 1) : Int) ≤ colA)
        (by omega : (0 : Int) ≤ px)
    have := BoxBounds.x1le hb
    split <;> omega
  · by_cases hxo' : colA < colF
    · refine Or.inl ?_
      have hA : (colA + 1) * px ≤ colF * px :=
        Int.mul_le_mul_of_nonneg_right (by omega : ((colA + 1) : Int) ≤ colF)
          (by omega : (0 : Int) ≤ px)
      have := BoxBounds.x0ge hb
      split <;> omega
    · have heq : colF = colA := by omega
      subst heq
      rcases hdiff with hne | hne
      · exact absurd rfl hne
      · by_cases hyo : rowF < rowA
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hA : (rowF + 1) * py ≤ rowA * py :=
            Int.mul_le_mul_of_nonneg_right (by omega : ((rowF + 1) : Int) ≤ rowA)
              (by omega : (0 : Int) ≤ py)
          have := BoxBounds.y1le hb
          split <;> omega
        · refine Or.inr (Or.inr (Or.inl ?_))
          have hA : (rowA + 1) * py ≤ rowF * py :=
            Int.mul_le_mul_of_nonneg_right (by omega : ((rowA + 1) : Int) ≤ rowF)
              (by omega : (0 : Int) ≤ py)
          have := BoxBounds.y0ge hb
          split <;> omega

/-- A horizontal stub segment inside the tile at `(colA, rowA)` misses every foreign
tile-bounded box. -/
theorem tile_hseg_misses (px py g colA rowA : Int) (p q : Point) (rect : Rect)
    (colF rowF : Int)
    (hy : p.y = q.y)
    (hy3 : rowA * py - g ≤ p.y) (hy4 : p.y ≤ (rowA + 1) * py - g)
    (hx1 : colA * px - g ≤ min p.x q.x) (hx2 : max p.x q.x ≤ (colA + 1) * px - g)
    (hdiff : colF ≠ colA ∨ rowF ≠ rowA)
    (hb : BoxBounds px py g rect colF rowF) :
    segMisses p q rect := by
  have hpx := BoxBounds.pxPos hb
  have hpy := BoxBounds.pyPos hb
  have hg := BoxBounds.gNonneg hb
  unfold segMisses
  simp only [Point.x, Point.y, Int.min_def, Int.max_def] at hx1 hx2 ⊢
  by_cases hyo : rowF < rowA
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hA : (rowF + 1) * py ≤ rowA * py :=
      Int.mul_le_mul_of_nonneg_right (by omega : ((rowF + 1) : Int) ≤ rowA)
        (by omega : (0 : Int) ≤ py)
    have := BoxBounds.y1le hb
    split <;> omega
  · by_cases hyo' : rowA < rowF
    · refine Or.inr (Or.inr (Or.inl ?_))
      have hA : (rowA + 1) * py ≤ rowF * py :=
        Int.mul_le_mul_of_nonneg_right (by omega : ((rowA + 1) : Int) ≤ rowF)
          (by omega : (0 : Int) ≤ py)
      have := BoxBounds.y0ge hb
      split <;> omega
    · have heq : rowF = rowA := by omega
      subst heq
      rcases hdiff with hne | hne
      · by_cases hxo : colF < colA
        · refine Or.inr (Or.inl ?_)
          have hA : (colF + 1) * px ≤ colA * px :=
            Int.mul_le_mul_of_nonneg_right (by omega : ((colF + 1) : Int) ≤ colA)
              (by omega : (0 : Int) ≤ px)
          have := BoxBounds.x1le hb
          split <;> omega
        · refine Or.inl ?_
          have hA : (colA + 1) * px ≤ colF * px :=
            Int.mul_le_mul_of_nonneg_right (by omega : ((colA + 1) : Int) ≤ colF)
              (by omega : (0 : Int) ≤ px)
          have := BoxBounds.x0ge hb
          split <;> omega
      · exact absurd rfl hne

/-- The dot product is equivariant under a common translation. -/
theorem dot_shift (nx ny dx dy x y : Int) :
    Polyline.dot nx ny ⟨x + dx, y + dy⟩ =
      Polyline.dot nx ny ⟨x, y⟩ + nx * dx + ny * dy := by
  simp only [Polyline.dot, Point.x, Point.y, Int.mul_add]
  omega

private theorem min_shift (a b c : Int) : min (a + c) (b + c) = min a b + c := by
  rw [Int.min_def, Int.min_def]
  omega

private theorem minCorner_shift (nx ny dx dy : Int) (r : Rect) :
    Polyline.minCorner nx ny ⟨r.x + dx, r.y + dy, r.w, r.h⟩ =
      Polyline.minCorner nx ny r + nx * dx + ny * dy := by
  unfold Polyline.minCorner
  simp only [Polyline.dot, Point.x, Point.y, Int.mul_add, Int.min_def, Int.max_def]
  omega

private theorem max_shift (a b c : Int) : max (a + c) (b + c) = max a b + c := by
  rw [Int.max_def, Int.max_def]
  omega

private theorem maxCorner_shift (nx ny dx dy : Int) (r : Rect) :
    Polyline.maxCorner nx ny ⟨r.x + dx, r.y + dy, r.w, r.h⟩ =
      Polyline.maxCorner nx ny r + nx * dx + ny * dy := by
  unfold Polyline.maxCorner
  simp only [Polyline.dot, Point.x, Point.y, Int.mul_add, Int.max_def, Int.min_def]
  omega

/-- `segMisses` is invariant under translating the segment and the rectangle by the
same offset. -/
theorem segMisses_translate (dx dy : Int) (p q : Point) (r : Rect) :
    segMisses p q r →
    segMisses ⟨p.x + dx, p.y + dy⟩ ⟨q.x + dx, q.y + dy⟩
      ⟨r.x + dx, r.y + dy, r.w, r.h⟩ := by
  intro h
  unfold segMisses at h ⊢
  simp only [Point.x, Point.y, Int.min_def, Int.max_def] at h ⊢
  rcases h with h | h | h | h | ⟨hne, hcmp⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
    · intro heq
      rw [Point.mk.injEq] at heq
      have : p = q := by
        rw [Point.mk.injEq]
        constructor <;> omega
      exact hne this
    · rw [minCorner_shift, maxCorner_shift]
      have hnorm : ((p.y + dy) - (q.y + dy) : Int) = p.y - q.y := by omega
      have hnorm2 : ((q.x + dx) - (p.x + dx) : Int) = q.x - p.x := by omega
      rw [hnorm, hnorm2]
      have hpx : Polyline.dot (p.y - q.y) (q.x - p.x) ⟨p.x + dx, p.y + dy⟩ =
          Polyline.dot (p.y - q.y) (q.x - p.x) p +
            (p.y - q.y) * dx + (q.x - p.x) * dy :=
        dot_shift _ _ _ _ _ _
      rw [hpx]
      rcases hcmp with hcmp | hcmp
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

/-- Consecutive-pair reachability along a polyline. -/
inductive HasSeg : List Point → Point → Point → Prop where
  | here (a b : Point) (rest : List Point) : HasSeg (a :: b :: rest) a b
  | cons (a u v : Point) (l : List Point) : HasSeg l u v → HasSeg (a :: l) u v

/-- Adjacent points of the list are distinct. -/
inductive AdjNe : List Point → Prop where
  | nil : AdjNe []
  | single (a : Point) : AdjNe [a]
  | cons (a b : Point) (rest : List Point) : a ≠ b → AdjNe (b :: rest) → AdjNe (a :: b :: rest)

/-- `compactPoints` keeps the first point's value. -/
theorem compactPoints_head_value : ∀ (ps : List Point) (_ : ps ≠ []),
    (compactPoints ps).head? = ps.head? := by
  intro ps
  induction ps with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _
    cases rest with
    | nil => simp only [compactPoints]
    | cons b more =>
      simp only [compactPoints]
      split
      · rename_i hab
        have := ih (List.cons_ne_nil b more)
        simpa [hab] using this
      · rename_i hab
        simp

theorem compactPoints_adjNe : ∀ (ps : List Point), AdjNe (compactPoints ps) := by
  intro ps
  induction ps with
  | nil => simp only [compactPoints]; exact AdjNe.nil
  | cons a rest ih =>
    cases rest with
    | nil => simp only [compactPoints]; exact AdjNe.single a
    | cons b more =>
      have hne : compactPoints (b :: more) ≠ [] := by
        intro hc
        have := compactPoints_head_value (b :: more) (by simp)
        simp [hc] at this
      simp only [compactPoints]
      split
      · rename_i hab
        exact ih
      · rename_i hab
        cases hc : compactPoints (b :: more) with
        | nil => exact absurd hc hne
        | cons c cs =>
          have hv := compactPoints_head_value (b :: more) (by simp)
          rw [hc, List.head?_cons] at hv
          have hcb : c = b := by simpa using hv
          refine AdjNe.cons a c cs ?_ ?_
          · rw [hcb]; exact hab
          · rw [← hc]; exact ih

theorem hasSeg_compact : ∀ (ps : List Point) (u v : Point),
    HasSeg (compactPoints ps) u v → u ≠ v → HasSeg ps u v := by
  intro ps
  induction ps with
  | nil => intro u v h _huv; simp only [compactPoints] at h; cases h
  | cons a rest ih =>
    intro u v h _huv
    cases rest with
    | nil =>
      simp only [compactPoints] at h
      cases h with
      | cons _ _ _ _ hbad => cases hbad
    | cons b more =>
      have hne : compactPoints (b :: more) ≠ [] := by
        intro hc
        have := compactPoints_head_value (b :: more) (by simp)
        simp [hc] at this
      rw [compactPoints.eq_1] at h
      split at h
      · rename_i _hab
        exact HasSeg.cons a u v (b :: more) (ih u v h _huv)
      · rename_i _hab
        revert h
        cases hc : compactPoints (b :: more) with
        | nil =>
          intro h
          cases h with
          | cons _ _ _ _ hbad => cases hbad
        | cons c cs =>
          intro h
          have hv := compactPoints_head_value (b :: more) (by simp)
          rw [hc, List.head?_cons] at hv
          have hcb : c = b := by simpa using hv
          rw [hcb] at h
          cases h
          case here => exact HasSeg.here _ _ _
          case cons =>
            rename_i h'
            rw [← hcb, ← hc] at h'
            exact HasSeg.cons _ u v (b :: more) (ih u v h' _huv)

theorem allSegsMiss_of_hasSeg : ∀ (xs : List Point) (r : Rect),
    AdjNe xs →
    (∀ u v, HasSeg xs u v → u ≠ v → segMisses u v r) →
    allSegsMiss xs r := by
  intro xs
  induction xs with
  | nil => intro r _ _; trivial
  | cons a rest ih =>
    intro r hadj h
    cases rest with
    | nil => trivial
    | cons b more =>
      simp only [allSegsMiss]
      cases hadj with
      | cons _ _ _ hne htail =>
        refine ⟨h a b (HasSeg.here a b more) (by simpa using hne), ?_⟩
        exact ih r htail
          (fun u v hmem huv => h u v (HasSeg.cons a u v (b :: more) hmem) huv)


end RouteClearance

end Elegant.Grid.Architecture
