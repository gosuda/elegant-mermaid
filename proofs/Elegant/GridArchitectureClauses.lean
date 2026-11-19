import Elegant.GridArchitectureCellContracts
import Elegant.GridArchitectureValidity
import ElegantGeometry.Validator

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Grid.Architecture

/-! Hard-constraint clauses for the architecture adapter under the `nodeTileFits`
admission guard.  This module contains the span/rect transport helpers, the
node-tile geometry derived from the guard, and the clause proofs. -/

/-! ### Generic `mapM` correspondence helpers -/

theorem mapped_source {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {y : β} (member : y ∈ ys) :
    ∃ x, x ∈ xs ∧ f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, except_pure, Except.ok.injEq] at h
    subst ys
    exact absurd member (by simp)
  | cons x rest ih =>
    rw [List.mapM_cons] at h
    cases hf : f x with
    | error e => rw [hf] at h; cases h
    | ok head =>
      rw [hf] at h
      cases hrest : rest.mapM f with
      | error e => rw [hrest] at h; cases h
      | ok tail =>
        rw [hrest] at h
        have hys : ys = head :: tail := (Except.ok.inj h).symm
        rw [hys] at member
        rcases List.mem_cons.mp member with eq | later
        · exact ⟨x, by simp, by rw [eq]; exact hf⟩
        · obtain ⟨x', hx', hf'⟩ := ih hrest later
          exact ⟨x', List.mem_cons_of_mem _ hx', hf'⟩

/-! ### Span-to-rect transport -/

theorem translateRect_nonempty_shape (dx dy : Int) (r : Span) (rect : Rect)
    (nonempty : r.x0 ≠ r.x1 ∨ r.y0 ≠ r.y1)
    (h : translateRect dx dy r = .ok rect) :
    rect.x = r.x0 + dx ∧ rect.y = r.y0 + dy ∧
      rect.w = r.x1 - r.x0 ∧ rect.h = r.y1 - r.y0 := by
  rcases translateRect_shape dx dy r rect h with degenerate | shape
  · rcases nonempty with hx | hy
    · exact False.elim (hx degenerate.1)
    · exact False.elim (hy degenerate.2.1)
  · exact shape

theorem translateRect_nonneg (dx dy : Int) (r : Span) (rect : Rect)
    (h : translateRect dx dy r = .ok rect) :
    0 ≤ rect.x ∧ 0 ≤ rect.y ∧ 0 ≤ rect.w ∧ 0 ≤ rect.h := by
  unfold translateRect at h
  by_cases hdeg : r.x0 = r.x1 ∧ r.y0 = r.y1
  · simp only [hdeg] at h
    cases h
    exact ⟨by simp, by simp, by simp, by simp⟩
  · simp only [hdeg, ite_false] at h
    split at h
    · cases h
      rename_i cond
      obtain ⟨_, _, h0y, _, h0w, _, h0h, _⟩ := cond
      exact ⟨by omega, h0y, h0w, h0h⟩
    · cases h

theorem zeroRect_disjoint_left (rb : Rect)
    (hn : 0 ≤ rb.x ∧ 0 ≤ rb.y ∧ 0 ≤ rb.w ∧ 0 ≤ rb.h) :
    Disjoint ⟨0, 0, 0, 0⟩ rb := by
  intro meet
  unfold Rect.meetsInterior at meet
  have h1 := meet.1
  have h2 := meet.2
  have hx : max (0 : Int) rb.x = rb.x := Int.max_eq_right hn.1
  have hy : max (0 : Int) rb.y = rb.y := Int.max_eq_right hn.2.1
  have mx : min (0 : Int) (rb.x + rb.w) = 0 := Int.min_eq_left (by omega)
  have my : min (0 : Int) (rb.y + rb.h) = 0 := Int.min_eq_left (by omega)
  simp only [show ((0 : Int) + 0) = 0 from rfl] at h1 h2
  rw [hx, mx] at h1
  rw [hy, my] at h2
  omega

theorem translateRect_disjoint_of_spans (dx dy : Int) (a b : Span) (ra rb : Rect)
    (ha : translateRect dx dy a = .ok ra) (hb : translateRect dx dy b = .ok rb)
    (separated : a.overlaps b = false) :
    Disjoint ra rb := by
  have hna := translateRect_nonneg dx dy a ra ha
  have hnb := translateRect_nonneg dx dy b rb hb
  rcases translateRect_shape dx dy a ra ha with dega | shapea
  · rcases translateRect_shape dx dy b rb hb with degb | shapeb
    · rw [dega.2.2]
      exact zeroRect_disjoint_left rb hnb
    · rw [dega.2.2]
      exact zeroRect_disjoint_left rb hnb
  · rcases translateRect_shape dx dy b rb hb with degb | shapeb
    · rw [degb.2.2]
      exact (Rect.disjoint_comm ra ⟨0, 0, 0, 0⟩).mpr (zeroRect_disjoint_left ra hna)
    · obtain ⟨ax, ayr, aw, ah⟩ := shapea
      obtain ⟨bx, byr, bw, bh⟩ := shapeb
      rw [ax, ayr, aw, ah] at hna
      rw [bx, byr, bw, bh] at hnb
      unfold Disjoint Rect.meetsInterior
      rw [ax, ayr, aw, ah, bx, byr, bw, bh]
      unfold Span.overlaps at separated
      simp only [decide_eq_false_iff_not] at separated
      omega

theorem spansSeparated_of_contains (outer other inner foreign : Span)
    (leftContains : outer.contains inner) (rightContains : other.contains foreign)
    (separated : outer.overlaps other = false) :
    inner.overlaps foreign = false := by
  simpa only [Span.shift, Int.add_zero] using
    separated_subtrees_after_origin_shift outer other inner foreign 0 0
      separated leftContains rightContains

/-! ### Pitch and guard facts -/

theorem pitch_floor_bounds (p : GeometryParams) (nodes : List Node)
    (edgeLabels : List Size) (px : 0 < p.pitchX) (py : 0 < p.pitchY) :
    0 < (pitch p nodes edgeLabels).x ∧
      0 < (pitch p nodes edgeLabels).y ∧
      0 ≤ (pitch p nodes edgeLabels).top := by
  have foldMaxW : ∀ (xs : List Node) (seed : Int), 0 ≤ seed →
      0 ≤ xs.foldl (fun a n => max a n.label.w) seed := by
    intro xs
    induction xs with
    | nil => intro seed h0; exact h0
    | cons x rest ih =>
      intro seed h0
      exact ih (max seed x.label.w) (by omega)
  have foldMaxH : ∀ (xs : List Node) (seed : Int), 0 ≤ seed →
      0 ≤ xs.foldl (fun a n => max a n.label.h) seed := by
    intro xs
    induction xs with
    | nil => intro seed h0; exact h0
    | cons x rest ih =>
      intro seed h0
      exact ih (max seed x.label.h) (by omega)
  have foldMaxEW : ∀ (xs : List Size) (seed : Int), 0 ≤ seed →
      0 ≤ xs.foldl (fun a s => max a s.w) seed := by
    intro xs
    induction xs with
    | nil => intro seed h0; exact h0
    | cons x rest ih =>
      intro seed h0
      exact ih (max seed x.w) (by omega)
  have foldMaxEH : ∀ (xs : List Size) (seed : Int), 0 ≤ seed →
      0 ≤ xs.foldl (fun a s => max a s.h) seed := by
    intro xs
    induction xs with
    | nil => intro seed h0; exact h0
    | cons x rest ih =>
      intro seed h0
      exact ih (max seed x.h) (by omega)
  have hw := foldMaxW nodes 0 (by omega)
  have hh := foldMaxH nodes 0 (by omega)
  have hew := foldMaxEW edgeLabels 0 (by omega)
  have heh := foldMaxEH edgeLabels 0 (by omega)
  unfold pitch
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · split <;> omega
  · omega
  · split <;> omega

theorem nodeTileFits_of_not_any {xs : List Node} (P : Node → Bool)
    (hnone : ¬(xs.any (fun n => !(P n)) = true)) :
    ∀ node ∈ xs, P node = true := by
  intro node hmem
  by_cases hc : P node = true
  · exact hc
  · exfalso
    have hany : xs.any (fun n => !(P n)) = true :=
      List.any_eq_true.mpr ⟨node, hmem, by simp [hc]⟩
    exact hnone hany

theorem nodeTileFits_true {p : GeometryParams} {pitch : Pitch} {n : Node}
    (h : Elegant.Kinds.Architecture.nodeTileFits p pitch n = true) :
    Int.fdiv (pitch.x - n.icon.w) 2 ≥ p.gutter ∧
      (if n.junction then Int.fdiv (pitch.y - n.icon.h) 2 else pitch.top) +
        n.icon.h + n.label.h + (if n.label.h > 0 then p.thickness else 0) ≤
        pitch.y - p.gutter := by
  unfold Elegant.Kinds.Architecture.nodeTileFits at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-! ### Node boxes stay inside their pitch tile -/

theorem nodeBoxInsideTile (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (groups : List Group) (resolved : Resolved) (n : Nat) (bound : n < nodes.length)
    (gutter : 0 ≤ p.gutter)
    (fx : Int.fdiv (pitch.x - (nodes.getD n default).icon.w) 2 ≥ p.gutter)
    (top : (if (nodes.getD n default).junction then
        Int.fdiv (pitch.y - (nodes.getD n default).icon.h) 2 else pitch.top) ≥ 0)
    (bottom : (if (nodes.getD n default).junction then
        Int.fdiv (pitch.y - (nodes.getD n default).icon.h) 2 else pitch.top) +
        (nodes.getD n default).icon.h + (nodes.getD n default).label.h +
          (if (nodes.getD n default).label.h > 0 then p.thickness else 0) ≤
        pitch.y - p.gutter) :
    ((⟨0, 0, pitch.x, pitch.y⟩ : Span).shift
        ((resolved.nodes.getD n default).x * pitch.x)
        ((resolved.nodes.getD n default).y * pitch.y)).contains
      ((geometry p pitch nodes groups resolved).boxes.getD n default) := by
  have icon := geometry_icon_at p pitch nodes groups resolved n bound
  have box := geometry_box_at p pitch nodes groups resolved n bound
  have fxNonneg : 0 ≤ Int.fdiv (pitch.x - (nodes.getD n default).icon.w) 2 :=
    Int.le_trans gutter fx
  have fxWidth : Int.fdiv (pitch.x - (nodes.getD n default).icon.w) 2 +
      (nodes.getD n default).icon.w ≤ pitch.x := by
    have decomp := Int.mul_fdiv_add_fmod (pitch.x - (nodes.getD n default).icon.w) 2
    have modNN := Int.fmod_nonneg_of_pos
      (pitch.x - (nodes.getD n default).icon.w) (show (0 : Int) < 2 by omega)
    have modLt := Int.fmod_lt_of_pos
      (pitch.x - (nodes.getD n default).icon.w) (show (0 : Int) < 2 by omega)
    omega
  rw [box, icon]
  dsimp only
  unfold Span.contains Span.shift sized
  dsimp only
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · omega

end Elegant.Grid.Architecture
