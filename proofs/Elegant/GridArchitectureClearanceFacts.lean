import Elegant.GridArchitecturePlacement

set_option autoImplicit false

namespace Elegant.Grid.Architecture

theorem clear_avoids_placed (p : Params) (l : Level) (v : Nat) (c : Cell)
    (h : clear p l v c = true) (entry : Bool × Span)
    (member : entry ∈ l.placed.zip l.absolute) (marked : entry.1 = true) :
    ((l.rects.getD v default).shift (c.x*p.pitchX) (c.y*p.pitchY)).overlaps entry.2 = false := by
  unfold clear at h
  simp only [Bool.not_eq_true',List.any_eq_false] at h
  have result := h entry member
  exact Bool.eq_false_of_ne_true (by simpa only [marked,Bool.true_and] using result)

/-- Every unit's relative rectangle contains its anchor grid cell. Two units at
one anchor therefore have intersecting open interiors, including container units. -/
def ContainsAnchor (p : Params) (r : Span) : Prop :=
  r.x0 ≤ 0 ∧ p.pitchX ≤ r.x1 ∧ r.y0 ≤ 0 ∧ p.pitchY ≤ r.y1

theorem same_anchor_overlaps (p : Params) (a b : Span) (c : Cell)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (ha : ContainsAnchor p a) (hb : ContainsAnchor p b) :
    (a.shift (c.x*p.pitchX) (c.y*p.pitchY)).overlaps
      (b.shift (c.x*p.pitchX) (c.y*p.pitchY)) = true := by
  simp only [ContainsAnchor] at ha hb
  unfold Span.overlaps
  apply decide_eq_true
  simp only [Span.shift]
  omega

theorem clear_anchor_distinct (p : Params) (l : Level) (v : Nat) (newCell oldCell : Cell)
    (oldRect : Span) (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (newContains : ContainsAnchor p (l.rects.getD v default))
    (oldContains : ContainsAnchor p oldRect)
    (member : (true,oldRect.shift (oldCell.x*p.pitchX) (oldCell.y*p.pitchY)) ∈ l.placed.zip l.absolute)
    (h : clear p l v newCell = true) : newCell ≠ oldCell := by
  intro same
  subst newCell
  have avoids := clear_avoids_placed p l v oldCell h _ member rfl
  have overlap := same_anchor_overlaps p (l.rects.getD v default) oldRect oldCell px py newContains oldContains
  rw [overlap] at avoids
  contradiction

theorem seed_right_of_bounds (p : Params) (l : Level) (v : Nat)
    (px : 0 < p.pitchX) (nonempty : l.bounds ≠ emptySpan) :
    l.bounds.x1 <
      ((l.rects.getD v default).shift ((seedCell p l v).x*p.pitchX)
        ((seedCell p l v).y*p.pitchY)).x0 := by
  let numerator := l.bounds.x1 - (l.rects.getD v default).x0 + p.pitchX - 1
  have division := Int.mul_fdiv_add_fmod numerator p.pitchX
  have remainder := Int.fmod_lt_of_pos numerator px
  have product : numerator.fdiv p.pitchX * p.pitchX + numerator.fmod p.pitchX = numerator := by
    simpa only [Int.mul_comm] using division
  simp only [seedCell,nonempty,↓reduceIte,Span.shift,ceilDiv,Int.add_mul,Int.one_mul]
  dsimp only [numerator] at product remainder
  omega

theorem seed_avoids_placed (p : Params) (l : Level) (v : Nat) (old : Span)
    (px : 0 < p.pitchX) (nonempty : l.bounds ≠ emptySpan) (inside : old.x1 ≤ l.bounds.x1) :
    ((l.rects.getD v default).shift ((seedCell p l v).x*p.pitchX)
      ((seedCell p l v).y*p.pitchY)).overlaps old = false := by
  have right := seed_right_of_bounds p l v px nonempty
  simp only [Span.overlaps,decide_eq_false_iff_not]
  omega

theorem ringRows_accept (origin : Cell) (distance : Int) (accept : Cell → Bool)
    (fuel : Nat) (dy : Int) (result : Cell)
    (h : ringRows origin distance accept fuel dy = some result) : accept result = true := by
  induction fuel generalizing dy result with
  | zero => simp [ringRows] at h
  | succ fuel ih =>
    dsimp only [ringRows] at h
    split at h
    · cases h
      assumption
    · split at h
      · cases h
        assumption
      · exact ih _ _ h

theorem ringSearch_accept (origin : Cell) (accept : Cell → Bool) (fuel distance : Nat)
    (result : Cell) (h : ringSearch origin accept fuel distance = some result) :
    accept result = true := by
  induction fuel generalizing distance result with
  | zero => simp [ringSearch] at h
  | succ fuel ih =>
    dsimp only [ringSearch] at h
    cases rows : ringRows origin (Int.ofNat distance) accept (2*distance+1) (-Int.ofNat distance) with
    | none =>
      simp only [rows] at h
      exact ih _ _ h
    | some found =>
      simp only [rows] at h
      cases h
      exact ringRows_accept _ _ _ _ _ _ rows

private def searchTier (candidates : List Cell) (origin : Cell) (accept : Cell → Bool)
    (radius : Nat) : Option Cell :=
  match candidates.find? accept with
  | some c => some c
  | none => ringSearch origin accept radius 1

private theorem searchTier_accept (candidates : List Cell) (origin : Cell) (accept : Cell → Bool)
    (radius : Nat) (result : Cell) (h : searchTier candidates origin accept radius = some result) :
    accept result = true := by
  unfold searchTier at h
  cases found : candidates.find? accept with
  | none =>
    simp only [found] at h
    exact ringSearch_accept _ _ _ _ _ h
  | some c =>
    simp only [found] at h
    cases h
    exact List.find?_some found

theorem choose_clear_of_seed (p : Params) (l : Level) (v u : Nat) (side : Side)
    (seedClear : clear p l v (seedCell p l v) = true) :
    clear p l v (choose p l v u side) = true := by
  let sides := side :: sideOrder.filter (· != side)
  let candidates := ([0,1] : List Int).flatMap fun extra => sides.map fun s =>
    let c := reach p l v u s
    (⟨c.x+extra*(step s).x,c.y+extra*(step s).y⟩ : Cell)
  let origin := l.cells.getD u default
  change clear p l v (match searchTier candidates origin
    (fun c => clear p l v c && aligned p l v c) p.ringCap with
    | some c => c
    | none => (searchTier candidates origin (clear p l v) (sweep p l v)).getD (seedCell p l v)) = true
  cases first : searchTier candidates origin (fun c => clear p l v c && aligned p l v c) p.ringCap with
  | some c =>
    have accepted := searchTier_accept _ _ _ _ _ first
    simp only [Bool.and_eq_true] at accepted
    exact accepted.1
  | none =>
    cases second : searchTier candidates origin (clear p l v) (sweep p l v) with
    | none => simpa only [second,Option.getD_none] using seedClear
    | some c =>
      simp only [Option.getD_some]
      exact searchTier_accept _ _ _ _ _ second

end Elegant.Grid.Architecture
