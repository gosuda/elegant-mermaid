 import Elegant.Layered.LaneBandsClearance
 import Init.Data.List.Sort.Lemmas
import Elegant.GridSimplify

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

theorem any_false_mem_aux2 {α : Type} (l : List α) (p : α → Bool) :
    ∀ (_h : l.any p = false) (x : α), x ∈ l → p x = false := by
  induction l with
  | nil =>
    intro _ _ hx
    simp at hx
  | cons hd tl ih =>
    intro h x hx
    have heq : (p hd || tl.any p) = false := by
      have heq2 : ((hd :: tl).any p) = (p hd || tl.any p) := by simp
      rw [heq2] at h
      exact h
    have hhd : p hd = false := by
      cases h1 : p hd with
      | false => rfl
      | true => simp [h1] at heq
    have htl : tl.any p = false := by
      cases h1 : p hd with
      | false => simpa [h1] using heq
      | true => simp [h1] at heq
    simp at hx
    rcases hx with rfl | hx
    · exact hhd
    · exact ih htl x hx

theorem all_true_mem_aux2 {α : Type} (l : List α) (p : α → Bool) :
    ∀ (_h : l.all p = true) (x : α), x ∈ l → p x = true := by
  induction l with
  | nil =>
    intro _ _ hx
    simp at hx
  | cons hd tl ih =>
    intro h x hx
    have heq : (p hd && tl.all p) = true := by
      have heq2 : ((hd :: tl).all p) = (p hd && tl.all p) := by simp
      rw [heq2] at h
      exact h
    have hhd : p hd = true := by
      cases h1 : p hd with
      | true => rfl
      | false => simp [h1] at heq
    have htl : tl.all p = true := by
      cases h1 : p hd with
      | true => simpa [h1] using heq
      | false => simp [h1] at heq
    simp at hx
    rcases hx with rfl | hx
    · exact hhd
    · exact ih htl x hx

theorem free_hits_false_aux (g : RouteGrid) (a b : GridPoint) (o : Obstacle)
    (hfree : g.free a b = true) (hobs : o ∈ g.obstacles) :
    o.hits a b = false := by
  unfold RouteGrid.free at hfree
  have hany : (g.obstacles.any (fun o => o.hits a b)) = false := by
    cases hAny : (g.obstacles.any (fun o => o.hits a b)) with
    | false => rfl
    | true => simp [hAny] at hfree
  exact any_false_mem_aux2 g.obstacles (fun o => o.hits a b) hany o hobs

theorem segMisses_x_horiz_aux (p q : Point) (r : Rect) (o : Obstacle)
    (hob : obstacleOf Axis.x r = o)
    (hhits : o.hits ⟨p.x, p.y⟩ ⟨q.x, q.y⟩ = false)
    (hy : p.y = q.y) :
    Polyline.segMisses p q r := by
  have ho : o = ⟨r.x, r.x + r.w, r.y, r.y + r.h⟩ := by
    rw [← hob]
    rfl
  subst ho
  have hEq : ((⟨r.x, r.x + r.w, r.y, r.y + r.h⟩ : Obstacle).hits ⟨p.x, p.y⟩ ⟨q.x, q.y⟩) =
      (((p.y == q.y && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
        min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x)) ||
      ((p.x == q.x) && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
        min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y)))) := rfl
  rw [hEq] at hhits
  have hNotTrue : ¬ ((((p.y == q.y && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
      min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x)) ||
      ((p.x == q.x) && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
      min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y))) = true)) := by
    rw [hhits]
    simp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_iff] at hNotTrue
  have hNotP : ¬ (r.y < p.y ∧ p.y < r.y + r.h ∧
      min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x) := by
    intro hP
    exact hNotTrue (Or.inl ⟨hy, hP⟩)
  unfold Polyline.segMisses
  omega

theorem segMisses_x_vert_aux (p q : Point) (r : Rect) (o : Obstacle)
    (hob : obstacleOf Axis.x r = o)
    (hhits : o.hits ⟨p.x, p.y⟩ ⟨q.x, q.y⟩ = false)
    (hx : p.x = q.x) :
    Polyline.segMisses p q r := by
  have ho : o = ⟨r.x, r.x + r.w, r.y, r.y + r.h⟩ := by
    rw [← hob]
    rfl
  subst ho
  have hEq : ((⟨r.x, r.x + r.w, r.y, r.y + r.h⟩ : Obstacle).hits ⟨p.x, p.y⟩ ⟨q.x, q.y⟩) =
      (((p.y == q.y && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
        min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x)) ||
      ((p.x == q.x) && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
        min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y)))) := rfl
  rw [hEq] at hhits
  have hNotTrue : ¬ ((((p.y == q.y && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
      min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x)) ||
      ((p.x == q.x) && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
      min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y))) = true)) := by
    rw [hhits]
    simp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_iff] at hNotTrue
  have hNotQ : ¬ (r.x < p.x ∧ p.x < r.x + r.w ∧
      min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y) := by
    intro hQ
    exact hNotTrue (Or.inr ⟨hx, hQ⟩)
  unfold Polyline.segMisses
  omega

theorem segMisses_y_horiz_aux (p q : Point) (r : Rect) (o : Obstacle)
    (hob : obstacleOf Axis.y r = o)
    (hhits : o.hits ⟨p.y, p.x⟩ ⟨q.y, q.x⟩ = false)
    (hy : p.y = q.y) :
    Polyline.segMisses p q r := by
  have ho : o = ⟨r.y, r.y + r.h, r.x, r.x + r.w⟩ := by
    rw [← hob]
    rfl
  subst ho
  have hEq : ((⟨r.y, r.y + r.h, r.x, r.x + r.w⟩ : Obstacle).hits ⟨p.y, p.x⟩ ⟨q.y, q.x⟩) =
      (((p.x == q.x && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
        min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y)) ||
      ((p.y == q.y) && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
        min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x)))) := rfl
  rw [hEq] at hhits
  have hNotTrue : ¬ ((((p.x == q.x && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
      min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y)) ||
      ((p.y == q.y) && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
      min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x))) = true)) := by
    rw [hhits]
    simp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_iff] at hNotTrue
  have hNotP : ¬ (r.y < p.y ∧ p.y < r.y + r.h ∧
      min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x) := by
    intro hP
    exact hNotTrue (Or.inr ⟨hy, hP⟩)
  unfold Polyline.segMisses
  omega

theorem segMisses_y_vert_aux (p q : Point) (r : Rect) (o : Obstacle)
    (hob : obstacleOf Axis.y r = o)
    (hhits : o.hits ⟨p.y, p.x⟩ ⟨q.y, q.x⟩ = false)
    (hx : p.x = q.x) :
    Polyline.segMisses p q r := by
  have ho : o = ⟨r.y, r.y + r.h, r.x, r.x + r.w⟩ := by
    rw [← hob]
    rfl
  subst ho
  have hEq : ((⟨r.y, r.y + r.h, r.x, r.x + r.w⟩ : Obstacle).hits ⟨p.y, p.x⟩ ⟨q.y, q.x⟩) =
      (((p.x == q.x && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
        min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y)) ||
      ((p.y == q.y) && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
        min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x)))) := rfl
  rw [hEq] at hhits
  have hNotTrue : ¬ ((((p.x == q.x && decide (r.x < p.x ∧ p.x < r.x + r.w ∧
      min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y)) ||
      ((p.y == q.y) && decide (r.y < p.y ∧ p.y < r.y + r.h ∧
      min p.x q.x < r.x + r.w ∧ r.x < max p.x q.x))) = true)) := by
    rw [hhits]
    simp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_iff] at hNotTrue
  have hNotQ : ¬ (r.x < p.x ∧ p.x < r.x + r.w ∧
      min p.y q.y < r.y + r.h ∧ r.y < max p.y q.y) := by
    intro hQ
    exact hNotTrue (Or.inl ⟨hx, hQ⟩)
  unfold Polyline.segMisses
  omega

/-- (1) A successful `findRoute` returned a polyline that passed the Bool
clearance test for the inflate it was found with. -/
theorem findRoute_ok_clear (axis : Axis) (ends : RouteEnds) (obs : List Obstacle)
    (bend : Int) (inflates : List Int) (points : List Point)
    (h : findRoute axis ends obs bend inflates = .ok points) :
    ∃ inflate ∈ inflates, ∃ g : RouteGrid,
      g = routeGrid obs inflate ends.entry ends.exit ∧
      g.obstacles = obs ∧
      clearPolyline g axis points = true := by
  induction inflates with
  | nil =>
    rw [findRoute.eq_1] at h
    cases h
  | cons inflate rest ih =>
    rw [findRoute.eq_2] at h
    split at h
    · have hRest : findRoute axis ends obs bend rest = .ok points := h
      obtain ⟨inf, hmem, g, hg, hobs, hclear⟩ := ih hRest
      exact ⟨inf, List.mem_cons_of_mem _ hmem, g, hg, hobs, hclear⟩
    · split at h
      · cases h
      · split at h
        · have hEq := Except.ok.inj h
          subst hEq
          exact ⟨inflate, List.mem_cons_self, routeGrid obs inflate ends.entry ends.exit,
            rfl, rfl, by assumption⟩
        · have hRest : findRoute axis ends obs bend rest = .ok points := h
          obtain ⟨inf, hmem, g, hg, hobs, hclear⟩ := ih hRest
          exact ⟨inf, List.mem_cons_of_mem _ hmem, g, hg, hobs, hclear⟩

/-- (2) The Bool segment test against an obstacle implies `segMisses` for the
rect that maps to that obstacle, for axis-aligned segments. -/
theorem clear_segment_misses (axis : Axis) (g : RouteGrid) (o : Obstacle)
    (p q : Point) (r : Rect)
    (hfree : g.free (axis.grid p) (axis.grid q) = true)
    (hobs : o ∈ g.obstacles)
    (hob : obstacleOf axis r = o)
     (hort : p.x = q.x ∨ p.y = q.y) :
     Polyline.segMisses p q r := by
   have hhits : o.hits (axis.grid p) (axis.grid q) = false :=
     free_hits_false_aux g (axis.grid p) (axis.grid q) o hfree hobs
   cases hAxis : axis with
   | x =>
     subst hAxis
     rcases hort with hx | hy
     · exact segMisses_x_vert_aux p q r o hob hhits hx
     · exact segMisses_x_horiz_aux p q r o hob hhits hy
   | y =>
     subst hAxis
     rcases hort with hx | hy
     · exact segMisses_y_vert_aux p q r o hob hhits hx
     · exact segMisses_y_horiz_aux p q r o hob hhits hy

 theorem clearPolyline_free_mem_aux (g : RouteGrid) (axis : Axis) (points : List Point)
     (hall : clearPolyline g axis points = true)
     (a b : Point) (hmem : (a, b) ∈ points.zip points.tail) :
     g.free (axis.grid a) (axis.grid b) = true := by
   unfold clearPolyline at hall
   have hmem2 := all_true_mem_aux2 (points.zip points.tail)
     (fun ab => g.free (axis.grid ab.1) (axis.grid ab.2)) hall (a, b) hmem
   simpa using hmem2

 theorem allSegs_of_mem_aux (points : List Point) (r : Rect)
     (h : ∀ a b : Point, ((a, b) ∈ points.zip points.tail) → Polyline.segMisses a b r) :
     Polyline.allSegsMiss points r := by
   induction points with
   | nil => simp [Polyline.allSegsMiss]
   | cons p rest ih =>
     cases rest with
     | nil => simp [Polyline.allSegsMiss]
     | cons q rest2 =>
       simp only [Polyline.allSegsMiss]
       constructor
       · exact h p q (by simp)
       · apply ih
         intro a b hmem
         apply h a b
         have heq : ((p :: q :: rest2).zip ((p :: q :: rest2).tail)) =
             (p, q) :: ((q :: rest2).zip ((q :: rest2).tail)) := by
           simp
         rw [heq]
         simp only [List.mem_cons]
         exact Or.inr hmem

 /-- (3) A polyline whose consecutive pairs all miss `r` never hits `r`. -/
 theorem clear_allSegs_of_free (axis : Axis) (g : RouteGrid) (points : List Point)
     (r : Rect) (o : Obstacle)
     (hobs : o ∈ g.obstacles)
     (hob : obstacleOf axis r = o)
     (hall : clearPolyline g axis points = true)
     (horth : ∀ a b : Point, ((a, b) ∈ points.zip points.tail) →
       a.x = b.x ∨ a.y = b.y) :
     Polyline.allSegsMiss points r := by
   apply allSegs_of_mem_aux points r
   intro a b hmem
   have hfree : g.free (axis.grid a) (axis.grid b) = true :=
     clearPolyline_free_mem_aux g axis points hall a b hmem
   have hort : a.x = b.x ∨ a.y = b.y := horth a b hmem
   exact clear_segment_misses axis g o a b r hfree hobs hob hort

/-- Candidate-construction fact replacing unconditional orthogonality: `Axis.at`
sends grid points that share `cross` or `rank` to points that share `x` or `y`.
Every neighbour step of the grid search shares one grid coordinate, so each
candidate step is axis-aligned once mapped with `axis.at`. Unconditional
`findRoute` orthogonality is false as stated: with ends whose entry shares
neither coordinate with source, the search still returns `.ok` (see the probe:
misaligned ends give `[(0,0),(5,5),(10,5),(10,0)]` with a diagonal first pair).
`pinBands` never builds such ends (`routeEnds` shifts rank only). -/
def atAligned : Prop :=
  ∀ (axis : Axis) (a b : GridPoint),
    a.cross = b.cross ∨ a.rank = b.rank →
    (axis.at a).x = (axis.at b).x ∨ (axis.at a).y = (axis.at b).y

theorem atAligned_holds : atAligned := by
  intro axis a b h
  cases axis with
  | x =>
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  | y =>
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Destructor for one `Except` bind; the same shape as the phase-facts helper. -/
theorem bindOk_inv {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- `routeEnds` inlined at its two shifted endpoints: the grid entries are
built from the shifted points with rank-only offsets. -/
theorem routeEnds_eq (axis : Axis) (sp : Spacing) (pin : Pin)
    (fromBox toBox : Box) (original : List Point)
    (source target : Point)
    (hs : shiftedPoint axis (pin.boxDelta fromBox.id) (original.headD ⟨0, 0⟩) = .ok source)
    (ht : shiftedPoint axis (pin.boxDelta toBox.id) (original.getLast?.getD ⟨0, 0⟩) = .ok target) :
    routeEnds axis sp pin fromBox toBox original =
      .ok ⟨source, target,
        ⟨(axis.grid source).cross,
          (axis.grid source).rank + outward axis fromBox.rect (axis.grid source).rank * sp.slot⟩,
        ⟨(axis.grid target).cross,
          (axis.grid target).rank + outward axis toBox.rect (axis.grid target).rank * sp.slot⟩,
        if outward axis fromBox.rect (axis.grid source).rank < 0 then 3 else 2,
        if outward axis toBox.rect (axis.grid target).rank < 0 then 2 else 3⟩ := by
  unfold routeEnds
  rw [hs, ht]
  rfl

/-- Attachment alignment for the ends `pinBands` actually passes: `routeEnds`
shifts the cross-axis rank only, so the source shares one coordinate with the
mapped entry and the mapped exit shares one with the target. This discharges
the attachment half of orthogonality for `rerouteBands` ends; the middle half
is the `SearchGridPathStep` residual below. -/
def routeEndsAligned : Prop :=
  ∀ (axis : Axis) (sp : Spacing) (pin : Pin) (fromBox toBox : Box)
    (original : List Point) (ends : RouteEnds),
    routeEnds axis sp pin fromBox toBox original = .ok ends →
    (ends.source.x = (axis.at ends.entry).x ∨ ends.source.y = (axis.at ends.entry).y) ∧
    ((axis.at ends.exit).x = ends.target.x ∨ (axis.at ends.exit).y = ends.target.y)

theorem routeEndsAligned_holds : routeEndsAligned := by
  intro axis sp pin fb tb orig ends h
  have h0 := h
  unfold routeEnds at h
  obtain ⟨source, hs, hrest⟩ := bindOk_inv h
  dsimp only at hrest
  obtain ⟨target, ht, _⟩ := bindOk_inv hrest
  have e := routeEnds_eq axis sp pin fb tb orig source target hs ht
  rw [e] at h0
  simp only [Except.ok.injEq] at h0
  subst h0
  cases axis with
  | x => exact ⟨Or.inl rfl, Or.inl rfl⟩
  | y => exact ⟨Or.inr rfl, Or.inr rfl⟩

/-- Weakest true variant of `pinBandsFindRouteClear`: clearance holds for every
returned polyline that is orthogonal. The orthogonality premise is exactly what
`clear_allSegs_of_free` needs; it holds on the executed swimlane-shaped control
(aligned ends return an orthogonal `.ok` route). The unconditional statement
needs the open search-chain induction (neighbour div-mod, `searchGrid`
invariant, `routePolyline` mapM roundtrip, `simplifyPoints` preservation).
`pinBands` passes `inflates = [sp.slot, 0]`; inflate only widens grid lines
while `g.obstacles` stays `obs`, so no nonnegativity hypothesis is needed. -/
theorem pinBandsFindRouteClear_of_orthogonal
    (axis : Axis) (ends : RouteEnds) (obs : List Obstacle) (bend : Int)
    (inflates : List Int) (points : List Point)
    (h : findRoute axis ends obs bend inflates = .ok points)
    (horth : ∀ a b : Point, (a, b) ∈ points.zip points.tail →
      a.x = b.x ∨ a.y = b.y)
    (o : Obstacle) (hos : o ∈ obs) (r : Rect) (hob : obstacleOf axis r = o) :
    ¬ Polyline.hitsRect points r := by
  obtain ⟨inflate, _, g, hg, hobs, hclear⟩ :=
    findRoute_ok_clear axis ends obs bend inflates points h
  subst hg
  have hmem : o ∈ (routeGrid obs inflate ends.entry ends.exit).obstacles := by
    rw [hobs]
    exact hos
  exact Polyline.not_hits_of_allMiss
    (clear_allSegs_of_free axis _ points r o hmem hob hclear horth)


/-- Clearance for the ends `rerouteBands` actually passes
(`LaneBands.lean:588`: `ends` from `routeEnds`, `inflates = [sp.slot, 0]`).
`_hends` is the exact witness `rerouteBands_mem` provides (line 868); it is
consumed by `routeEndsAligned_holds` for the attachment half once the middle
closes under `SearchGridPathStep` plus the vertex roundtrip, `routePolyline`
mapM, and `simplifyPoints` assembly. Until then the per-pair orthogonality
premise stands. `pinBands_c6` (lines 982-984) applies the pinned `hfind`
with `fb tb old.points ends hends` from its fresh-route tuple. -/
theorem pinBandsFindRouteClear_of_routeEnds
    (axis : Axis) (sp : Spacing) (pin : Pin) (fromBox toBox : Box)
    (original : List Point) (ends : RouteEnds)
    (_hends : routeEnds axis sp pin fromBox toBox original = .ok ends)
    (obs : List Obstacle) (bend : Int) (points : List Point)
    (h : findRoute axis ends obs bend [sp.slot, 0] = .ok points)
    (horth : ∀ a b : Point, (a, b) ∈ points.zip points.tail →
      a.x = b.x ∨ a.y = b.y)
    (o : Obstacle) (hos : o ∈ obs) (r : Rect) (hob : obstacleOf axis r = o) :
    ¬ Polyline.hitsRect points r := by
  exact pinBandsFindRouteClear_of_orthogonal axis ends obs bend [sp.slot, 0]
    points h horth o hos r hob

/-- Consecutive vertices of a search path share a grid coordinate: the
assembly-level reading of one neighbour step. -/
def NeighbourChain (g : RouteGrid) (path : List Nat) : Prop :=
  ∀ a b : Nat, (a, b) ∈ path.zip path.tail →
    (g.point a).cross = (g.point b).cross ∨ (g.point a).rank = (g.point b).rank

/-- A queued or best search node is usable for the assembly: its path is
nonempty, ends at the initial `start` vertex, starts (head) at its own
state vertex, and steps to grid neighbours. -/
def SearchNodeOk (g : RouteGrid) (start : Nat) (node : SearchNode) : Prop :=
  node.path ≠ [] ∧ node.path.getLast? = some start ∧
    node.path.head? = some (node.state / 4) ∧ NeighbourChain g node.path

/-- The search-chain residual, in true form: from usable queues and bests
the search returns a usable node aimed at the goal. The earlier universal
form (every returned path, from any queue and best) is false: an arbitrary
injected `best` is returned as-is by the empty-queue branch, so a junk path
such as `[5, 2]` refutes it on grids whose points differ in both
coordinates. What `pinBands` needs — and what holds — is this conditional
preservation, proved below by induction on `searchGrid` with the invariant
that every queued or best node satisfies `SearchNodeOk` (preserved by
`relaxNode`, queue filtering, and the merge sort via `List.mem_mergeSort`).
Probed on swimlane-shaped grids (`FindRouteClearProbe`): the
aligned-control search returns `[1, 0]` and the blocked-middle search
`[4, 5, 2, 1]`, each satisfying `SearchNodeOk` at its initial vertex. -/
def SearchGridPathStep : Prop :=
  ∀ (g : RouteGrid) (goal endMove : Nat) (bend : Int) (start : Nat)
    (remaining : List Nat) (search : RouteSearch),
    (∀ n ∈ search.queue, SearchNodeOk g start n) →
    (∀ b, search.best = some b → SearchNodeOk g start b ∧ b.state / 4 = goal) →
    ∀ node, searchGrid g goal endMove bend remaining search = some node →
      SearchNodeOk g start node ∧ node.state / 4 = goal

/-- One neighbour step shares a grid coordinate: moves `0`/`1` keep the
rank index, moves `2`/`3` keep the cross index (indices are `v / size` and
`v % size`). -/
theorem neighbour_step_aligned (g : RouteGrid) (v w move : Nat)
    (h : g.neighbour v move = some w) :
    (g.point v).cross = (g.point w).cross ∨
      (g.point v).rank = (g.point w).rank := by
  simp only [RouteGrid.neighbour] at h
  split at h
  · simp at h
    obtain ⟨-, heq⟩ := h
    subst heq
    have hmod : ((v / g.rank.size + 1) * g.rank.size + v % g.rank.size) %
        g.rank.size = v % g.rank.size := by
      by_cases hsize : g.rank.size = 0
      · simp [hsize]
      · have hpos : 0 < g.rank.size := Nat.pos_of_ne_zero hsize
        have hlt : v % g.rank.size < g.rank.size := Nat.mod_lt _ hpos
        rw [Nat.add_comm ((v / g.rank.size + 1) * g.rank.size) (v % g.rank.size),
          Nat.mul_comm (v / g.rank.size + 1) (g.rank.size)]
        exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt hlt)
    simp only [RouteGrid.point]
    exact Or.inr (by rw [hmod])
  · simp at h
    obtain ⟨-, heq⟩ := h
    rw [← heq.2]
    have hmod : ((v / g.rank.size - 1) * g.rank.size + v % g.rank.size) %
        g.rank.size = v % g.rank.size := by
      by_cases hsize : g.rank.size = 0
      · simp [hsize]
      · have hpos : 0 < g.rank.size := Nat.pos_of_ne_zero hsize
        have hlt : v % g.rank.size < g.rank.size := Nat.mod_lt _ hpos
        rw [Nat.add_comm ((v / g.rank.size - 1) * g.rank.size) (v % g.rank.size),
          Nat.mul_comm (v / g.rank.size - 1) (g.rank.size)]
        exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt hlt)
    simp only [RouteGrid.point]
    exact Or.inr (by rw [hmod])
  · simp at h
    obtain ⟨hguard, heq⟩ := h
    subst heq
    have hdiv : (v / g.rank.size * g.rank.size + (v % g.rank.size + 1)) /
        g.rank.size = v / g.rank.size := by
      by_cases hsize : g.rank.size = 0
      · simp [hsize]
      · have hpos : 0 < g.rank.size := Nat.pos_of_ne_zero hsize
        have h0 : (v % g.rank.size + 1) / g.rank.size = 0 :=
          Nat.div_eq_zero_iff.mpr (Or.inr hguard.2)
        rw [Nat.add_comm (v / g.rank.size * g.rank.size) (v % g.rank.size + 1),
          Nat.mul_comm (v / g.rank.size) (g.rank.size),
          Nat.add_mul_div_left _ _ hpos, h0, Nat.zero_add]
    simp only [RouteGrid.point]
    exact Or.inl (by rw [hdiv])
  · simp at h
    obtain ⟨hguard, heq⟩ := h
    rw [← heq.2]
    have hdiv : (v / g.rank.size * g.rank.size + (v % g.rank.size - 1)) /
        g.rank.size = v / g.rank.size := by
      by_cases hsize : g.rank.size = 0
      · simp [hsize]
      · have hpos : 0 < g.rank.size := Nat.pos_of_ne_zero hsize
        have h0 : (v % g.rank.size - 1) / g.rank.size = 0 :=
          Nat.div_eq_zero_iff.mpr (Or.inr heq.1.2)
        rw [Nat.add_comm (v / g.rank.size * g.rank.size) (v % g.rank.size - 1),
          Nat.mul_comm (v / g.rank.size) (g.rank.size),
          Nat.add_mul_div_left _ _ hpos, h0, Nat.zero_add]
    simp only [RouteGrid.point]
    exact Or.inl (by rw [hdiv])

/-- Every element of `eraseDups` comes from the original list. -/
theorem eraseDups_sublist {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Sublist l := by
  have key : ∀ n : Nat, ∀ l : List α, l.length = n → l.eraseDups.Sublist l := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l hl
      induction l with
      | nil => exact List.Sublist.refl []
      | cons a as =>
        rw [List.eraseDups_cons]
        refine List.Sublist.cons_cons a ?_
        have hlen : (List.filter (fun b => !b == a) as).length < n := by
          have h1 := List.length_filter_le (fun b => !b == a) as
          have h2 : as.length + 1 = n := by
            have := hl; simp at this; omega
          omega
        have h3 := ih _ hlen _ rfl
        exact h3.trans List.filter_sublist
  exact key l.length l rfl

/-- `eraseDups` never duplicates. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup := by
  have key : ∀ n : Nat, ∀ l : List α, l.length = n → l.eraseDups.Nodup := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l hl
      induction l with
      | nil => exact List.nodup_nil
      | cons a as =>
        rw [List.eraseDups_cons, List.nodup_cons]
        have hlen : (List.filter (fun b => !b == a) as).length < n := by
          have h1 := List.length_filter_le (fun b => !b == a) as
          have h2 : as.length + 1 = n := by
            have := hl; simp at this; omega
          omega
        refine ⟨?_, ih _ hlen _ rfl⟩
        intro hmem
        rw [List.mem_eraseDups, List.mem_filter] at hmem
        simp at hmem
  exact key l.length l rfl

/-- Sorted coordinates stay sorted. -/
theorem sortedCoordinates_sorted (xs : List Int) :
    List.Pairwise (· ≤ ·) (sortedCoordinates xs).toList := by
  unfold sortedCoordinates
  rw [List.toList_toArray]
  apply List.Pairwise.imp (fun {a b} h => of_decide_eq_true h)
  have h1 := List.pairwise_mergeSort
    (le := fun a b => decide (a ≤ b))
    (fun a b c h1 h2 => decide_eq_true (Int.le_trans (of_decide_eq_true h1)
      (of_decide_eq_true h2)))
    (fun a b => by
      rw [Bool.or_eq_true]
      by_cases h : a ≤ b
      · exact Or.inl (decide_eq_true h)
      · exact Or.inr (decide_eq_true (Int.le_of_lt (Int.not_le.mp h))))
    xs
  exact List.Pairwise.sublist (eraseDups_sublist _) h1

/-- Sorted coordinates never duplicate. -/
theorem sortedCoordinates_nodup (xs : List Int) :
    (sortedCoordinates xs).toList.Nodup := by
  unfold sortedCoordinates
  rw [List.toList_toArray]
  exact nodup_eraseDups _

/-- Sorted coordinates keep every input. -/
theorem sortedCoordinates_mem {a : Int} {xs : List Int} (h : a ∈ xs) :
    a ∈ (sortedCoordinates xs).toList := by
  unfold sortedCoordinates
  rw [List.toList_toArray, List.mem_eraseDups, List.mem_mergeSort]
  exact h

/-- In a sorted nodup list, the index of `x` equals the number of elements
below `x`, and the element there is `x` itself. -/
theorem sorted_takeWhile_getElem? {xs : List Int}
    (hs : List.Pairwise (· ≤ ·) xs) (hn : xs.Nodup) {x : Int} (hx : x ∈ xs) :
    xs[(xs.takeWhile (fun v => decide (v < x))).length]? = some x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    rw [List.pairwise_cons] at hs
    rw [List.nodup_cons] at hn
    obtain ⟨hhead, htail⟩ := hs
    obtain ⟨ha_not, hn_tail⟩ := hn
    rw [List.mem_cons] at hx
    by_cases hlt : a < x
    · have hdec : decide (a < x) = true := decide_eq_true hlt
      rw [List.takeWhile_cons, ite_eq_left hdec, List.length_cons,
        List.getElem?_cons_succ]
      have hx' : x ∈ as := by
        rcases hx with rfl | h
        · omega
        · exact h
      exact ih htail hn_tail hx'
    · have hxle : x ≤ a := Int.not_lt.mp hlt
      rw [List.takeWhile_cons,
        ite_eq_right (fun h => hlt (of_decide_eq_true h))]
      rw [List.length_nil, List.getElem?_cons_zero]
      rcases hx with rfl | h
      · rfl
      · have hax : a ≤ x := hhead x h
        have : a = x := Int.le_antisymm hax hxle
        subst this
        exact (ha_not h).elim

/-- Arithmetic core of the vertex roundtrip: div/mod split a flat grid
index back into its cross and rank parts. -/
theorem point_vertex_aux (c r : Array Int) (k1 k2 : Nat) (x y : Int)
    (h1 : c[k1]? = some x) (h2 : r[k2]? = some y) (hk2 : k2 < r.size) :
    (c[(k1 * r.size + k2) / r.size]?).getD 0 = x ∧
    (r[(k1 * r.size + k2) % r.size]?).getD 0 = y := by
  have hpos : 0 < r.size := by omega
  have hdiv : (k1 * r.size + k2) / r.size = k1 := by
    rw [Nat.add_comm (k1 * r.size) k2, Nat.mul_comm k1 r.size,
      Nat.add_mul_div_left _ _ hpos,
      Nat.div_eq_zero_iff.mpr (Or.inr hk2), Nat.zero_add]
  have hmod : (k1 * r.size + k2) % r.size = k2 := by
    rw [Nat.add_comm (k1 * r.size) k2, Nat.mul_comm k1 r.size]
    exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt hk2)
  rw [hdiv, hmod]
  exact ⟨by rw [h1, Option.getD_some], by rw [h2, Option.getD_some]⟩

/-- TakeWhile lengths index into sorted coordinate arrays. -/
theorem sortedCoordinates_idx (xs : List Int) (x : Int)
    (hs : List.Pairwise (· ≤ ·) (sortedCoordinates xs).toList)
    (hn : (sortedCoordinates xs).toList.Nodup)
    (hx : x ∈ (sortedCoordinates xs).toList) :
    ∃ k : Nat, (sortedCoordinates xs)[k]? = some x ∧
      k = (((sortedCoordinates xs).toList.takeWhile (fun v => decide (v < x))).length) := by
  refine ⟨_, ?_, rfl⟩
  rw [← Array.getElem?_toList]
  exact sorted_takeWhile_getElem? hs hn hx


/-- The vertex of `entry` reads back to `entry`. -/
theorem vertex_point_entry (obs : List Obstacle) (inflate : Int)
    (entry exit_ : GridPoint) :
    (routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex entry) = entry := by
  have hboth : ((routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex entry)).cross = entry.cross ∧
      ((routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex entry)).rank = entry.rank := by
    have hsortC := sortedCoordinates_sorted
      ([entry.cross, exit_.cross] ++ obs.flatMap (fun o => [o.cross0 - inflate, o.cross1 + inflate]))
    have hnodC := sortedCoordinates_nodup
      ([entry.cross, exit_.cross] ++ obs.flatMap (fun o => [o.cross0 - inflate, o.cross1 + inflate]))
    have hmemC : entry.cross ∈ (sortedCoordinates
      ([entry.cross, exit_.cross] ++ obs.flatMap (fun o => [o.cross0 - inflate, o.cross1 + inflate]))).toList :=
      sortedCoordinates_mem (List.mem_append.mpr (Or.inl List.mem_cons_self))
    have hsortR := sortedCoordinates_sorted
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))
    have hnodR := sortedCoordinates_nodup
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))
    have hmemR : entry.rank ∈ (sortedCoordinates
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))).toList :=
      sortedCoordinates_mem (List.mem_append.mpr (Or.inl List.mem_cons_self))
    obtain ⟨K1, e1, hK1⟩ := sortedCoordinates_idx _ _ hsortC hnodC hmemC
    obtain ⟨K2, e2, hK2⟩ := sortedCoordinates_idx _ _ hsortR hnodR hmemR
    have hk : K2 < (sortedCoordinates
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))).size := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp e2
      exact hlt
    unfold RouteGrid.vertex RouteGrid.point routeGrid
    rw [← hK1, ← hK2]
    exact point_vertex_aux _ _ _ _ _ _ e1 e2 hk
  have hc := hboth.1
  have hr := hboth.2
  revert hc hr
  cases hP : ((routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex entry)) with
  | mk px py =>
    intro hc hr
    have hcx : px = entry.cross := hc
    have hcy : py = entry.rank := hr
    subst hcx
    subst hcy
    rfl

/-- The vertex of `exit` reads back to `exit`. -/
theorem vertex_point_exit (obs : List Obstacle) (inflate : Int)
    (entry exit_ : GridPoint) :
    (routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex exit_) = exit_ := by
  have hboth : ((routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex exit_)).cross = exit_.cross ∧
      ((routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex exit_)).rank = exit_.rank := by
    have hsortC := sortedCoordinates_sorted
      ([entry.cross, exit_.cross] ++ obs.flatMap (fun o => [o.cross0 - inflate, o.cross1 + inflate]))
    have hnodC := sortedCoordinates_nodup
      ([entry.cross, exit_.cross] ++ obs.flatMap (fun o => [o.cross0 - inflate, o.cross1 + inflate]))
    have hmemC : exit_.cross ∈ (sortedCoordinates
      ([entry.cross, exit_.cross] ++ obs.flatMap (fun o => [o.cross0 - inflate, o.cross1 + inflate]))).toList :=
      sortedCoordinates_mem (List.mem_append.mpr
        (Or.inl (List.mem_cons.mpr (Or.inr List.mem_cons_self))))
    have hsortR := sortedCoordinates_sorted
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))
    have hnodR := sortedCoordinates_nodup
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))
    have hmemR : exit_.rank ∈ (sortedCoordinates
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))).toList :=
      sortedCoordinates_mem (List.mem_append.mpr
        (Or.inl (List.mem_cons.mpr (Or.inr List.mem_cons_self))))
    obtain ⟨K1, e1, hK1⟩ := sortedCoordinates_idx _ _ hsortC hnodC hmemC
    obtain ⟨K2, e2, hK2⟩ := sortedCoordinates_idx _ _ hsortR hnodR hmemR
    have hk : K2 < (sortedCoordinates
      ([entry.rank, exit_.rank] ++ obs.flatMap (fun o => [o.rank0 - inflate, o.rank1 + inflate]))).size := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp e2
      exact hlt
    unfold RouteGrid.vertex RouteGrid.point routeGrid
    rw [← hK1, ← hK2]
    exact point_vertex_aux _ _ _ _ _ _ e1 e2 hk
  have hc := hboth.1
  have hr := hboth.2
  revert hc hr
  cases hP : ((routeGrid obs inflate entry exit_).point
      ((routeGrid obs inflate entry exit_).vertex exit_)) with
  | mk px py =>
    intro hc hr
    have hcx : px = exit_.cross := hc
    have hcy : py = exit_.rank := hr
    subst hcx
    subst hcy
    rfl
/-- `relaxNode` preserves usability: it either keeps the queue or prepends a
neighbour vertex, keeping the start tail, head-state consistency, and the
neighbour chain. -/
theorem relaxNode_ok (g : RouteGrid) (bend : Int) (remaining : List Nat)
    (node : SearchNode) (queue : List SearchNode) (move : Nat) (start : Nat)
    (hok : SearchNodeOk g start node)
    (hall : ∀ n ∈ queue, SearchNodeOk g start n)
    (hmove : move < 4) :
    ∀ n ∈ relaxNode g bend remaining node queue move, SearchNodeOk g start n := by
  obtain ⟨hne, hlast, hhead, hchain⟩ := hok
  obtain ⟨hd, tl, hpath⟩ := List.exists_cons_of_ne_nil hne
  unfold relaxNode
  intro n hn
  split at hn
  · exact hall n hn
  · split at hn
    · exact hall n hn
    · rename_i v hnb
      dsimp only at hn
      split at hn
      · exact hall n hn
      · split at hn
        · exact hall n hn
        · rw [List.mem_cons] at hn
          rcases hn with rfl | hn
          · refine ⟨?_, ?_, ?_, ?_⟩
            · simp
            · rw [hpath, List.getLast?_cons_cons, ← hpath]
              exact hlast
            · have h4 : (v * 4 + move) / 4 = v := by omega
              show (v :: node.path).head? = some ((v * 4 + move) / 4)
              simp [h4]
            · intro a b hmem
              have heq : ((v :: node.path).zip (v :: node.path).tail) =
                  (v, hd) :: ((hd :: tl).zip tl) := by
                rw [hpath]
                rfl
              rw [heq] at hmem
              rcases List.mem_cons.mp hmem with hxy | hmem
              · simp only [Prod.mk.injEq] at hxy
                obtain ⟨ha, hb⟩ := hxy
                rw [ha, hb]
                have hhd : hd = node.state / 4 := by
                  have hh := hhead
                  rw [hpath] at hh
                  simpa using hh
                have hN := neighbour_step_aligned g (node.state / 4) v move hnb
                rw [← hhd] at hN
                rcases hN with h | h
                · exact Or.inl h.symm
                · exact Or.inr h.symm
              · exact hchain a b (by rw [hpath]; exact hmem)
          · exact hall n (List.mem_filter.mp hn).1
/-- Folding `relaxNode` over the four moves preserves usability. -/
theorem foldl_relax_ok (g : RouteGrid) (bend : Int) (rest : List Nat)
    (node : SearchNode) (queue : List SearchNode) (start : Nat)
    (hok : SearchNodeOk g start node)
    (hall : ∀ n ∈ queue, SearchNodeOk g start n) :
    ∀ m ∈ [0, 1, 2, 3].foldl (relaxNode g bend rest node) queue,
      SearchNodeOk g start m := by
  intro m hm
  have h0 : ∀ m ∈ relaxNode g bend rest node queue 0, SearchNodeOk g start m :=
    relaxNode_ok g bend rest node queue 0 start hok hall (by decide)
  have h1 : ∀ m ∈ relaxNode g bend rest node (relaxNode g bend rest node queue 0) 1,
      SearchNodeOk g start m :=
    relaxNode_ok g bend rest node _ 1 start hok h0 (by decide)
  have h2 : ∀ m ∈ relaxNode g bend rest node
      (relaxNode g bend rest node (relaxNode g bend rest node queue 0) 1) 2,
      SearchNodeOk g start m :=
    relaxNode_ok g bend rest node _ 2 start hok h1 (by decide)
  have h3 : ∀ m ∈ relaxNode g bend rest node
      (relaxNode g bend rest node
        (relaxNode g bend rest node (relaxNode g bend rest node queue 0) 1) 2) 3,
      SearchNodeOk g start m :=
    relaxNode_ok g bend rest node _ 3 start hok h2 (by decide)
  have e : [0, 1, 2, 3].foldl (relaxNode g bend rest node) queue =
      relaxNode g bend rest node
        (relaxNode g bend rest node
          (relaxNode g bend rest node (relaxNode g bend rest node queue 0) 1) 2) 3 := rfl
  rw [e] at hm
  exact h3 m hm
/-- The `best` update preserves usability and the goal aim: it either keeps
the old best or installs the expanded node (whose state aims at the goal). -/
theorem best_update_ok (g : RouteGrid) (goal : Nat) (start : Nat)
    (node : SearchNode) (old : Option SearchNode) (total : Int)
    (hok : SearchNodeOk g start node)
    (hb : ∀ b, old = some b → SearchNodeOk g start b ∧ b.state / 4 = goal) :
    ∀ b, (if _h : (node.state / 4 == goal &&
      old.all (fun best => decide (total < best.cost))) = true
      then some ({ state := node.state, cost := total, path := node.path } : SearchNode)
      else old) = some b →
      SearchNodeOk g start b ∧ b.state / 4 = goal := by
  intro b h
  by_cases hc : (node.state / 4 == goal &&
    old.all (fun best => decide (total < best.cost))) = true
  · simp [hc] at h
    subst h
    obtain ⟨hne', hlast', hhead', hchain'⟩ := hok
    have hgoal : node.state / 4 = goal :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).1
    exact ⟨⟨hne', hlast', hhead', hchain'⟩, hgoal⟩
  · simp [hc] at h
    exact hb b h
/-- The search loop invariant: from usable queues and bests the search
returns a usable node aimed at the goal. The queue half is preserved by
`relaxNode` (`relaxNode_ok`, `foldl_relax_ok`) across the sorted head and
tail (`List.mem_mergeSort`); the best half by `best_update_ok` (the
installed node keeps its path, and the guard supplies the aim). -/
theorem searchGrid_ok (g : RouteGrid) (goal endMove : Nat) (bend : Int) (start : Nat)
    (remaining : List Nat) (search : RouteSearch)
    (hq : ∀ n ∈ search.queue, SearchNodeOk g start n)
    (hb : ∀ b, search.best = some b → SearchNodeOk g start b ∧ b.state / 4 = goal)
    (node : SearchNode)
    (h : searchGrid g goal endMove bend remaining search = some node) :
    SearchNodeOk g start node ∧ node.state / 4 = goal := by
  refine searchGrid.induct g goal endMove bend
    (motive := fun remaining search =>
      (∀ n ∈ search.queue, SearchNodeOk g start n) →
      (∀ b, search.best = some b → SearchNodeOk g start b ∧ b.state / 4 = goal) →
      ∀ node, searchGrid g goal endMove bend remaining search = some node →
      SearchNodeOk g start node ∧ node.state / 4 = goal) ?_ ?_ ?_ ?_ remaining search hq hb node h
  · intro remaining search hsorted hq hb node h
    rw [searchGrid.eq_def, hsorted] at h
    exact hb node h
  · intro remaining search n queue hsorted hcut hq hb node h
    rw [searchGrid.eq_def, hsorted] at h
    dsimp only at h
    simp only [hcut, ↓reduceIte] at h
    exact hb node h
  · intro remaining search n queue hsorted hcut hmem rest total best next ih hq hb node h
    rw [searchGrid.eq_def, hsorted] at h
    dsimp only at h
    simp only [hcut, Bool.false_eq_true, ↓reduceIte, hmem, ↓reduceDIte] at h
    have hmem_sorted : ∀ x ∈ search.queue.mergeSort (queueLe g goal), SearchNodeOk g start x := by
      intro x hx
      rw [List.mem_mergeSort] at hx
      exact hq x hx
    have hn : SearchNodeOk g start n := by
      have : n ∈ search.queue.mergeSort (queueLe g goal) := by rw [hsorted]; exact List.mem_cons_self
      exact hmem_sorted n this
    have hqueue : ∀ m ∈ queue, SearchNodeOk g start m := by
      intro m hm
      have : m ∈ search.queue.mergeSort (queueLe g goal) := by
        rw [hsorted]; exact List.mem_cons_of_mem n hm
      exact hmem_sorted m this
    have hnext : ∀ m ∈ next, SearchNodeOk g start m := by
      show ∀ m ∈ List.foldl (relaxNode g bend rest n) queue [0, 1, 2, 3], SearchNodeOk g start m
      exact foldl_relax_ok g bend rest n queue start hn hqueue
    have hbest : ∀ b, best = some b → SearchNodeOk g start b ∧ b.state / 4 = goal := by
      show ∀ b, (if _h : (n.state / 4 == goal &&
        search.best.all (fun best => decide (total < best.cost))) = true
        then some ({ state := n.state, cost := total, path := n.path } : SearchNode)
        else search.best) = some b → _
      intro b hb'
      by_cases hc : (n.state / 4 == goal &&
        search.best.all (fun best => decide (total < best.cost))) = true
      · simp only [hc] at hb'
        have hbb : ({ state := n.state, cost := total, path := n.path } : SearchNode) = b :=
          Option.some.inj hb'
        subst hbb
        obtain ⟨hne', hlast', hhead', hchain'⟩ := hn
        have hgoal : n.state / 4 = goal :=
          beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).1
        exact ⟨⟨hne', hlast', hhead', hchain'⟩, hgoal⟩
      · simp only [hc] at hb'
        exact hb b hb'
    exact ih hnext hbest node h
  · intro remaining search n queue hsorted hcut hnotmem hq hb node h
    rw [searchGrid.eq_def, hsorted] at h
    dsimp only at h
    simp only [hcut, Bool.false_eq_true, ↓reduceIte, hnotmem, ↓reduceDIte] at h
    exact hb node h

/-- The search-chain residual holds: the conditional preservation above is
exactly the restated `SearchGridPathStep`. -/
theorem SearchGridPathStep_holds : SearchGridPathStep := searchGrid_ok
-- `LaneBands.checkedI32_ok` already proves a successful `checkedI32`
-- returns its input; the assembly below uses that form.
/-- The local `trim` inside `simplifyPoints` is `Grid.popCollinear`. -/
theorem trim_popCollinear (p : Point) (acc : List Point) :
    simplifyPoints.trim p acc = Grid.popCollinear acc p := by
  induction acc with
  | nil => rfl
  | cons b rest ih =>
    cases rest with
    | nil => rfl
    | cons a rest' =>
      rw [simplifyPoints.trim.eq_1, Grid.popCollinear.eq_def]
      dsimp only
      simp only [Grid.collinear]
      by_cases hC : (a.x == b.x && b.x == p.x || a.y == b.y && b.y == p.y) = true
      · simp only [hC, ↓reduceIte, ih]
      · simp only [hC, Bool.false_eq_true, ↓reduceIte]

/-- One fold step of `simplifyPoints` is one fold step of `Grid.simplify`. -/
theorem simplify_step_eq (acc : List Point) (p : Point) :
    (if (acc.head? == some p) = true then acc
      else p :: simplifyPoints.trim p acc) =
    (if acc.head? = some p then acc else p :: Grid.popCollinear acc p) := by
  have htrim := trim_popCollinear p acc
  by_cases h : acc.head? = some p
  · have hb : (acc.head? == some p) = true := beq_iff_eq.mpr h
    rw [ite_eq_left hb, ite_eq_left h]
  · have hb : ¬ (acc.head? == some p) = true := fun ht => h (beq_iff_eq.mp ht)
    rw [ite_eq_right hb, ite_eq_right h, htrim]

/-- The two folds agree from any accumulator. -/
theorem simplify_fold_eq (acc : List Point) (ps : List Point) :
    List.foldl (fun acc p => if (acc.head? == some p) = true then acc
      else p :: simplifyPoints.trim p acc) acc ps =
    List.foldl (fun acc p => if acc.head? = some p then acc
      else p :: Grid.popCollinear acc p) acc ps := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [simplify_step_eq]
    exact ih _

/-- `simplifyPoints` is `Grid.simplify`: the same dedup/collinear-merge fold. -/
theorem simplifyPoints_eq_simplify (ps : List Point) :
    simplifyPoints ps = Grid.simplify ps := by
  unfold simplifyPoints Grid.simplify
  rw [simplify_fold_eq]

/-- A chain supplies every consecutive pair. -/
theorem chain_mem_pairs {R : Point → Point → Prop} {l : List Point}
    (h : Grid.Chain R l) : ∀ (a b : Point), (a, b) ∈ l.zip l.tail → R a b := by
  induction l with
  | nil =>
    intro a b hmem
    have hz : (([] : List Point).zip ([] : List Point).tail) = [] := rfl
    rw [hz] at hmem
    exact (List.not_mem_nil hmem).elim
  | cons p rest ih =>
    intro a b hmem
    cases rest with
    | nil =>
      have hz : (([p]).zip ([p]).tail) = [] := rfl
      rw [hz] at hmem
      exact (List.not_mem_nil hmem).elim
    | cons q tail =>
      have heq : ((p :: q :: tail).zip (p :: q :: tail).tail) =
          (p, q) :: ((q :: tail).zip (q :: tail).tail) := by simp
      rw [heq, List.mem_cons] at hmem
      rcases hmem with hxy | hmem
      · simp only [Prod.mk.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        exact h.1
      · exact ih h.2 a b hmem

/-- The search's initial node is usable: its path is the singleton start
vertex, whose head matches its state. -/
theorem searchNodeOk_singleton (g : RouteGrid) (start move : Nat) (hm : move < 4) :
    SearchNodeOk g start ⟨start * 4 + move, 0, [start]⟩ := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · show ([start] : List Nat).head? = some ((start * 4 + move) / 4)
    have hdiv : (start * 4 + move) / 4 = start := by omega
    rw [hdiv]
    rfl
  · intro a b hmem
    have hz : (([start] : List Nat).zip ([start]).tail) = [] := rfl
    rw [hz] at hmem
    exact (List.not_mem_nil hmem).elim

/-- `routeEnds` builds start moves `2` or `3`: the initial search state is a
valid directional state. -/
theorem routeEnds_startMove_lt (axis : Axis) (sp : Spacing) (pin : Pin)
    (fromBox toBox : Box) (original : List Point) (ends : RouteEnds)
    (h : routeEnds axis sp pin fromBox toBox original = .ok ends) :
    ends.startMove < 4 := by
  have h0 := h
  unfold routeEnds at h
  obtain ⟨source, hs, hrest⟩ := bindOk_inv h
  dsimp only at hrest
  obtain ⟨target, ht, hrest2⟩ := bindOk_inv hrest
  have e := routeEnds_eq axis sp pin fromBox toBox original source target hs ht
  rw [e] at h0
  simp only [Except.ok.injEq] at h0
  subst h0
  show (if outward axis fromBox.rect (axis.grid source).rank < 0 then 3 else 2) < 4
  split <;> decide

/-- A successful `mapM` with pointwise values is the mapped list. -/
theorem mapM_map_eq (f : Nat → Except LayoutError Point) (k : Nat → Point)
    (l : List Nat) (middle : List Point)
    (hf : ∀ v ∈ l, f v = .ok (k v))
    (h : l.mapM f = .ok middle) : middle = l.map k := by
  induction l generalizing middle with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons v vs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y, hfy, hrest⟩ := bindOk_inv h
    obtain ⟨tl, htl, hpure⟩ := bindOk_inv hrest
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    have hfv : f v = .ok (k v) := hf v List.mem_cons_self
    rw [hfv] at hfy
    have hy : k v = y := Except.ok.inj hfy
    subst hy
    have hvs : ∀ v ∈ vs, f v = .ok (k v) := fun v hv => hf v (List.mem_cons_of_mem _ hv)
    rw [ih _ hvs htl]
    rfl

/-- Alignment is symmetric. -/
theorem aligned_symm {p q : Point} (h : Grid.Aligned p q) : Grid.Aligned q p := by
  unfold Grid.Aligned at h ⊢
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- A neighbour-chained vertex path maps (reversed) to an aligned point
chain: each grid step shares a coordinate (`neighbour_step_aligned`), hence
each mapped step shares an axis coordinate (`atAligned_holds`), and
reversal keeps the symmetric relation. -/
theorem chain_middle (g : RouteGrid) (axis : Axis) (l : List Nat)
    (hchain : NeighbourChain g l) :
    Grid.Chain Grid.Aligned ((l.reverse).map fun v => axis.at (g.point v)) := by
  induction l with
  | nil => trivial
  | cons v rest ih =>
    cases rest with
    | nil => trivial
    | cons w rest' =>
      have heq : ((v :: w :: rest').zip (v :: w :: rest').tail) =
          (v, w) :: ((w :: rest').zip (w :: rest').tail) := by simp
      have hchain' : NeighbourChain g (w :: rest') := by
        intro a b hmem
        apply hchain
        rw [heq]
        exact List.mem_cons_of_mem _ hmem
      have hfirst : (v, w) ∈ ((v :: w :: rest').zip (v :: w :: rest').tail) := by
        rw [heq]
        exact List.mem_cons_self
      have hstep := hchain v w hfirst
      have halign : Grid.Aligned (axis.at (g.point w)) (axis.at (g.point v)) :=
        aligned_symm (atAligned_holds axis (g.point v) (g.point w) hstep)
      have hrev : (((v :: w :: rest').reverse).map fun v => axis.at (g.point v)) =
          (((w :: rest').reverse).map fun v => axis.at (g.point v)) ++
            [(axis.at (g.point v))] := by simp
      rw [hrev]
      refine Grid.chain_snoc (ih hchain') ?_ halign
      simp

/-- Attaching aligned source and target stubs around an aligned middle
keeps the chain. -/
theorem raw_chain (source target : Point)
    (middle : List Point) (m0 : Point) (ms : List Point)
    (hm : middle = m0 :: ms)
    (hsrc : Grid.Aligned source m0)
    (hmid : Grid.Chain Grid.Aligned middle)
    (htgt : ∀ mlast, middle.getLast? = some mlast → Grid.Aligned mlast target) :
    Grid.Chain Grid.Aligned ([source] ++ middle ++ [target]) := by
  rw [hm]
  have happ : ([source] ++ (m0 :: ms) ++ [target]) = source :: m0 :: (ms ++ [target]) := rfl
  rw [happ]
  refine ⟨hsrc, ?_⟩
  have hmid' : Grid.Chain Grid.Aligned (m0 :: ms) := by rwa [← hm]
  have heq2 : ((m0 :: ms) ++ [target]) = m0 :: (ms ++ [target]) := rfl
  rw [← heq2]
  have hne : middle ≠ [] := by rw [hm]; simp
  have hlast : middle.getLast? = some (middle.getLast hne) :=
    List.getLast?_eq_some_getLast hne
  exact Grid.chain_snoc hmid' (by rwa [← hm]) (htgt _ hlast)

/-- A successful `findRoute` also returns the search node and the unsimplified
clearance witness: the search really found `node`, and `routePolyline` plus
`clearPolyline` approved its path. -/
theorem findRoute_ok_node (axis : Axis) (ends : RouteEnds) (obs : List Obstacle)
    (bend : Int) (inflates : List Int) (points : List Point)
    (h : findRoute axis ends obs bend inflates = .ok points) :
    ∃ inflate ∈ inflates, ∃ g : RouteGrid,
      g = routeGrid obs inflate ends.entry ends.exit ∧
      g.obstacles = obs ∧
      ∃ node : SearchNode,
        searchGrid g (g.vertex ends.exit) ends.endMove bend
          (List.range (g.cross.size * g.rank.size * 4))
          ⟨[⟨(g.vertex ends.entry) * 4 + ends.startMove, 0, [g.vertex ends.entry]⟩], none⟩ =
          some node ∧
        routePolyline axis g ends node.path = .ok points ∧
        clearPolyline g axis points = true := by
  induction inflates with
  | nil =>
    rw [findRoute.eq_1] at h
    cases h
  | cons inflate rest ih =>
    rw [findRoute.eq_2] at h
    cases hsg : searchGrid (routeGrid obs inflate ends.entry ends.exit)
        ((routeGrid obs inflate ends.entry ends.exit).vertex ends.exit)
        ends.endMove bend
        (List.range ((routeGrid obs inflate ends.entry ends.exit).cross.size *
          (routeGrid obs inflate ends.entry ends.exit).rank.size * 4))
        { queue :=
            [{ state := (routeGrid obs inflate ends.entry ends.exit).vertex ends.entry * 4 +
                ends.startMove, cost := 0,
                path := [(routeGrid obs inflate ends.entry ends.exit).vertex ends.entry] }],
          best := none } with
    | none =>
      simp only [hsg] at h
      obtain ⟨inf, hmem, g, hg, hobs, node, hnode, hpoly, hclear⟩ := ih h
      exact ⟨inf, List.mem_cons_of_mem _ hmem, g, hg, hobs, node, hnode, hpoly, hclear⟩
    | some node =>
      simp only [hsg] at h
      cases hpoly : routePolyline axis
          (routeGrid obs inflate ends.entry ends.exit) ends node.path with
      | error e =>
        simp only [hpoly, Bind.bind, Except.bind] at h
        cases h
      | ok mid =>
        simp only [hpoly, Bind.bind, Except.bind] at h
        split at h
        · obtain rfl := Except.ok.inj h
          exact ⟨inflate, List.mem_cons_self,
            routeGrid obs inflate ends.entry ends.exit, rfl, rfl,
            node, hsg, hpoly, by assumption⟩
        · obtain ⟨inf, hmem, g, hg, hobs, node', hnode, hpoly', hclear⟩ := ih h
          exact ⟨inf, List.mem_cons_of_mem _ hmem, g, hg, hobs, node', hnode, hpoly', hclear⟩
/-- Every `findRoute` polyline from `routeEnds` ends is pairwise aligned:
the search node is usable (`searchGrid_ok` over the singleton start queue),
so its reversed path maps through the grid to an aligned middle
(`chain_middle`); the vertex roundtrips pin the middle ends to the route
entries, and `routeEndsAligned_holds` aligns the source/target stubs; the
raw chain survives `simplifyPoints` (`simplifyPoints_eq_simplify` plus
`Grid.simplify_aligned`). No blocked-set premise is needed beyond the
proved `obstacle_cover`: `rerouteBands` keeps every exclusive box except
the two endpoints, a superset of the C6-relevant boxes. -/
theorem findRoute_orthogonal (axis : Axis) (sp : Spacing) (pin : Pin)
    (fromBox toBox : Box) (original : List Point) (ends : RouteEnds)
    (hends : routeEnds axis sp pin fromBox toBox original = .ok ends)
    (obs : List Obstacle) (bend : Int) (points : List Point)
    (hfind : findRoute axis ends obs bend [sp.slot, 0] = .ok points) :
    ∀ a b : Point, (a, b) ∈ points.zip points.tail → a.x = b.x ∨ a.y = b.y := by
  obtain ⟨inflate, -, g, hg, hobs, node, hnode, hpoly, hclear⟩ :=
    findRoute_ok_node axis ends obs bend [sp.slot, 0] points hfind
  have hstart : ends.startMove < 4 :=
    routeEnds_startMove_lt axis sp pin fromBox toBox original ends hends
  have hq : ∀ n ∈ ([⟨(g.vertex ends.entry) * 4 + ends.startMove, 0,
      [g.vertex ends.entry]⟩] : List SearchNode),
      SearchNodeOk g (g.vertex ends.entry) n := by
    intro n hn
    rw [List.mem_singleton] at hn
    subst hn
    exact searchNodeOk_singleton g (g.vertex ends.entry) ends.startMove hstart
  have hb : ∀ b, (none : Option SearchNode) = some b →
      SearchNodeOk g (g.vertex ends.entry) b ∧ b.state / 4 = g.vertex ends.exit := by
    intro b h
    cases h
  have hok := searchGrid_ok g (g.vertex ends.exit) ends.endMove bend
    (g.vertex ends.entry) _ _ hq hb node hnode
  obtain ⟨hne, hlast, hhead, hchain⟩ := hok.1
  have haim := hok.2
  have hps : g.point (g.vertex ends.entry) = ends.entry := by
    have h := vertex_point_entry obs inflate ends.entry ends.exit
    rwa [← hg] at h
  have hpt : g.point (g.vertex ends.exit) = ends.exit := by
    have h := vertex_point_exit obs inflate ends.entry ends.exit
    rwa [← hg] at h
  have hal := routeEndsAligned_holds axis sp pin fromBox toBox original ends hends
  obtain ⟨hsrcA, htgtA⟩ := hal
  rw [routePolyline.eq_def] at hpoly
  obtain ⟨middle, hmap, hrest⟩ := bindOk_inv hpoly
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrest
  subst hrest
  have hfk : ∀ v ∈ node.path.reverse, (Measure.checkedI32 (g.point v).cross >>= fun c =>
      Measure.checkedI32 (g.point v).rank >>= fun r =>
      pure (axis.at (⟨c, r⟩ : GridPoint))) = .ok (axis.at (g.point v)) := by
    intro v hv
    obtain ⟨y, hfy⟩ := mapM_mem_ok _ _ _ hmap v hv
    have hfy' : (Measure.checkedI32 (g.point v).cross >>= fun c =>
        Measure.checkedI32 (g.point v).rank >>= fun r =>
        pure (axis.at (⟨c, r⟩ : GridPoint))) = .ok y := hfy
    obtain ⟨c, hc, hrest2⟩ := bindOk_inv hfy'
    obtain ⟨r', hr, hpure⟩ := bindOk_inv hrest2
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    have hcc : c = (g.point v).cross := checkedI32_ok hc
    have hrr : r' = (g.point v).rank := checkedI32_ok hr
    have hgp : ((⟨c, r'⟩ : GridPoint)) = g.point v := by rw [hcc, hrr]
    subst hpure
    rw [hgp] at hfy'
    exact hfy'
  have hmid_eq : middle = node.path.reverse.map (fun v => axis.at (g.point v)) :=
    mapM_map_eq _ _ _ _ hfk hmap
  have hmid_chain : Grid.Chain Grid.Aligned middle := by
    rw [hmid_eq]
    exact chain_middle g axis node.path hchain
  have hrev_head : (node.path.reverse).head? = some (g.vertex ends.entry) := by
    rw [List.head?_reverse]
    exact hlast
  have hmid_head : middle.head? = some (axis.at ends.entry) := by
    rw [hmid_eq, List.head?_map, hrev_head, Option.map_some, hps]
  have hrev_last : (node.path.reverse).getLast? = some (g.vertex ends.exit) := by
    rw [List.getLast?_reverse, hhead, haim]
  have hmid_last : middle.getLast? = some (axis.at ends.exit) := by
    rw [hmid_eq, List.getLast?_map, hrev_last, Option.map_some, hpt]
  obtain ⟨p0, ps, hpath⟩ := List.exists_cons_of_ne_nil hne
  have hne_rev : node.path.reverse ≠ [] := by rw [hpath]; simp
  have hne_mid : middle ≠ [] := by rw [hmid_eq]; simpa using hne_rev
  obtain ⟨m0, ms, hm⟩ := List.exists_cons_of_ne_nil hne_mid
  have hm0 : m0 = axis.at ends.entry := by
    have e2 : (m0 :: ms).head? = some (axis.at ends.entry) := by rwa [← hm]
    simp only [List.head?_cons] at e2
    exact Option.some.inj e2
  have hsrc : Grid.Aligned ends.source m0 := by
    rw [hm0]
    unfold Grid.Aligned
    exact hsrcA
  have htgt : ∀ mlast, middle.getLast? = some mlast → Grid.Aligned mlast ends.target := by
    intro mlast hml
    rw [hmid_last] at hml
    have hme : mlast = axis.at ends.exit := Option.some.inj hml.symm
    subst hme
    unfold Grid.Aligned
    exact htgtA
  have hraw : Grid.Chain Grid.Aligned ([ends.source] ++ middle ++ [ends.target]) :=
    raw_chain ends.source ends.target middle m0 ms hm hsrc hmid_chain htgt
  have hchain_pts : Grid.Chain Grid.Aligned (simplifyPoints ([ends.source] ++ middle ++ [ends.target])) := by
    rw [simplifyPoints_eq_simplify]
    exact Grid.simplify_aligned hraw
  intro a b hmem
  have hmem' := chain_mem_pairs hchain_pts a b hmem
  unfold Grid.Aligned at hmem'
  exact hmem'

/-- The stage-(b) residual holds: every `findRoute` polyline from `routeEnds`
ends clears every obstacle. Orthogonality (`findRoute_orthogonal`) feeds the
proved orthogonal-clearance theorem; the blocked set needs no extra premise
(`obstacle_cover` already shows the filter keeps a superset of C6 boxes). -/
theorem pinBandsFindRouteClear_holds : pinBandsFindRouteClear := by
  intro axis sp pin fromBox toBox original ends hends obs bend points hfind o hos r hob
  exact pinBandsFindRouteClear_of_routeEnds axis sp pin fromBox toBox original ends hends
    obs bend points hfind
    (findRoute_orthogonal axis sp pin fromBox toBox original ends hends obs bend points hfind)
    o hos r hob


end LaneBands

end Layered
end Elegant

namespace Elegant
namespace Layered
namespace LaneBands

/-- Pinning keeps clause C6 (route clearance) of the validator, by real
stages: rigid same-band pairs via translation, cross-band bands via the
`applyPin` residual, re-routed paths via the proved `findRoute` residual
(`pinBandsFindRouteClear_holds`), and the tail phases by frame equalities
plus uniform-shift transport. -/
theorem pinBands_c6 {m : Model} {base : FamilyResult} {pinned : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned)
    (hbase : HardConstraints base.scene.layoutDump)
    (happly : pinBandsApplyPinKeptClear) :
    Validator.C6 pinned.layoutDump := by
  have _ := hfam
  cases hlanes : lanesOf m.boxes with
  | nil =>
    rw [pinBands_no_lanes hlanes] at hpin
    have heq : base.scene = pinned := Except.ok.inj hpin
    subst heq
    exact hbase.2.2.2.2.2.1
  | cons _ _ =>
    have hlanes' : lanesOf m.boxes ≠ [] := by
      rw [hlanes]
      intro h
      cases h
    obtain ⟨sp, axis, bands, s1, s2, s3, strip, s4, hsp, haxis, hbands, happ, hroute, horig, hstrip, hstripEq, hgrow⟩ :=
      pinBands_spec (boxes := m.boxes) (o := m.options)
        (s := base.scene) (r := pinned) hlanes' hpin
    have hbaseC6 : Validator.C6 base.scene.layoutDump := hbase.2.2.2.2.2.1
    have hfr := rerouteBands_frame hroute
    have hfr1 : s2.layoutDump.boxes = s1.layoutDump.boxes := hfr.1
    have hC6s2 : Validator.C6 s2.layoutDump := by
      intro r' hr' b' hb' hex hscope
      have hb's1 : b' ∈ s1.boxes := by
        have hbeq : s2.layoutDump.boxes = s1.layoutDump.boxes := hfr.1
        rw [hbeq] at hb'
        exact hb'
      obtain ⟨r, hrmem, old, holdmem, hpair, _hidr, hfromr, htor, hcase⟩ :=
        rerouteBands_mem axis sp (LayoutConst.rank_gap.get m.options.profile)
        bands (buildPin axis bands base.scene) base.scene.routes s1 s2 hroute r' hr'
      have hscope1 : b'.id ∉ s1.layoutDump.routeScope r := by
        have heq : s2.layoutDump.routeScope r' = s1.layoutDump.routeScope r := by
          simp only [LayoutDump.routeScope, hfromr, htor]
          rw [ancestors_boxes_eq hfr1, ancestors_boxes_eq hfr1]
        rw [heq] at hscope
        exact hscope
      rcases hcase with ⟨hpts, hreason⟩ | ⟨fi, ti, fb, tb, ends, obs, pts, hfi, hti, hfb, htb, hends, hobs, hfind_pt, hpts⟩
      · -- Kept route: the `applyPin` residual.
        have hclear := happly axis bands base.scene s1 m.boxes sp hbands happ hbaseC6
          r b' old hrmem holdmem hpair hb's1 hex hscope1 hreason
        rw [hpts]
        exact hclear
      · -- Fresh route: proved `findRoute` soundness plus obstacle coverage.
        have hmem : obstacleOf axis b'.rect ∈ obs := by
          rw [hobs]
          exact List.mem_append.mpr (Or.inl (obstacle_cover s1 axis r b' hb's1 hex hscope1))
        have hclear := pinBandsFindRouteClear_holds axis sp (buildPin axis bands base.scene) fb tb
          old.points ends hends obs (LayoutConst.rank_gap.get m.options.profile)
          pts hfind_pt (obstacleOf axis b'.rect) hmem b'.rect rfl
        rw [hpts]
        exact hclear
    have hC6s3 : Validator.C6 s3.layoutDump :=
      restoreOrigin_C6 axis s2 s3 horig hC6s2
    have hb43 : s4.layoutDump.boxes = s3.layoutDump.boxes := relocateLabels_boxes hstripEq
    have hr43 : s4.layoutDump.routes = s3.layoutDump.routes := relocateLabels_routes hstripEq
    have hC6s4 : Validator.C6 s4.layoutDump :=
      C6_of_boxes_routes_eq hb43 hr43 hC6s3
    have hgrowF := growCanvas_frame hgrow
    have hbP : pinned.layoutDump.boxes = s4.layoutDump.boxes := hgrowF.1
    have hrP : pinned.layoutDump.routes = s4.layoutDump.routes := hgrowF.2.1
    exact C6_of_boxes_routes_eq hbP hrP hC6s4

end LaneBands
end Layered
end Elegant

namespace Elegant
namespace Kinds
namespace Swimlane

/-- The swimlane adapter keeps clause C6 after lane-band pinning, given the
`applyPin` stage residual; the `findRoute` stage is proved. -/
theorem swimlane_pinBands_c6 {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene}
    (hfam : Layered.layoutFamily (input m) m.options = .ok base)
    (hpin : Layered.LaneBands.pinBands m.boxes m.options base.scene = .ok pinned)
    (hbase : HardConstraints base.scene.layoutDump)
    (happly : Layered.LaneBands.pinBandsApplyPinKeptClear) :
    Validator.C6 pinned.layoutDump :=
  Layered.LaneBands.pinBands_c6 hfam hpin hbase happly

end Swimlane
end Kinds
end Elegant
