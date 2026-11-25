import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.GridRoute
import Elegant.GridSimplify

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-! Clause transport of `pinBands` for C4 (route orthogonality) and C5
(route endpoints on their endpoint-box boundaries). C4 holds outright:
`applyPin` moves each route by a `Move` whose offset depends only on the
point's own cross coordinate, so orthogonal pairs stay orthogonal, and
`rerouteBands` either keeps those points or replaces them by a grid
polyline whose consecutive points share one axis. C5 holds under
`pinBandsPortsResidual`: no route endpoint names a lane band (the band
stretch would move the frame away from the port), and whenever two
endpoint bands differ every route has at least two points and both
endpoints banded, so `rerouteBands` re-routes it and `routeEnds` puts
the ends on the shifted endpoint boxes. -/

/-- Binding step of an `Except` computation. -/
private theorem bindOk {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- One point moved by `Move.point` keeps the other axis and gains the
checked cross value. -/
theorem movePoint_ok {m : Move} {axis : Axis} {p p' : Point}
    (h : m.point axis p = .ok p') :
    ∃ w, m.apply (axis.point p) = .ok w ∧
      p' = axis.withPoint p w ∧
      axis.other.point p' = axis.other.point p := by
  unfold Move.point at h
  obtain ⟨w, hw, hrfl⟩ := bindOk h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  refine ⟨w, hw, rfl, ?_⟩
  cases axis <;> simp [Axis.withPoint, Axis.other, Axis.point]

/-- An orthogonal pair stays orthogonal under `Move.point`: equal other
coordinates are untouched, and equal cross coordinates get equal shifts. -/
theorem movePair_forward {m : Move} {axis : Axis} {p q p' q' : Point}
    (hp : m.point axis p = .ok p') (hq : m.point axis q = .ok q')
    (h : axis.point p = axis.point q ∨ axis.other.point p = axis.other.point q) :
    axis.point p' = axis.point q' ∨ axis.other.point p' = axis.other.point q' := by
  obtain ⟨wp, hwpp, hpe, hpo⟩ := movePoint_ok hp
  obtain ⟨wq, hwqp, hqe, hqo⟩ := movePoint_ok hq
  have hcrossP : axis.point p' = wp := by cases axis <;> simp [Axis.point, Axis.withPoint, hpe]
  have hcrossQ : axis.point q' = wq := by cases axis <;> simp [Axis.point, Axis.withPoint, hqe]
  rcases h with h | h
  · left
    have hEq : m.apply (axis.point p) = m.apply (axis.point q) := by rw [h]
    rw [hwpp, hwqp] at hEq
    have hw : wp = wq := by simpa using hEq
    rw [hcrossP, hcrossQ, hw]
  · right
    rw [hpo, hqo]
    exact h

/-- `mapM` of `Move.point` preserves orthogonality: an orthogonal input
polyline maps to an orthogonal output polyline. -/
theorem isOrthogonal_mapM_move {m : Move} {axis : Axis} :
    ∀ (ps : List Point) (qs : List Point),
      ps.mapM (m.point axis) = .ok qs → Polyline.isOrthogonal ps = true →
      Polyline.isOrthogonal qs = true := by
  intro ps
  induction ps with
  | nil =>
    intro qs h ho
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [Polyline.isOrthogonal] at ho ⊢
  | cons p rest ih =>
    intro qs h ho
    rw [List.mapM_cons] at h
    obtain ⟨p', hp', h⟩ := bindOk h
    obtain ⟨rest', hrest, hrfl⟩ := bindOk h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    have hqs : qs = p' :: rest' := hrfl.symm
    subst hqs
    cases rest with
    | nil =>
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hrest
      subst hrest
      rfl
    | cons q rest'' =>
      have htail_in : Polyline.isOrthogonal (q :: rest'') = true := by
        have h2 := ho
        rw [Polyline.isOrthogonal_cons, Bool.and_eq_true] at h2
        exact h2.2
      have hD : (decide (p.x = q.x) || decide (p.y = q.y)) = true := by
        have h2 := ho
        rw [Polyline.isOrthogonal_cons, Bool.and_eq_true] at h2
        exact h2.1
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hD
      have htail0 := ih rest' hrest htail_in
      rw [List.mapM_cons] at hrest
      obtain ⟨q', hq', hrest2⟩ := bindOk hrest
      obtain ⟨rest3, hrest3, hrfl2⟩ := bindOk hrest2
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl2
      have hqs2 : rest' = q' :: rest3 := hrfl2.symm
      subst hqs2
      have hpair : axis.point p = axis.point q ∨ axis.other.point p = axis.other.point q := by
        cases axis
        · exact hD
        · exact Iff.mp or_comm hD
      have hD' := movePair_forward hp' hq' hpair
      have hD'b : (decide (p'.x = q'.x) || decide (p'.y = q'.y)) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        cases axis
        · exact hD'
        · exact Iff.mp or_comm hD'
      rw [Polyline.isOrthogonal_cons, Bool.and_eq_true]
      exact ⟨hD'b, htail0⟩


/-- A cross-axis shift of a point and a rectangle start by the same
delta preserves `onBoundary`. -/
theorem onBoundary_crossShift {axis : Axis} {p : Point} {r : Rect} {d : Int} :
    Validator.onBoundary (axis.withPoint p (axis.point p + d))
      (axis.withStart r (axis.start r + d)) ↔ Validator.onBoundary p r := by
  cases axis <;>
    simp only [Validator.onBoundary, Axis.withPoint, Axis.withStart, Axis.point,
      Axis.start] <;>
    omega


/-! ## Sorted coordinate infrastructure

`sortedCoordinates` merge-sorts and deduplicates its input. The grid search
needs the sorted list's membership, nodup, and the index of an element as
the length of the `< x` prefix. -/

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

theorem sortedCoordinates_nodup (xs : List Int) :
    (sortedCoordinates xs).toList.Nodup := by
  unfold sortedCoordinates
  rw [List.toList_toArray]
  exact nodup_eraseDups _

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


/-! ## Bridge to `Grid.simplify`

`LaneBands.simplifyPoints` is the same fold as `Elegant.Grid.simplify` with an
inline `trim` recursion. `GridSimplify` proves chain preservation, endpoint
preservation, and orthogonality for `Grid.simplify`; this section transports
them to `simplifyPoints`. -/

theorem trim_eq_popCollinear : ∀ (p : Point) (acc : List Point),
    simplifyPoints.trim p acc = Elegant.Grid.popCollinear acc p := by
  intro p acc
  induction acc with
  | nil => rfl
  | cons b rest ih =>
    cases rest with
    | nil => rfl
    | cons a rest' =>
      rw [simplifyPoints.trim.eq_1, Elegant.Grid.popCollinear.eq_1]
      by_cases h : Elegant.Grid.collinear a b p = true
      · have h2 : ((a.x == b.x && b.x == p.x) ||
            (a.y == b.y && b.y == p.y)) = true := h
        rw [ite_eq_left h, ite_eq_left h2]
        exact ih
      · have h2 : ¬(((a.x == b.x && b.x == p.x) ||
            (a.y == b.y && b.y == p.y)) = true) := h
        rw [ite_eq_right h, ite_eq_right h2]

theorem simplifyStep_eq (acc : List Point) (p : Point) :
    (if (acc.head? == some p) = true then acc
      else p :: simplifyPoints.trim p acc) =
    (if acc.head? = some p then acc
      else p :: Elegant.Grid.popCollinear acc p) := by
  by_cases h : acc.head? = some p
  · have hb : (acc.head? == some p) = true := beq_iff_eq.mpr h
    rw [ite_eq_left hb, ite_eq_left h]
  · have hb : ¬((acc.head? == some p) = true) := fun hh => h (beq_iff_eq.mp hh)
    rw [ite_eq_right hb, ite_eq_right h, trim_eq_popCollinear]

theorem foldl_simplify_bridge : ∀ (acc ps : List Point),
    (ps.foldl (fun a p => if (a.head? == some p) = true then a
        else p :: simplifyPoints.trim p a) acc).reverse =
    (ps.foldl (fun a p => if a.head? = some p then a
        else p :: Elegant.Grid.popCollinear a p) acc).reverse := by
  intro acc ps
  induction ps generalizing acc with
  | nil => rfl
  | cons q ps ih =>
    simp only [List.foldl_cons]
    rw [simplifyStep_eq acc q]
    exact ih _


theorem simplifyPoints_eq_grid_simplify (ps : List Point) :
    simplifyPoints ps = Elegant.Grid.simplify ps := by
  unfold simplifyPoints Elegant.Grid.simplify
  exact foldl_simplify_bridge [] ps

theorem simplifyPoints_endpoints (ps : List Point) :
    (simplifyPoints ps).head? = ps.head? ∧ (simplifyPoints ps).getLast? = ps.getLast? := by
  rw [simplifyPoints_eq_grid_simplify]
  exact Elegant.Grid.simplify_endpoints ps

theorem simplifyPoints_orthogonal {ps : List Point}
    (h : Elegant.Grid.Chain Elegant.Grid.Aligned ps) :
    Polyline.isOrthogonal (simplifyPoints ps) = true := by
  rw [simplifyPoints_eq_grid_simplify]
  exact Elegant.Grid.Chain.orthogonal (Elegant.Grid.simplify_aligned h)


/-! ## Per-element specifications for the `Except` `mapM` passes

`applyPin` and `rerouteBands` rewrite route lists with `List.mapM`. The
clauses are pointwise, so we need the elementwise reading of a successful
`mapM`: same length, and each output element is the `ok` value of the
corresponding input element's function. -/

theorem mapM_except_spec {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (out : List β),
      l.mapM f = .ok out →
      out.length = l.length ∧
        ∀ i (_hi : i < l.length) (_hj : i < out.length),
          ∃ a b, l[i]? = some a ∧ out[i]? = some b ∧ f a = .ok b := by
  intro l
  induction l with
  | nil =>
    intro out h
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a l ih =>
    intro out h
    rw [List.mapM_cons] at h
    cases hf : f a with
    | error e => simp [hf] at h
    | ok x =>
      rw [hf] at h
      cases hm : l.mapM f with
      | error e => simp [hm] at h
      | ok xs =>
        rw [hm] at h
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        obtain ⟨hlen, hall⟩ := ih xs hm
        refine ⟨by simp [hlen], ?_⟩
        intro i hi hj
        cases i with
        | zero =>
          refine ⟨a, x, ?_, ?_, hf⟩
          · rw [List.getElem?_cons_zero]
          · rw [List.getElem?_cons_zero]
        | succ i' =>
          have hi' : i' < l.length := by
            simp at hi; omega
          have hj' : i' < xs.length := by
            simp [hlen] at hj; omega
          obtain ⟨a', b', ha', hb', hab'⟩ := hall i' hi' hj'
          refine ⟨a', b', ?_, ?_, hab'⟩
          · rw [List.getElem?_cons_succ, ha']
          · rw [List.getElem?_cons_succ, hb']

theorem getElem?_zip_iff {α β : Type} {l₁ : List α} {l₂ : List β} {i : Nat}
    {p : α × β} :
    (l₁.zip l₂)[i]? = some p ↔ l₁[i]? = some p.1 ∧ l₂[i]? = some p.2 := by
  rw [List.zip_eq_zipWith, List.getElem?_zipWith]
  cases h1 : l₁[i]? <;> cases h2 : l₂[i]? <;> simp [Prod.ext_iff]

theorem getElem?_mapM_of_spec {α β ε : Type} {f : α → Except ε β}
    {l : List α} {out : List β} (h : l.mapM f = .ok out)
    {i : Nat} (hi : i < l.length) (hj : i < out.length) :
    ∃ a b, l[i]? = some a ∧ out[i]? = some b ∧ f a = .ok b :=
  (mapM_except_spec f l out h).2 i hi hj


/-! ## Residuals for the grid-search rewrite

`rerouteBands` rewrites cross-band routes through `findRoute` on a
coordinate grid. The orthogonality of the produced polyline and the
attachment of its endpoints are the search's correctness obligations; they
are stated here as named residuals pinned to the executed run, exactly as
the sibling clause files do for C1/C2/C3/C8. -/

/-- A route of the routed scene is a grid rewrite of `old` when its endpoints
lie in different bands, the original had at least two points, and both
endpoint boxes exist in the pinned scene — precisely the branch of
`rerouteBands` that calls `findRoute`. -/
def Rerouted (bands : List Band) (s : Scene) (rt old : Route) : Prop :=
  ∃ fi ti : Nat,
    bands.findIdx? (fun b => b.id == rt.fromId || b.members.contains rt.fromId) = some fi ∧
    bands.findIdx? (fun b => b.id == rt.toId || b.members.contains rt.toId) = some ti ∧
    fi ≠ ti ∧ 1 < old.points.length ∧
    (s.boxes.find? (·.id == rt.fromId)).isSome = true ∧
    (s.boxes.find? (·.id == rt.toId)).isSome = true

/-- A kept route whose endpoint attachment is not transported rigidly: its
`RouteDelta` does not match the canonical `buildPin` entry for `old`
(degenerate or duplicate route ids), an endpoint box is a band frame whose
rect `replaceFrame` rewrites, or the `.ends` move collapses both endpoint
deltas onto one cross coordinate. -/
def PinDeltaBad (axis : Axis) (bands : List Band) (pin : Pin)
    (rt old : Route) : Prop :=
  match pin.route rt.id with
  | none => old.points ≠ []
  | some d =>
    d.fromDelta ≠ bandShift bands old.fromId ∨
    d.toDelta ≠ bandShift bands old.toId ∨
    d.first ≠ axis.point (old.points.head?.getD ⟨0, 0⟩) ∨
    d.last ≠ axis.point (old.points.getLast?.getD ⟨0, 0⟩) ∨
    (d.fromDelta ≠ d.toDelta ∧
      (d.first = d.last ∨ old.points.length ≤ 1)) ∨
    bands.any (fun b => b.id == rt.fromId) ∨
    bands.any (fun b => b.id == rt.toId)

/-- Residual for C4: every grid-rewritten route of the routed scene keeps
orthogonal points. -/
def PinC4Grid (bands : List Band) (original : List Route)
    (s routed : Scene) : Prop :=
  ∀ rt ∈ routed.routes, ∀ old ∈ original, Rerouted bands s rt old →
    rt.orthogonal = true → Polyline.isOrthogonal rt.points = true

/-- Residual for C5: every route whose endpoint attachment is not a rigid
move — grid rewrites and the `PinDeltaBad` cases — keeps its endpoint boxes'
boundaries in the routed scene. -/
def PinC5Hard (axis : Axis) (bands : List Band) (pin : Pin)
    (original : List Route) (s routed : Scene) : Prop :=
  ∀ rt ∈ routed.routes, ∀ old ∈ original,
    Rerouted bands s rt old ∨ PinDeltaBad axis bands pin rt old →
    ∃ p q fb tb, rt.points.head? = some p ∧ rt.points.getLast? = some q ∧
      routed.boxes.find? (·.id == rt.fromId) = some fb ∧
      routed.boxes.find? (·.id == rt.toId) = some tb ∧
      Validator.onBoundary p fb.rect ∧ Validator.onBoundary q tb.rect


/-! ## Route-list specifications of the pinning phases

Each phase either leaves `routes` untouched or rewrites it elementwise.
These lemmas give the elementwise reading used by the clause transports. -/

theorem replaceFrame_routes {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') : s'.routes = s.routes := by
  unfold replaceFrame at h
  split at h
  · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  · cases hg : Measure.checkedI32 band.start with
    | error e => simp [hg, Bind.bind, Except.bind] at h
    | ok start =>
      cases ht : Measure.checkedI32 band.thickness with
      | error e => simp [hg, ht, Bind.bind, Except.bind] at h
      | ok thickness =>
        simp only [hg, ht, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        rfl

theorem foldlM_replaceFrame_routes {axis : Axis} {bands : List Band}
    {scene pinned : Scene}
    (h : bands.foldlM (fun sc band => replaceFrame axis band sc) scene = .ok pinned) :
    pinned.routes = scene.routes := by
  induction bands generalizing scene pinned with
  | nil =>
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons band rest ih =>
    rw [List.foldlM_cons] at h
    cases hb : replaceFrame axis band scene with
    | error e => simp [hb, Bind.bind, Except.bind] at h
    | ok sc =>
      simp only [hb, Bind.bind, Except.bind] at h
      exact (ih h).trans (replaceFrame_routes hb)
/-! ## Clause transport helpers

Every phase either leaves `routes` untouched or rewrites it elementwise;
the clause transports read those specifications pointwise. -/

/-- Residual for C4: a polyline returned by the grid search is orthogonal.
About `findRoute`'s result alone: each grid neighbour step changes one
coordinate, so the returned points are orthogonal. -/
def FindRouteOrtho : Prop :=
  ∀ (axis : Axis) (ends : RouteEnds) (obs : List Obstacle) (bend : Int)
    (inflates : List Int) (pts : List Point),
    findRoute axis ends obs bend inflates = .ok pts →
    Polyline.isOrthogonal pts = true

/-- Residual for C5: a polyline returned by the grid search keeps the
route ends. About `findRoute`'s result alone: the search wraps its path
with the entry `source` and `target` ports. -/
def FindRouteEnds : Prop :=
  ∀ (axis : Axis) (ends : RouteEnds) (obs : List Obstacle) (bend : Int)
    (inflates : List Int) (pts : List Point),
    findRoute axis ends obs bend inflates = .ok pts →
    pts.head? = some ends.source ∧ pts.getLast? = some ends.target

/-! ## Generic `mapM`/`find?` helpers -/

private theorem mapM_ne_nil {α β : Type} (f : α → Except LayoutError β)
    {ps : List α} {qs : List β} (hne : ps ≠ []) (h : ps.mapM f = .ok qs) :
    qs ≠ [] := by
  have hlen := (mapM_except_spec f ps qs h).1
  intro hnil
  subst hnil
  cases ps with
  | nil => exact (hne rfl).elim
  | cons x xs => simp at hlen

private theorem mapM_point_head {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.head? = some p →
        ∃ q, qs.head? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x xs ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := bindOk h
    obtain ⟨rest', hrest, hrfl⟩ := bindOk h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    have hpx : x = p := by simpa using hp
    subst hpx
    exact ⟨x', rfl, hx'⟩

private theorem mapM_point_getLast? {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.getLast? = some p →
        ∃ q, qs.getLast? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x rest ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := bindOk h
    obtain ⟨rest', hrest, hrfl⟩ := bindOk h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    cases rest with
    | nil =>
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hrest
      subst hrest
      have hpx : p = x := by
        have hgl : (x :: []).getLast? = some x := rfl
        rw [hgl] at hp
        exact (Option.some.inj hp).symm
      subst hpx
      exact ⟨x', rfl, hx'⟩
    | cons y ys =>
      obtain ⟨q, hq, hfun⟩ := ih rest' hrest p hp
      refine ⟨q, ?_, hfun⟩
      rw [List.getLast?_cons, hq]
      rfl

private theorem headD_of_head? {α : Type} [Inhabited α] {l : List α} {p d : α}
    (h : l.head? = some p) : l.headD d = p := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    have hx : x = p := by simpa using h
    show x = p
    exact hx

private theorem find?_idx {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a →
      ∃ j : Nat, l[j]? = some a ∧ p a = true ∧
        ∀ k, k < j → ∀ y, l[k]? = some y → p y = false := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons x xs ih =>
    intro a h
    rw [List.find?_cons] at h
    cases hpx : p x with
    | true =>
      simp [hpx] at h
      subst h
      refine ⟨0, rfl, hpx, ?_⟩
      intro k hk _ _
      simp at hk
    | false =>
      simp [hpx] at h
      obtain ⟨j, hjget, hjp, hj4⟩ := ih a h
      refine ⟨j + 1, ?_, hjp, ?_⟩
      · rw [List.getElem?_cons_succ]
        exact hjget
      · intro k hk y hy
        cases k with
        | zero =>
          rw [List.getElem?_cons_zero] at hy
          cases hy
          exact hpx
        | succ k' =>
          rw [List.getElem?_cons_succ] at hy
          exact hj4 k' (by omega) _ hy

private theorem find?_at {α : Type} (p : α → Bool) :
    ∀ (l : List α) (j : Nat) (a : α), l[j]? = some a → p a = true →
      (∀ k, k < j → ∀ y, l[k]? = some y → p y = false) → l.find? p = some a := by
  intro l
  induction l with
  | nil => intro j a hj _ _; simp at hj
  | cons x xs ih =>
    intro j a hj hpj hprev
    rw [List.find?_cons]
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at hj
      obtain rfl : x = a := Option.some.inj hj
      cases hp : p x with
      | true => rfl
      | false => rw [hp] at hpj; cases hpj
    | succ j' =>
      rw [List.getElem?_cons_succ] at hj
      have hpx : p x = false := hprev 0 (by omega) x List.getElem?_cons_zero
      cases hp : p x with
      | true => rw [hp] at hpx; cases hpx
      | false =>
        exact ih j' a hj hpj (fun k hk y hy =>
          hprev (k + 1) (by omega) y (by rwa [List.getElem?_cons_succ]))

private theorem find?_ex {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∃ a, a ∈ l ∧ p a = true) →
      ∃ a, l.find? p = some a := by
  intro l
  induction l with
  | nil => intro ⟨a, ha, _⟩; cases ha
  | cons x xs ih =>
    intro ⟨a, ha, hp⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [List.find?_cons]
      cases hpx : p a with
      | true => exact ⟨a, rfl⟩
      | false => rw [hpx] at hp; cases hp
    · obtain ⟨b, hb⟩ := ih ⟨a, ha', hp⟩
      rw [List.find?_cons]
      cases hpx : p x with
      | true => exact ⟨x, rfl⟩
      | false => exact ⟨b, hb⟩

private theorem nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
    {l : List α} (h : (l.map g).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hnot, htail⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨y, hy', hgx.symm⟩
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨x, hx', hgx⟩
      · exact ih htail hx' hy'

/-! ## `buildPin` lookup lemmas

`boxDelta` searches the flattened `(id, shift)` pair list; `bandShift`
searches the bands directly. Both return the shift of the first band
containing the id, so they agree. -/

private theorem beq_comm' {α : Type} [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = (b == a) := by
  by_cases h : a = b
  · have e1 : (a == b) = true := beq_iff_eq.mpr h
    have e2 : (b == a) = true := beq_iff_eq.mpr h.symm
    rw [e1, e2]
  · have e1 : (a == b) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      exact h (beq_iff_eq.mp hb)
    have e2 : (b == a) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      exact h (beq_iff_eq.mp hb).symm
    rw [e1, e2]

private theorem find?_isSome_contains {l : List String} {a : String} :
    (l.find? (fun x => x == a)).isSome = l.contains a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.find?_cons, List.contains_cons]
    by_cases hx : (x == a) = true
    · have hax : (a == x) = true := by
        have hc := beq_comm' x a
        rw [hc] at hx
        exact hx
      simp [hx, hax]
    · have hx' : (x == a) = false := Bool.eq_false_iff.mpr hx
      have hax : (a == x) = false := by
        have hc := beq_comm' a x
        rw [hc]
        exact hx'
      simp [hx', hax, ih]

private theorem find?_map_id_eq {ms : List String} {s : Int} {id : String} :
    (ms.map fun m => (m, s)).find? (fun e => e.1 == id) =
      (ms.find? fun m => m == id).map fun m => (m, s) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [List.map_cons, List.find?_cons, List.find?_cons, ih]
    by_cases h : (m == id) = true
    · simp [h]
    · have h' : (m == id) = false := Bool.eq_false_iff.mpr h
      simp [h']

private def bandPairs (b : Band) : List (String × Int) :=
  (b.id, b.shift) :: b.members.map fun m => (m, b.shift)

private theorem bandPairs_map_snd (b : Band) (id : String) :
    ((bandPairs b).find? fun e => e.1 == id).map Prod.snd =
      if b.id == id || b.members.contains id then some b.shift else none := by
  unfold bandPairs
  rw [List.find?_cons]
  show ((match b.id == id with
    | true => some (b.id, b.shift)
    | false => (b.members.map fun m => (m, b.shift)).find? fun e => e.1 == id).map
      Prod.snd) = _
  cases hb : (b.id == id) with
  | true => simp
  | false =>
    dsimp only
    rw [find?_map_id_eq (ms := b.members) (s := b.shift) (id := id), Option.map_map]
    have hcomp : (Prod.snd ∘ fun (m : String) => (m, b.shift)) =
        fun (_ : String) => b.shift := by
      funext m; rfl
    rw [hcomp]
    have hcontains : b.members.contains id =
        (b.members.find? fun m => m == id).isSome := (find?_isSome_contains).symm
    cases hX : b.members.find? (fun m => m == id) with
    | none =>
      simp
      intro hmem
      obtain ⟨a, ha⟩ := find?_ex (fun m => m == id) b.members
        ⟨id, hmem, beq_iff_eq.mpr rfl⟩
      rw [hX] at ha
      cases ha
    | some m =>
      simp
      obtain ⟨x, hxm, hxid⟩ := (List.find?_isSome).mp
        ((Option.isSome_iff_exists).mpr ⟨m, hX⟩)
      have hx : x = id := beq_iff_eq.mp hxid
      rwa [hx] at hxm
private theorem flatMapShift_find? :
    ∀ (bands : List Band) (id : String),
      ((bands.flatMap bandPairs).find? fun e => e.1 == id).map Prod.snd =
        (bands.find? fun b => b.id == id || b.members.contains id).map (·.shift) := by
  intro bands
  induction bands with
  | nil => intro id; rfl
  | cons b bs ih =>
    intro id
    rw [List.flatMap_cons, List.find?_append, Option.map_or, bandPairs_map_snd,
      ih id, List.find?_cons]
    cases hb : (b.id == id) with
    | true => simp
    | false =>
      cases hm : b.members.contains id with
      | true => simp
      | false => simp



/-- `boxDelta` agrees with `bandShift`: both return the shift of the first
band containing the id. -/
theorem buildPin_boxDelta {axis : Axis} {bands : List Band} {s : Scene}
    (id : String) :
    (buildPin axis bands s).boxDelta id = bandShift bands id := by
  show (((bands.flatMap bandPairs).find? fun e => e.1 == id).map Prod.snd).getD 0 =
    ((bands.find? fun b => b.id == id || b.members.contains id).map (·.shift)).getD 0
  rw [flatMapShift_find?]

/-- A `RouteDelta` found by `pin.route` for `old.id` is the canonical
`buildPin` entry of `old`, provided route ids are unique. -/
theorem buildPin_route_find {axis : Axis} {bands : List Band} {s : Scene}
    {old : Route} {d : RouteDelta}
    (hnodup : (s.routes.map (·.id)).Nodup) (hold : old ∈ s.routes)
    (h : (buildPin axis bands s).route old.id = some d) :
    d.fromDelta = bandShift bands old.fromId ∧
    d.toDelta = bandShift bands old.toId ∧
    d.first = axis.point (old.points.head?.getD ⟨0, 0⟩) ∧
    d.last = axis.point (old.points.getLast?.getD ⟨0, 0⟩) := by
  unfold Pin.route buildPin at h
  obtain ⟨j, hjget, hpred, -⟩ := find?_idx _ _ _ h
  have hdmem : d ∈ (s.routes.filterMap fun r =>
      match r.points.head?, r.points.getLast? with
      | some first, some last =>
        some ⟨r.id, bandShift bands r.fromId, bandShift bands r.toId,
          axis.point first, axis.point last⟩
      | _, _ => none) :=
    (List.mem_iff_getElem?).mpr ⟨j, hjget⟩
  obtain ⟨old', hold', hf'⟩ := (List.mem_filterMap).mp hdmem
  cases hh : old'.points.head? with
  | none => simp [hh] at hf'
  | some first =>
    cases hl : old'.points.getLast? with
    | none => simp [hh, hl] at hf'
    | some last =>
      rw [hh, hl] at hf'
      dsimp only at hf'
      have hdEq : d = ⟨old'.id, bandShift bands old'.fromId,
          bandShift bands old'.toId, axis.point first, axis.point last⟩ :=
        (Option.some.inj hf').symm
      have hid : d.id = old.id := beq_iff_eq.mp hpred
      have hid' : d.id = old'.id := congrArg RouteDelta.id hdEq
      have heq : old' = old := nodup_map_inj (·.id) hnodup hold' hold
        (hid'.symm.trans hid)
      rw [heq] at hh hl hdEq
      have hhead : old.points.head? = some first := hh
      have hlast : old.points.getLast? = some last := hl
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact congrArg RouteDelta.fromDelta hdEq
      · exact congrArg RouteDelta.toDelta hdEq
      · rw [hhead]
        exact congrArg RouteDelta.first hdEq
      · rw [hlast]
        exact congrArg RouteDelta.last hdEq

end LaneBands
end Layered
end Elegant
