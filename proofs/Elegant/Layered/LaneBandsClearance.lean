import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Kinds.Swimlane
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-!
# Lane-band pinning keeps route clearance (C6).

`pinBands` runs five phases (`pinBands_spec`): `applyPin`, `rerouteBands`,
`restoreOrigin`, `relocateLabels`, `growCanvas`. Clause C6 (`Validator.C6`:
a route does not hit the interior of an exclusive box outside its route
scope, where the scope is both endpoints plus all their ancestors) is kept
by real stages:

* (a) `applyPin`: a route that stays inside one band moves by that band's
  shift, and so does every box of the same band, so translation keeps
  `¬ hitsRect` for pairs in one band (proved below as `hitsRect_shift`,
  applied through the executed `Move.constant` shifts). A rigid route
  against a box of another band is separated by the band tiling
  (`layLanes_tiled`, `laneBand_thickness_nonneg`); the leftover band
  geometry is the named residual `pinBandsApplyPinKeptClear`, about
  `applyPin` only. The base `HardConstraints` (hence base C6) is taken as
  the hypothesis it already is.
* (b) `rerouteBands`: a cross-lane route gets new points from `findRoute`
  on the grid (`routeGrid`, `searchGrid`, `clearPolyline`, `obstacleOf`).
  Search soundness for the calls `rerouteBands` makes (`ends` from
  `routeEnds`, `inflates = [sp.slot, 0]`), when `findRoute` returns
  `.ok points` the polyline misses every obstacle rect in the obstacle
  list, is the named residual `pinBandsFindRouteClear` (`clearPolyline` is
  the Bool test the search applies). The obstacle list contains every
  exclusive box outside the route's scope (proved as `obstacle_cover`
  below). Scope note: `obstacleOf` selection in `rerouteBands` keeps every
  box with `b.exclusive && b.id != r.fromId && b.id != r.toId`, while C6
  exempts the whole scope (endpoints plus ancestors). The obstacle list
  is therefore a superset of the C6-relevant boxes: ancestors stay in the
  obstacle list, which is conservative (more obstacles, never fewer).
  `PinBandsProbe.c6Bad` checks exactly this superset direction with
  `hitsRectB` on every executed swimlane layout.
* (c) `restoreOrigin` shifts all boxes and routes by one vector:
  translation invariance of `hitsRect` (proved). `relocateLabels` and
  `growCanvas` do not move boxes or routes: C6 is unchanged (proved box
  and route list equalities, reusing `relocateLabels_boxes`,
  `relocateLabels_routes`, `growCanvas_frame`).
-/

/-- Shift a point by `(dx, dy)`. -/
def shiftPoint (dx dy : Int) (p : Point) : Point :=
  ⟨p.x + dx, p.y + dy⟩

/-- Shift a rectangle by `(dx, dy)`, keeping its sizes. -/
def shiftRect (dx dy : Int) (r : Rect) : Rect :=
  ⟨r.x + dx, r.y + dy, r.w, r.h⟩

theorem shiftPoint_x (dx dy : Int) (p : Point) :
    (shiftPoint dx dy p).x = p.x + dx := rfl

theorem shiftPoint_y (dx dy : Int) (p : Point) :
    (shiftPoint dx dy p).y = p.y + dy := rfl

theorem shiftRect_x (dx dy : Int) (r : Rect) :
    (shiftRect dx dy r).x = r.x + dx := rfl

theorem shiftRect_y (dx dy : Int) (r : Rect) :
    (shiftRect dx dy r).y = r.y + dy := rfl

theorem shiftRect_w (dx dy : Int) (r : Rect) :
    (shiftRect dx dy r).w = r.w := rfl

theorem shiftRect_h (dx dy : Int) (r : Rect) :
    (shiftRect dx dy r).h = r.h := rfl

theorem shiftPoint_inj (dx dy : Int) (p q : Point)
    (h : shiftPoint dx dy p = shiftPoint dx dy q) : p = q := by
  obtain ⟨px, py⟩ := p
  obtain ⟨qx, qy⟩ := q
  simp only [shiftPoint, Point.mk.injEq] at h ⊢
  omega

theorem shiftPoint_ne (dx dy : Int) (p q : Point) :
    (shiftPoint dx dy p ≠ shiftPoint dx dy q) ↔ (p ≠ q) := by
  constructor
  · intro h heq
    apply h
    rw [heq]
  · intro h heq
    apply h
    exact shiftPoint_inj dx dy p q heq

theorem min_add (a b k : Int) : min (a + k) (b + k) = min a b + k := by
  by_cases h : a ≤ b
  · have h2 : a + k ≤ b + k := by omega
    omega
  · omega

theorem max_add (a b k : Int) : max (a + k) (b + k) = max a b + k := by
  by_cases h : a ≤ b
  · have h2 : a + k ≤ b + k := by omega
    omega
  · omega

theorem dot_shift (nx ny dx dy : Int) (p : Point) :
    Polyline.dot nx ny (shiftPoint dx dy p) =
      Polyline.dot nx ny p + (nx * dx + ny * dy) := by
  simp only [Polyline.dot, shiftPoint, Int.mul_add]
  omega

theorem minCorner_shift (nx ny dx dy : Int) (r : Rect) :
    Polyline.minCorner nx ny (shiftRect dx dy r) =
      Polyline.minCorner nx ny r + (nx * dx + ny * dy) := by
  have d1 : Polyline.dot nx ny (⟨r.x + dx, r.y + dy⟩ : Point) =
      Polyline.dot nx ny (⟨r.x, r.y⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  have d2 : Polyline.dot nx ny (⟨r.x + dx + r.w, r.y + dy⟩ : Point) =
      Polyline.dot nx ny (⟨r.x + r.w, r.y⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  have d3 : Polyline.dot nx ny (⟨r.x + dx, r.y + dy + r.h⟩ : Point) =
      Polyline.dot nx ny (⟨r.x, r.y + r.h⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  have d4 : Polyline.dot nx ny (⟨r.x + dx + r.w, r.y + dy + r.h⟩ : Point) =
      Polyline.dot nx ny (⟨r.x + r.w, r.y + r.h⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  simp only [Polyline.minCorner, shiftRect]
  rw [d1, d2, d3, d4, min_add, min_add, min_add]

theorem maxCorner_shift (nx ny dx dy : Int) (r : Rect) :
    Polyline.maxCorner nx ny (shiftRect dx dy r) =
      Polyline.maxCorner nx ny r + (nx * dx + ny * dy) := by
  have d1 : Polyline.dot nx ny (⟨r.x + dx, r.y + dy⟩ : Point) =
      Polyline.dot nx ny (⟨r.x, r.y⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  have d2 : Polyline.dot nx ny (⟨r.x + dx + r.w, r.y + dy⟩ : Point) =
      Polyline.dot nx ny (⟨r.x + r.w, r.y⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  have d3 : Polyline.dot nx ny (⟨r.x + dx, r.y + dy + r.h⟩ : Point) =
      Polyline.dot nx ny (⟨r.x, r.y + r.h⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  have d4 : Polyline.dot nx ny (⟨r.x + dx + r.w, r.y + dy + r.h⟩ : Point) =
      Polyline.dot nx ny (⟨r.x + r.w, r.y + r.h⟩ : Point) + (nx * dx + ny * dy) := by
    simp only [Polyline.dot, Int.mul_add]
    omega
  simp only [Polyline.maxCorner, shiftRect]
  rw [d1, d2, d3, d4, max_add, max_add, max_add]

/-- Translation keeps every segment miss: shifting the segment and the
rectangle by one vector preserves `segMisses` in both directions. -/
theorem segMisses_shift (dx dy : Int) (p q : Point) (r : Rect) :
    Polyline.segMisses (shiftPoint dx dy p) (shiftPoint dx dy q)
        (shiftRect dx dy r) ↔
      Polyline.segMisses p q r := by
  have n1 : p.y + dy - (q.y + dy) = p.y - q.y := by omega
  have n2 : q.x + dx - (p.x + dx) = q.x - p.x := by omega
  simp only [Polyline.segMisses, shiftPoint_x, shiftPoint_y, shiftRect_x,
    shiftRect_y, shiftRect_w, shiftRect_h, min_add, max_add,
    dot_shift, minCorner_shift, maxCorner_shift, shiftPoint_ne, n1, n2]
  constructor <;> intro h
  · rcases h with h | h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · rcases h with ⟨hne, hle | hge⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inl (by omega)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inr (by omega)⟩)))
  · rcases h with h | h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · rcases h with ⟨hne, hle | hge⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inl (by omega)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inr (by omega)⟩)))

/-- Translation keeps every polyline miss. -/
theorem allSegsMiss_shift (dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.allSegsMiss (points.map (shiftPoint dx dy)) (shiftRect dx dy r) ↔
      Polyline.allSegsMiss points r := by
  induction points with
  | nil => simp [Polyline.allSegsMiss]
  | cons p rest ih =>
    cases rest with
    | nil => simp [Polyline.allSegsMiss]
    | cons q rest2 =>
      have e : List.map (shiftPoint dx dy) (p :: q :: rest2)
          = shiftPoint dx dy p :: shiftPoint dx dy q ::
            List.map (shiftPoint dx dy) rest2 := rfl
      rw [e]
      simp only [Polyline.allSegsMiss, segMisses_shift, ← List.map_cons, ih]

/-- Translation invariance of `hitsRect`: shifting the polyline and the
rectangle by one vector preserves hits in both directions. Stage (a)
same-band pairs and stage (c) `restoreOrigin` both rest on this. -/
theorem hitsRect_shift (dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.map (shiftPoint dx dy)) (shiftRect dx dy r) ↔
      Polyline.hitsRect points r := by
  show (0 < (shiftRect dx dy r).w ∧ 0 < (shiftRect dx dy r).h ∧
    ¬ Polyline.allSegsMiss (points.map (shiftPoint dx dy)) (shiftRect dx dy r)) ↔
    (0 < r.w ∧ 0 < r.h ∧ ¬ Polyline.allSegsMiss points r)
  simp only [shiftRect_w, shiftRect_h]
  rw [allSegsMiss_shift]

/-- A polyline of fewer than two points never hits any rectangle. Kept
short routes (`old.points.length < 2` in `rerouteBands`) are therefore
always clear, with no search needed. -/
theorem not_hits_of_short {points : List Point} {r : Rect}
    (h : points.length < 2) : ¬ Polyline.hitsRect points r := by
  apply Polyline.not_hits_of_allMiss
  cases points with
  | nil => simp [Polyline.allSegsMiss]
  | cons p rest =>
    cases rest with
    | nil => simp [Polyline.allSegsMiss]
    | cons q rest2 =>
      simp at h
      omega

/-- Local bind destructor (the same shape as the phase-facts helper). -/
private theorem bind_ok' {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A successful `mapM` preserves length. -/
theorem mapM_length {α β : Type} (f : α → Except LayoutError β)
    (l : List α) (l' : List β)
    (h : l.mapM f = .ok l') : l'.length = l.length := by
  induction l generalizing l' with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons a rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b, hfb, hrest⟩ := bind_ok' h
    obtain ⟨tl, htl, hpure⟩ := bind_ok' hrest
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    simp only [List.length_cons]
    rw [ih _ htl]

/-- A successful `mapM` whose elements all agree with a pure map equals
that pure map. -/
theorem mapM_ok_map {α β : Type} (f : α → Except LayoutError β) (g : α → β)
    (l : List α) (l' : List β)
    (h : l.mapM f = .ok l') (hg : ∀ x ∈ l, f x = .ok (g x)) :
    l' = l.map g := by
  induction l generalizing l' with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons a rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b, hfb, hrest⟩ := bind_ok' h
    obtain ⟨tl, htl, hpure⟩ := bind_ok' hrest
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    have hga : g a = b := by
      have h1 := hg a List.mem_cons_self
      rw [hfb] at h1
      simp only [Except.ok.injEq] at h1
      exact h1.symm
    subst hga
    rw [List.map_cons]
    exact congrArg (g a :: ·) (ih _ htl (fun x hx => hg x (List.mem_cons_of_mem a hx)))

/-- Every element of a successful `mapM` succeeds. -/
theorem mapM_mem_ok {α β : Type} (f : α → Except LayoutError β)
    (l : List α) (l' : List β)
    (h : l.mapM f = .ok l') (x : α) (hx : x ∈ l) : ∃ y, f x = .ok y := by
  induction l generalizing l' with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b, hfb, hrest⟩ := bind_ok' h
    obtain ⟨tl, htl, hpure⟩ := bind_ok' hrest
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    simp at hx
    rcases hx with rfl | hx
    · exact ⟨b, hfb⟩
    · exact ih _ htl hx

/-- `find?` by id commutes with an id-preserving box map. -/
theorem find_map_id (boxes : List Box) (f : Box → Box)
    (hid : ∀ b ∈ boxes, (f b).id = b.id) (id : String) :
    (boxes.map f).find? (fun b => b.id == id) =
      (boxes.find? (fun b => b.id == id)).map f := by
  induction boxes with
  | nil => simp
  | cons b rest ih =>
    have hb : (f b).id = b.id := hid b List.mem_cons_self
    unfold List.find?
    by_cases h : (b.id == id) = true
    · have hf : ((f b).id == id) = true := by rw [hb]; exact h
      simp [h, hf]
    · have hf : ¬ (((f b).id == id) = true) := by rw [hb]; exact h
      simp only [List.map_cons, h, hf]
      exact ih (fun b' hb' => hid b' (List.mem_cons_of_mem b hb'))

/-- The ancestor walk only reads ids and parents, so it survives an
id- and parent-preserving box map. -/
theorem ancestors_go_map (d : LayoutDump) (f : Box → Box)
    (hid : ∀ b ∈ d.boxes, (f b).id = b.id)
    (hp : ∀ b ∈ d.boxes, (f b).parent = b.parent)
    (fuel : Nat) (id : String) :
    LayoutDump.ancestors.go ⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ fuel id =
      LayoutDump.ancestors.go d fuel id := by
  induction fuel generalizing id with
  | zero =>
    simp only [LayoutDump.ancestors.go]
  | succ n ih =>
    have hfind := find_map_id d.boxes f hid id
    have hbox : (⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ : LayoutDump).box? id =
        (d.box? id).map f := by
      simp only [LayoutDump.box?, hfind]
    cases hfb : d.box? id with
    | none =>
      have hnone : (⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ : LayoutDump).box? id =
          none := by
        rw [hbox, hfb]
        rfl
      simp only [LayoutDump.ancestors.go, hnone, hfb]
    | some b =>
      have hmem : b ∈ d.boxes := by
        have hfind2 : d.boxes.find? (fun b => b.id == id) = some b := hfb
        exact List.mem_of_find?_eq_some hfind2
      have hsome : (⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ : LayoutDump).box? id =
          some (f b) := by
        rw [hbox, hfb]
        rfl
      have hpar : (f b).parent = b.parent := hp b hmem
      by_cases hpar0 : b.parent = ""
      · simp only [LayoutDump.ancestors.go, hsome, hfb, hpar, hpar0, ↓reduceIte]
      · simp only [LayoutDump.ancestors.go, hsome, hfb, hpar, hpar0, ↓reduceIte]
        exact congrArg (b.parent :: ·) (ih b.parent)

/-- Ancestors survive an id- and parent-preserving box map. -/
theorem ancestors_map (d : LayoutDump) (f : Box → Box)
    (hid : ∀ b ∈ d.boxes, (f b).id = b.id)
    (hp : ∀ b ∈ d.boxes, (f b).parent = b.parent)
    (id : String) :
    (⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ : LayoutDump).ancestors id =
      d.ancestors id := by
  have hgo : (⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ : LayoutDump).ancestors id =
      LayoutDump.ancestors.go ⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩
        ((d.boxes.map f).length) id := rfl
  have hgo2 : d.ancestors id =
      LayoutDump.ancestors.go d (d.boxes.length) id := rfl
  rw [hgo, hgo2, List.length_map]
  exact ancestors_go_map d f hid hp _ id

/-- Route scopes survive an id- and parent-preserving box map. -/
theorem routeScope_map (d : LayoutDump) (f : Box → Box)
    (hid : ∀ b ∈ d.boxes, (f b).id = b.id)
    (hp : ∀ b ∈ d.boxes, (f b).parent = b.parent)
    (s : Route) :
    (⟨d.canvas, d.boxes.map f, d.routes, d.labels⟩ : LayoutDump).routeScope s =
      d.routeScope s := by
  simp only [LayoutDump.routeScope]
  rw [ancestors_map d f hid hp, ancestors_map d f hid hp]

/-- The ancestor walk only reads the box list, so equal box lists give
equal walks at every fuel. -/
theorem ancestors_go_boxes_eq (d₁ d₂ : LayoutDump)
    (hb : d₁.boxes = d₂.boxes) (fuel : Nat) (id : String) :
    LayoutDump.ancestors.go d₁ fuel id =
      LayoutDump.ancestors.go d₂ fuel id := by
  induction fuel generalizing id with
  | zero =>
    simp only [LayoutDump.ancestors.go]
  | succ n ih =>
    have hbox : d₁.box? id = d₂.box? id := by
      simp only [LayoutDump.box?, hb]
    cases hfb : d₁.box? id with
    | none =>
      have hnone : d₂.box? id = none := by
        rw [← hbox]
        exact hfb
      simp only [LayoutDump.ancestors.go, hfb, hnone]
    | some b =>
      have hsome : d₂.box? id = some b := by
        rw [← hbox]
        exact hfb
      by_cases hpar : b.parent = ""
      · simp only [LayoutDump.ancestors.go, hfb, hsome, hpar, ↓reduceIte]
      · simp only [LayoutDump.ancestors.go, hfb, hsome, hpar, ↓reduceIte]
        exact congrArg (b.parent :: ·) (ih b.parent)

/-- Ancestors agree when the box lists agree. -/
theorem ancestors_boxes_eq {d₁ d₂ : LayoutDump}
    (hb : d₁.boxes = d₂.boxes) (id : String) :
    d₁.ancestors id = d₂.ancestors id := by
  have h1 : d₁.ancestors id = LayoutDump.ancestors.go d₁ (d₁.boxes.length) id := rfl
  have hgo1 : d₁.ancestors id =
      LayoutDump.ancestors.go d₁ (d₂.boxes.length) id := by
    rw [h1, hb]
  have hgo2 : d₂.ancestors id =
      LayoutDump.ancestors.go d₂ (d₂.boxes.length) id := rfl
  rw [hgo1, hgo2]
  exact ancestors_go_boxes_eq d₁ d₂ hb _ id

/-- Route scopes agree when the box lists agree. -/
theorem routeScope_boxes_eq {d₁ d₂ : LayoutDump}
    (hb : d₁.boxes = d₂.boxes) (s : Route) :
    d₁.routeScope s = d₂.routeScope s := by
  simp only [LayoutDump.routeScope]
  rw [ancestors_boxes_eq hb, ancestors_boxes_eq hb]

/-- C6 transfers across dumps with equal boxes and routes (labels and
canvas are irrelevant to C6). This covers `relocateLabels` and
`growCanvas` via their frame equalities. -/
theorem C6_of_boxes_routes_eq {d₁ d₂ : LayoutDump}
    (hb : d₂.boxes = d₁.boxes) (hr : d₂.routes = d₁.routes)
    (h : Validator.C6 d₁) : Validator.C6 d₂ := by
  intro r hr' b hb' hex hscope
  rw [hr] at hr'
  rw [hb] at hb'
  have hscope' : b.id ∉ d₁.routeScope r := by
    have heq := routeScope_boxes_eq hb r
    rw [heq] at hscope
    exact hscope
  exact h r hr' b hb' hex hscope'

/-- C6 transfers across a uniform shift of all route points and box
rects (ids, parents, and exclusivity are untouched, so scopes agree).
This covers stage (c) `restoreOrigin`. -/
theorem C6_map_shift (d : LayoutDump) (dx dy : Int)
    (boxes' : List Box) (routes' : List Route) (labels' : List Label)
    (hb : boxes' = d.boxes.map (fun b => { b with rect := shiftRect dx dy b.rect }))
    (hr : routes' = d.routes.map (fun r => { r with points := r.points.map (shiftPoint dx dy) }))
    (hC6 : Validator.C6 d) : Validator.C6 ⟨d.canvas, boxes', routes', labels'⟩ := by
  intro r' hr' b' hb' hex hscope
  rw [hr] at hr'
  rw [hb] at hb'
  obtain ⟨r, hrmem, hreq⟩ := List.mem_map.mp hr'
  obtain ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hb'
  subst hreq
  subst hbeq
  have hex' : b.exclusive = true := hex
  have hse : (⟨d.canvas, boxes', routes', labels'⟩ : LayoutDump).routeScope
      { r with points := r.points.map (shiftPoint dx dy) } = d.routeScope r := by
    rw [hb, hr]
    have hbx : (⟨d.canvas, d.boxes.map (fun b => { b with rect := shiftRect dx dy b.rect }),
        d.routes.map (fun r => { r with points := r.points.map (shiftPoint dx dy) }),
        labels'⟩ : LayoutDump).boxes =
      (⟨d.canvas, d.boxes.map (fun b => { b with rect := shiftRect dx dy b.rect }),
        d.routes, d.labels⟩ : LayoutDump).boxes := rfl
    rw [routeScope_boxes_eq hbx]
    exact routeScope_map d (fun b => { b with rect := shiftRect dx dy b.rect })
      (fun b _ => rfl) (fun b _ => rfl)
      { r with points := r.points.map (shiftPoint dx dy) }
  have hscope' : b.id ∉ d.routeScope r := hse ▸ hscope
  have hclear := hC6 r hrmem b hbmem hex' hscope'
  intro hcon
  exact hclear ((hitsRect_shift dx dy r.points b.rect).mp hcon)

/-- Axis projections and updates compute definitionally. -/
theorem Axis_start_x (r : Rect) : Axis.start .x r = r.x := rfl

theorem Axis_start_y (r : Rect) : Axis.start .y r = r.y := rfl

theorem Axis_point_x (p : Point) : Axis.point .x p = p.x := rfl

theorem Axis_point_y (p : Point) : Axis.point .y p = p.y := rfl

/-- A successful constant cross-axis shift of a rectangle is the axis shift. -/
theorem moveConstant_rect_shift_x (delta : Int) (r r' : Rect)
    (h : (Move.constant delta).rect .x r = .ok r') :
    r' = shiftRect delta 0 r := by
  obtain ⟨w, hw, hrfl, hval⟩ := moveConstant_rect_value h
  subst hrfl
  have h1 : Axis.withStart .x r w = { r with x := w } := rfl
  have h2 : Axis.start .x r = r.x := rfl
  rw [h1]
  rw [h2] at hval
  show (⟨w, r.y, r.w, r.h⟩ : Rect) = ⟨r.x + delta, r.y + 0, r.w, r.h⟩
  rw [Rect.mk.injEq]
  omega

theorem moveConstant_rect_shift_y (delta : Int) (r r' : Rect)
    (h : (Move.constant delta).rect .y r = .ok r') :
    r' = shiftRect 0 delta r := by
  obtain ⟨w, hw, hrfl, hval⟩ := moveConstant_rect_value h
  subst hrfl
  have h1 : Axis.withStart .y r w = { r with y := w } := rfl
  have h2 : Axis.start .y r = r.y := rfl
  rw [h1]
  rw [h2] at hval
  show (⟨r.x, w, r.w, r.h⟩ : Rect) = ⟨r.x + 0, r.y + delta, r.w, r.h⟩
  rw [Rect.mk.injEq]
  omega

/-- A successful constant cross-axis shift of a point is the axis shift. -/
theorem moveConstant_point_shift_x (delta : Int) (p p' : Point)
    (h : (Move.constant delta).point .x p = .ok p') :
    p' = shiftPoint delta 0 p := by
  unfold Move.point at h
  obtain ⟨v, hv, hrfl⟩ := bind_ok' h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have hval : v = Axis.point .x p + delta := moveConstant_value hv
  have h1 : Axis.withPoint .x p v = { p with x := v } := rfl
  have h2 : Axis.point .x p = p.x := rfl
  rw [h1]
  rw [h2] at hval
  show (⟨v, p.y⟩ : Point) = ⟨p.x + delta, p.y + 0⟩
  rw [Point.mk.injEq]
  omega

theorem moveConstant_point_shift_y (delta : Int) (p p' : Point)
    (h : (Move.constant delta).point .y p = .ok p') :
    p' = shiftPoint 0 delta p := by
  unfold Move.point at h
  obtain ⟨v, hv, hrfl⟩ := bind_ok' h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have hval : v = Axis.point .y p + delta := moveConstant_value hv
  have h1 : Axis.withPoint .y p v = { p with y := v } := rfl
  have h2 : Axis.point .y p = p.y := rfl
  rw [h1]
  rw [h2] at hval
  show (⟨p.x, v⟩ : Point) = ⟨p.x + 0, p.y + delta⟩
  rw [Point.mk.injEq]
  omega

/-- A successful `shiftAll` along `.x` shifts every box rect and route
point by `(delta, 0)` and keeps the canvas. -/
theorem shiftAll_eq_map_x (delta : Int) (s s' : Scene)
    (h : shiftAll .x delta s = .ok s') :
    s'.boxes = s.boxes.map (fun b => { b with rect := shiftRect delta 0 b.rect }) ∧
    s'.routes = s.routes.map (fun r => { r with points := r.points.map (shiftPoint delta 0) }) ∧
    s'.canvas = s.canvas := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := bind_ok' h
  obtain ⟨labels, hlabels, h⟩ := bind_ok' h
  obtain ⟨routes, hroutes, h⟩ := bind_ok' h
  obtain ⟨items, hitems, h⟩ := bind_ok' h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨?_, ?_, rfl⟩
  · exact mapM_ok_map _ _ _ _ hboxes (fun b hb => by
      obtain ⟨y, hy⟩ := mapM_mem_ok _ _ _ hboxes b hb
      obtain ⟨rect', hrect, hpure⟩ := bind_ok' hy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      have hshift : rect' = shiftRect delta 0 b.rect :=
        moveConstant_rect_shift_x delta b.rect rect' hrect
      rw [hy, ← hpure, hshift])
  · exact mapM_ok_map _ _ _ _ hroutes (fun r hr => by
      obtain ⟨y, hy⟩ := mapM_mem_ok _ _ _ hroutes r hr
      obtain ⟨pts, hpts, hpure⟩ := bind_ok' hy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      have hpts_eq : pts = r.points.map (shiftPoint delta 0) := by
        exact mapM_ok_map _ _ _ _ hpts (fun p hp => by
          obtain ⟨q, hq⟩ := mapM_mem_ok _ _ _ hpts p hp
          have hshift : q = shiftPoint delta 0 p :=
            moveConstant_point_shift_x delta p q hq
          exact hshift ▸ hq)
      rw [hy, ← hpure, hpts_eq])

/-- A successful `shiftAll` along `.y` shifts every box rect and route
point by `(0, delta)` and keeps the canvas. -/
theorem shiftAll_eq_map_y (delta : Int) (s s' : Scene)
    (h : shiftAll .y delta s = .ok s') :
    s'.boxes = s.boxes.map (fun b => { b with rect := shiftRect 0 delta b.rect }) ∧
    s'.routes = s.routes.map (fun r => { r with points := r.points.map (shiftPoint 0 delta) }) ∧
    s'.canvas = s.canvas := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := bind_ok' h
  obtain ⟨labels, hlabels, h⟩ := bind_ok' h
  obtain ⟨routes, hroutes, h⟩ := bind_ok' h
  obtain ⟨items, hitems, h⟩ := bind_ok' h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨?_, ?_, rfl⟩
  · exact mapM_ok_map _ _ _ _ hboxes (fun b hb => by
      obtain ⟨y, hy⟩ := mapM_mem_ok _ _ _ hboxes b hb
      obtain ⟨rect', hrect, hpure⟩ := bind_ok' hy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      have hshift : rect' = shiftRect 0 delta b.rect :=
        moveConstant_rect_shift_y delta b.rect rect' hrect
      rw [hy, ← hpure, hshift])
  · exact mapM_ok_map _ _ _ _ hroutes (fun r hr => by
      obtain ⟨y, hy⟩ := mapM_mem_ok _ _ _ hroutes r hr
      obtain ⟨pts, hpts, hpure⟩ := bind_ok' hy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      have hpts_eq : pts = r.points.map (shiftPoint 0 delta) := by
        exact mapM_ok_map _ _ _ _ hpts (fun p hp => by
          obtain ⟨q, hq⟩ := mapM_mem_ok _ _ _ hpts p hp
          have hshift : q = shiftPoint 0 delta p :=
            moveConstant_point_shift_y delta p q hq
          exact hshift ▸ hq)
      rw [hy, ← hpure, hpts_eq])

/-- `restoreOrigin` keeps C6: it either returns the scene unchanged or
shifts every box and route by one vector (stage (c)). -/
theorem restoreOrigin_C6 (axis : Axis) (s s' : Scene)
    (h : restoreOrigin axis s = .ok s') (hC6 : Validator.C6 s.layoutDump) :
    Validator.C6 s'.layoutDump := by
  unfold restoreOrigin at h
  cases hbounds : bounds (geometryValues axis false s) with
  | none =>
    simp only [hbounds] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hC6
  | some p =>
    simp only [hbounds] at h
    cases p with
    | mk lo hi =>
      dsimp only at h
      by_cases hlo : lo < 0
      · simp [hlo] at h
        cases axis with
        | x =>
          obtain ⟨hb, hr, hc⟩ := shiftAll_eq_map_x (-lo) s s' h
          have hdump : s'.layoutDump =
              ⟨s.canvas, s.boxes.map (fun b => { b with rect := shiftRect (-lo) 0 b.rect }),
                s.routes.map (fun r => { r with points := r.points.map (shiftPoint (-lo) 0) }),
                s'.labels.map (·.toLabel)⟩ := by
            simp [Scene.layoutDump, hb, hr, hc]
          rw [hdump]
          exact C6_map_shift _ _ _ _ _ _ rfl rfl hC6
        | y =>
          obtain ⟨hb, hr, hc⟩ := shiftAll_eq_map_y (-lo) s s' h
          have hdump : s'.layoutDump =
              ⟨s.canvas, s.boxes.map (fun b => { b with rect := shiftRect 0 (-lo) b.rect }),
                s.routes.map (fun r => { r with points := r.points.map (shiftPoint 0 (-lo)) }),
                s'.labels.map (·.toLabel)⟩ := by
            simp [Scene.layoutDump, hb, hr, hc]
          rw [hdump]
          exact C6_map_shift _ _ _ _ _ _ rfl rfl hC6
      · simp [hlo] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact hC6

/-- The `rerouteBands` obstacle list contains every exclusive box outside
the route's scope. C6 exempts endpoints plus ancestors while the filter
keeps every box except the two endpoints, so the obstacle list is a
superset of the C6-relevant boxes (conservative for soundness). -/
theorem obstacle_cover (s : Scene) (axis : Axis) (r : Route) (b : Box)
    (hb : b ∈ s.boxes)
    (hex : b.exclusive = true)
    (hscope : b.id ∉ s.layoutDump.routeScope r) :
    obstacleOf axis b.rect ∈
      (s.boxes.filter (fun b => b.exclusive && b.id != r.fromId && b.id != r.toId)).map
        (fun b => obstacleOf axis b.rect) := by
  have hfrom : r.fromId ∈ s.layoutDump.routeScope r := by
    simp [LayoutDump.routeScope]
  have hto : r.toId ∈ s.layoutDump.routeScope r := by
    simp [LayoutDump.routeScope]
  have hne_from : b.id ≠ r.fromId := fun heq => hscope (heq.symm ▸ hfrom)
  have hne_to : b.id ≠ r.toId := fun heq => hscope (heq.symm ▸ hto)
  have hmem : b ∈ s.boxes.filter
      (fun b => b.exclusive && b.id != r.fromId && b.id != r.toId) := by
    rw [List.mem_filter]
    refine ⟨hb, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne]
    exact ⟨⟨hex, hne_from⟩, hne_to⟩
  exact List.mem_map.mpr ⟨b, hmem, rfl⟩

/-- `replaceFrame` never changes the route list. -/
theorem replaceFrame_routes (axis : Axis) (band : Band) (s s' : Scene)
    (h : replaceFrame axis band s = .ok s') : s'.routes = s.routes := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | some index =>
    simp only [hfind] at h
    obtain ⟨st, hst, h⟩ := bind_ok' h
    obtain ⟨th, hth, h⟩ := bind_ok' h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl

/-- Folding `replaceFrame` over bands never changes the route list. -/
theorem foldlM_replaceFrame_routes (axis : Axis) (bands : List Band)
    (s s' : Scene)
    (h : bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s') :
    s'.routes = s.routes := by
  induction bands generalizing s with
  | nil =>
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons b bs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok' h
    have h1 : mid.routes = s.routes := replaceFrame_routes axis b s mid hmid
    have h2 : s'.routes = mid.routes := ih _ hrest
    rw [h2, h1]

/-- The `applyPin` route shift preserves every route's point count. -/
theorem shiftRoutes_length_map (pin : Pin)
    (rs : List Route) (out : List Route)
    (h : rs.mapM (fun r : Route => (match pin.route r.id with | none => (pure r : Except LayoutError Route) | some d => (do pure { r with points := ← r.points.mapM ((routeMove d).point pin.axis) } : Except LayoutError Route))) = .ok out) :
    out.map (fun r => r.points.length) = rs.map (fun r => r.points.length) := by
  induction rs generalizing out with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons r rs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y, hfy, hrest⟩ := bind_ok' h
    obtain ⟨tl, htl, hpure⟩ := bind_ok' hrest
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    cases hpr : pin.route r.id with
    | none =>
      simp only [hpr, Pure.pure, Except.pure, Except.ok.injEq] at hfy
      subst hfy
      simp only [List.map_cons]
      exact congrArg (r.points.length :: ·) (ih _ htl)
    | some d =>
      simp only [hpr] at hfy
      obtain ⟨pts, hpts, hpure⟩ := bind_ok' hfy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      subst hpure
      have hlen : pts.length = r.points.length := mapM_length _ _ _ hpts
      show pts.length :: tl.map (fun r => r.points.length) =
        r.points.length :: rs.map (fun r => r.points.length)
      rw [hlen]
      exact congrArg (r.points.length :: ·) (ih _ htl)

/-- `applyPin` preserves every route's point count. -/
theorem applyPin_routes_length_map (pin : Pin) (bands : List Band)
    (s s1 : Scene)
    (h : applyPin pin bands s = .ok s1) :
    s1.routes.map (fun r => r.points.length) =
      s.routes.map (fun r => r.points.length) := by
  obtain ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems,
      hboxes, hlabels, hroutes, hitems, hfold⟩ := applyPin_shifted h
  have hshift : shiftedRoutes.map (fun r => r.points.length) =
      s.routes.map (fun r => r.points.length) :=
    shiftRoutes_length_map pin s.routes shiftedRoutes hroutes
  have hfold' : s1.routes = shiftedRoutes :=
    foldlM_replaceFrame_routes pin.axis bands _ s1 hfold
  rw [hfold']
  exact hshift

/-- Every output of a `mapM` over a zip comes from a zipped pair. -/
theorem mapM_zip_mem {α β γ : Type} (f : α × β → Except LayoutError γ)
    (l₁ : List α) (l₂ : List β) (out : List γ)
    (h : (l₁.zip l₂).mapM f = .ok out) (x : γ) (hx : x ∈ out) :
    ∃ a ∈ l₁, ∃ b ∈ l₂, (a, b) ∈ l₁.zip l₂ ∧ f (a, b) = .ok x := by
  induction l₁ generalizing l₂ out with
  | nil =>
    have hzip : ([] : List α).zip l₂ = [] := rfl
    rw [hzip] at h
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hx
  | cons a as ih =>
    cases l₂ with
    | nil =>
      have hzip : (a :: as).zip ([] : List β) = [] := rfl
      rw [hzip] at h
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp at hx
    | cons b bs =>
      simp only [List.zip_cons_cons] at h
      rw [List.mapM_cons] at h
      obtain ⟨y, hfy, hrest⟩ := bind_ok' h
      obtain ⟨tl, htl, hpure⟩ := bind_ok' hrest
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      subst hpure
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [List.zip_cons_cons]
        exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, List.mem_cons_self, hfy⟩
      · obtain ⟨a', ha', b', hb', hpair, hf⟩ := ih _ _ htl hx
        refine ⟨a', List.mem_cons_of_mem a ha', b', List.mem_cons_of_mem b hb', ?_, hf⟩
        simp only [List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hpair

/-- Stage-(b) residual, about the `findRoute` calls `rerouteBands` makes:
`ends` come from `routeEnds` and `inflates = [sp.slot, 0]`
(`LaneBands.lean:588-591`). The unpinned form (arbitrary `ends` and
`inflates`) is false: misaligned ends make the search return a polyline
whose diagonal first segment crosses an obstacle hugging grid lines
(`FindRouteClearProbe`: `wEnds`/`wObs` give `.ok` with `hitsRectB` true),
because the Bool `hits` test never fires on diagonal steps. Pinning `ends`
to `routeEnds` output (rank-only shift, `routeEndsAligned_holds` in the
sibling proof module) rules out that witness. -/
def pinBandsFindRouteClear : Prop :=
  ∀ (axis : Axis) (sp : Spacing) (pin : Pin) (fromBox toBox : Box)
    (original : List Point) (ends : RouteEnds),
    routeEnds axis sp pin fromBox toBox original = .ok ends →
    ∀ (obs : List Obstacle) (bend : Int) (points : List Point),
    findRoute axis ends obs bend [sp.slot, 0] = .ok points →
    ∀ (o : Obstacle), o ∈ obs → ∀ (r : Rect), obstacleOf axis r = o →
      ¬ Polyline.hitsRect points r


/-- Stage-(a) residual, about `applyPin` alone: pinning keeps clear every
route the router keeps. A kept route either shares one band at both ends
(so `buildPin` moves it rigidly by that band's shift, and translation
keeps `¬ hitsRect` from the base C6, which is taken as the hypothesis it
already is), or its base preimage is short (lengths are preserved by
`applyPin`), or a band/box lookup missed. Bands tile the cross axis
(`layLanes_tiled`, `laneBand_thickness_nonneg`), which separates a rigid
route from boxes of other bands. Lookup misses are vacuous on executed
family output (every laid-out endpoint is covered: lanes, their members
including nested groups via `inLane`, and loose nodes; `PinBandsProbe`
covers all three shapes plus hand-built slack scenes). -/
def pinBandsApplyPinKeptClear : Prop :=
  ∀ (axis : Axis) (bands : List Band) (s pinned : Scene)
    (boxes : List ModelBox) (sp : Spacing),
    bands = layBands boxes s axis sp (lanesOf boxes) →
    applyPin (buildPin axis bands s) bands s = .ok pinned →
    Validator.C6 s.layoutDump →
    ∀ (r : Route) (b : Box) (old : Route),
      r ∈ pinned.routes → old ∈ s.routes →
      (r, old) ∈ pinned.routes.zip s.routes →
      b ∈ pinned.boxes →
      b.exclusive = true → b.id ∉ pinned.layoutDump.routeScope r →
      ((∃ fi ti : Nat,
        bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) = some fi ∧
        bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) = some ti ∧
        (fi = ti ∨ old.points.length < 2)) ∨
      bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) = none ∨
      bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) = none ∨
      pinned.boxes.find? (fun b => b.id == r.fromId) = none ∨
      pinned.boxes.find? (fun b => b.id == r.toId) = none) →
      ¬ Polyline.hitsRect r.points b.rect
/-- Stage-(b) structure: every routed route is kept (same points, with its
keep reason) or freshly re-routed by `findRoute` (with its witnesses). -/
theorem rerouteBands_mem (axis : Axis) (sp : Spacing) (bend : Int)
    (bands : List Band) (pin : Pin) (original : List Route) (s routed : Scene)
    (h : rerouteBands axis sp bend bands pin original s = .ok routed) :
    ∀ r' ∈ routed.routes, ∃ r ∈ s.routes, ∃ old ∈ original,
      (r, old) ∈ s.routes.zip original ∧
      r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      ((r'.points = r.points ∧
        ((∃ fi ti : Nat,
          bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) = some fi ∧
          bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) = some ti ∧
          (fi = ti ∨ old.points.length < 2)) ∨
        bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) = none ∨
        bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) = none ∨
        s.boxes.find? (fun b => b.id == r.fromId) = none ∨
        s.boxes.find? (fun b => b.id == r.toId) = none)) ∨
      (∃ fi ti fb tb ends obs pts,
        bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) = some fi ∧
        bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) = some ti ∧
        s.boxes.find? (fun b => b.id == r.fromId) = some fb ∧
        s.boxes.find? (fun b => b.id == r.toId) = some tb ∧
        routeEnds axis sp pin fb tb old.points = .ok ends ∧
        obs = ((s.boxes.filter (fun b => b.exclusive && b.id != r.fromId &&
          b.id != r.toId)).map (fun b => obstacleOf axis b.rect) ++
          textObstacles axis s) ∧
        findRoute axis ends obs bend [sp.slot, 0] = .ok pts ∧ r'.points = pts)) := by
  unfold rerouteBands at h
  obtain ⟨routes, hmap, h⟩ := bind_ok' h
  dsimp only at h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro r' hr'
  have hr'' : r' ∈ routes := hr'
  obtain ⟨r, hrmem, old, holdmem, hpair, hfy⟩ := mapM_zip_mem _ _ _ _ hmap r' hr''
  dsimp only at hfy
  cases hfi : bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) with
  | none =>
    simp [hfi] at hfy
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
    subst hfy
    exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl,
      Or.inl ⟨rfl, Or.inr (Or.inl hfi)⟩⟩
  | some fi =>
    cases hti : bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) with
    | none =>
      simp [hti] at hfy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
      subst hfy
      exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl,
        Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl hti))⟩⟩
    | some ti =>
      cases hfb : s.boxes.find? (fun b => b.id == r.fromId) with
      | none =>
        simp [hfb] at hfy
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
        subst hfy
        exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl,
          Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl hfb)))⟩⟩
      | some fb =>
        cases htb : s.boxes.find? (fun b => b.id == r.toId) with
        | none =>
          simp [htb] at hfy
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
          subst hfy
          exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl,
            Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr htb)))⟩⟩
        | some tb =>
          simp [hfi, hti, hfb, htb] at hfy
          by_cases hcond : fi = ti ∨ old.points.length < 2
          · simp [hcond] at hfy
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
            subst hfy
            exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl,
              Or.inl ⟨rfl, Or.inl ⟨fi, ti, hfi, hti, hcond⟩⟩⟩
          · simp [hcond] at hfy
            obtain ⟨ends, hends, hrest⟩ := bind_ok' hfy
            obtain ⟨pts, hfind, hpure⟩ := bind_ok' hrest
            simp only [Except.ok.injEq] at hpure
            subst hpure
            exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl,
              Or.inr ⟨fi, ti, fb, tb, ends, _, pts, hfi, hti, hfb, htb, hends, rfl, hfind, rfl⟩⟩


end LaneBands
end Layered
end Elegant

namespace Elegant
namespace Kinds
namespace Swimlane

end Swimlane
end Kinds
end Elegant

