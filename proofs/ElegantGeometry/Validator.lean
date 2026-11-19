import ElegantGeometry.Route

/-! The layout validator: the layout dump structures, `WellFormed`, the eight
hard-constraint clauses with their fixed order and messages, and `Validator.sound`.

Each clause has a Boolean test (`c1` to `c8`) and a predicate (`C1` to `C8`). The predicate
is stated in the vocabulary of `spec/layout-dump.md`: containment, `Disjoint`,
`StrictInside`, `Polyline.isOrthogonal`, `on_boundary`, `Polyline.hitsRect`, and
ancestors. The Boolean test is the executable form, and `c1_iff` to `c8_iff` prove that
the test is `true` exactly when the predicate holds. `Validator.sound` then follows by
unfolding `check` and rewriting each test to its predicate. -/

set_option autoImplicit false

/-- A box of the canonical layout dump. -/
structure Box where
  id : String
  role : String
  rect : Rect
  parent : String
  exclusive : Bool
deriving DecidableEq, Repr

/-- A route of the canonical layout dump. -/
structure Route where
  id : String
  fromId : String
  toId : String
  orthogonal : Bool
  points : List Point
deriving DecidableEq, Repr

/-- A label of the canonical layout dump. -/
structure Label where
  id : String
  owner : String
  rect : Rect
  lines : List String
deriving DecidableEq, Repr

/-- The part of the canonical layout dump that the validator reads. -/
structure LayoutDump where
  canvas : Size
  boxes : List Box
  routes : List Route
  labels : List Label
deriving DecidableEq, Repr

namespace LayoutDump

/-- The box with id `id`, when one exists. -/
def box? (d : LayoutDump) (id : String) : Option Box :=
  d.boxes.find? (fun b => b.id == id)

/-- The proper ancestors of `id`, following `parent`. The fuel is the box count, so the
walk stops on a cycle and the list is always finite. -/
def ancestors (d : LayoutDump) (id : String) : List String :=
  let rec go : Nat → String → List String
    | 0, _ => []
    | n + 1, s =>
      match d.box? s with
      | none => []
      | some b => if b.parent = "" then [] else b.parent :: go n b.parent
  go d.boxes.length id

/-- The scope of a route: both endpoints and their ancestors. -/
def routeScope (d : LayoutDump) (r : Route) : List String :=
  [r.fromId, r.toId] ++ d.ancestors r.fromId ++ d.ancestors r.toId

/-- The label's owning box and its ancestors, or a route's endpoint ancestors. -/
def labelOwnerAnc (d : LayoutDump) (l : Label) : List String :=
  match d.routes.find? (fun r => r.id == l.owner) with
  | some r => d.ancestors r.fromId ++ d.ancestors r.toId
  | none => l.owner :: d.ancestors l.owner

/-- The box ids, in dump order. -/
def boxIds (d : LayoutDump) : List String := d.boxes.map (fun b => b.id)

/-- The route ids, in dump order. -/
def routeIds (d : LayoutDump) : List String := d.routes.map (fun r => r.id)

/-- The label ids, in dump order. -/
def labelIds (d : LayoutDump) : List String := d.labels.map (fun l => l.id)

end LayoutDump

/-- `n` lies within `±COORD_LIMIT`. -/
abbrev WithinLimit (n : Int) : Prop := -COORD_LIMIT ≤ n ∧ n ≤ COORD_LIMIT

/-- A rectangle with non-negative sizes whose coordinates and far edges lie within
`±COORD_LIMIT`. -/
abbrev RectBounded (r : Rect) : Prop :=
  0 ≤ r.w ∧ 0 ≤ r.h ∧ WithinLimit r.x ∧ WithinLimit r.y ∧
    WithinLimit (r.x + r.w) ∧ WithinLimit (r.y + r.h)

/-- A bounded rectangle is a valid rectangle, so the checked rectangle operations never
return an error on it. -/
theorem RectBounded.valid {r : Rect} (h : RectBounded r) : r.Valid := by
  obtain ⟨hw, hh, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hxw1, hxw2⟩, ⟨hyh1, hyh2⟩⟩ := h
  unfold Rect.Valid InI32 COORD_LIMIT I32_MIN I32_MAX at *
  omega

/-- On bounded rectangles `intersects` returns its test and never an error. -/
theorem Rect.intersects_of_bounded {a b : Rect} (ha : RectBounded a) (hb : RectBounded b) :
    a.intersects b = .ok (decide (a.meetsInterior b)) := by
  unfold Rect.intersects
  rw [ite_eq_left (show a.Valid ∧ b.Valid from ⟨ha.valid, hb.valid⟩)]

/-- On bounded rectangles `contains` returns its test and never an error. -/
theorem Rect.contains_of_bounded {a b : Rect} (ha : RectBounded a) (hb : RectBounded b) :
    a.contains b = .ok (decide (a.Contained b)) := by
  unfold Rect.contains
  rw [ite_eq_left (show a.Valid ∧ b.Valid from ⟨ha.valid, hb.valid⟩)]

/-- The box ids are unique. -/
abbrev WF1 (d : LayoutDump) : Prop := d.boxIds.Nodup

/-- The route ids are unique. -/
abbrev WF2 (d : LayoutDump) : Prop := d.routeIds.Nodup

/-- The label ids are unique. -/
abbrev WF3 (d : LayoutDump) : Prop := d.labelIds.Nodup

/-- Both ends of every route name boxes. -/
abbrev WF4 (d : LayoutDump) : Prop :=
  ∀ r ∈ d.routes, r.fromId ∈ d.boxIds ∧ r.toId ∈ d.boxIds

/-- The owner of every label names a route or a box. -/
abbrev WF5 (d : LayoutDump) : Prop :=
  ∀ l ∈ d.labels, l.owner ∈ d.routeIds ∨ l.owner ∈ d.boxIds

/-- Every parent is `""` or a box id. -/
abbrev WF6 (d : LayoutDump) : Prop :=
  ∀ b ∈ d.boxes, b.parent = "" ∨ b.parent ∈ d.boxIds

/-- The parent chain of every box has no cycle: no box is its own proper ancestor. -/
abbrev WF7 (d : LayoutDump) : Prop := ∀ b ∈ d.boxes, b.id ∉ d.ancestors b.id

/-- The canvas size is non-negative and within the coordinate limit. -/
abbrev WF8 (d : LayoutDump) : Prop :=
  0 ≤ d.canvas.w ∧ 0 ≤ d.canvas.h ∧ WithinLimit d.canvas.w ∧ WithinLimit d.canvas.h

/-- Every box rectangle and every label rectangle is bounded. -/
abbrev WF9 (d : LayoutDump) : Prop :=
  (∀ b ∈ d.boxes, RectBounded b.rect) ∧ (∀ l ∈ d.labels, RectBounded l.rect)

/-- Every route point lies within the coordinate limit. -/
abbrev WF10 (d : LayoutDump) : Prop :=
  ∀ r ∈ d.routes, ∀ p ∈ r.points, WithinLimit p.x ∧ WithinLimit p.y

/-- `WellFormed d`: the input conditions of `spec/layout-dump.md` under which the checked
rectangle and polyline operations never return an error. -/
abbrev WellFormed (d : LayoutDump) : Prop :=
  WF1 d ∧ WF2 d ∧ WF3 d ∧ WF4 d ∧ WF5 d ∧ WF6 d ∧ WF7 d ∧ WF8 d ∧ WF9 d ∧ WF10 d

/-- The first violated well-formedness condition, as the reason that `geomcheck validate`
prints, or none. -/
def wellFormedReason (d : LayoutDump) : Option String :=
  if _ : WF1 d then
    if _ : WF2 d then
      if _ : WF3 d then
        if _ : WF4 d then
          if _ : WF5 d then
            if _ : WF6 d then
              if _ : WF7 d then
                if _ : WF8 d then
                  if _ : WF9 d then
                    if _ : WF10 d then none
                    else some "a route point lies outside the coordinate limit"
                  else some "a rectangle has a negative size or lies outside the coordinate limit"
                else some "the canvas size is negative or outside the coordinate limit"
              else some "a box parent chain has a cycle"
            else some "a box parent names no box"
          else some "a label owner names neither a route nor a box"
        else some "a route end names no box"
      else some "label ids are not unique"
    else some "route ids are not unique"
  else some "box ids are not unique"

/-- The reader accepts exactly the well-formed dumps. -/
theorem wellFormedReason_eq_none_iff (d : LayoutDump) :
    wellFormedReason d = none ↔ WellFormed d := by
  unfold wellFormedReason
  by_cases n1 : ¬WF1 d
  · rw [dite_eq_right n1]
    exact ⟨(fun h => nomatch h), fun h => absurd h.1 n1⟩
  have h1 : WF1 d := Decidable.of_not_not n1
  rw [dite_eq_left h1]
  by_cases n2 : ¬WF2 d
  · rw [dite_eq_right n2]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.1 n2⟩
  have h2 : WF2 d := Decidable.of_not_not n2
  rw [dite_eq_left h2]
  by_cases n3 : ¬WF3 d
  · rw [dite_eq_right n3]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.1 n3⟩
  have h3 : WF3 d := Decidable.of_not_not n3
  rw [dite_eq_left h3]
  by_cases n4 : ¬WF4 d
  · rw [dite_eq_right n4]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.1 n4⟩
  have h4 : WF4 d := Decidable.of_not_not n4
  rw [dite_eq_left h4]
  by_cases n5 : ¬WF5 d
  · rw [dite_eq_right n5]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.2.1 n5⟩
  have h5 : WF5 d := Decidable.of_not_not n5
  rw [dite_eq_left h5]
  by_cases n6 : ¬WF6 d
  · rw [dite_eq_right n6]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.2.2.1 n6⟩
  have h6 : WF6 d := Decidable.of_not_not n6
  rw [dite_eq_left h6]
  by_cases n7 : ¬WF7 d
  · rw [dite_eq_right n7]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.2.2.2.1 n7⟩
  have h7 : WF7 d := Decidable.of_not_not n7
  rw [dite_eq_left h7]
  by_cases n8 : ¬WF8 d
  · rw [dite_eq_right n8]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.2.2.2.2.1 n8⟩
  have h8 : WF8 d := Decidable.of_not_not n8
  rw [dite_eq_left h8]
  by_cases n9 : ¬WF9 d
  · rw [dite_eq_right n9]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.2.2.2.2.2.1 n9⟩
  have h9 : WF9 d := Decidable.of_not_not n9
  rw [dite_eq_left h9]
  by_cases n10 : ¬WF10 d
  · rw [dite_eq_right n10]
    exact ⟨(fun h => nomatch h), fun h => absurd h.2.2.2.2.2.2.2.2.2 n10⟩
  have h10 : WF10 d := Decidable.of_not_not n10
  rw [dite_eq_left h10]
  exact ⟨fun _ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, fun _ => rfl⟩

/-- `i` lies strictly inside `o`: it keeps a positive distance from every side of `o`. -/
abbrev Rect.StrictInside (o i : Rect) : Prop :=
  o.x < i.x ∧ i.x + i.w < o.x + o.w ∧ o.y < i.y ∧ i.y + i.h < o.y + o.h

namespace Validator

/-- The canvas rectangle. -/
def canvasRect (d : LayoutDump) : Rect := ⟨0, 0, d.canvas.w, d.canvas.h⟩

/-- `p` lies on the boundary of `r`: inside the closed rectangle, on one of its sides. -/
abbrev onBoundary (p : Point) (r : Rect) : Prop :=
  r.x ≤ p.x ∧ p.x ≤ r.x + r.w ∧ r.y ≤ p.y ∧ p.y ≤ r.y + r.h ∧
    (p.x = r.x ∨ p.x = r.x + r.w ∨ p.y = r.y ∨ p.y = r.y + r.h)

/-- Clause 1: every box is contained in the canvas. -/
abbrev C1 (d : LayoutDump) : Prop := ∀ b ∈ d.boxes, (canvasRect d).Contained b.rect

/-- Clause 2: exclusive boxes with the same parent are disjoint. -/
abbrev C2 (d : LayoutDump) : Prop :=
  ∀ b ∈ d.boxes, ∀ c ∈ d.boxes, b.id ≠ c.id → b.exclusive = true → c.exclusive = true →
    b.parent = c.parent → Disjoint b.rect c.rect

/-- Clause 3: a box with a parent lies inside that parent. -/
abbrev C3 (d : LayoutDump) : Prop :=
  ∀ b ∈ d.boxes, b.parent ≠ "" → ∀ p : Box, d.box? b.parent = some p → p.rect.Contained b.rect

/-- Clause 4: every orthogonal route is orthogonal. -/
abbrev C4 (d : LayoutDump) : Prop :=
  ∀ r ∈ d.routes, r.orthogonal = true → Polyline.isOrthogonal r.points = true

/-- Clause 5: a route has a first point on the boundary of its `from` box and a last point
on the boundary of its `to` box. -/
abbrev C5 (d : LayoutDump) : Prop :=
  ∀ r ∈ d.routes, ∃ p q : Point, ∃ fb tb : Box,
    r.points.head? = some p ∧ r.points.getLast? = some q ∧
      d.box? r.fromId = some fb ∧ d.box? r.toId = some tb ∧
      onBoundary p fb.rect ∧ onBoundary q tb.rect

/-- Clause 6: a route does not meet the interior of an exclusive box outside its scope. -/
abbrev C6 (d : LayoutDump) : Prop :=
  ∀ r ∈ d.routes, ∀ b ∈ d.boxes, b.exclusive = true → b.id ∉ d.routeScope r →
    ¬ Polyline.hitsRect r.points b.rect

/-- Clause 7: a label does not overlap an exclusive box outside its owner scope. -/
abbrev C7 (d : LayoutDump) : Prop :=
  ∀ l ∈ d.labels, ∀ b ∈ d.boxes, b.exclusive = true → b.id ∉ d.labelOwnerAnc l →
    ¬ l.rect.meetsInterior b.rect

/-- Clause 8, condition 1: a group frame is disjoint from every other box that is neither
its ancestor nor its descendant. -/
abbrev C8a (d : LayoutDump) : Prop :=
  ∀ g ∈ d.boxes, g.role = "group" → ∀ b ∈ d.boxes, b.id ≠ g.id →
    g.id ∉ d.ancestors b.id → b.id ∉ d.ancestors g.id → Disjoint g.rect b.rect

/-- Clause 8, condition 2: a group frame is disjoint from every label or strictly contains
it. -/
abbrev C8b (d : LayoutDump) : Prop :=
  ∀ g ∈ d.boxes, g.role = "group" → ∀ l ∈ d.labels,
    Disjoint g.rect l.rect ∨ g.rect.StrictInside l.rect

/-- Clause 8: no group frame overlaps a foreign box or label. -/
abbrev C8 (d : LayoutDump) : Prop := C8a d ∧ C8b d

/-- Clause 1 as a Boolean test. -/
def c1 (d : LayoutDump) : Bool :=
  decide (∀ b ∈ d.boxes, (canvasRect d).Contained b.rect)

/-- Clause 2 as a Boolean test. -/
def c2 (d : LayoutDump) : Bool :=
  decide (∀ b ∈ d.boxes, ∀ c ∈ d.boxes, b.id ≠ c.id → b.exclusive = true →
    c.exclusive = true → b.parent = c.parent → Disjoint b.rect c.rect)

/-- The parent test of one box. -/
def parentOk (d : LayoutDump) (b : Box) : Bool :=
  b.parent == "" ||
    match d.box? b.parent with
    | some p => decide (p.rect.Contained b.rect)
    | none => true

/-- Clause 3 as a Boolean test. -/
def c3 (d : LayoutDump) : Bool := d.boxes.all (parentOk d)

/-- Clause 4 as a Boolean test. -/
def c4 (d : LayoutDump) : Bool :=
  decide (∀ r ∈ d.routes, r.orthogonal = true → Polyline.isOrthogonal r.points = true)

/-- The port test of one route. -/
def routePortsOk (d : LayoutDump) (r : Route) : Bool :=
  match r.points.head?, r.points.getLast?, d.box? r.fromId, d.box? r.toId with
  | some p, some q, some fb, some tb =>
    decide (onBoundary p fb.rect) && decide (onBoundary q tb.rect)
  | _, _, _, _ => false

/-- Clause 5 as a Boolean test. -/
def c5 (d : LayoutDump) : Bool := d.routes.all (routePortsOk d)

/-- The clearance test of one route against one box. -/
def routeClear (d : LayoutDump) (r : Route) (b : Box) : Bool :=
  !b.exclusive || (d.routeScope r).contains b.id || !(Polyline.hitsRectB r.points b.rect)

/-- Clause 6 as a Boolean test. -/
def c6 (d : LayoutDump) : Bool := d.routes.all (fun r => d.boxes.all (routeClear d r))

/-- The clearance test of one label against one box. -/
def labelClear (d : LayoutDump) (l : Label) (b : Box) : Bool :=
  !b.exclusive || (d.labelOwnerAnc l).contains b.id || !(decide (l.rect.meetsInterior b.rect))

/-- Clause 7 as a Boolean test. -/
def c7 (d : LayoutDump) : Bool := d.labels.all (fun l => d.boxes.all (labelClear d l))

/-- The frame test of one group candidate `g` against one box `b`. The rectangle test comes
first, so the ancestor walks run only for overlapping pairs. -/
def frameBoxClear (d : LayoutDump) (g b : Box) : Bool :=
  g.role != "group" || b.id == g.id || !(decide (g.rect.meetsInterior b.rect)) ||
    (d.ancestors b.id).contains g.id || (d.ancestors g.id).contains b.id

/-- The frame test of one group candidate `g` against one label `l`. -/
def frameLabelClear (g : Box) (l : Label) : Bool :=
  g.role != "group" || !(decide (g.rect.meetsInterior l.rect)) ||
    decide (g.rect.StrictInside l.rect)

/-- Clause 8 as a Boolean test. -/
def c8 (d : LayoutDump) : Bool :=
  d.boxes.all (fun g => d.boxes.all (frameBoxClear d g)) &&
    d.boxes.all (fun g => d.labels.all (frameLabelClear g))

theorem c1_iff (d : LayoutDump) : c1 d = true ↔ C1 d := decide_eq_true_iff

theorem c2_iff (d : LayoutDump) : c2 d = true ↔ C2 d := decide_eq_true_iff

theorem c3_iff (d : LayoutDump) : c3 d = true ↔ C3 d := by
  unfold c3 C3
  rw [List.all_eq_true]
  constructor
  · intro h b hb hne p hp
    have hb' := h b hb
    unfold parentOk at hb'
    rw [hp] at hb'
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hb'
    exact hb'.resolve_left hne
  · intro h b hb
    unfold parentOk
    by_cases hne : b.parent = ""
    · simp [hne]
    · cases hq : d.box? b.parent with
      | none => simp
      | some p =>
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
        exact Or.inr (h b hb hne p hq)

theorem c4_iff (d : LayoutDump) : c4 d = true ↔ C4 d := decide_eq_true_iff

theorem c5_iff (d : LayoutDump) : c5 d = true ↔ C5 d := by
  unfold c5 C5
  rw [List.all_eq_true]
  refine forall_congr' (fun r => imp_congr_right (fun _ => ?_))
  unfold routePortsOk
  constructor
  · intro h
    cases hp : r.points.head? with
    | none => simp [hp] at h
    | some p =>
      cases hq : r.points.getLast? with
      | none => simp [hp, hq] at h
      | some q =>
        cases hf : d.box? r.fromId with
        | none => simp [hp, hq, hf] at h
        | some fb =>
          cases ht : d.box? r.toId with
          | none => simp [hp, hq, hf, ht] at h
          | some tb =>
            simp only [hp, hq, hf, ht, Bool.and_eq_true, decide_eq_true_eq] at h
            exact ⟨p, q, fb, tb, rfl, rfl, rfl, rfl, h.1, h.2⟩
  · rintro ⟨p, q, fb, tb, hp, hq, hf, ht, hpb, hqb⟩
    rw [hp, hq, hf, ht]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hpb, hqb⟩

theorem c6_iff (d : LayoutDump) : c6 d = true ↔ C6 d := by
  unfold c6 C6 routeClear
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem,
    Polyline.hitsRectB_eq_false_iff]
  constructor
  · intro h r hr b hb hex hnot
    rcases h r hr b hb with (h1 | h2) | h3
    · exact absurd hex (by simp [h1])
    · exact absurd h2 hnot
    · exact h3
  · intro h r hr b hb
    by_cases hex : b.exclusive = true
    · by_cases hmem : b.id ∈ d.routeScope r
      · exact Or.inl (Or.inr hmem)
      · exact Or.inr (h r hr b hb hex hmem)
    · exact Or.inl (Or.inl (by simpa using hex))

theorem c7_iff (d : LayoutDump) : c7 d = true ↔ C7 d := by
  unfold c7 C7 labelClear
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem,
    decide_eq_false_iff_not]
  constructor
  · intro h l hl b hb hex hnot
    rcases h l hl b hb with (h1 | h2) | h3
    · exact absurd hex (by simp [h1])
    · exact absurd h2 hnot
    · exact h3
  · intro h l hl b hb
    by_cases hex : b.exclusive = true
    · by_cases hmem : b.id ∈ d.labelOwnerAnc l
      · exact Or.inl (Or.inr hmem)
      · exact Or.inr (h l hl b hb hex hmem)
    · exact Or.inl (Or.inl (by simpa using hex))

theorem c8_iff (d : LayoutDump) : c8 d = true ↔ C8 d := by
  unfold c8 C8 C8a C8b frameBoxClear frameLabelClear
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq,
    decide_eq_false_iff_not, Disjoint]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg hr b hb hne hn1 hn2 => ?_, fun g hg hr l hl => ?_⟩
    · rcases (h1 g hg b hb) with ((((h | h) | h) | h) | h)
      · exact absurd hr h
      · exact absurd h hne
      · exact h
      · exact absurd h hn1
      · exact absurd h hn2
    · rcases (h2 g hg l hl) with ((h | h) | h)
      · exact absurd hr h
      · exact Or.inl h
      · exact Or.inr h
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg b hb => ?_, fun g hg l hl => ?_⟩
    · by_cases hr : g.role = "group"
      · by_cases hne : b.id = g.id
        · exact Or.inl (Or.inl (Or.inl (Or.inr hne)))
        · by_cases hn1 : g.id ∈ d.ancestors b.id
          · exact Or.inl (Or.inr hn1)
          · by_cases hn2 : b.id ∈ d.ancestors g.id
            · exact Or.inr hn2
            · exact Or.inl (Or.inl (Or.inr (h1 g hg hr b hb hne hn1 hn2)))
      · exact Or.inl (Or.inl (Or.inl (Or.inl hr)))
    · by_cases hr : g.role = "group"
      · rcases h2 g hg hr l hl with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl hr)

end Validator

/-- The conjunction of the eight clause predicates. -/
abbrev HardConstraints (d : LayoutDump) : Prop :=
  Validator.C1 d ∧ Validator.C2 d ∧ Validator.C3 d ∧ Validator.C4 d ∧ Validator.C5 d ∧
    Validator.C6 d ∧ Validator.C7 d ∧ Validator.C8 d

namespace Validator

/-- Every clause passes. -/
def check (d : LayoutDump) : Bool :=
  c1 d && c2 d && c3 d && c4 d && c5 d && c6 d && c7 d && c8 d

/-- The fixed clause ids, in clause order. -/
def clauseIds : List String :=
  ["canvas", "exclusive-siblings", "parent", "orthogonal", "ports", "route-clearance",
   "label-clearance", "frame-clearance"]

/-- The fixed clause messages, in clause order. -/
def clauseMessages : List String :=
  ["box outside canvas", "exclusive sibling boxes overlap", "box outside its parent",
   "orthogonal route has a diagonal segment", "route end is off its box boundary",
   "route crosses an exclusive box", "label overlaps an exclusive box",
   "group frame overlaps a foreign box or label"]

/-- The Boolean tests, in clause order. -/
def clauseTests (d : LayoutDump) : List Bool :=
  [c1 d, c2 d, c3 d, c4 d, c5 d, c6 d, c7 d, c8 d]

/-- The first failing clause, as an index, or none. -/
def firstFailure (d : LayoutDump) : Option Nat :=
  match c1 d, c2 d, c3 d, c4 d, c5 d, c6 d, c7 d, c8 d with
  | false, _, _, _, _, _, _, _ => some 0
  | _, false, _, _, _, _, _, _ => some 1
  | _, _, false, _, _, _, _, _ => some 2
  | _, _, _, false, _, _, _, _ => some 3
  | _, _, _, _, false, _, _, _ => some 4
  | _, _, _, _, _, false, _, _ => some 5
  | _, _, _, _, _, _, false, _ => some 6
  | _, _, _, _, _, _, _, false => some 7
  | true, true, true, true, true, true, true, true => none

/-- The id and message of a clause index. -/
def failureOf (i : Nat) : Option (String × String) :=
  match clauseIds[i]?, clauseMessages[i]? with
  | some c, some m => some (c, m)
  | _, _ => none

/-- The validation result: none when every clause passes, else the first failing clause's
id and message. -/
def validate (d : LayoutDump) : Option (String × String) :=
  match firstFailure d with
  | none => none
  | some i => failureOf i

/-- Eight `&&` values are true exactly when the eight right-nested propositions hold. -/
theorem and8 (a b c d e f g h : Bool) :
    (a && b && c && d && e && f && g && h) = true ↔
      (a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true ∧ g = true ∧
        h = true) := by
  simp only [Bool.and_eq_true]
  constructor
  · intro ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩, hh⟩; exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  · intro ⟨ha, hb, hc, hd, he, hf, hg, hh⟩; exact ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩, hh⟩

/-- `check` is exactly `HardConstraints`. -/
theorem check_iff (d : LayoutDump) : check d = true ↔ HardConstraints d := by
  unfold check
  rw [and8, c1_iff, c2_iff, c3_iff, c4_iff, c5_iff, c6_iff, c7_iff, c8_iff]

/-- `Validator.sound`: on a well-formed dump, a passing check implies the hard
constraints. The check is exact on every dump, so the well-formedness hypothesis is not
used by the proof; it records the input conditions under which the checked rectangle and
polyline operations never fail. -/
theorem sound (d : LayoutDump) (_wf : WellFormed d) (h : check d = true) :
    HardConstraints d :=
  (check_iff d).mp h

/-- `validate` returns none exactly when the dump satisfies every hard constraint. -/
theorem validate_none_iff (d : LayoutDump) : validate d = none ↔ HardConstraints d := by
  rw [← check_iff]
  unfold validate firstFailure check
  cases h1 : c1 d <;> cases h2 : c2 d <;> cases h3 : c3 d <;> cases h4 : c4 d <;>
    cases h5 : c5 d <;> cases h6 : c6 d <;> cases h7 : c7 d <;> cases h8 : c8 d <;>
    simp_all [failureOf, clauseIds, clauseMessages]

end Validator
