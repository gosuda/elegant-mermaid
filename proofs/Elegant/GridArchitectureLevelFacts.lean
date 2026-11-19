import Elegant.GridArchitectureClearanceFacts
import Elegant.GridArchitectureCountFacts

set_option autoImplicit false

namespace Elegant.Grid.Architecture

private theorem getD_set_self {α : Type} (items : List α) (i : Nat) (value fallback : α)
    (bound : i < items.length) : (items.set i value).getD i fallback = value := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_set_self bound,Option.getD_some]

private theorem getD_set_ne {α : Type} (items : List α) (i j : Nat) (value fallback : α)
    (different : i ≠ j) : (items.set i value).getD j fallback = items.getD j fallback := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_set_ne different]

private theorem span_contains_trans (a b c : Span) (ab : a.contains b) (bc : b.contains c) :
    a.contains c := by
  unfold Span.contains at ab bc ⊢
  omega

/-- Bounds contain every visited unit, including queued units. -/
def BoundsInvariant (l : Level) : Prop :=
  ∀ i, i < l.placed.length → l.placed.getD i false = true →
    l.bounds.contains (l.absolute.getD i default)

/-- Parallel arrays carry the unit's actual translated rectangle. -/
def CoordinateInvariant (p : Params) (l : Level) : Prop :=
  l.absolute.length = l.placed.length ∧ l.cells.length = l.placed.length ∧
    ∀ i, i < l.placed.length → l.placed.getD i false = true →
      l.absolute.getD i default = (l.rects.getD i default).shift
        ((l.cells.getD i default).x*p.pitchX) ((l.cells.getD i default).y*p.pitchY)

theorem put_bounds_invariant (p : Params) (l : Level) (v : Nat) (c : Cell)
    (bounds : BoundsInvariant l) (lengths : l.absolute.length = l.placed.length)
    (valid : v < l.placed.length) : BoundsInvariant (put p l v c) := by
  intro i hi marked
  simp only [put,List.length_set] at hi marked ⊢
  by_cases same : v = i
  · subst i
    rw [getD_set_self l.absolute v _ default (by omega)]
    exact union_contains_right _ _
  · rw [getD_set_ne l.placed v i true false same] at marked
    rw [getD_set_ne l.absolute v i _ default same]
    exact span_contains_trans _ _ _ (union_contains_left _ _) (bounds i hi marked)

theorem put_coordinate_invariant (p : Params) (l : Level) (v : Nat) (c : Cell)
    (coordinates : CoordinateInvariant p l) (valid : v < l.placed.length) :
    CoordinateInvariant p (put p l v c) := by
  rcases coordinates with ⟨absoluteLength,cellLength,coordinates⟩
  constructor
  · simpa only [put,List.length_set] using absoluteLength
  constructor
  · simpa only [put,List.length_set] using cellLength
  intro i hi marked
  simp only [put,List.length_set] at hi marked ⊢
  by_cases same : v = i
  · subst i
    rw [getD_set_self l.absolute v _ default (by omega),getD_set_self l.cells v c default (by omega)]
  · rw [getD_set_ne l.placed v i true false same] at marked
    rw [getD_set_ne l.absolute v i _ default same,getD_set_ne l.cells v i c default same]
    exact coordinates i hi marked

theorem boundsInvariant_entry (l : Level) (bounds : BoundsInvariant l)
    (entry : Bool × Span) (member : entry ∈ l.placed.zip l.absolute) (marked : entry.1 = true) :
    l.bounds.contains entry.2 := by
  rcases List.mem_iff_getElem?.mp member with ⟨i,lookup⟩
  have pair := List.getElem?_zip_eq_some.mp lookup
  have bound := (List.getElem?_eq_some_iff.mp pair.1).choose
  have markedD : l.placed.getD i false = true := by
    simp only [List.getD_eq_getElem?_getD,pair.1,Option.getD_some,marked]
  have inside := bounds i bound markedD
  simpa only [List.getD_eq_getElem?_getD,pair.2,Option.getD_some] using inside

def AnchorsInvariant (p : Params) (l : Level) : Prop :=
  ∀ i, i < l.placed.length → ContainsAnchor p (l.rects.getD i default)

theorem coordinate_entry_positive (p : Params) (l : Level) (px : 0 < p.pitchX)
    (coordinates : CoordinateInvariant p l) (anchors : AnchorsInvariant p l)
    (entry : Bool × Span) (member : entry ∈ l.placed.zip l.absolute) (marked : entry.1 = true) :
    entry.2.x0 < entry.2.x1 := by
  rcases List.mem_iff_getElem?.mp member with ⟨i,lookup⟩
  have pair := List.getElem?_zip_eq_some.mp lookup
  have bound := (List.getElem?_eq_some_iff.mp pair.1).choose
  have markedD : l.placed.getD i false = true := by
    simp only [List.getD_eq_getElem?_getD,pair.1,Option.getD_some,marked]
  have actual := coordinates.2.2 i bound markedD
  have anchor := anchors i bound
  have absolute : l.absolute.getD i default = entry.2 := by
    simp only [List.getD_eq_getElem?_getD,pair.2,Option.getD_some]
  rw [absolute] at actual
  rw [actual]
  simp only [Span.shift]
  unfold ContainsAnchor at anchor
  omega

theorem seed_clear (p : Params) (l : Level) (v : Nat) (px : 0 < p.pitchX)
    (bounds : BoundsInvariant l) (coordinates : CoordinateInvariant p l)
    (anchors : AnchorsInvariant p l) :
    clear p l v (seedCell p l v) = true := by
  unfold clear
  simp only [Bool.not_eq_true',List.any_eq_false]
  intro entry member
  cases marked : entry.1 with
  | false => simp
  | true =>
    have contained := boundsInvariant_entry l bounds entry member marked
    have positive := coordinate_entry_positive p l px coordinates anchors entry member marked
    have nonempty : l.bounds ≠ emptySpan := by
      intro empty
      rw [empty] at contained
      unfold Span.contains emptySpan at contained
      dsimp only at contained
      omega
    have right : entry.2.x1 ≤ l.bounds.x1 := contained.2.1
    have avoids := seed_avoids_placed p l v entry.2 px nonempty right
    simp only [Bool.true_and]
    rw [avoids]
    decide

private theorem lookup_of_getD {α : Type} (items : List α) (i : Nat) (fallback value : α)
    (bound : i < items.length) (h : items.getD i fallback = value) : items[i]? = some value := by
  have lookup := List.getElem?_eq_getElem bound
  rw [List.getD_eq_getElem?_getD,lookup] at h
  rw [lookup]
  exact congrArg some h

theorem visited_entry (p : Params) (l : Level) (coordinates : CoordinateInvariant p l)
    (i : Nat) (bound : i < l.placed.length) (marked : l.placed.getD i false = true) :
    (true,(l.rects.getD i default).shift ((l.cells.getD i default).x*p.pitchX)
      ((l.cells.getD i default).y*p.pitchY)) ∈ l.placed.zip l.absolute := by
  have flags := lookup_of_getD l.placed i false true bound marked
  have actual := coordinates.2.2 i bound marked
  have rectLookup : l.absolute[i]? = some (l.absolute.getD i default) :=
    lookup_of_getD l.absolute i default _ (by rw [coordinates.1]; exact bound) rfl
  have member : (true,l.absolute.getD i default) ∈ l.placed.zip l.absolute :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨flags,rectLookup⟩)
  simpa only [actual] using member

def CellsUnique (l : Level) : Prop :=
  ∀ i j, i < l.placed.length → j < l.placed.length →
    l.placed.getD i false = true → l.placed.getD j false = true →
    i ≠ j → l.cells.getD i default ≠ l.cells.getD j default

theorem put_cells_unique (p : Params) (l : Level) (v : Nat) (c : Cell)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (coordinates : CoordinateInvariant p l)
    (anchors : AnchorsInvariant p l) (unique : CellsUnique l)
    (valid : v < l.placed.length) (clearance : clear p l v c = true) :
    CellsUnique (put p l v c) := by
  intro i j hi hj markedI markedJ distinct
  simp only [put,List.length_set] at hi hj markedI markedJ ⊢
  have fresh : ∀ k, k < l.placed.length → l.placed.getD k false = true →
      c ≠ l.cells.getD k default := by
    intro k hk marked
    exact clear_anchor_distinct p l v c (l.cells.getD k default) (l.rects.getD k default)
      px py (anchors v valid) (anchors k hk) (visited_entry p l coordinates k hk marked) clearance
  by_cases sameI : v = i
  · subst i
    have sameJ : v ≠ j := distinct
    rw [getD_set_self l.cells v c default (by rw [coordinates.2.1]; exact valid),
      getD_set_ne l.cells v j c default sameJ]
    rw [getD_set_ne l.placed v j true false sameJ] at markedJ
    exact fresh j hj markedJ
  · by_cases sameJ : v = j
    · subst j
      rw [getD_set_ne l.cells v i c default sameI,
        getD_set_self l.cells v c default (by rw [coordinates.2.1]; exact valid)]
      rw [getD_set_ne l.placed v i true false sameI] at markedI
      exact Ne.symm (fresh i hi markedI)
    · rw [getD_set_ne l.cells v i c default sameI,getD_set_ne l.cells v j c default sameJ]
      rw [getD_set_ne l.placed v i true false sameI] at markedI
      rw [getD_set_ne l.placed v j true false sameJ] at markedJ
      exact unique i j hi hj markedI markedJ distinct

def LevelInvariant (p : Params) (l : Level) : Prop :=
  BoundsInvariant l ∧ CoordinateInvariant p l ∧ AnchorsInvariant p l ∧ CellsUnique l

theorem put_level_invariant (p : Params) (l : Level) (v : Nat) (c : Cell)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (valid : v < l.placed.length)
    (invariant : LevelInvariant p l) (clearance : clear p l v c = true) :
    LevelInvariant p (put p l v c) := by
  rcases invariant with ⟨bounds,coordinates,anchors,unique⟩
  refine ⟨put_bounds_invariant p l v c bounds coordinates.1 valid,
    put_coordinate_invariant p l v c coordinates valid,?_,
    put_cells_unique p l v c px py coordinates anchors unique valid clearance⟩
  intro i hi
  simpa only [put] using anchors i (by simpa only [put,List.length_set] using hi)

theorem expandOne_level_invariant (p : Params) (u : Nat) (state : Level × List Nat) (e : Edge)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p state.1)
    (ha : e.a < state.1.placed.length) (hb : e.b < state.1.placed.length) :
    LevelInvariant p (expandOne p u state e).1 := by
  unfold expandOne
  split
  · exact invariant
  · split <;> dsimp only <;> split
    all_goals first
      | exact invariant
      | apply put_level_invariant p _ _ _ px py
        · first | exact ha | exact hb
        · exact invariant
        · apply choose_clear_of_seed
          exact seed_clear p _ _ px invariant.1 invariant.2.1 invariant.2.2.1

theorem expand_level_invariant (p : Params) (u : Nat) (l : Level) (queue : List Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p l)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    LevelInvariant p (expand p u l queue).1 := by
  have fold : ∀ (es : List Edge) (state : Level × List Nat),
      LevelInvariant p state.1 →
      (∀ e ∈ es, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) →
      LevelInvariant p (es.foldl (expandOne p u) state).1 := by
    intro es
    induction es with
    | nil => intro state h _; exact h
    | cons e rest ih =>
      intro state h bounds
      simp only [List.foldl_cons]
      apply ih
      · exact expandOne_level_invariant p u state e px py h
          (bounds e (by simp)).1 (bounds e (by simp)).2
      · intro edge he
        rw [expandOne_length]
        exact bounds edge (by simp [he])
  exact fold l.edges (l,queue) invariant valid

theorem drain_level_invariant (p : Params) (fuel : Nat) (l : Level) (queue : List Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p l)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    LevelInvariant p (drain p fuel l queue).1 := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> exact invariant
  | succ fuel ih =>
    cases queue with
    | nil => exact invariant
    | cons u rest =>
      simp only [drain]
      apply ih
      · exact expand_level_invariant p u l rest px py invariant valid
      · rw [expand_edges,expand_placed_length]
        exact valid

theorem visit_level_invariant (p : Params) (state : Level × Nat) (first : Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p state.1)
    (bound : first < state.1.placed.length)
    (valid : ∀ e ∈ state.1.edges, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) :
    LevelInvariant p (visit p state first).1 := by
  unfold visit
  split
  · exact invariant
  · apply drain_level_invariant p _ _ _ px py
    · exact put_level_invariant p _ first _ px py bound invariant
        (seed_clear p _ first px invariant.1 invariant.2.1 invariant.2.2.1)
    · simpa only [put,List.length_set] using valid

theorem visit_fold_level_invariant (p : Params) (indices : List Nat) (state : Level × Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p state.1)
    (bounds : ∀ i ∈ indices, i < state.1.placed.length)
    (valid : ∀ e ∈ state.1.edges, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) :
    LevelInvariant p (indices.foldl (visit p) state).1 := by
  induction indices generalizing state with
  | nil => exact invariant
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact visit_level_invariant p state first px py invariant (bounds first (by simp)) valid
    · intro i hi
      rw [visit_placed_length]
      exact bounds i (by simp [hi])
    · rw [visit_edges,visit_placed_length]
      exact valid

theorem arrange_level_invariant (p : Params) (fuel : Nat) (l : Level)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p l)
    (lengths : l.placed.length = l.units.length)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    LevelInvariant p (arrange p fuel l).1 := by
  change LevelInvariant p ((List.range l.units.length).foldl (visit p) (l,fuel)).1
  apply visit_fold_level_invariant p _ _ px py invariant
  · intro i hi
    have bound := List.mem_range.mp hi
    change i < l.placed.length
    omega
  · exact valid

theorem initial_level_invariant (input : Input) (p : Params) (relative : List Span) (parent : Int)
    (anchors : AnchorsInvariant p (levelOf input p relative parent)) :
    LevelInvariant p (levelOf input p relative parent) := by
  have unmarked : ∀ i, (levelOf input p relative parent).placed.getD i false = false := by
    intro i
    simp only [levelOf,List.getD_eq_getElem?_getD,List.getElem?_replicate]
    split <;> rfl
  refine ⟨?_,?_,anchors,?_⟩
  · intro i _ marked
    rw [unmarked] at marked
    contradiction
  · refine ⟨?_,?_,?_⟩
    · simp only [levelOf,List.length_replicate]
    · simp only [levelOf,List.length_replicate]
    · intro i _ marked
      rw [unmarked] at marked
      contradiction
  · intro i j _ _ marked _ _
    rw [unmarked] at marked
    contradiction

theorem fold_union_contains_initial (rects : List Span) (initial : Span) :
    (rects.foldl Span.union initial).contains initial := by
  induction rects generalizing initial with
  | nil => simp [Span.contains]
  | cons rect rest ih =>
    simp only [List.foldl_cons]
    exact span_contains_trans _ _ _ (ih (initial.union rect)) (union_contains_left _ _)

theorem fold_union_contains_member (rects : List Span) (initial : Span) (r : Span)
    (member : r ∈ rects) : (rects.foldl Span.union initial).contains r := by
  induction rects generalizing initial with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with equal | tail
    · subst r
      exact span_contains_trans _ _ _ (fold_union_contains_initial rest (initial.union first))
        (union_contains_right _ _)
    · exact ih _ tail

theorem arch_group_frame_contains_all_members (p : FrameParams) (g : Group) (members : List Span)
    (padding : 0 ≤ p.padding) (line : 0 ≤ p.lineHeight) :
    ∀ member ∈ members, (frameOf p g (members.foldl Span.union emptySpan)).contains member := by
  intro member h
  exact span_contains_trans _ _ _ (frameOf_contains_inner p g _ padding line)
    (fold_union_contains_member members emptySpan member h)

theorem contains_preserves_anchor (p : Params) (outer inner : Span)
    (contains : outer.contains inner) (anchor : ContainsAnchor p inner) :
    ContainsAnchor p outer := by
  unfold Span.contains at contains
  unfold ContainsAnchor at anchor ⊢
  omega

theorem frame_contains_anchor (p : Params) (fp : FrameParams) (g : Group) (members : List Span)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (member : Span) (present : member ∈ members) (anchor : ContainsAnchor p member) :
    ContainsAnchor p (frameOf fp g (members.foldl Span.union emptySpan)) := by
  exact contains_preserves_anchor p _ member
    (arch_group_frame_contains_all_members fp g members padding line member present) anchor

def RectsSeparated (l : Level) : Prop :=
  ∀ i j, i < l.placed.length → j < l.placed.length →
    l.placed.getD i false = true → l.placed.getD j false = true →
    i ≠ j → (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false

private theorem overlaps_symm (a b : Span) : a.overlaps b = b.overlaps a := by
  unfold Span.overlaps
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> exact ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

theorem put_rects_separated (p : Params) (l : Level) (v : Nat) (c : Cell)
    (coordinates : CoordinateInvariant p l) (separated : RectsSeparated l)
    (valid : v < l.placed.length) (clearance : clear p l v c = true) :
    RectsSeparated (put p l v c) := by
  have absoluteBound : v < l.absolute.length := by
    rw [coordinates.1]
    exact valid
  have avoids : ∀ k, k < l.placed.length → l.placed.getD k false = true →
      ((l.rects.getD v default).shift (c.x*p.pitchX) (c.y*p.pitchY)).overlaps
        (l.absolute.getD k default) = false := by
    intro k hk marked
    have entry := visited_entry p l coordinates k hk marked
    rw [← coordinates.2.2 k hk marked] at entry
    exact clear_avoids_placed p l v c clearance _ entry rfl
  intro i j hi hj markedI markedJ different
  simp only [put,List.length_set] at hi hj markedI markedJ ⊢
  by_cases sameI : v = i
  · subst i
    rw [getD_set_self l.absolute v _ default absoluteBound,
      getD_set_ne l.absolute v j _ default different]
    rw [getD_set_ne l.placed v j true false different] at markedJ
    exact avoids j hj markedJ
  · by_cases sameJ : v = j
    · subst j
      rw [getD_set_ne l.absolute v i _ default sameI,
        getD_set_self l.absolute v _ default absoluteBound]
      rw [getD_set_ne l.placed v i true false sameI] at markedI
      rw [overlaps_symm]
      exact avoids i hi markedI
    · rw [getD_set_ne l.absolute v i _ default sameI,
        getD_set_ne l.absolute v j _ default sameJ]
      rw [getD_set_ne l.placed v i true false sameI] at markedI
      rw [getD_set_ne l.placed v j true false sameJ] at markedJ
      exact separated i j hi hj markedI markedJ different

theorem expandOne_rects_separated (p : Params) (u : Nat) (state : Level × List Nat)
    (e : Edge) (px : 0 < p.pitchX) (invariant : LevelInvariant p state.1)
    (separated : RectsSeparated state.1)
    (ha : e.a < state.1.placed.length) (hb : e.b < state.1.placed.length) :
    RectsSeparated (expandOne p u state e).1 := by
  unfold expandOne
  split
  · exact separated
  · split <;> dsimp only <;> split
    all_goals first
      | exact separated
      | apply put_rects_separated p _ _ _ invariant.2.1 separated
        · first | exact ha | exact hb
        · apply choose_clear_of_seed
          exact seed_clear p _ _ px invariant.1 invariant.2.1 invariant.2.2.1

theorem expand_rects_separated (p : Params) (u : Nat) (l : Level) (queue : List Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p l)
    (separated : RectsSeparated l)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    RectsSeparated (expand p u l queue).1 := by
  have fold : ∀ (es : List Edge) (state : Level × List Nat),
      LevelInvariant p state.1 → RectsSeparated state.1 →
      (∀ e ∈ es, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) →
      RectsSeparated (es.foldl (expandOne p u) state).1 := by
    intro es
    induction es with
    | nil => intro state _ h _; exact h
    | cons e rest ih =>
      intro state h separated bounds
      simp only [List.foldl_cons]
      apply ih
      · exact expandOne_level_invariant p u state e px py h
          (bounds e (by simp)).1 (bounds e (by simp)).2
      · exact expandOne_rects_separated p u state e px h separated
          (bounds e (by simp)).1 (bounds e (by simp)).2
      · intro edge he
        rw [expandOne_length]
        exact bounds edge (by simp [he])
  exact fold l.edges (l,queue) invariant separated valid

theorem drain_rects_separated (p : Params) (fuel : Nat) (l : Level) (queue : List Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p l)
    (separated : RectsSeparated l)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    RectsSeparated (drain p fuel l queue).1 := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> exact separated
  | succ fuel ih =>
    cases queue with
    | nil => exact separated
    | cons u rest =>
      simp only [drain]
      apply ih
      · exact expand_level_invariant p u l rest px py invariant valid
      · exact expand_rects_separated p u l rest px py invariant separated valid
      · rw [expand_edges,expand_placed_length]
        exact valid

theorem visit_rects_separated (p : Params) (state : Level × Nat) (first : Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p state.1)
    (separated : RectsSeparated state.1) (bound : first < state.1.placed.length)
    (valid : ∀ e ∈ state.1.edges, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) :
    RectsSeparated (visit p state first).1 := by
  unfold visit
  split
  · exact separated
  · have clearance := seed_clear p state.1 first px
      invariant.1 invariant.2.1 invariant.2.2.1
    apply drain_rects_separated p _ _ _ px py
    · exact put_level_invariant p _ first _ px py bound invariant clearance
    · exact put_rects_separated p _ first _ invariant.2.1 separated bound clearance
    · simpa only [put,List.length_set] using valid

theorem arrange_rects_separated (p : Params) (fuel : Nat) (l : Level)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY) (invariant : LevelInvariant p l)
    (separated : RectsSeparated l) (lengths : l.placed.length = l.units.length)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    RectsSeparated (arrange p fuel l).1 := by
  have fold : ∀ (indices : List Nat) (state : Level × Nat),
      LevelInvariant p state.1 → RectsSeparated state.1 →
      (∀ i ∈ indices, i < state.1.placed.length) →
      (∀ e ∈ state.1.edges, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) →
      RectsSeparated (indices.foldl (visit p) state).1 := by
    intro indices
    induction indices with
    | nil => intro state _ h _ _; exact h
    | cons first rest ih =>
      intro state h separated bounds edges
      simp only [List.foldl_cons]
      apply ih
      · exact visit_level_invariant p state first px py h (bounds first (by simp)) edges
      · exact visit_rects_separated p state first px py h separated (bounds first (by simp)) edges
      · intro i hi
        rw [visit_placed_length]
        exact bounds i (by simp [hi])
      · rw [visit_edges,visit_placed_length]
        exact edges
  apply fold _ (l,fuel) invariant separated
  · intro i hi
    have bound := List.mem_range.mp hi
    change i < l.placed.length
    omega
  · exact valid

theorem expand_units (p : Params) (u : Nat) (l : Level) (queue : List Nat) :
    (expand p u l queue).1.units = l.units := by
  have step : ∀ state e, (expandOne p u state e).1.units = state.1.units := by
    intro state e
    unfold expandOne
    split
    · rfl
    · split <;> dsimp only <;> split <;> rfl
  have fold : ∀ (edges : List Edge) (state : Level × List Nat),
      (edges.foldl (expandOne p u) state).1.units = state.1.units := by
    intro edges
    induction edges with
    | nil => intro state; rfl
    | cons edge rest ih =>
      intro state
      rw [List.foldl_cons,ih,step]
  exact fold l.edges (l,queue)

theorem drain_units (p : Params) (fuel : Nat) (l : Level) (queue : List Nat) :
    (drain p fuel l queue).1.units = l.units := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> rfl
  | succ fuel ih =>
    cases queue with
    | nil => rfl
    | cons u rest => simp only [drain]; rw [ih,expand_units]

theorem visit_units (p : Params) (state : Level × Nat) (first : Nat) :
    (visit p state first).1.units = state.1.units := by
  unfold visit
  split
  · rfl
  · rw [drain_units]
    rfl

theorem arrange_units (p : Params) (fuel : Nat) (l : Level) :
    (arrange p fuel l).1.units = l.units := by
  have fold : ∀ (indices : List Nat) (state : Level × Nat),
      (indices.foldl (visit p) state).1.units = state.1.units := by
    intro indices
    induction indices with
    | nil => intro state; rfl
    | cons first rest ih =>
      intro state
      rw [List.foldl_cons,ih,visit_units]
  exact fold (List.range l.units.length) (l,fuel)

end Elegant.Grid.Architecture
