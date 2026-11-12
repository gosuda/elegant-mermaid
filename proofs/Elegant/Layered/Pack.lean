import ElegantGeometry.Basic
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.Layered.Pack

structure Item where
  width : Int
  height : Int
  area : Int
  deriving DecidableEq, Repr

structure State where
  x : Int := 0
  y : Int := 0
  rowHeight : Int := 0
  width : Int := 0
  height : Int := 0
  occupied : Bool := false
  boxes : List Rect := []
  deriving DecidableEq, Repr

def append (target gap : Int) (s : State) (item : Item) : Except LayoutError State := do
  if item.width < 0 ∨ item.height < 0 then throw .domain
  let wrap := s.occupied && decide (target < s.x + gap + item.width)
  let x := if wrap then 0 else if s.occupied then s.x + gap else 0
  let y := if wrap then s.y + s.rowHeight + gap else s.y
  let rowHeight := if wrap then item.height else max s.rowHeight item.height
  let right := x + item.width
  let bottom := y + item.height
  if I32_MAX < right ∨ I32_MAX < bottom then throw .overflow
  pure { x := right
         y := y
         rowHeight := rowHeight
         width := max s.width right
         height := max s.height bottom
         occupied := true
         boxes := s.boxes ++ [⟨x, y, item.width, item.height⟩] }

def targetWidth (maxWidth : Nat) (aspectNum aspectDen : Int) (items : List Item) :
    Except LayoutError Int := do
  if maxWidth > 0 then pure (maxWidth : Int)
  else
    if aspectNum < 0 ∨ aspectDen ≤ 0 ∨ items.any (fun i => i.area < 0) then throw .domain
    let area := items.foldl (fun n i => n + i.area) 0
    let product := area * aspectNum
    if 9223372036854775807 < product then throw .overflow
    Rect.isqrt (Int.fdiv product aspectDen)

def pack (maxWidth : Nat) (gap margin aspectNum aspectDen : Int) (items : List Item) :
    Except LayoutError State := do
  if gap < 0 ∨ margin < 0 then throw .domain
  let target ← targetWidth maxWidth aspectNum aspectDen items
  let result ← items.foldlM (append target gap) {}
  let width := result.width + 2 * margin
  let height := result.height + 2 * margin
  if I32_MAX < width ∨ I32_MAX < height then throw .overflow
  pure { result with
    width := width
    height := height
    boxes := result.boxes.map (fun r => { r with x := r.x + margin, y := r.y + margin }) }

def Inv (s : State) : Prop :=
  0 ≤ s.x ∧ 0 ≤ s.y ∧ 0 ≤ s.rowHeight ∧ 0 ≤ s.width ∧ 0 ≤ s.height ∧
  (s.occupied = false → s.x = 0) ∧
  s.boxes.Pairwise Disjoint ∧
  ∀ r ∈ s.boxes, 0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧
    r.x + r.w ≤ s.width ∧ r.y + r.h ≤ s.height ∧
    r.y + r.h ≤ s.y + s.rowHeight ∧
    (r.y + r.h ≤ s.y ∨ r.x + r.w ≤ s.x)

theorem append_inv {target gap : Int} {s out : State} {item : Item}
    (hg : 0 ≤ gap) (hs : Inv s) (h : append target gap s item = .ok out) : Inv out := by
  unfold append at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp at h
  all_goals try contradiction
  all_goals subst out
  all_goals rcases hs with ⟨hx, hy, hr, hw, hh, hempty, hp, hb⟩
  all_goals have he : s.occupied ≠ true → s.x = 0 := fun hn => hempty (by cases hbool : s.occupied <;> simp_all)
  all_goals simp only [Inv, List.pairwise_append, List.pairwise_singleton,
    List.mem_append, List.mem_singleton, forall_eq, true_and]
  all_goals repeat' apply And.intro
  all_goals try omega
  all_goals try exact hp
  all_goals try { intro hfalse; contradiction }
  all_goals try have hx0 : s.x = 0 := he (by assumption)
  all_goals try solve
    | intro r hin
      have := hb r hin
      unfold Disjoint Rect.meetsInterior
      dsimp
      omega
  all_goals intro r hin
  all_goals rcases hin with hin | hin
  all_goals try
    have := hb r hin
    rcases this with ⟨_, _, _, _, _, _, _, _⟩
    repeat' apply And.intro
    all_goals omega
  all_goals subst r <;> simp only
  all_goals repeat' apply And.intro
  all_goals omega

theorem fold_inv {target gap : Int} (hg : 0 ≤ gap) (items : List Item)
    {s out : State} (hs : Inv s)
    (h : items.foldlM (append target gap) s = .ok out) : Inv out := by
  induction items generalizing s with
  | nil => simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst out; exact hs
  | cons item items ih =>
    simp only [List.foldlM_cons] at h
    cases ha : append target gap s item with
    | error e => simp [ha, bind, Except.bind] at h
    | ok next =>
      simp [ha, bind, Except.bind] at h
      exact ih (append_inv hg hs ha) h

theorem pack_bounds {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Item} {out : State}
    (h : pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    out.boxes.Pairwise Disjoint ∧
    ∀ r ∈ out.boxes, margin ≤ r.x ∧ margin ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧
      r.x + r.w + margin ≤ out.width ∧ r.y + r.h + margin ≤ out.height := by
  unfold pack at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i hn
    cases ht : targetWidth maxWidth aspectNum aspectDen items with
    | error e => simp [ht] at h
    | ok target =>
      simp only [ht] at h
      cases hf : items.foldlM (append target gap) {} with
      | error e => simp [hf] at h
      | ok result =>
        simp only [hf] at h
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst out
          have hi := fold_inv (target := target) (by omega) items (s := {}) (by simp [Inv]) hf
          rcases hi with ⟨_, _, _, _, _, _, hp, hb⟩
          constructor
          · exact List.Pairwise.map (S := Disjoint) (fun r => { r with x := r.x + margin, y := r.y + margin }) (by
              intro a b hab
              unfold Disjoint Rect.meetsInterior at *
              dsimp
              omega) hp
          · intro r hr
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
            have := hb a ha
            dsimp
            omega

def dimensions (boxes : List Rect) : List (Int × Int) := boxes.map (fun r => (r.w, r.h))

theorem append_dimensions {target gap : Int} {s out : State} {item : Item}
    (h : append target gap s item = .ok out) :
    dimensions out.boxes = dimensions s.boxes ++ [(item.width, item.height)] := by
  unfold append at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp at h
  all_goals subst out
  all_goals simp [dimensions]

theorem fold_dimensions {target gap : Int} (items : List Item) {s out : State}
    (h : items.foldlM (append target gap) s = .ok out) :
    dimensions out.boxes = dimensions s.boxes ++ items.map (fun i => (i.width, i.height)) := by
  induction items generalizing s with
  | nil => simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst out; simp
  | cons item items ih =>
    simp only [List.foldlM_cons] at h
    cases ha : append target gap s item with
    | error e => simp [ha, bind, Except.bind] at h
    | ok next =>
      simp [ha, bind, Except.bind] at h
      rw [ih h, append_dimensions ha]
      simp [List.append_assoc]

theorem pack_dimensions {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Item} {out : State}
    (h : pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    dimensions out.boxes = items.map (fun i => (i.width, i.height)) := by
  unfold pack at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · cases ht : targetWidth maxWidth aspectNum aspectDen items with
    | error e => simp [ht] at h
    | ok target =>
      simp only [ht] at h
      cases hf : items.foldlM (append target gap) {} with
      | error e => simp [hf] at h
      | ok result =>
        simp only [hf] at h
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst out
          have hd := fold_dimensions items hf
          simpa [dimensions, List.map_map, Function.comp_def] using hd

theorem pack_count {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Item} {out : State}
    (h : pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    out.boxes.length = items.length := by
  have := congrArg List.length (pack_dimensions h)
  simpa [dimensions] using this

theorem pack_components_disjoint {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Item} {out : State}
    (h : pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    out.boxes.Pairwise Disjoint := (pack_bounds h).1

theorem pack_boxes_disjoint {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Item} {out : State}
    (h : pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    (i j : Nat) (hi : i < out.boxes.length) (hj : j < out.boxes.length) (hne : i ≠ j) :
    Disjoint out.boxes[i] out.boxes[j] := by
  have hp := List.pairwise_iff_getElem.mp (pack_components_disjoint h)
  by_cases hij : i < j
  · exact hp i j hi hj hij
  · exact (Disjoint.comm _ _).mpr (hp j i hj hi (by omega))

end Elegant.Layered.Pack
