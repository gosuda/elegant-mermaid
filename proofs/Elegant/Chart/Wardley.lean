import Std.Data.HashMap.Lemmas
/-- Lookup provenance is preserved through the executed insertion folds. -/
private theorem fold_preserves {α σ : Type} (step : σ → α → σ)
    (P : σ → Prop) (entries : List α) (initial : σ)
    (hinit : P initial)
    (hstep : ∀ state entry, P state → entry ∈ entries → P (step state entry)) :
    P (entries.foldl step initial) := by
  induction entries generalizing initial with
  | nil => exact hinit
  | cons entry rest ih =>
      apply ih (step initial entry)
      · exact hstep initial entry hinit (by simp)
      · intro state next hs hn
        exact hstep state next hs (List.mem_cons_of_mem entry hn)

def GeometryLookup.PointsSound (lookup : GeometryLookup)
    (P : String → Point → Prop) : Prop :=
  ∀ id point, lookup.points[id]? = some point → P id point

private theorem insert_point_sound (lookup : GeometryLookup)
    (P : String → Point → Prop) (id : String) (point : Point)
    (h : lookup.PointsSound P) (hp : P id point) :
    ∀ key value, (lookup.points.insert id point)[key]? = some value → P key value := by
  intro key value hv
  rw [Std.HashMap.getElem?_insert] at hv
  split at hv
  · rename_i heq
    have hid : id = key := by simpa using heq
    subst key
    cases hv
    exact hp
  · exact h key value hv

theorem indexNodes_points_sound (nodes : List Node) (positions : List Point)
    (P : String → Point → Prop)
    (h : ∀ entry ∈ (nodes.zip positions).zipIdx,
      P ("n" ++ toString entry.2) entry.1.2) :
    (indexNodes nodes positions).PointsSound P := by
  unfold indexNodes
  apply fold_preserves (α := (Node × Point) × Nat) (σ := GeometryLookup)
    _ (fun lookup : GeometryLookup => GeometryLookup.PointsSound lookup P) _ _
  · intro id point hp
    simp at hp
  · intro lookup entry hs he
    exact insert_point_sound lookup P _ _ hs (h entry he)

theorem indexPoints_points_sound (stem : String) (points : List Point)
    (lookup : GeometryLookup) (P : String → Point → Prop)
    (hinit : lookup.PointsSound P)
    (h : ∀ entry ∈ points.zipIdx, P (stem ++ toString entry.2) entry.1) :
    (indexPoints stem points lookup).PointsSound P := by
  unfold indexPoints
  apply fold_preserves (α := Point × Nat) (σ := GeometryLookup)
    _ (fun state : GeometryLookup => GeometryLookup.PointsSound state P) _ _
  · exact hinit
  · intro state entry hs he
    exact insert_point_sound state P _ _ hs (h entry he)

theorem indexRectangles_points_sound (stem : String) (rectangles : List Rect)
    (lookup : GeometryLookup) (P : String → Point → Prop)
    (h : lookup.PointsSound P) :
    (indexRectangles stem rectangles lookup).PointsSound P := by
  unfold indexRectangles
  apply fold_preserves (α := Rect × Nat) (σ := GeometryLookup)
    _ (fun state : GeometryLookup => GeometryLookup.PointsSound state P) _ _
  · exact h
  · intro state entry hs _
    exact hs

/-- Endpoint IDs come from the declarations inserted into the hash lookup, never
from parsing a numeric suffix of the requested ID. -/
theorem arrange_lookup_points_sound (c : GeometryConstants) (input : Input)
    (id : String) (point : Point)
    (h : (arrange c input).lookup.points[id]? = some point) :
    (∃ entry ∈ (input.nodes.zip (arrange c input).positions).zipIdx,
      id = "n" ++ toString entry.2 ∧ point = entry.1.2) ∨
    (∃ entry ∈ (arrange c input).ghosts.zipIdx,
      id = "tg" ++ toString entry.2 ∧ point = entry.1) := by
  let P : String → Point → Prop := fun key value =>
    (∃ entry ∈ (input.nodes.zip (arrange c input).positions).zipIdx,
      key = "n" ++ toString entry.2 ∧ value = entry.1.2) ∨
    (∃ entry ∈ (arrange c input).ghosts.zipIdx,
      key = "tg" ++ toString entry.2 ∧ value = entry.1)
  have hn : (indexNodes input.nodes (arrange c input).positions).PointsSound P := by
    apply indexNodes_points_sound
    intro entry he
    exact Or.inl ⟨entry, he, rfl, rfl⟩
  have hg := indexPoints_points_sound "tg" (arrange c input).ghosts _ P hn
    (fun entry he => Or.inr ⟨entry, he, rfl, rfl⟩)
  have hpl := indexRectangles_points_sound "pl" (arrange c input).frames _ P hg
  have hac := indexRectangles_points_sound "ac" (arrange c input).accelerators _ P hpl
  have hde := indexRectangles_points_sound "de" (arrange c input).deaccelerators _ P hac
  have hall : (arrange c input).lookup.PointsSound P := by
    change GeometryLookup.PointsSound
      (((arrange c input).annotations.zipIdx).foldl _ _) P
    apply fold_preserves (α := Point × Nat) (σ := GeometryLookup)
      _ (fun state : GeometryLookup => GeometryLookup.PointsSound state P) _ _
    · exact hde
    · intro state entry hs _
      exact hs
  exact hall id point h
