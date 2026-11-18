import Elegant.Chart.Scale
import Elegant.Scene
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.String.ToNat

set_option autoImplicit false

namespace Elegant.Chart.Wardley

structure Node where
  flags : Nat
  strategy : Nat
  x : Int
  y : Int
  offsetX : Int
  offsetY : Int
  deriving DecidableEq, Repr, Inhabited

structure Pipeline where
  parent : Nat
  children : List Nat
  deriving DecidableEq, Repr, Inhabited

structure Trend where
  node : Nat
  x : Int
  y : Int
  deriving DecidableEq, Repr, Inhabited

structure Input where
  nodes : List Node := []
  pipelines : List Pipeline := []
  trends : List Trend := []
  accelerators : List Point := []
  deaccelerators : List Point := []
  annotations : List Point := []
  notes : List Point := []
  box : Option Point := none
  stageCount : Nat := 0
  boundaries : List Int := []
  deriving DecidableEq, Repr

structure GeometryConstants where
  width : Int
  height : Int
  padX : Int
  padY : Int
  arrowWidth : Int
  arrowShaft : Int
  arrowHead : Int
  pipelinePad : Int
  pipelineHeight : Int
  squareSize : Int
  edge : Int
  deriving DecidableEq, Repr

/-- A Wardley node is represented in the canonical dump by its centre, not its painted radius. -/
def nodeRect (p : Point) : Rect := ⟨p.x, p.y, 0, 0⟩
structure GeometryLookup where
  points : Std.HashMap String Point := {}
  rectangles : Std.HashMap String Rect := {}
  nodes : Std.HashMap String Node := {}

private def indexNodes (nodes : List Node) (positions : List Point) : GeometryLookup :=
  ((nodes.zip positions).zipIdx).foldl (fun lookup (entry, i) =>
    let id := "n" ++ toString i
    { lookup with
      points := lookup.points.insert id entry.2
      rectangles := lookup.rectangles.insert id (nodeRect entry.2)
      nodes := lookup.nodes.insert id entry.1 }) {}

private def indexPoints (stem : String) (points : List Point) (lookup : GeometryLookup) :
    GeometryLookup :=
  points.zipIdx.foldl (fun lookup (p, i) =>
    let id := stem ++ toString i
    { lookup with
      points := lookup.points.insert id p
      rectangles := lookup.rectangles.insert id (nodeRect p) }) lookup

private def indexRectangles (stem : String) (rectangles : List Rect) (lookup : GeometryLookup) :
    GeometryLookup :=
  rectangles.zipIdx.foldl (fun lookup (r, i) =>
    { lookup with rectangles := lookup.rectangles.insert (stem ++ toString i) r }) lookup

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

structure Geometry where
  canvas : Size
  plot : Rect
  base : List Point
  positions : List Point
  frames : List Rect
  ghosts : List Point
  accelerators : List Rect
  deaccelerators : List Rect
  annotations : List Point
  notes : List Point
  lookup : GeometryLookup

def unzigzag (n : Int) : Int :=
  if Int.fmod n 2 = 1 then -Int.fdiv (n + 1) 2 else Int.fdiv n 2

def project (plot : Rect) (x y : Int) : Point :=
  ⟨plot.x + Int.fdiv (clamp x 0 100000 * plot.w) 100000,
   plot.y + plot.h - Int.fdiv (clamp y 0 100000 * plot.h) 100000⟩

def clampPlot (plot : Rect) (p : Point) : Point :=
  ⟨clamp p.x plot.x (plot.x + plot.w), clamp p.y plot.y (plot.y + plot.h)⟩

def fitPlot (plot r : Rect) : Rect :=
  { r with x := clamp r.x plot.x (max (plot.x + plot.w - r.w) plot.x)
           y := clamp r.y plot.y (max (plot.y + plot.h - r.h) plot.y) }

def clipPlot (plot r : Rect) : Rect :=
  let x0 := max r.x plot.x
  let y0 := max r.y plot.y
  ⟨x0, y0, max (min (r.x + r.w) (plot.x + plot.w) - x0) 0,
    max (min (r.y + r.h) (plot.y + plot.h) - y0) 0⟩

def forceRect (c : GeometryConstants) (plot : Rect) (p : Point) : Rect :=
  let pos := project plot p.x p.y
  let half := c.arrowShaft + c.arrowHead
  fitPlot plot ⟨pos.x, pos.y - half, c.arrowWidth + c.edge, 2 * half + c.edge⟩

def pipelineGeometry (c : GeometryConstants) (plot : Rect) (base : List Point)
    (p : Pipeline) : Rect × Point :=
  let first := (base[p.children.headD 0]?).getD ⟨0, 0⟩
  let bounds := p.children.drop 1 |>.foldl (fun (a : Point × Point) i =>
    let q := (base[i]?).getD ⟨0, 0⟩
    (⟨min a.1.x q.x, min a.1.y q.y⟩, ⟨max a.2.x q.x, max a.2.y q.y⟩)) (first, first)
  let lo := bounds.1
  let hi := bounds.2
  let half := Int.fdiv c.pipelineHeight 2
  let top := lo.y - half
  (clipPlot plot ⟨lo.x - c.pipelinePad, top, hi.x - lo.x + 2 * c.pipelinePad + c.edge,
      hi.y - lo.y + 2 * half + c.edge⟩,
   clampPlot plot ⟨Int.fdiv (lo.x + hi.x) 2, top - Int.fdiv c.squareSize 6⟩)

def arrange (c : GeometryConstants) (input : Input) : Geometry :=
  let width := max c.width (2 * c.padX + c.arrowWidth + c.edge)
  let height := max c.height (2 * c.padY + 2 * (c.arrowShaft + c.arrowHead) + c.edge)
  let plot : Rect := ⟨c.padX, c.padY, width - 2 * c.padX, height - 2 * c.padY⟩
  let base := input.nodes.map fun n => project plot n.x n.y
  let pipelines := input.pipelines.map (pipelineGeometry c plot base)
  let positions := (input.pipelines.zip pipelines).foldl
    (fun ps (p, g) => ps.set p.parent g.2) base
  let frames := pipelines.map (·.1)
  let ghosts := input.trends.map fun t => project plot t.x t.y
  let accelerators := input.accelerators.map (forceRect c plot)
  let deaccelerators := input.deaccelerators.map (forceRect c plot)
  let annotations := input.annotations.map fun p => project plot p.x p.y
  let lookup := indexNodes input.nodes positions
  let lookup := indexPoints "tg" ghosts lookup
  let lookup := indexRectangles "pl" frames lookup
  let lookup := indexRectangles "ac" accelerators lookup
  let lookup := indexRectangles "de" deaccelerators lookup
  let lookup := annotations.zipIdx.foldl (fun lookup (p, i) =>
    { lookup with rectangles := lookup.rectangles.insert ("an" ++ toString i) (nodeRect p) }) lookup
  { canvas := ⟨width, height⟩, plot, base, positions, frames, ghosts, accelerators, deaccelerators,
    annotations, notes := input.notes.map (fun p => project plot p.x p.y), lookup }

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

private def PointKey (id : String) : Prop :=
  (∃ suffix, id = "n" ++ suffix) ∨ (∃ suffix, id = "tg" ++ suffix)

private def PointIndexed (lookup : GeometryLookup) : Prop :=
  lookup.PointsSound (fun id _ => PointKey id) ∧
    ∀ (id : String) (p : Point), lookup.points[id]? = some p →
      lookup.rectangles[id]? = some (nodeRect p)

private theorem pointKey_disjoint (id : String) (h : PointKey id) :
    id ≠ "plot" ∧ id ≠ "ab" ∧
      ∀ suffix, id ≠ "pl" ++ suffix ∧ id ≠ "ac" ++ suffix ∧
        id ≠ "de" ++ suffix ∧ id ≠ "an" ++ suffix := by
  rcases h with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
    constructor
  all_goals
    first
    | intro he
      have ht := congrArg String.toList he
      simp [String.toList_append] at ht
    | constructor
      · intro he
        have ht := congrArg String.toList he
        simp [String.toList_append] at ht
      · intro other
        repeat' constructor
        all_goals
          intro he
          have ht := congrArg String.toList he
          simp [String.toList_append] at ht

private theorem pointIndexed_insert (lookup : GeometryLookup) (id : String) (p : Point)
    (h : PointIndexed lookup) (hk : PointKey id) :
    PointIndexed { lookup with
      points := lookup.points.insert id p
      rectangles := lookup.rectangles.insert id (nodeRect p) } := by
  constructor
  · exact insert_point_sound lookup (fun key _ => PointKey key) id p h.1 hk
  · intro key value hv
    simp only [Std.HashMap.getElem?_insert] at hv ⊢
    split at hv
    · rename_i he
      simp only [he, ↓reduceIte]
      cases hv
      rfl
    · rename_i he
      simpa [he] using h.2 key value hv

private theorem pointIndexed_rectangle (lookup : GeometryLookup) (id : String) (r : Rect)
    (h : PointIndexed lookup) (hk : ¬ PointKey id) :
    PointIndexed { lookup with rectangles := lookup.rectangles.insert id r } := by
  refine ⟨h.1, ?_⟩
  intro key p hp
  have hn : id ≠ key := fun he => hk (he.symm ▸ h.1 key p hp)
  simpa [Std.HashMap.getElem?_insert, hn] using h.2 key p hp

private theorem indexRectangles_pointIndexed (stem : String) (rectangles : List Rect)
    (lookup : GeometryLookup) (h : PointIndexed lookup)
    (hs : ∀ suffix, ¬ PointKey (stem ++ suffix)) :
    PointIndexed (indexRectangles stem rectangles lookup) := by
  unfold indexRectangles
  apply fold_preserves _ PointIndexed _ _ h
  intro state entry hi _
  exact pointIndexed_rectangle state _ _ hi (hs _)

private theorem arrange_pointIndexed (c : GeometryConstants) (input : Input) :
    PointIndexed (arrange c input).lookup := by
  have hn : PointIndexed (indexNodes input.nodes (arrange c input).positions) := by
    unfold indexNodes
    apply fold_preserves _ PointIndexed _ _
    · constructor <;> intro id p hp <;> simp at hp
    · intro state entry hs _
      have hi := pointIndexed_insert state ("n" ++ toString entry.2) entry.1.2 hs
        (Or.inl ⟨_, rfl⟩)
      exact ⟨hi.1, hi.2⟩
  have ht : PointIndexed
      (indexPoints "tg" (arrange c input).ghosts
        (indexNodes input.nodes (arrange c input).positions)) := by
    unfold indexPoints
    apply fold_preserves _ PointIndexed _ _ hn
    intro state entry hs _
    exact pointIndexed_insert state _ _ hs (Or.inr ⟨_, rfl⟩)
  have hp := indexRectangles_pointIndexed "pl" (arrange c input).frames _ ht
    (fun suffix hk => ((pointKey_disjoint _ hk).2.2 suffix).1 rfl)
  have ha := indexRectangles_pointIndexed "ac" (arrange c input).accelerators _ hp
    (fun suffix hk => ((pointKey_disjoint _ hk).2.2 suffix).2.1 rfl)
  have hd := indexRectangles_pointIndexed "de" (arrange c input).deaccelerators _ ha
    (fun suffix hk => ((pointKey_disjoint _ hk).2.2 suffix).2.2.1 rfl)
  change PointIndexed (((arrange c input).annotations.zipIdx).foldl _ _)
  apply fold_preserves _ PointIndexed _ _ hd
  intro state entry hs _
  apply pointIndexed_rectangle state _ _ hs
  intro hk
  exact ((pointKey_disjoint _ hk).2.2 (toString entry.2)).2.2.2 rfl

theorem arrange_point_rectangle (c : GeometryConstants) (input : Input)
    (id : String) (p : Point)
    (h : (arrange c input).lookup.points[id]? = some p) :
    (arrange c input).lookup.rectangles[id]? = some (nodeRect p) :=
  (arrange_pointIndexed c input).2 id p h

theorem arrange_point_not_reserved (c : GeometryConstants) (input : Input)
    (id : String) (p : Point)
    (h : (arrange c input).lookup.points[id]? = some p) :
    id ≠ "plot" ∧ id ≠ "ab" := by
  have hk := (arrange_pointIndexed c input).1 id p h
  exact ⟨(pointKey_disjoint id hk).1, (pointKey_disjoint id hk).2.1⟩

private theorem fold_lookup_complete {α β σ : Type} (entries : List α)
    (step : σ → α → σ) (read : σ → Option β) (hit : α → Prop)
    [DecidablePred hit] (value : α → β) (wanted : β)
    (hstep : ∀ state entry, read (step state entry) =
      if hit entry then some (value entry) else read state)
    (hvalue : ∀ entry ∈ entries, hit entry → value entry = wanted)
    (hfound : ∃ entry ∈ entries, hit entry) (initial : σ) :
    read (entries.foldl step initial) = some wanted := by
  induction entries generalizing initial with
  | nil => simp at hfound
  | cons first rest ih =>
      obtain ⟨entry, he, hm⟩ := hfound
      rcases List.mem_cons.mp he with he | he
      · subst entry
        have hfirst : read (step initial first) = some wanted := by
          rw [hstep, ite_eq_left hm, hvalue first (by simp) hm]
        apply fold_preserves step (fun state => read state = some wanted)
          rest (step initial first) hfirst
        intro state next hs hn
        rw [hstep]
        split
        · rename_i hmatch
          rw [hvalue next (List.mem_cons_of_mem first hn) hmatch]
        · exact hs
      · exact ih (fun next hn => hvalue next (List.mem_cons_of_mem first hn))
          ⟨entry, he, hm⟩ (step initial first)

private theorem canonical_index_eq (stem : String) (i j : Nat)
    (h : stem ++ toString i = stem ++ toString j) : i = j := by
  have hs := (String.append_right_inj stem).mp h
  exact Nat.repr_injective hs

private theorem indexed_value_eq {α : Type} (entries : List α) (stem : String)
    (i : Nat) (wanted : α) (h : entries[i]? = some wanted)
    (entry : α × Nat) (he : entry ∈ entries.zipIdx)
    (hk : stem ++ toString entry.2 = stem ++ toString i) :
    entry.1 = wanted := by
  have hi := canonical_index_eq stem entry.2 i hk
  have hv := List.mem_zipIdx_iff_getElem?.mp he
  rw [hi, h] at hv
  exact (Option.some.inj hv).symm

private theorem indexNodes_point_complete (nodes : List Node) (positions : List Point)
    (i : Nat) (node : Node) (p : Point)
    (hn : nodes[i]? = some node) (hp : positions[i]? = some p) :
    (indexNodes nodes positions).points["n" ++ toString i]? = some p := by
  have hz : (nodes.zip positions)[i]? = some (node, p) := by
    exact List.getElem?_zip_eq_some.mpr ⟨hn, hp⟩
  unfold indexNodes
  apply fold_lookup_complete _ _
    (fun lookup : GeometryLookup => lookup.points["n" ++ toString i]?)
    (fun entry => "n" ++ toString entry.2 = "n" ++ toString i)
    (fun entry => entry.1.2) p
  · intro state entry
    simp [Std.HashMap.getElem?_insert, beq_iff_eq]
  · intro entry he hk
    exact congrArg Prod.snd (indexed_value_eq _ "n" i (node, p) hz entry he hk)
  · exact ⟨((node, p), i), List.mk_mem_zipIdx_iff_getElem?.mpr hz, rfl⟩

private theorem indexRectangles_complete (stem : String) (rectangles : List Rect)
    (lookup : GeometryLookup) (i : Nat) (r : Rect)
    (h : rectangles[i]? = some r) :
    (indexRectangles stem rectangles lookup).rectangles[stem ++ toString i]? = some r := by
  unfold indexRectangles
  apply fold_lookup_complete _ _
    (fun state : GeometryLookup => state.rectangles[stem ++ toString i]?)
    (fun entry => stem ++ toString entry.2 = stem ++ toString i)
    Prod.fst r
  · intro state entry
    simp [Std.HashMap.getElem?_insert, beq_iff_eq]
  · intro entry he hk
    exact indexed_value_eq rectangles stem i r h entry he hk
  · exact ⟨(r, i), List.mk_mem_zipIdx_iff_getElem?.mpr h, rfl⟩

private theorem indexRectangles_points_eq (stem : String) (rectangles : List Rect)
    (lookup : GeometryLookup) :
    (indexRectangles stem rectangles lookup).points = lookup.points := by
  unfold indexRectangles
  apply fold_preserves _ (fun state : GeometryLookup => state.points = lookup.points)
    _ _ rfl
  intro state entry hs _
  exact hs

private theorem indexRectangles_preserves (stem key : String) (rectangles : List Rect)
    (lookup : GeometryLookup)
    (h : ∀ suffix : String, stem ++ suffix ≠ key) :
    (indexRectangles stem rectangles lookup).rectangles[key]? = lookup.rectangles[key]? := by
  unfold indexRectangles
  apply fold_preserves _
    (fun state : GeometryLookup => state.rectangles[key]? = lookup.rectangles[key]?)
    _ _ rfl
  intro state entry hs _
  simpa [Std.HashMap.getElem?_insert, h] using hs

private theorem canonical_prefix_disjoint (i : Nat) :
    (∀ suffix : String, "tg" ++ suffix ≠ "n" ++ toString i) ∧
    (∀ suffix : String, "ac" ++ suffix ≠ "pl" ++ toString i) ∧
    (∀ suffix : String, "de" ++ suffix ≠ "pl" ++ toString i) ∧
    (∀ suffix : String, "an" ++ suffix ≠ "pl" ++ toString i) := by
  repeat' constructor
  all_goals
    intro suffix he
    have ht := congrArg String.toList he
    simp [String.toList_append] at ht

theorem arrange_node_point (c : GeometryConstants) (input : Input)
    (i : Nat) (node : Node) (p : Point)
    (hn : input.nodes[i]? = some node)
    (hp : (arrange c input).positions[i]? = some p) :
    (arrange c input).lookup.points["n" ++ toString i]? = some p := by
  have hnodes := indexNodes_point_complete input.nodes (arrange c input).positions
    i node p hn hp
  have htrends : (indexPoints "tg" (arrange c input).ghosts
      (indexNodes input.nodes (arrange c input).positions)).points["n" ++ toString i]? =
      some p := by
    unfold indexPoints
    apply fold_preserves _
      (fun state : GeometryLookup => state.points["n" ++ toString i]? = some p)
      _ _ hnodes
    intro state entry hs _
    have hne := (canonical_prefix_disjoint i).1 (toString entry.2)
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i he
      exact False.elim (hne (by simpa only [beq_iff_eq] using he))
    · exact hs
  have hpl := indexRectangles_points_eq "pl" (arrange c input).frames
    (indexPoints "tg" (arrange c input).ghosts
      (indexNodes input.nodes (arrange c input).positions))
  have hac := indexRectangles_points_eq "ac" (arrange c input).accelerators
    (indexRectangles "pl" (arrange c input).frames
      (indexPoints "tg" (arrange c input).ghosts
        (indexNodes input.nodes (arrange c input).positions)))
  have hde := indexRectangles_points_eq "de" (arrange c input).deaccelerators
    (indexRectangles "ac" (arrange c input).accelerators
      (indexRectangles "pl" (arrange c input).frames
        (indexPoints "tg" (arrange c input).ghosts
          (indexNodes input.nodes (arrange c input).positions))))
  change (GeometryLookup.points
    (((arrange c input).annotations.zipIdx).foldl _ _))["n" ++ toString i]? = some p
  apply fold_preserves _
    (fun state : GeometryLookup => state.points["n" ++ toString i]? = some p) _ _
  · exact (congrArg (fun points : Std.HashMap String Point =>
      points["n" ++ toString i]?) (hde.trans (hac.trans hpl))).trans htrends
  · intro state entry hs _
    exact hs

theorem arrange_frame_rectangle (c : GeometryConstants) (input : Input)
    (i : Nat) (r : Rect) (h : (arrange c input).frames[i]? = some r) :
    (arrange c input).lookup.rectangles["pl" ++ toString i]? = some r := by
  have hpl := indexRectangles_complete "pl" (arrange c input).frames
    (indexPoints "tg" (arrange c input).ghosts
      (indexNodes input.nodes (arrange c input).positions)) i r h
  have hac := indexRectangles_preserves "ac" ("pl" ++ toString i)
    (arrange c input).accelerators
    (indexRectangles "pl" (arrange c input).frames
      (indexPoints "tg" (arrange c input).ghosts
        (indexNodes input.nodes (arrange c input).positions)))
    (canonical_prefix_disjoint i).2.1
  have hde := indexRectangles_preserves "de" ("pl" ++ toString i)
    (arrange c input).deaccelerators
    (indexRectangles "ac" (arrange c input).accelerators
      (indexRectangles "pl" (arrange c input).frames
        (indexPoints "tg" (arrange c input).ghosts
          (indexNodes input.nodes (arrange c input).positions))))
    (canonical_prefix_disjoint i).2.2.1
  change (GeometryLookup.rectangles
    (((arrange c input).annotations.zipIdx).foldl _ _))["pl" ++ toString i]? = some r
  apply fold_preserves _
    (fun state : GeometryLookup => state.rectangles["pl" ++ toString i]? = some r) _ _
  · exact hde.trans (hac.trans hpl)
  · intro state entry hs _
    have hne := (canonical_prefix_disjoint i).2.2.2 (toString entry.2)
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i he
      exact False.elim (hne (by simpa only [beq_iff_eq] using he))
    · exact hs

theorem arrange_positions_length (c : GeometryConstants) (input : Input) :
    (arrange c input).positions.length = input.nodes.length := by
  change ((input.pipelines.zip _).foldl _
    (input.nodes.map fun n => project (arrange c input).plot n.x n.y)).length = _
  apply fold_preserves _ (fun positions : List Point =>
    positions.length = input.nodes.length) _ _
  · simp
  · intro positions entry hs _
    simpa only [List.length_set] using hs

theorem arrange_node_rectangle (c : GeometryConstants) (input : Input)
    (i : Nat) (node : Node) (hn : input.nodes[i]? = some node) :
    (arrange c input).lookup.rectangles["n" ++ toString i]? =
      some (nodeRect (((arrange c input).positions[i]?).getD ⟨0, 0⟩)) := by
  have hi : i < (arrange c input).positions.length := by
    rw [arrange_positions_length]
    exact (List.getElem?_eq_some_iff.mp hn).1
  have hp : (arrange c input).positions[i]? =
      some ((arrange c input).positions[i]) :=
    List.getElem?_eq_getElem hi
  have hpoint := arrange_node_point c input i node _ hn hp
  have hrect := arrange_point_rectangle c input ("n" ++ toString i) _ hpoint
  simpa only [hp, Option.getD_some] using hrect

theorem arrange_pipeline_frame (c : GeometryConstants) (input : Input)
    (i : Nat) (pipeline : Pipeline) (h : input.pipelines[i]? = some pipeline) :
    (arrange c input).frames[i]? =
      some (pipelineGeometry c (arrange c input).plot
        (arrange c input).base pipeline).1 := by
  change ((input.pipelines.map
    (pipelineGeometry c (arrange c input).plot (arrange c input).base)).map
    Prod.fst)[i]? = _
  simp only [List.getElem?_map, h, Option.map_some]

theorem arrange_pipeline_rectangle (c : GeometryConstants) (input : Input)
    (i : Nat) (pipeline : Pipeline) (h : input.pipelines[i]? = some pipeline) :
    (arrange c input).lookup.rectangles["pl" ++ toString i]? =
      some (pipelineGeometry c (arrange c input).plot
        (arrange c input).base pipeline).1 :=
  arrange_frame_rectangle c input i _ (arrange_pipeline_frame c input i pipeline h)

def linkPoints (g : Geometry) (source target : Nat) : List Point :=
  [(g.positions[source]?).getD ⟨0, 0⟩, (g.positions[target]?).getD ⟨0, 0⟩]


end Elegant.Chart.Wardley
