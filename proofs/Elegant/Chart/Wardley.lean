import Elegant.Chart.Scale
import Elegant.Scene
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

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

def linkPoints (g : Geometry) (source target : Nat) : List Point :=
  [(g.positions[source]?).getD ⟨0, 0⟩, (g.positions[target]?).getD ⟨0, 0⟩]


end Elegant.Chart.Wardley
