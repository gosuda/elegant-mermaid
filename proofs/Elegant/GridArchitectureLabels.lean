import Elegant.GridArchitectureGeometry

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def Span.inflate (r : Span) (d : Int) : Span := ⟨r.x0-d, r.y0-d, r.x1+d, r.y1+d⟩

def Span.strictlyInside (r outer : Span) : Bool :=
  decide (outer.x0 < r.x0 ∧ outer.y0 < r.y0 ∧ r.x1 < outer.x1 ∧ r.y1 < outer.y1)

def segments : List Point → List (Point × Point)
  | a :: b :: rest => (a, b) :: segments (b :: rest)
  | _ => []

def widened (a b : Point) (thickness : Int) : Span :=
  ⟨min a.x b.x - thickness, min a.y b.y - thickness,
    max a.x b.x + thickness, max a.y b.y + thickness⟩

def beside (p : GeometryParams) (a b : Point) (size : Size) : List Span :=
  let mx := Int.fdiv (a.x + b.x) 2
  let my := Int.fdiv (a.y + b.y) 2
  if a.y = b.y then
    [sized (mx - Int.fdiv size.w 2) (my - p.labelGap - size.h) size,
      sized (mx - Int.fdiv size.w 2) (my + p.thickness + p.labelGap) size]
  else
    [sized (mx + p.thickness + p.labelGap) (my - Int.fdiv size.h 2) size,
      sized (mx - p.labelGap - size.w) (my - Int.fdiv size.h 2) size]

def labelCandidates (p : GeometryParams) (route : List Point) (size : Size) : List Span :=
  let ordered := ((segments route).filter fun q => q.1 != q.2).mergeSort fun a b =>
    decide (Grid.manhattan b.1 b.2 ≤ Grid.manhattan a.1 a.2)
  ordered.flatMap fun q => beside p q.1 q.2 size

def content (g : Geometry) (routes : List (List Point)) : Span :=
  let bounds := (g.boxes ++ g.labels ++ g.frames ++ g.titles ++ g.badges).foldl Span.union emptySpan
  routes.foldl (fun bounds route => route.foldl
    (fun bounds point => bounds.union ⟨point.x, point.y, point.x, point.y⟩) bounds) bounds

structure LabelState where
  region : Span
  placed : List Span
  output : List Span
  spillY : Int
  deriving Repr

def labelClear (p : GeometryParams) (g : Geometry) (routes : List (List Point))
    (state : LabelState) (r : Span) : Bool :=
  r.strictlyInside state.region &&
    g.frames.all (fun frame => !r.overlaps frame || r.strictlyInside frame) &&
    !(g.boxes ++ g.labels ++ g.titles ++ g.badges ++ state.placed).any r.overlaps &&
    !routes.any (fun route => (segments route).any fun q => r.overlaps (widened q.1 q.2 p.thickness))

def placeLabels (p : GeometryParams) (margin : Int) (g : Geometry)
    (routes : List (List Point)) (sizes : List Size) (bounds : Span) : List Span :=
  let region := bounds.inflate margin
  let spillX := region.x1 + margin
  let initial : LabelState := ⟨region, [], [], region.y0 + margin⟩
  let final := sizes.zipIdx.foldl (fun (state : LabelState) (q : Size × Nat) =>
    if q.1.w = 0 ∧ q.1.h = 0 then
      { state with output := state.output ++ [⟨0,0,0,0⟩] }
    else
      match (labelCandidates p (routes.getD q.2 []) q.1).find? (labelClear p g routes state) with
      | some r => { state with placed := state.placed ++ [r], output := state.output ++ [r] }
      | none =>
        let r := sized spillX state.spillY q.1
        let nextY := state.spillY + q.1.h + margin
        { region := { state.region with x1 := max state.region.x1 (r.x1 + margin), y1 := max state.region.y1 nextY }, placed := state.placed ++ [r], output := state.output ++ [r], spillY := nextY }) initial
  final.output

def translateRect (dx dy : Int) (r : Span) : Except LayoutError Rect := do
  if r.x0 = r.x1 ∧ r.y0 = r.y1 then return ⟨0,0,0,0⟩
  let x := r.x0 + dx
  let y := r.y0 + dy
  let w := r.x1 - r.x0
  let h := r.y1 - r.y0
  if 0 ≤ x ∧ x ≤ COORD_LIMIT ∧ 0 ≤ y ∧ y ≤ COORD_LIMIT ∧
      0 ≤ w ∧ w ≤ COORD_LIMIT ∧ 0 ≤ h ∧ h ≤ COORD_LIMIT then
    return ⟨x,y,w,h⟩
  else throw .overflow

def translatePoint (dx dy : Int) (point : Point) : Except LayoutError Point :=
  if 0 ≤ point.x + dx ∧ point.x + dx ≤ COORD_LIMIT ∧
      0 ≤ point.y + dy ∧ point.y + dy ≤ COORD_LIMIT then
    .ok ⟨point.x + dx, point.y + dy⟩ else .error .overflow

end Elegant.Grid.Architecture
