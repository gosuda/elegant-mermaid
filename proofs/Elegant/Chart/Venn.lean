import Elegant.Chart.XY
import ElegantGeometry.Trig

set_option autoImplicit false

namespace Elegant.Chart.Venn

structure Circle where
  x : Int
  y : Int
  r : Int
  deriving DecidableEq, Repr

def arccos (x : Int) : Nat → Int → Int → Int
  | 0, lo, _ => lo
  | n + 1, lo, hi =>
    let mid := Int.fdiv (lo + hi + 1) 2
    if cosQ15 mid ≥ x then arccos x n mid hi else arccos x n lo (mid - 1)

def halfChord (d own other : Int) : Int :=
  arccos (clamp (Int.fdiv ((d*d + own*own - other*other)*32768) (2*d*own))
    (-32768) 32768) (LayoutConst.venn_acos_iterations.get .vector).toNat 0 32768

def lensTerm (d own other : Int) : Int :=
  let u := halfChord d own other
  own * own * (131072*u - 20861*sinQ15 (2*u))

def lens (d r1 r2 : Int) : Int :=
  if d = 0 then min r1 r2 * min r1 r2 * 4294967296
  else lensTerm d r1 r2 + lensTerm d r2 r1

def bisect (g : Int → Bool) : Nat → Int → Int → Int × Int
  | 0, lo, hi => (lo, hi)
  | n + 1, lo, hi =>
    let mid := Int.fdiv (lo + hi) 2
    if g mid then bisect g n mid hi else bisect g n lo mid

def distance (r1 r2 target : Int) : Int :=
  let lo := (r1-r2).natAbs
  let hi := r1+r2
  if min r1 r2 * min r1 r2 ≤ target then lo
  else if target = 0 then hi
  else
    let b := bisect (fun d => decide (lens d r1 r2 > target*4294967296))
      (LayoutConst.venn_bisect_iterations.get .vector).toNat lo hi
    Int.fdiv (b.1+b.2) 2

def centres (radii : List Int) (radius dist : Int) : List Circle :=
  let dx := Int.fdiv (radius * LayoutConst.venn_sqrt3_half_q15.get .vector) 32768
  let low := 2*radius + Int.fdiv radius 2
  match radii with
  | [a] => [⟨2*radius, 2*radius, a⟩]
  | [a,b] =>
    let x := 2*radius-Int.fdiv dist 2
    [⟨x,2*radius,a⟩, ⟨x+dist,2*radius,b⟩]
  | [a,b,c] => [⟨2*radius,radius,a⟩, ⟨2*radius+dx,low,b⟩, ⟨2*radius-dx,low,c⟩]
  | _ => []

def unzigzag (n : Int) : Int :=
  if Int.fmod n 2 = 0 then Int.fdiv n 2 else -(Int.fdiv n 2)-1

def sizes (m : Model) : List Int :=
  m.regionSets.filterMap fun s => match s.regions with
    | [0,v] => some (unzigzag v)
    | _ => none

def overlap (m : Model) : Int :=
  m.regionSets.foldl (fun v s => match s.regions with
    | [1,0,1,n] => unzigzag n
    | _ => v) 0

def members (m : Model) : List (List Nat) :=
  m.regionSets.filterMap fun s => match s.regions with
    | 2 :: ns => some (ns.map Int.toNat)
    | _ => none

def config (m : Model) (key : String) (fallback : Int) : Int :=
  match m.options.config.lookup key with
  | some (.integer n) => n
  | _ => fallback

structure Item where
  label : ModelLabel
  box : XY.TextBox
  rect : Rect

structure Result where
  radius : Int
  circles : List Circle
  items : List Item
  rects : List Rect
  width : Int
  height : Int

def fit (width height : Int) (r : Rect) : Rect :=
  { r with
    x := clamp r.x 0 (max (width-r.w) 0)
    y := clamp r.y 0 (max (height-r.h) 0) }

def measure (width : Int) (l : ModelLabel) (fontFamily : Bool := false) : Except LayoutError Item := do
  let role := if l.id == "title" then Measure.Role.title else Measure.Role.label
  let metric ← XY.metricOf false role role.sizePx fontFamily
  let lines ← match StyledMeasure.wrap metric width l.text.toList with
    | .error _ => throw .overflow
    | .ok ls => pure ls
  let box : XY.TextBox := ⟨lines, lines.foldl (fun w l => max w l.width) 0,
    (lines.length : Int)*role.lineHeightPx*64⟩
  return ⟨l, box, ⟨0,0,box.w,box.h⟩⟩

def setAnchor (cs : List Circle) (i : Nat) : Except LayoutError Point := do
  let c := cs.getD i ⟨0,0,0⟩
  if cs.length ≤ 1 then return ⟨c.x,c.y⟩
  let others := cs.zipIdx |>.filter (fun p => p.2 != i)
  let n : Int := others.length
  let dx := c.x-Int.fdiv (others.foldl (fun s p => s+p.1.x) 0) n
  let dy := c.y-Int.fdiv (others.foldl (fun s p => s+p.1.y) 0) n
  let length ← Rect.isqrt (dx*dx+dy*dy)
  if length = 0 then return ⟨c.x,c.y⟩
  return ⟨c.x+Int.fdiv (dx*c.r) (2*length), c.y+Int.fdiv (dy*c.r) (2*length)⟩

def anchor (m : Model) (cs : List Circle) (id : String) : Except LayoutError Point := do
  match (List.range cs.length).find? (fun i => id == "set" ++ toString i) with
  | some i => setAnchor cs i
  | none =>
    let regions := members m
    let ns := match (List.range regions.length).find? (fun i => id == "region" ++ toString i) with
      | some i => regions.getD i []
      | none => []
    let n : Int := ns.length
    return ⟨Int.fdiv (ns.foldl (fun s i => s+(cs.getD i ⟨0,0,0⟩).x) 0) n,
      Int.fdiv (ns.foldl (fun s i => s+(cs.getD i ⟨0,0,0⟩).y) 0) n⟩

def clearEarlier (previous : List Item) : Nat → Rect → Rect
  | 0, r => r
  | fuel + 1, r =>
    match previous.find? (fun it => decide
      (0 < r.w ∧ 0 < r.h ∧ 0 < it.rect.w ∧ 0 < it.rect.h ∧ r.meetsInterior it.rect)) with
    | none => r
    | some it => clearEarlier previous fuel { r with y := it.rect.y+it.rect.h }

structure StackState where
  top : Int
  out : List Item
  history : List Item
  left : Int
  right : Int
  low : Int
  high : Int

def stackStep (width height band : Int) (a : Point) (s : StackState) (it : Item) : StackState :=
  let initial := fit width height ⟨a.x-Int.fdiv it.box.w 2,s.top,it.box.w,it.box.h⟩
  let index := s.history.findIdx (fun p => p.label.id == it.label.id)
  let r := clearEarlier (s.history.take index) index { initial with y := max initial.y band }
  let placed := { it with rect := r }
  { top := r.y+r.h
    out := s.out ++ [placed]
    history := s.history.map (fun p => if p.label.id == it.label.id then placed else p)
    left := min s.left r.x
    right := max s.right (r.x+r.w)
    low := min s.low r.y
    high := max s.high (r.y+r.h) }

def stackLoop (width height band : Int) (a : Point) : List Item → StackState → StackState
  | [], s => s
  | it :: rest, s => stackLoop width height band a rest (stackStep width height band a s it)

def stack (width height band : Int) (a : Point) (previous items : List Item) : List Item × Rect :=
  let initial : StackState :=
    ⟨a.y-Int.fdiv (items.foldl (fun s i => s+i.box.h) 0) 2, [], previous, a.x,a.x,a.y,a.y⟩
  let s := stackLoop width height band a items initial
  (s.out, ⟨s.left,s.low,s.right-s.left,s.high-s.low⟩)

structure BoxState where
  placed : List Item
  rects : List Rect

def placeBox (m : Model) (circles : List Circle) (items : List Item)
    (width height band : Int) (b : ModelBox) (s : BoxState) : Except LayoutError BoxState := do
  if b.id == "venn" then
    let rects := s.rects ++ [⟨0,0,width,height⟩]
    let placed := s.placed.map fun it => if it.label.id == "title" then
      { it with rect := fit width height ⟨Int.fdiv (width-it.box.w) 2,0,it.box.w,it.box.h⟩ } else it
    return ⟨placed,rects⟩
  else
    let a ← anchor m circles b.id
    let (own, bounds) := stack width height band a s.placed (items.filter (fun it => it.label.owner == b.id))
    let placed := s.placed.map fun it => (own.find? (fun p => p.label.id == it.label.id)).getD it
    let r := match (List.range circles.length).find? (fun i => b.id == "set" ++ toString i) with
      | some i => let c := circles.getD i ⟨0,0,0⟩; ⟨c.x-c.r,c.y-c.r,2*c.r,2*c.r⟩
      | none => bounds
    return ⟨placed,s.rects ++ [r]⟩

def placeBoxes (m : Model) (circles : List Circle) (items : List Item)
    (width height band : Int) : List ModelBox → BoxState → Except LayoutError BoxState
  | [], s => .ok s
  | b :: rest, s => do
    let next ← placeBox m circles items width height band b s
    placeBoxes m circles items width height band rest next

def layoutCore (m : Model) : Except LayoutError Result := do
  let vs := sizes m
  XY.checkMagnitude (vs ++ [overlap m])
  let radius := Int.fdiv (min
    (config m "width" (Int.fdiv (LayoutConst.venn_width.get .vector) 64))
    (config m "height" (Int.fdiv (LayoutConst.venn_height.get .vector) 64))) 4 * 64
  let width := 4*radius
  let items ← m.labels.mapM (measure (fontFamily := m.options.fontFamily) width)
  let band := ((items.find? (fun i => i.label.id == "title")).map (·.box.h)).getD 0
  let width := items.foldl (fun w it => max w it.box.w) width
  let height := 4*radius+band
  let largest := vs.foldl max 1
  let rs ← vs.mapM (fun v => Rect.isqrt (Int.fdiv (radius*radius*max v 0) largest))
  let target := Int.fdiv (radius*radius*max (overlap m) 0) largest
  let dist := distance (rs.getD 0 0) (rs.getD 1 0) target
  let circles := (centres rs radius dist).map (fun c => { c with y := c.y+band })
  let state ← placeBoxes m circles items width height band m.boxes ⟨items,[]⟩
  let placed := state.placed
  let rects := state.rects
  let width := rects.foldl (fun w r => max w (r.x+r.w))
    (placed.foldl (fun w it => max w (it.rect.x+it.rect.w)) width)
  let height := rects.foldl (fun h r => max h (r.y+r.h))
    (placed.foldl (fun h it => max h (it.rect.y+it.rect.h)) height)
  let rects := (m.boxes.zip rects).map (fun (b,r) =>
    if b.id == "venn" then ⟨0,0,width,height⟩ else r)
  XY.checkMagnitude ([width,height] ++ rects.flatMap (fun r => [r.x,r.y,r.w,r.h]))
  return ⟨radius,circles,placed,rects,width,height⟩

def layout (m : Model) : Except LayoutError Result :=
  if (sizes m).isEmpty ∨ (sizes m).length > 3 then .error .domain else layoutCore m

def sceneOf (m : Model) (r : Result) : Scene :=
  { kind := "venn"
    profile := .vector
    options := { m.options with profile := .vector, direction := .TB }
    canvas := ⟨r.width,r.height⟩
    boxes := m.boxes.zipIdx |>.map (fun (b,i) =>
      ⟨b.id,b.role.id,r.rects.getD i ⟨0,0,0,0⟩,b.parent,b.exclusive⟩)
    labels := r.items.map (fun it =>
      { id := it.label.id
        owner := it.label.owner
        text := it.label.text
        rect := it.rect
        lines := it.box.lines.map (fun l => String.ofList l.text) })
    items := m.boxes.map fun b =>
      let shapes := match (List.range r.circles.length).find? (fun i => b.id == "set" ++ toString i) with
        | some i =>
          let c := r.circles.getD i ⟨0,0,0⟩
          [Primitive.ellipse c.x c.y c.r c.r
            { style := "series-tint", series := ⟨i % 12, Nat.mod_lt _ (by decide)⟩ }]
        | none => []
      let texts := (r.items.filter (fun it => it.label.owner == b.id)).map fun it =>
        Primitive.text
          { rect := it.rect
            role := if it.label.id == "title" then .title else .label
            size := if it.label.id == "title" then 16 else 14
            align := .middle
            style := "text"
            lines := XY.runsOf it.box.lines }
      ⟨.node,b.id,shapes ++ texts⟩ }
