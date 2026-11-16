import Elegant.Chart.XY

set_option autoImplicit false

namespace Elegant.Chart.Sankey

structure Node where
  incoming : List Nat := []
  outgoing : List Nat := []
  value : Int := 0
  depth : Nat := 0
  height : Nat := 0
  layer : Nat := 0
  y0 : Int := 0
  y1 : Int := 0
  deriving Inhabited, Repr

structure Link where
  source : Nat
  target : Nat
  value : Int
  width : Int := 0
  y0 : Int := 0
  y1 : Int := 0
  deriving Inhabited, Repr

structure Flow where
  nodes : Array Node
  links : Array Link
  columns : Array (List Nat) := #[]
  extent : Int
  padding : Int
  py : Int := 0
  arithmeticFailed : Bool := false
  deriving Inhabited, Repr

def roundHalfUp (n d : Int) : Int := Int.fdiv (2 * n + d) (2 * d)

def fitsI64 (n : Int) : Bool := decide (-(2^63) ≤ n ∧ n < 2^63)

def unzigzag (n : Int) : Int :=
  if Int.fmod n 2 = 0 then Int.fdiv n 2 else -(Int.fdiv n 2) - 1

def nodeIndex (m : Model) (id : String) : Nat :=
  (m.boxes.findIdx? (fun b => b.id == id)).getD m.boxes.length

def decode (m : Model) (extent padding : Int) : Except LayoutError Flow := do
  let regions := (m.regionSets.head?).map (·.regions) |>.getD []
  let mut links := #[]
  let mut nodes := (m.boxes.map (fun _ => ({} : Node))).toArray
  for (r, i) in m.routes.zipIdx do
    let kind := regions.getD (2 * i) 0
    let value := unzigzag (regions.getD (2 * i + 1) 0)
    if kind = 2 then throw .overflow
    if kind != 0 ∨ value < 0 then throw .domain
    let source := nodeIndex m r.fromId
    let target := nodeIndex m r.toId
    if source ≥ nodes.size ∨ target ≥ nodes.size then throw .domain
    links := links.push { source, target, value }
    nodes := nodes.modify source (fun n => { n with outgoing := n.outgoing ++ [i] })
    nodes := nodes.modify target (fun n => { n with incoming := n.incoming ++ [i] })
  nodes := nodes.map (fun n =>
    let incoming := n.incoming.foldl (fun s i => s + (links[i]!).value) 0
    let outgoing := n.outgoing.foldl (fun s i => s + (links[i]!).value) 0
    { n with value := max incoming outgoing })
  return { nodes, links, extent, padding }

def levels (f : Flow) (reverse : Bool) : Except LayoutError (Array Nat) :=
  go (f.nodes.size + 1) 0 (List.range f.nodes.size) (Array.replicate f.nodes.size 0)
where
  go : Nat → Nat → List Nat → Array Nat → Except LayoutError (Array Nat)
    | _, _, [], values => .ok values
    | 0, _, _ :: _, _ => .error .domain
    | fuel + 1, level, current, values =>
      let values := current.foldl (fun a i => a.set! i level) values
      let next := current.flatMap (fun i =>
        let n := f.nodes[i]!
        (if reverse then n.incoming else n.outgoing).map (fun j =>
          if reverse then (f.links[j]!).source else (f.links[j]!).target))
      go fuel (level + 1) ((List.range f.nodes.size).filter next.contains) values

def place (f : Flow) (alignment : String) : Except LayoutError Flow := do
  let depths ← levels f false
  let heights ← levels f true
  let count := depths.foldl (fun n d => max n (d + 1)) 1
  let nodes := f.nodes.mapIdx fun i n =>
    let depth := depths[i]!
    let height := heights[i]!
    let layer := if alignment == "left" then depth
      else if alignment == "right" then count - 1 - height
      else if alignment == "center" then
        if !n.incoming.isEmpty then depth
        else if n.outgoing.isEmpty then 0
        else (n.outgoing.foldl (fun d j => min d (depths[(f.links[j]!).target]!)) count) - 1
      else if n.outgoing.isEmpty then count - 1 else depth
    { n with depth, height, layer := min layer (count - 1) }
  let columns := (List.range nodes.size).foldl (fun a i =>
    a.modify (nodes[i]!).layer (fun c => c ++ [i])) (Array.replicate count [])
  return { f with nodes, columns }

def withPadding (f : Flow) : Flow :=
  let widest := f.columns.foldl (fun n c => max n c.length) 0
  { f with py := if widest > 1 then min f.padding (Int.fdiv f.extent (widest - 1)) else f.padding }

def scale (f : Flow) : Except LayoutError Int := do
  let mut best : Option Int := none
  for c in f.columns do
    if !c.isEmpty then
      let room := f.extent - (Int.ofNat c.length - 1) * f.py
      if room < 0 then throw .domain
      let total := c.foldl (fun s i => s + (f.nodes[i]!).value) 0
      if total > 0 then
        let _ ← Measure.checkedI64 total
        let _ ← Measure.checkedI64 (room * 65536)
        let candidate := Int.fdiv (room * 65536) total
        best := some (match best with | none => candidate | some v => min v candidate)
  return best.getD 0

def byTarget (f : Flow) (a b : Nat) : Bool :=
  let x := (f.nodes[(f.links[a]!).target]!).y0
  let y := (f.nodes[(f.links[b]!).target]!).y0
  x < y || (x == y && a ≤ b)

def bySource (f : Flow) (a b : Nat) : Bool :=
  let x := (f.nodes[(f.links[a]!).source]!).y0
  let y := (f.nodes[(f.links[b]!).source]!).y0
  x < y || (x == y && a ≤ b)

def reorderLinks (f : Flow) (column : List Nat) : Flow :=
  column.foldl (fun f i =>
    let n := f.nodes[i]!
    { f with nodes := f.nodes.set! i { n with
      outgoing := n.outgoing.mergeSort (byTarget f)
      incoming := n.incoming.mergeSort (bySource f) } }) f

def reorderNodeLinks (f : Flow) (i : Nat) : Flow :=
  let f := (f.nodes[i]!).incoming.foldl (fun f j =>
    let s := (f.links[j]!).source
    { f with nodes := f.nodes.modify s (fun n =>
      { n with outgoing := n.outgoing.mergeSort (byTarget f) }) }) f
  (f.nodes[i]!).outgoing.foldl (fun f j =>
    let t := (f.links[j]!).target
    { f with nodes := f.nodes.modify t (fun n =>
      { n with incoming := n.incoming.mergeSort (bySource f) }) }) f

def stack (f : Flow) (column : List Nat) (ky : Int) : Flow := Id.run do
  let mut f := f
  let mut y := 0
  for i in column do
    let n := f.nodes[i]!
    let y1 := y + Int.fdiv (n.value * ky) 65536
    let safe := [n.value * ky, y1, y1 + f.py].all fitsI64
    f := { f with nodes := f.nodes.set! i { n with y0 := y, y1 }, arithmeticFailed := f.arithmeticFailed || !safe }
    y := y1 + f.py
    for j in n.outgoing do
      let l := f.links[j]!
      f := { f with links := f.links.set! j { l with width := Int.fdiv (l.value * ky) 65536 }, arithmeticFailed := f.arithmeticFailed || !(fitsI64 (l.value * ky)) }
  let free := f.extent - (y - f.py)
  for (i, k) in column.zipIdx do
    let shift := Int.fdiv ((Int.ofNat k + 1) * free) (Int.ofNat column.length + 1)
    let n := f.nodes[i]!
    let safe := [(Int.ofNat k + 1) * free, n.y0 + shift, n.y1 + shift].all fitsI64
    f := { f with nodes := f.nodes.set! i { n with y0 := n.y0 + shift, y1 := n.y1 + shift }, arithmeticFailed := f.arithmeticFailed || !safe }
  return f

def initialise (f : Flow) : Except LayoutError Flow := do
  let ky ← scale f
  return f.columns.foldl (fun f c => reorderLinks (stack f c ky) c) f

def linkPrefix (f : Flow) (list : List Nat) (stop : Nat → Bool) (gap : Int) : Int :=
  (list.takeWhile (fun i => !stop i)).foldl (fun s i => s + (f.links[i]!).width + gap) 0

def targetTop (f : Flow) (s t : Nat) : Int :=
  let src := f.nodes[s]!
  let tgt := f.nodes[t]!
  let a := linkPrefix f src.outgoing (fun i => (f.links[i]!).target == t) f.py
  let b := linkPrefix f tgt.incoming (fun i => (f.links[i]!).source == s) 0
  Int.fdiv (2 * src.y0 - (Int.ofNat src.outgoing.length - 1) * f.py + 2 * a - 2 * b) 2

def sourceTop (f : Flow) (s t : Nat) : Int :=
  let src := f.nodes[s]!
  let tgt := f.nodes[t]!
  let a := linkPrefix f tgt.incoming (fun i => (f.links[i]!).source == s) f.py
  let b := linkPrefix f src.outgoing (fun i => (f.links[i]!).target == t) 0
  Int.fdiv (2 * tgt.y0 - (Int.ofNat tgt.incoming.length - 1) * f.py + 2 * a - 2 * b) 2

def shiftNode (f : Flow) (i : Nat) (y w alpha : Int) : Flow :=
  if w ≤ 0 then f else
    let mean := roundHalfUp y w
    let delta := mean - (f.nodes[i]!).y0
    let product := delta * alpha
    let dy := roundHalfUp product 65536
    let safe := [2 * y, 2 * y + w, 2 * w, delta, product, 2 * product,
      2 * product + 65536, (f.nodes[i]!).y0 + dy, (f.nodes[i]!).y1 + dy].all fitsI64
    reorderNodeLinks { f with
      arithmeticFailed := f.arithmeticFailed || !safe
      nodes := f.nodes.modify i (fun n => { n with y0 := n.y0 + dy, y1 := n.y1 + dy }) } i

def pull (f : Flow) (i : Nat) (alpha : Int) (reverse : Bool) : Flow :=
  let n := f.nodes[i]!
  let links := if reverse then n.outgoing else n.incoming
  let (y, w, safe) := links.foldl (fun (acc : Int × Int × Bool) j =>
    let l := f.links[j]!
    let s := if reverse then i else l.source
    let t := if reverse then l.target else i
    let v := l.value * (Int.ofNat (f.nodes[t]!).layer - Int.ofNat (f.nodes[s]!).layer)
    let top := if reverse then sourceTop f s t else targetTop f s t
    let product := top * v
    let y := acc.1 + product
    let w := acc.2.1 + v
    (y, w, acc.2.2 && [v, product, y, w].all fitsI64)) (0, 0, true)
  shiftNode { f with arithmeticFailed := f.arithmeticFailed || !safe } i y w alpha

def pushDownNode (n : Node) (y beta : Int) : Node :=
  let dy := max 0 (roundHalfUp ((y - n.y0) * beta) 65536)
  { n with y0 := n.y0 + dy, y1 := n.y1 + dy }

def pushDown (f : Flow) (column : List Nat) (y beta : Int) : Flow :=
  (column.foldl (fun (acc : Flow × Int) i =>
    let n := pushDownNode (acc.1.nodes[i]!) acc.2 beta
    let old := acc.1.nodes[i]!
    let product := (acc.2 - old.y0) * beta
    let safe := [product, 2 * product, 2 * product + 65536, n.y0, n.y1, n.y1 + acc.1.py].all fitsI64
    ({ acc.1 with nodes := acc.1.nodes.set! i n, arithmeticFailed := acc.1.arithmeticFailed || !safe }, n.y1 + acc.1.py)) (f, y)).1

def pushUp (f : Flow) (column : List Nat) (y beta : Int) : Flow :=
  (column.reverse.foldl (fun (acc : Flow × Int) i =>
    let n := acc.1.nodes[i]!
    let product := (n.y1 - acc.2) * beta
    let dy := max 0 (roundHalfUp product 65536)
    let n := { n with y0 := n.y0 - dy, y1 := n.y1 - dy }
    let safe := [product, 2 * product, 2 * product + 65536, dy, n.y0, n.y1, n.y0 - acc.1.py].all fitsI64
    ({ acc.1 with nodes := acc.1.nodes.set! i n, arithmeticFailed := acc.1.arithmeticFailed || !safe }, n.y0 - acc.1.py)) (f, y)).1

def resolveCollisions (f : Flow) (column : List Nat) (beta : Int) : Flow :=
  if column.isEmpty then f else
    let k := column.length / 2
    let subject := f.nodes[column.getD k 0]!
    let f := pushUp f (column.take k) (subject.y0 - f.py) beta
    let f := pushDown f (column.drop (k + 1)) (subject.y1 + f.py) beta
    let f := pushUp f column f.extent beta
    pushDown f column 0 beta

def settle (f : Flow) (c : Nat) (beta : Int) : Flow :=
  let column := (f.columns[c]!).mergeSort (fun i j => (f.nodes[i]!).y0 ≤ (f.nodes[j]!).y0)
  resolveCollisions { f with columns := f.columns.set! c column } column beta

def pass (f : Flow) (alpha beta : Int) (reverse : Bool) : Flow :=
  let columns := if reverse then (List.range (f.columns.size - 1)).reverse
    else (List.range f.columns.size).drop 1
  columns.foldl (fun f c =>
    let f := (f.columns[c]!).foldl (fun f i => pull f i alpha reverse) f
    settle f c beta) f

def iteration (count i : Nat) (f : Flow) : Flow :=
  let alpha := Int.fdiv (65536 * (99 : Int)^i) ((100 : Int)^i)
  let beta := max (65536 - alpha) (Int.fdiv ((Int.ofNat i + 1) * 65536) count)
  pass (pass f alpha beta true) alpha beta false

def relax (count : Nat) (f : Flow) : Flow :=
  (List.range count).foldl (fun f i => iteration count i f) f

def countedRelax (count : Nat) (f : Flow) : Flow × Nat :=
  (List.range count).foldl (fun acc i => (iteration count i acc.1, acc.2 + 1)) (f, 0)

def anchorLinks (f : Flow) : Flow :=
  (List.range f.nodes.size).foldl (fun f i =>
    let n := f.nodes[i]!
    let f := (n.outgoing.foldl (fun (acc : Flow × Int) j =>
      let l := acc.1.links[j]!
      ({ acc.1 with links := acc.1.links.set! j { l with y0 := acc.2 + Int.fdiv l.width 2 } },
        acc.2 + l.width)) (f, n.y0)).1
    (n.incoming.foldl (fun (acc : Flow × Int) j =>
      let l := acc.1.links[j]!
      ({ acc.1 with links := acc.1.links.set! j { l with y1 := acc.2 + Int.fdiv l.width 2 } },
        acc.2 + l.width)) (f, n.y0)).1) f

def run (f : Flow) (alignment : String) (iterations : Nat) : Except LayoutError Flow := do
  let f ← place f alignment
  let f ← initialise (withPadding f)
  let f := anchorLinks (countedRelax iterations f).1
  if f.arithmeticFailed then throw .overflow else return f

def configInt (m : Model) (key : String) (fallback : Int) : Int :=
  match m.options.config.lookup key with
  | some (.integer n) => n
  | _ => fallback

def configString (m : Model) (key : String) (fallback : String) : String :=
  match m.options.config.lookup key with
  | some (.string s) => s
  | _ => fallback

def showValues (m : Model) : Bool :=
  match m.options.config.lookup "showValues" with
  | some (.boolean b) => b
  | _ => true

structure LabelPlacement where
  label : ModelLabel
  box : XY.TextBox
  rect : Rect
  cells : Int
  align : Align

def reach (p : LabelPlacement) : Rect :=
  let width := max p.rect.w p.cells + 1024
  let left := if p.align = .«end» then p.rect.x + p.rect.w + 512 - width else p.rect.x - 512
  ⟨left, p.rect.y, width, p.rect.h⟩

def separateLabel : Nat → List LabelPlacement → LabelPlacement → LabelPlacement
  | 0, _, p => p
  | fuel + 1, previous, p =>
    let next := previous.foldl (fun p q =>
      if (reach p).meetsInterior (reach q) then
        { p with rect := { p.rect with y := q.rect.y + q.rect.h } }
      else p) p
    if next.rect.y = p.rect.y then next else separateLabel fuel previous next

def separateLabels (ps : List LabelPlacement) : List LabelPlacement :=
  let sorted := ps.mergeSort (fun p q => p.rect.y ≤ q.rect.y)
  let placed := sorted.foldl (fun previous p =>
    previous ++ [separateLabel (previous.length + 1) previous p]) []
  ps.map (fun p => (placed.find? (fun q => q.label.id == p.label.id)).getD p)

def nodeRects (f : Flow) (width nodeWidth : Int) : Array Rect :=
  let depth := f.nodes.foldl (fun d n => max d n.depth) 0
  f.nodes.map (fun n =>
    let x := if depth = 0 then 0 else Int.fdiv (Int.ofNat n.layer * (width - nodeWidth)) depth
    ⟨x, n.y0, nodeWidth, n.y1 - n.y0⟩)

def splitForced (text : List Char) : List (List Char) :=
  go text [] []
where
  go : List Char → List Char → List (List Char) → List (List Char)
    | [], current, parts => parts ++ [current.reverse]
    | '<' :: b :: r :: '>' :: rest, current, parts =>
      if b.toLower = 'b' ∧ r.toLower = 'r' then
        go rest [] (parts ++ [current.reverse])
      else go (b :: r :: '>' :: rest) ('<' :: current) parts
    | '<' :: b :: r :: '/' :: '>' :: rest, current, parts =>
      if b.toLower = 'b' ∧ r.toLower = 'r' then
        go rest [] (parts ++ [current.reverse])
      else go (b :: r :: '/' :: '>' :: rest) ('<' :: current) parts
    | '<' :: b :: r :: ' ' :: '/' :: '>' :: rest, current, parts =>
      if b.toLower = 'b' ∧ r.toLower = 'r' then
        go rest [] (parts ++ [current.reverse])
      else go (b :: r :: ' ' :: '/' :: '>' :: rest) ('<' :: current) parts
    | c :: rest, current, parts => go rest (c :: current) parts

def measureLabel (text : String) : Except LayoutError XY.TextBox := do
  let metric ← XY.metricOf false .label 14
  let mut lines := []
  let parts := splitForced text.toList
  for (part, i) in parts.zipIdx do
    let ls ← Measure.wrap metric I32_MAX part
    lines := lines ++ (if ls.isEmpty ∧ i + 1 < parts.length then [⟨[], [], 0⟩] else ls)
  return ⟨lines, lines.foldl (fun w l => max w l.width) 0, Int.ofNat lines.length * 1280⟩

def measureLabels (m : Model) (rects : Array Rect) (width height gap : Int) :
    Except LayoutError (List LabelPlacement) := do
  let mut result := []
  for label in m.labels do
    let i := nodeIndex m label.owner
    if i ≥ rects.size then throw .domain
    let node := rects[i]!
    let box ← measureLabel label.text
    let mut cells := 0
    for line in box.lines do
      let w : Int := Measure.cellWidth line.text
      cells := max cells (w * 512)
    let y := max 0 (min (Int.fdiv (2 * node.y + node.h) 2 - Int.fdiv box.h 2)
      (max (height - box.h) 0))
    let (x, align) := if 2 * node.x < width then (node.x + node.w + gap, Align.start)
      else (max (node.x - gap - box.w) 0, Align.«end»)
    result := result ++ [{ label, box, cells, align, rect := ⟨x, y, box.w, box.h⟩ }]
  return separateLabels result

def series (i : Nat) : Fin 12 := ⟨i % 12, Nat.mod_lt _ (by decide)⟩

def sceneOf (m : Model) (f : Flow) (rects : Array Rect) (labels : List LabelPlacement)
    (width height : Int) : Scene :=
  let boxes := m.boxes.zipIdx.map (fun (b, i) =>
    ({ id := b.id, role := b.role.id, parent := b.parent, exclusive := b.exclusive, rect := rects[i]! } : Box))
  let routes := m.routes.zipIdx.map (fun (r, i) =>
    let l := f.links[i]!
    let src := rects[l.source]!
    let tgt := rects[l.target]!
    ({ id := r.id, fromId := r.fromId, toId := r.toId, orthogonal := r.orthogonal, points := [⟨src.x + src.w, l.y0⟩, ⟨tgt.x, l.y1⟩] } : Route))
  let edges := m.routes.zipIdx.map (fun (r, i) =>
    let l := f.links[i]!
    let src := rects[l.source]!
    let tgt := rects[l.target]!
    let a : Point := ⟨src.x + src.w, l.y0⟩
    let b : Point := ⟨tgt.x, l.y1⟩
    let mid := Int.fdiv (a.x + b.x) 2
    ({ role := .edge, owner := r.id, items := [
      .path [.M a, .C ⟨mid, a.y⟩ ⟨mid, b.y⟩ b]
        { style := "series-flow", series := series l.source, width := .units l.width }] } : Group))
  let nodes := boxes.zipIdx.map (fun (b, i) =>
    let text := labels.filter (fun p => p.label.owner == b.id) |>.map (fun p =>
      Primitive.text { rect := p.rect, role := .label, size := 14, align := p.align, style := "text", lines := XY.runsOf p.box.lines })
    ({ role := .node, owner := b.id, items := .rect b.rect { style := "series", series := series i } :: text } : Group))
  { kind := "sankey", profile := .vector,
    options := { m.options with profile := .vector, direction := .TB },
    canvas := ⟨labels.foldl (fun w p => max w (p.rect.x + p.rect.w)) width,
      labels.foldl (fun h p => max h (p.rect.y + p.rect.h)) height⟩,
    boxes, routes, labels := labels.map (fun p =>
      { id := p.label.id, owner := p.label.owner, text := p.label.text, rect := p.rect,
        lines := p.box.lines.map (fun l => String.ofList l.text) }),
    items := edges ++ nodes }

def normalize (f : Flow) (rects : Array Rect) (labels : List LabelPlacement)
    (width height : Int) : Flow × Array Rect × List LabelPlacement × Int × Int :=
  let all := rects.toList ++ labels.map (·.rect)
  let minX := all.foldl (fun x r => min x r.x) 0
  let minY := all.foldl (fun y r => min y r.y) 0
  let minY := f.links.foldl (fun y l => min (min y l.y0) l.y1) minY
  let maxX := all.foldl (fun x r => max x (r.x + r.w))
    (labels.foldl (fun x p => max x (p.rect.x + p.rect.w)) width)
  let maxY := all.foldl (fun y r => max y (r.y + r.h))
    (labels.foldl (fun y p => max y (p.rect.y + p.rect.h)) height)
  let maxY := f.links.foldl (fun y l => max (max y l.y0) l.y1) maxY
  let move := fun (r : Rect) => { r with x := r.x - minX, y := r.y - minY }
  ({ f with links := f.links.map (fun l => { l with y0 := l.y0 - minY, y1 := l.y1 - minY }) },
    rects.map move, labels.map (fun p => { p with rect := move p.rect }),
    maxX - minX, maxY - minY)

def checkRect (r : Rect) : Except LayoutError Unit := do
  if r.w < 0 ∨ r.h < 0 then throw .domain
  for v in [r.x, r.y, r.w, r.h, r.x + r.w, r.y + r.h] do
    let _ ← Measure.checkedI32 v

def layoutCore (m : Model) : Except LayoutError Scene := do
  let width := configInt m "width" (Int.fdiv (LayoutConst.sankey_width.get .vector) 64) * 64
  let height := configInt m "height" (Int.fdiv (LayoutConst.sankey_height.get .vector) 64) * 64
  let padding := LayoutConst.sankey_node_padding.get .vector +
    (if showValues m then LayoutConst.sankey_show_values_pad.get .vector else 0)
  let f ← decode m height padding
  let f ← run f (configString m "nodeAlignment" "justify")
    (LayoutConst.sankey_iterations.get .vector).toNat
  let rects := nodeRects f width (LayoutConst.sankey_node_width.get .vector)
  let labels ← measureLabels m rects width height (LayoutConst.sankey_label_gap.get .vector)
  let (f, rects, labels, width, height) := normalize f rects labels width height
  let scene := sceneOf m f rects labels width height
  let _ ← Measure.checkedI32 scene.canvas.w
  let _ ← Measure.checkedI32 scene.canvas.h
  for b in scene.boxes do checkRect b.rect
  for l in scene.labels do checkRect l.rect
  for r in scene.routes do
    for p in r.points do
      let _ ← Measure.checkedI32 p.x
      let _ ← Measure.checkedI32 p.y
  return scene

def admissible (m : Model) : Bool :=
  !(m.routes.any (·.orthogonal) ||
    m.boxes.any (fun b => b.parent != "" || b.exclusive || b.role != .node))

def layout (m : Model) : Except LayoutError Scene :=
  if admissible m then layoutCore m else .error .domain

end Elegant.Chart.Sankey
