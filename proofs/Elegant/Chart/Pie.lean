import Elegant.Chart.Radar

set_option autoImplicit false

namespace Elegant.Chart.Pie

structure Slice where
  index : Nat
  start : Int
  sweep : Int
  deriving Repr, DecidableEq

def bases (values : List Int) : List Int :=
  values.map (fun v => Int.fdiv (65536 * v) values.sum)

def remainderLE (total : Int) (a b : Int × Nat) : Bool :=
  let ra := Int.fmod (65536 * a.1) total
  let rb := Int.fmod (65536 * b.1) total
  ra > rb || (ra == rb && a.2 ≤ b.2)

def remainderPairs (values : List Int) : List (Int × Nat) :=
  values.zipIdx.mergeSort (remainderLE values.sum)

def remainderOrder (values : List Int) : List Nat :=
  (remainderPairs values).map Prod.snd

def extras (values : List Int) : List Nat :=
  (remainderOrder values).take (65536 - (bases values).sum).toNat

def sweeps (values : List Int) : List Int :=
  if values.sum = 0 then values.map (fun _ => 0) else
    (bases values).zipIdx.map fun (v, i) => v + if (extras values).contains i then 1 else 0

def scanSlices (start : Int) (index : Nat) : List Int → List Slice
  | [] => []
  | sweep :: rest =>
    (if sweep > 0 then [⟨index, start, sweep⟩] else []) ++
      scanSlices (start + sweep) (index + 1) rest

def slices (values : List Int) : List Slice :=
  scanSlices 0 0 (sweeps values)

def vertex (cx cy radius angle : Int) : Point :=
  ⟨cx + Int.fdiv (2 * radius * cosQ15 angle + 32768) 65536,
   cy + Int.fdiv (2 * radius * sinQ15 angle + 32768) 65536⟩

def arcPoints (cx cy radius start sweep : Int) : List Point :=
  let lo := min start (start + sweep)
  let hi := max start (start + sweep)
  let first := Int.fdiv (lo + 16383) 16384 * 16384
  [vertex cx cy radius start, vertex cx cy radius (start + sweep)] ++
    (List.range (Int.fdiv (hi - first) 16384 + 1).toNat).map
      (fun (i : Nat) => vertex cx cy radius (first + (i : Int) * 16384))

def circle (cx cy radius start half : Int) : List PathCommand :=
  [.M (vertex cx cy radius start), .A ⟨cx, cy⟩ radius (Int.fmod start 65536) half,
   .A ⟨cx, cy⟩ radius (Int.fmod (start + half) 65536) half, .Z]

def path (cx cy radius inner : Int) (sl : Slice) : List PathCommand :=
  let start := Int.fmod (sl.start - 16384) 65536
  if sl.sweep = 65536 then circle cx cy radius start 32768 ++
    if inner > 0 then circle cx cy inner start (-32768) else []
  else
    (if inner = 0 then [.M ⟨cx, cy⟩, .L (vertex cx cy radius start)]
     else [.M (vertex cx cy radius start)]) ++
    [.A ⟨cx, cy⟩ radius start sl.sweep] ++
    (if inner > 0 then [.L (vertex cx cy inner (start + sl.sweep)),
      .A ⟨cx, cy⟩ inner (Int.fmod (start + sl.sweep) 65536) (-sl.sweep)] else []) ++ [.Z]

def sliceRect (cx cy radius inner : Int) (sl : Slice) : Rect :=
  let a := Int.fmod (sl.start - 16384) 65536
  Radar.bounds (arcPoints cx cy radius a sl.sweep ++
    if inner = 0 then [⟨cx, cy⟩] else arcPoints cx cy inner a sl.sweep)

def values (m : Model) : List Int :=
  m.regionSets.filterMap fun r =>
    if r.regions.length ≥ 3 && r.regions.head? == some 1 then some (r.regions.getD 1 0) else none

def modelRelations (m : Model) : Bool :=
  match m.boxes with
  | [] => false
  | root :: rest =>
    root.id == "plot" && root.role == .node && root.parent == "" && !root.exclusive &&
      rest.all (fun b => b.role == .node && b.parent == "plot" && !b.exclusive) &&
      m.routes.isEmpty

structure Caption where
  source : ModelLabel
  lines : List Measure.Line
  rect : Rect
  kind : Nat
  index : Nat

def constant (name : String) : Int :=
  match name with
  | "pie.height" => LayoutConst.pie_height.vector
  | "pie.margin" => LayoutConst.pie_margin.vector
  | "pie.legend_row" => LayoutConst.pie_legend_row.vector
  | "pie.legend_size" => LayoutConst.pie_legend_size.vector
  | "pie.legend_offset" => LayoutConst.pie_legend_offset.vector
  | "pie.text_position_m" => LayoutConst.pie_text_position_m.vector
  | "pie.title_pad" => LayoutConst.pie_title_pad.vector
  | _ => 0

def assemble (m : Model) (inner : Int) (captions : List Caption) : Scene :=
  let height := constant "pie.height"
  let margin := constant "pie.margin"
  let row := constant "pie.legend_row"
  let size := constant "pie.legend_size"
  let offset := constant "pie.legend_offset"
  let cx := Int.fdiv height 2
  let cy := cx
  let radius := cx - margin
  let vs := values m
  let ss := slices vs
  let top := cy - Int.fdiv (row * (vs.length : Int)) 2
  let left := cx + offset
  let swatches := (List.range vs.length).map fun (i : Nat) =>
    (⟨left, top + (i : Int) * row, size, size⟩ : Rect)
  let longest := (captions.filter (fun t => t.kind == 2)).foldl (fun n t => max n t.rect.w) 0
  let points := Radar.corners ⟨0, 0, height, height⟩ ++ captions.flatMap (fun t => Radar.corners t.rect) ++
    swatches.flatMap Radar.corners ++ if vs.isEmpty then [] else [⟨height + margin + row + longest, height⟩]
  let extent := Radar.bounds points
  let dx := -extent.x
  let dy := -extent.y
  let rectAt := Radar.shiftRect dx dy
  let captionAt := captions.map fun t => { t with rect := rectAt t.rect }
  let plot := rectAt ⟨0, 0, height, height⟩
  let boxes := m.boxes.map fun b =>
    let sl := ss.find? (fun s => b.id == "s" ++ toString s.index)
    let rect := if b.id == "plot" then plot else match sl with
      | none => plot
      | some sl => sliceRect (cx + dx) (cy + dy) radius inner sl
    ({ id := b.id, role := b.role.id, parent := b.parent, exclusive := b.exclusive, rect } : Box)
  let labels := captionAt.map fun t =>
    ({ id := t.source.id, owner := t.source.owner, text := t.source.text, rect := t.rect,
       lines := t.lines.map (fun l => String.ofList l.text) } : SceneLabel)
  let text := fun t => Primitive.text {
    rect := t.rect, role := if t.kind = 0 then .title else .label,
    size := if t.kind = 0 then 16 else 14, align := if t.kind = 2 then .start else .middle,
    style := "text", lines := t.lines.map (fun l => [⟨String.ofList l.text, false, false⟩]) }
  let plotItems := swatches.zipIdx.map (fun (r, i) => Primitive.rect (rectAt r) (Radar.seriesPaint "series" i)) ++
    (captionAt.filter (fun t => t.kind != 1)).map text
  let groups := (⟨.node, "plot", plotItems⟩ : Group) :: ss.map fun sl =>
    let owner := "s" ++ toString sl.index
    let ts := captionAt.filter (fun t => t.kind == 1 && t.source.owner == owner)
    ⟨.node, owner, [.path (path (cx + dx) (cy + dy) radius inner sl) (Radar.seriesPaint "series" sl.index)] ++
      ts.flatMap (fun t => [.rect t.rect { style := "plate" }, text t])⟩
  {
    kind := m.kind
    profile := .vector
    options := { m.options with profile := .vector, direction := .TB }
    canvas := ⟨extent.w, extent.h⟩
    boxes
    labels
    items := groups }

def layout (m : Model) : Except LayoutError Scene := do
  if !modelRelations m then throw .domain
  let c := constant
  let height := c "pie.height"
  let margin := c "pie.margin"
  let row := c "pie.legend_row"
  let size := c "pie.legend_size"
  let offset := c "pie.legend_offset"
  let cx := Int.fdiv height 2
  let cy := cx
  let radius := cx - margin
  let donut := Radar.config m.options "donutHole" 0
  let inner := if 0 < donut ∧ donut ≤ 900 then Int.fdiv (radius * donut) 1000 else 0
  let pos := Radar.config m.options "textPosition" (c "pie.text_position_m")
  let pos := if 0 ≤ pos ∧ pos ≤ 1000 then pos else c "pie.text_position_m"
  let labelRadius := Int.fdiv (radius * pos) 1000
  let vs := values m
  Radar.checkRange (vs ++ [vs.sum])
  let ss := slices vs
  let top := cy - Int.fdiv (row * (vs.length : Int)) 2
  let left := cx + offset
  let captions ← m.labels.mapM fun l => do
    let kind := if l.id == "title" then 0 else if l.id.startsWith "legend." then 2 else 1
    let index := if kind = 2 then ((String.ofList (l.id.toList.drop 7)).toNat?).getD 0
      else ((String.ofList ((l.owner.toList).drop 1)).toNat?).getD 0
    let metric ← if kind = 0 then Measure.Role.title.metric else Measure.Role.label.metric
    let lines ← Kinds.Common.unwrapped metric l.text
    let w := Kinds.Common.widest lines
    let h := (lines.length : Int) * (if kind = 0 then 1536 else 1280)
    let sl := (ss.find? (fun s => s.index == index)).getD ⟨0, 0, 0⟩
    let a := sl.start + Int.fdiv sl.sweep 2
    let x := cx + Int.fdiv (labelRadius * sinQ15 a) 32768
    let y := cy - Int.fdiv (labelRadius * cosQ15 a) 32768
    let rect := if kind = 0 then ⟨cx - Int.fdiv w 2, c "pie.title_pad", w, h⟩
      else if kind = 2 then ⟨left + row, top + (index : Int) * row + Int.fdiv (size - h) 2, w, h⟩
      else ⟨x - Int.fdiv w 2, y - Int.fdiv h 2, w, h⟩
    pure ({ source := l, lines, rect, kind, index } : Caption)
  let scene := assemble m inner captions
  Radar.checkRange ([scene.canvas.w, scene.canvas.h] ++ scene.boxes.flatMap (fun b =>
    [b.rect.x, b.rect.y, b.rect.w, b.rect.h, b.rect.x + b.rect.w, b.rect.y + b.rect.h]) ++
    scene.labels.flatMap (fun l => [l.rect.x, l.rect.y, l.rect.w, l.rect.h, l.rect.x + l.rect.w, l.rect.y + l.rect.h]))
  return scene

end Elegant.Chart.Pie
