import Elegant.Chart.GanttTicks
import Elegant.Chart.XY

set_option autoImplicit false

namespace Elegant.Chart.Gantt
open Validator


structure Task where
  «section» : Int
  startTime : Int
  endTime : Int
  renderEnd : Int
  milestone : Bool
  vert : Bool
  crit : Bool
  active : Bool
  done : Bool
  deriving Repr

def unzigzag (n : Int) : Int :=
  if Int.fmod n 2 = 0 then Int.fdiv n 2 else -(Int.fdiv n 2) - 1

def decodeTask (r : ModelRegionSet) : Option Task :=
  match r.regions with
  | flags :: sectionIndex :: startTime :: endTime :: renderEnd :: _ =>
    let flag (bit : Int) := Int.fmod (Int.fdiv flags bit) 2 == 1
    some ⟨sectionIndex - 1, unzigzag startTime, unzigzag endTime, unzigzag renderEnd,
      flag 1, flag 2, flag 4, flag 8, flag 16⟩
  | _ => none

def boxIndex (initial : Char) (id : String) : Option Nat :=
  match id.toList with
  | c :: rest => if c == initial then (String.ofList rest).toNat? else none
  | _ => none

def stringConfig (m : Model) (key : String) (fallback : String := "") : String :=
  match m.options.config.find? (fun e => e.1 == key) with
  | some (_, .string value) => value
  | _ => fallback

def boolConfig (m : Model) (key : String) : Bool :=
  match m.options.config.find? (fun e => e.1 == key) with
  | some (_, .boolean value) => value
  | _ => false

structure Consts where
  width : Int
  barH : Int
  rowGap : Int
  topPad : Int
  gutter : Int
  sidePad : Int
  axisH : Int
  tickLen : Int
  tickGap : Int
  titlePad : Int
  labelGap : Int
  sectionPad : Int
  vertW : Int
  tickCap : Int
  estimateCap : Int
  excludeYears : Int
  edge : Int

def loadConsts (m : Model) : Except LayoutError Consts := do
  let p := m.profile
  let configured (key : String) (fallback cellPx : Int) : Except LayoutError Int :=
    match m.options.config.find? (fun e => e.1 == key) with
    | some (_, .integer value) =>
      if value < -33554432 ∨ 33554432 < value then .error .overflow
      else pure (if p == .cell then ceilDiv value cellPx else value * 64)
    | _ => pure fallback
  let barH ← configured "barHeight" (LayoutConst.gantt_bar_height.get p) 16
  let rowGap ← configured "barGap" (LayoutConst.gantt_row_gap.get p) 16
  let topPad ← configured "topPadding" (LayoutConst.gantt_top_pad.get p) 16
  let gutter ← configured "leftPadding" (LayoutConst.gantt_label_gutter.get p) 8
  let sidePad ← configured "rightPadding" (LayoutConst.gantt_side_pad.get p) 8
  return ⟨LayoutConst.gantt_width.get p, barH, rowGap, topPad, gutter, sidePad,
    LayoutConst.gantt_axis_height.get p, LayoutConst.gantt_tick_length.get p,
    LayoutConst.gantt_tick_label_gap.get p, LayoutConst.gantt_title_pad.get p,
    LayoutConst.gantt_label_gap.get p, LayoutConst.gantt_section_pad.get p,
    LayoutConst.gantt_vert_width.get p, LayoutConst.gantt_tick_cap.get p,
    LayoutConst.gantt_tick_estimate_cap.get p, LayoutConst.gantt_exclude_years_max.get p,
    if p == .cell then 1 else 0⟩

structure Plan where
  model : Model
  c : Consts
  tasks : List Task
  rows : List String
  axis : Axis
  tickValues : List Int
  capped : Bool

def Plan.pitch (p : Plan) : Int := p.c.barH + p.c.rowGap

def Plan.axisY (p : Plan) : Int := p.c.topPad + (p.rows.length : Int) * p.pitch

def Plan.height (p : Plan) : Int := p.axisY + p.c.axisH

def Plan.plot (p : Plan) : Rect :=
  ⟨0, p.c.topPad, p.c.width, (p.rows.length : Int) * p.pitch⟩

def Plan.row (p : Plan) (id : String) : Int :=
  ((p.rows.zipIdx.find? (fun entry => entry.1 == id)).map (fun entry => (entry.2 : Int))).getD (-1)

def semanticConfig (m : Model) : Bool :=
  m.options.config.all fun entry =>
    if entry.1 == "barGap" then
      match entry.2 with
      | .integer value => 0 ≤ value
      | _ => true
    else true

def prepare (m : Model) : Except LayoutError Plan := do
  if !semanticConfig m then throw .domain
  let c ← loadConsts m
  let tasks := m.regionSets.filterMap decodeTask
  if tasks.any (fun t => [t.startTime, t.endTime, t.renderEnd].any
      (fun value => value < -8640000000000 || 8640000000000 < value)) then throw .overflow
  let sections := m.boxes.filter (fun b => (boxIndex 's' b.id).isSome)
  if tasks.any (fun t => t.section < -1 || (sections.length : Int) ≤ t.section) then throw .domain
  let rows := m.boxes.filterMap fun b =>
    if (boxIndex 's' b.id).isSome then some b.id else
      match boxIndex 't' b.id with
      | some i => match tasks[i]? with
        | some task => if task.vert then none else some b.id
        | none => none
      | none => none
  let domain : Int × Int := match tasks with
    | [] => (0, 86400)
    | first :: rest => rest.foldl (fun (range : Int × Int) (t : Task) =>
        (min range.1 t.startTime, max range.2 t.endTime)) (first.startTime, first.endTime)
  let axis : Axis := ⟨domain.1, domain.2, c.gutter, c.width - c.sidePad⟩
  let (tickValues, capped) := ticks axis c.tickCap c.estimateCap
    (stringConfig m "tickInterval") (stringConfig m "weekday" "sunday")
  for tick in tickValues do
    let _ ← axis.positionChecked tick
    pure ()
  pure ⟨m, c, tasks, rows, axis, tickValues, capped⟩

def Plan.taskRect (p : Plan) (task : Task) (row : Int) : Rect :=
  let start := p.axis.position task.startTime
  let top := rowStart p.c.topPad p.c.barH p.c.rowGap row
  if task.vert then
    ⟨start - Int.fdiv p.c.vertW 2, p.c.topPad, p.c.vertW, (p.rows.length : Int) * p.pitch⟩
  else if task.milestone then
    ⟨milestoneLeft p.axis p.c.barH task.startTime task.endTime, top, p.c.barH, p.c.barH⟩
  else ⟨start, top, barWidth p.axis task.startTime task.renderEnd p.c.edge, p.c.barH⟩

def Plan.boxRect (p : Plan) (b : ModelBox) : Except LayoutError Rect := do
  let r ← if b.id == "plot" then pure p.plot
    else if (boxIndex 's' b.id).isSome then
      pure ⟨0, rowStart p.c.topPad p.c.barH p.c.rowGap (p.row b.id), p.c.width, p.pitch⟩
    else match boxIndex 't' b.id with
      | some i => match p.tasks[i]? with
        | some task => do
          let _ ← p.axis.positionChecked task.startTime
          if !task.vert then
            let _ ← p.axis.positionChecked (if task.milestone then task.endTime else task.renderEnd)
            pure ()
          pure (p.taskRect task (p.row b.id))
        | none => throw .domain
      | none => throw .domain
  let r := if b.id == "plot" then r else
    { r with x := clamp r.x 0 (max (p.c.width - r.w) 0) }
  if Rect.Valid r then pure r else throw .overflow

inductive LabelKind where
  | title | section | task | tick | topTick
  deriving DecidableEq

structure LabelSpec where
  source : ModelLabel
  kind : LabelKind
  index : Nat
  role : Measure.Role
  size : Int
  box : XY.TextBox

structure PlacedLabel where
  spec : LabelSpec
  rect : Rect
  align : Align
  shown : Bool
  chip : Bool

def measureLabel (p : Plan) (l : ModelLabel) : Except LayoutError LabelSpec := do
  let (kind, index, role, size) :=
    if l.id == "title" then (LabelKind.title, 0, Measure.Role.title, 16)
    else if (boxIndex 's' l.owner).isSome then
      (.section, (boxIndex 's' l.owner).getD 0, .label, 14)
    else if (boxIndex 't' l.owner).isSome then
      (.task, (boxIndex 't' l.owner).getD 0, .label, 12)
    else if l.id.startsWith "xt.t" then
      (.topTick, ((String.ofList (l.id.toList.drop 4)).toNat?).getD 0, .label, 10)
    else (.tick, ((String.ofList (l.id.toList.drop 3)).toNat?).getD 0, .label, 10)
  let box ← XY.measureText (fontFamily := p.model.options.fontFamily) (p.model.profile == .cell) l.text role size
  pure ⟨l, kind, index, role, size, box⟩

def Plan.taskLabelRect (p : Plan) (task : Task) (box : Rect) (text : XY.TextBox) : Rect × Align :=
  let x0 := box.x
  let x1 := box.x + box.w
  if task.vert then
    let below := p.axisY + p.c.tickLen + p.c.edge + p.c.tickGap +
      XY.lineHeight (p.model.profile == .cell) .label 10 + p.c.tickGap
    (⟨x0 + Int.fdiv (box.w - text.w) 2, below, text.w, text.h⟩, .middle)
  else
    let y := box.y + Int.fdiv (p.c.barH - text.h) 2
    let inside : Rect := ⟨x0 + Int.fdiv (box.w - text.w) 2, y, text.w, text.h⟩
    let left : Rect := ⟨x0 - p.c.labelGap - text.w, y, text.w, text.h⟩
    let right : Rect := ⟨x1 + p.c.labelGap, y, text.w, text.h⟩
    if p.model.profile != .cell && !task.milestone && text.w ≤ box.w then (inside, .middle)
    else if 2 * (x1 + text.w) + p.c.gutter > 2 * p.c.width && 0 ≤ left.x then (left, .«end»)
    else if right.x + right.w ≤ p.c.width then (right, .start)
    else if 0 ≤ left.x then (left, .«end»)
    else if p.model.profile == .cell then (⟨x0, box.y + p.c.barH, text.w, text.h⟩, .start)
    else (inside, .middle)

def Plan.labelRect (p : Plan) (boxes : List Box) (l : LabelSpec) : Except LayoutError (Rect × Align) := do
  let text := l.box
  match l.kind with
  | .title =>
    let half := Int.fdiv text.w 2
    let centre := clamp (Int.fdiv p.c.width 2) half (p.c.width - half)
    pure (⟨centre - half, p.c.titlePad, text.w, text.h⟩, .middle)
  | .section => pure (⟨p.c.sectionPad,
      rowStart p.c.topPad p.c.barH p.c.rowGap (p.row l.source.owner) +
      Int.fdiv (p.c.barH - text.h) 2, text.w, text.h⟩, .start)
  | .task =>
    match p.tasks[l.index]?, boxes.find? (fun b => b.id == l.source.owner) with
    | some task, some box => pure (p.taskLabelRect task box.rect text)
    | _, _ => throw .domain
  | kind =>
    match p.tickValues[l.index]? with
    | none => throw .domain
    | some tick => do
      let _ ← p.axis.positionChecked tick
      let y := if kind == .topTick then p.c.topPad - p.c.edge - p.c.tickLen - p.c.tickGap - text.h
        else p.axisY + p.c.tickLen + p.c.edge + p.c.tickGap
      pure (⟨p.axis.position tick - Int.fdiv text.w 2, y, text.w, text.h⟩, .middle)

def hasSeries (task : Task) : Bool :=
  !task.crit && !task.done && !task.active && 0 ≤ task.section

def placeLabel (p : Plan) (boxes : List Box) (previous : List PlacedLabel) (spec : LabelSpec) :
    Except LayoutError PlacedLabel := do
  let (r, align) ← p.labelRect boxes spec
  let r := { r with
    x := clamp r.x 0 (max (p.c.width - r.w) 0)
    y := clamp r.y 0 (max (p.height - r.h) 0) }
  let overlap := p.model.profile == .cell && previous.any (fun other =>
    other.shown && r.x < other.rect.x + other.rect.w + p.c.edge &&
    other.rect.x < r.x + r.w + p.c.edge && r.y < other.rect.y + other.rect.h &&
    other.rect.y < r.y + r.h)
  if overlap then pure ⟨spec, ⟨0, 0, 0, 0⟩, .middle, false, false⟩ else
    if ¬ Rect.Valid r then throw .overflow else
      let chip := spec.kind == .task && align == .middle &&
        (p.tasks[spec.index]?).any (fun task => !task.vert && !task.milestone && hasSeries task)
      pure ⟨spec, r, align, true, chip⟩

def placeLabels (p : Plan) (boxes : List Box) : List ModelLabel → List PlacedLabel →
    Except LayoutError (List PlacedLabel)
  | [], previous => pure previous
  | source :: rest, previous => do
    let spec ← measureLabel p source
    let placed ← placeLabel p boxes previous spec
    placeLabels p boxes rest (previous ++ [placed])

def ruleLine (x0 y0 x1 y1 : Int) : Primitive :=
  .polyline [⟨x0, y0⟩, ⟨x1, y1⟩] 0 { style := "rule" }

def axisItems (p : Plan) (y sign : Int) : List Primitive :=
  [ruleLine p.c.gutter y (p.c.width - p.c.sidePad) y] ++ p.tickValues.flatMap fun t =>
    let x := p.axis.position t
    (if 0 < p.c.tickLen then [ruleLine x y x (y + sign * p.c.tickLen)] else []) ++
    (if p.model.profile == .cell || sign < 0 || p.rows.isEmpty then []
     else [ruleLine x p.c.topPad x y])

def barPaint (task : Task) : Paint :=
  if task.crit then { style := "error" }
  else if task.done then { style := "success" }
  else if task.active then { style := "note" }
  else if task.section < 0 then { style := "node" }
  else { style := "series", series := ⟨(Int.fmod task.section 12).toNat % 12, Nat.mod_lt _ (by decide)⟩ }

def taskItems (p : Plan) (task : Task) (r : Rect) : List Primitive :=
  if task.vert then [.rect r { style := "ink" }]
  else if task.milestone then
    if p.model.profile == .cell then [.symbolRef "diamond" ⟨r.x, r.y⟩ "ink"]
    else
      let cx := r.x + Int.fdiv r.w 2
      let cy := r.y + Int.fdiv r.h 2
      [.polygon [⟨cx, r.y⟩, ⟨r.x + r.w, cy⟩, ⟨cx, r.y + r.h⟩, ⟨r.x, cy⟩] { style := "ink" }]
  else [.rect r (barPaint task)]

def labelItems (owner : String) (labels : List PlacedLabel) : List Primitive :=
  labels.flatMap fun l =>
    if l.spec.source.owner != owner || !l.shown then [] else
      (if l.chip then [.rect l.rect { style := "plate" }] else []) ++
      [.text {
        rect := l.rect
        role := XY.textRoleOf l.spec.role
        size := l.spec.size
        align := l.align
        style := if l.spec.kind == .tick || l.spec.kind == .topTick then "text-muted" else "text"
        lines := XY.runsOf l.spec.box.lines }]

def sceneOf (p : Plan) (boxes : List Box) (labels : List PlacedLabel)
    (excluded : List Primitive) : Scene :=
  let under := excluded ++ axisItems p p.axisY 1 ++
    (if boolConfig p.model "topAxis" then axisItems p (p.c.topPad - p.c.edge) (-1) else [])
  let groups := boxes.map fun b =>
    let shapes := if (boxIndex 's' b.id).isSome then [.rect b.rect { style := "band" }]
      else match boxIndex 't' b.id with
        | some i => match p.tasks[i]? with
          | some task => taskItems p task b.rect
          | none => []
        | none => []
    { role := GroupRole.node, owner := b.id, items := shapes ++ labelItems b.id labels : Group }
  { kind := "gantt", profile := p.model.profile,
    options := { p.model.options with direction := .TB }, canvas := ⟨p.c.width, p.height⟩,
    boxes := boxes,
    labels := labels.map (fun l => {
      id := l.spec.source.id
      owner := l.spec.source.owner
      text := l.spec.source.text
      rect := l.rect
      lines := if l.shown then l.spec.box.lines.map (fun line => String.ofList line.text) else [] })
    items := (if under.isEmpty then [] else [{ role := .decor, owner := "", items := under }]) ++ groups }

end Elegant.Chart.Gantt
