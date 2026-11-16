import Elegant.Kinds.Common
import Elegant.GridArchitectureLabels
import Elegant.GridArchitectureText
import Elegant.GridArchitectureIcons
import Elegant.GridArchitectureDecode

set_option autoImplicit false

namespace Elegant.Kinds.Architecture

private def field (shape key : String) : String :=
  let value := (((shape.splitOn ";").find? (fun s => s.startsWith (key ++ "="))).getD "").drop
    (key.length + 1) |>.toString
  if key == "icontext" then Grid.Architecture.unescapeShape value else value

private def side : Elegant.Side → Grid.Architecture.Side
  | .left => .left | .right => .right | .top => .top | _ => .bottom

private def text (_m : Model) (b : ModelBox) : String := b.text.getD ""

private def lines (metric : Measure.Metric) (width : Int) (s : String) :
    Except LayoutError (List Measure.Line) :=
  if s.isEmpty then .ok [] else StyledMeasure.wrap metric width s.toList

private def extent (lh : Int) (ls : List Measure.Line) : Size :=
  ⟨min COORD_LIMIT (Common.widest ls), min COORD_LIMIT ((ls.length : Int) * lh)⟩

private def textItem (source : String) (r : Rect) (align : Align) (ls : List Measure.Line) : Primitive :=
  Grid.Architecture.styledText source r align ls
private def axis (a b : Point) : MarkerAxis :=
  if (b.x-a.x).natAbs ≥ (b.y-a.y).natAbs then
    if b.x ≥ a.x then .positiveX else .negativeX
  else if b.y ≥ a.y then .positiveY else .negativeY

private def parentIndex (groups : List ModelBox) (id : String) : Except LayoutError Int :=
  if id.isEmpty then .ok (-1) else
    match groups.findIdx? (fun b => b.id == id) with
    | some i => .ok i | none => .error .domain

private def configInt (m : Model) (key : String) : Option Int :=
  match m.options.config.find? (fun q => q.1 == key) with
  | some (_, .integer v) => if 0 ≤ v ∧ v ≤ I32_MAX then some v else none
  | _ => none

private def alignments (nodes : List ModelBox) : List Grid.Architecture.Alignment :=
  let members := nodes.zipIdx.flatMap fun q =>
    (q.1.shape.splitOn ";").filterMap fun f =>
      if !f.startsWith "align=" then none else
      match ((f.drop 6).toString.splitOn ":") with
      | [set, direction, position] =>
        match set.toNat?, position.toNat? with
        | some s, some pos => some (s, direction == "c", pos, q.2)
        | _, _ => none
      | _ => none
  let sets := (members.map (·.1)).eraseDups.mergeSort (· ≤ ·)
  sets.map fun s =>
    let entries := (members.filter (fun q => q.1 == s)).mergeSort fun a b =>
      decide (a.2.2.1 < b.2.2.1) ||
        (a.2.2.1 == b.2.2.1 && decide (a.2.2.2 ≤ b.2.2.2))
    { column := ((entries.getLast?).map (fun q => q.2.1)).getD false,
      members := entries.map (fun q => q.2.2.2) }

def build (m : Model) : Except LayoutError (Scene × Bool) := do
  let profile := m.profile
  let cell := profile == .cell
  let lh := LayoutConst.line_h.get profile
  let inset := LayoutConst.architecture_title_inset.get profile
  let thickness := LayoutConst.architecture_line_thickness.get profile
  let border := LayoutConst.node_border.get profile
  let corner := LayoutConst.corner_radius.get profile
  let mut iw := LayoutConst.architecture_icon_width.get profile
  let mut ih := LayoutConst.architecture_icon_height.get profile
  let mut padding := LayoutConst.architecture_padding.get profile
  if let some px := configInt m "padding" then
    padding := if cell then Int.fdiv (2*px+20) 40 else px*64
  if let some px := configInt m "iconSize" then
    if px > 0 then
      iw := if cell then max 1 (Int.fdiv (14*px+80) 160) else px*64
      ih := if cell then max 1 (Int.fdiv (6*px+80) 160) else px*64
  let p : Grid.Architecture.GeometryParams :=
    ⟨LayoutConst.architecture_pitch_x.get profile, LayoutConst.architecture_pitch_y.get profile,
      LayoutConst.architecture_label_wrap.get profile, iw, ih, inset, lh,
      LayoutConst.architecture_label_gap.get profile, thickness, if cell then 1 else 0,
      LayoutConst.architecture_badge.get profile⟩
  let groups := m.boxes.filter (fun b => b.role == .group)
  let nodes := m.boxes.filter (fun b => b.role != .group)
  let metric ← Common.labelMetric profile
  let titles ← groups.mapM (fun b => lines metric I32_MAX (text m b))
  let captions ← nodes.mapM (fun b => lines metric p.labelWrap (text m b))
  let inner ← nodes.mapM (fun b => lines metric (max 1 (iw-2*inset)) (field b.shape "icontext"))
  let edgeTexts := m.routes.map fun r =>
    ((m.labels.find? (fun l => l.owner == r.id)).map (·.text)).getD ""
  let edgeLines ← edgeTexts.mapM (lines metric I32_MAX)
  let groupInput ← (groups.zip titles).mapM fun q => do
    let parent ← parentIndex groups q.1.parent
    let size := extent lh q.2
    pure (⟨parent, size.w, size.h, !(field q.1.shape "icon").isEmpty⟩ : Grid.Architecture.Group)
  if groupInput.zipIdx.any (fun q => decide (q.1.parent ≥ Int.ofNat q.2)) then throw .domain
  let nodeInput ← (nodes.zip captions).mapM fun q => do
    let parent ← parentIndex groups q.1.parent
    let junction := (q.1.shape.splitOn ";").head! == "junction"
    let size := if junction then LayoutConst.architecture_junction_size.get profile else iw
    let height := if junction then size else ih
    pure (⟨parent, junction, ⟨size,height⟩, extent lh q.2⟩ : Grid.Architecture.Node)
  let edges ← m.routes.mapM fun r => do
    let some a := nodes.findIdx? (fun b => b.id == r.fromId) | throw .domain
    let some b := nodes.findIdx? (fun b => b.id == r.toId) | throw .domain
    pure (⟨a,b,side r.fromSide,side r.toSide⟩ : Grid.Architecture.Edge)
  let input : Grid.Architecture.Input := ⟨nodeInput.map (·.parent), groupInput, edges⟩
  let sizes := edgeLines.map (extent lh)
  let pitch := Grid.Architecture.pitch p nodeInput sizes
  let params : Grid.Architecture.Params := ⟨pitch.x,pitch.y,
    (LayoutConst.architecture_ring_cap.get profile).toNat, alignments nodes⟩
  let frameParams : Grid.Architecture.FrameParams := ⟨padding,inset,lh,p.badge⟩
  let placed := Grid.Architecture.placeHierarchy input params frameParams
    (LayoutConst.architecture_bfs_cap.get profile).toNat
  let resolved := Grid.Architecture.resolveHierarchy input params placed
  let geometry := Grid.Architecture.geometry p pitch nodeInput groupInput resolved
  let rawRoutes := Grid.Architecture.routes p pitch nodeInput edges resolved geometry
  let rawBounds := Grid.Architecture.content geometry rawRoutes
  let bounds := if rawBounds = Grid.Architecture.emptySpan then
    (⟨0,0,0,0⟩ : Grid.Architecture.Span) else rawBounds
  let margin := LayoutConst.canvas_margin.get profile
  let rawLabels := Grid.Architecture.placeLabels p margin geometry rawRoutes sizes bounds
  let bounds := rawLabels.foldl (fun acc r =>
    if r.x0 < r.x1 ∧ r.y0 < r.y1 then acc.union r else acc) bounds
  let dx := margin-bounds.x0
  let dy := margin-bounds.y0
  let rect := Grid.Architecture.translateRect dx dy
  let boxes ← geometry.boxes.mapM rect
  let icons ← geometry.icons.mapM rect
  let labels ← geometry.labels.mapM rect
  let frames ← geometry.frames.mapM rect
  let titleRects ← geometry.titles.mapM rect
  let edgeRects ← rawLabels.mapM rect
  let routes ← rawRoutes.mapM (List.mapM (Grid.Architecture.translatePoint dx dy))
  let width := bounds.x1-bounds.x0+2*margin
  let height := bounds.y1-bounds.y0+2*margin
  if width < 0 ∨ height < 0 ∨ COORD_LIMIT < width ∨ COORD_LIMIT < height then throw .overflow
  let dumpBoxes ← m.boxes.mapM fun b => do
    let r ← if b.role == .group then
      match groups.findIdx? (fun q => q.id == b.id) with
      | some i => pure (frames.getD i ⟨0,0,0,0⟩) | none => throw .domain
    else
      match nodes.findIdx? (fun q => q.id == b.id) with
      | some i => pure (boxes.getD i ⟨0,0,0,0⟩) | none => throw .domain
    pure ({ id := b.id, role := b.role.id, parent := b.parent, exclusive := b.exclusive, rect := r } : Box)
  let dumpRoutes := m.routes.zipIdx.map fun q =>
    ({ id := q.1.id, fromId := q.1.fromId, toId := q.1.toId, orthogonal := q.1.orthogonal, points := routes.getD q.2 [] } : Route)
  let dumpLabels ← m.labels.mapM fun l => do
    let some i := m.routes.findIdx? (fun r => r.id == l.owner) | throw .domain
    pure ({ id := l.id, owner := l.owner, text := l.text, rect := edgeRects.getD i ⟨0,0,0,0⟩, lines := (edgeLines.getD i []).map (fun line => String.ofList line.text) } : SceneLabel)
  let mut items : List Elegant.Group := []
  for (b,i) in groups.zipIdx do
    let ls := titles.getD i []
    let frame := frames.getD i ⟨0,0,0,0⟩
    let name := field b.shape "icon"
    let iconItems := if name.isEmpty then [] else Grid.Architecture.iconItems profile name ⟨frame.x+inset,frame.y+inset⟩
    let primitives := [.rect frame { style := "group" }] ++ iconItems ++
      (if ls.isEmpty then [] else [textItem (text m b) (titleRects.getD i ⟨0,0,0,0⟩) .start ls])
    items := items ++ [{ role := .group, owner := b.id, items := primitives }]
  for (r,i) in m.routes.zipIdx do
    let points := routes.getD i []
    let mut primitives : List Primitive := []
    if points.length ≥ 2 then
      primitives := [.polyline points corner { style := "edge" }]
      if r.markerStart != "" ∧ r.markerStart != "none" then
        primitives := primitives ++ [.markerRef r.markerStart (points.getD 0 ⟨0,0⟩)
          (axis (points.getD 1 ⟨0,0⟩) (points.getD 0 ⟨0,0⟩))]
      if r.markerEnd != "" ∧ r.markerEnd != "none" then
        primitives := primitives ++ [.markerRef r.markerEnd (points.getD (points.length-1) ⟨0,0⟩)
          (axis (points.getD (points.length-2) ⟨0,0⟩) (points.getD (points.length-1) ⟨0,0⟩))]
    let ls := edgeLines.getD i []
    if !ls.isEmpty then primitives := primitives ++ [textItem (edgeTexts.getD i "") (edgeRects.getD i ⟨0,0,0,0⟩) .middle ls]
    items := items ++ [{role := .edge,owner := r.id,items := primitives}]
  for (b,i) in nodes.zipIdx do
    let box := boxes.getD i ⟨0,0,0,0⟩
    let icon := icons.getD i ⟨0,0,0,0⟩
    let n := nodeInput.getD i default
    let mut primitives : List Primitive := []
    if n.junction then
      primitives := if cell then [.symbolRef "disc" ⟨box.x,box.y⟩ "ink"] else
        [.ellipse (box.x+Int.fdiv box.w 2) (box.y+Int.fdiv box.h 2)
          (Int.fdiv box.w 2) (Int.fdiv box.h 2) {style := "ink"}]
    else
      primitives := if cell then [.rect icon {style := "node"}] else
        [.roundRect icon (min corner (min (Int.fdiv icon.w 2) (Int.fdiv icon.h 2))) {style := "node"}]
      let name := field b.shape "icon"
      if !name.isEmpty then
        let center : Point := ⟨icon.x+Int.fdiv icon.w 2,icon.y+Int.fdiv icon.h 2⟩
        let origin := if cell then center else (⟨center.x-768,center.y-768⟩ : Point)
        primitives := primitives ++ Grid.Architecture.iconItems profile name origin
      let room := max 1 (Int.fdiv (icon.h-2*border) lh)
      let inside := (inner.getD i []).take room.toNat
      if !inside.isEmpty then
        let h := (inside.length : Int)*lh
        primitives := primitives ++ [textItem (field b.shape "icontext")
          ⟨icon.x+inset,icon.y+border+Int.fdiv (icon.h-2*border-h) 2,max 1 (icon.w-2*inset),h⟩ .middle inside]
      let ls := captions.getD i []
      if !ls.isEmpty then primitives := primitives ++ [textItem (text m b) (labels.getD i ⟨0,0,0,0⟩) .middle ls]
    items := items ++ [{role := .node,owner := b.id,items := primitives}]
  pure ({kind := m.kind,profile := profile,options := m.options,canvas := ⟨width,height⟩,boxes := dumpBoxes,routes := dumpRoutes,labels := dumpLabels,items := items}, placed.budgetExhausted)

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if m.boxes.length > m.options.limits.maxNodes then
    throw (.tooLarge m.options.limits.maxNodes m.boxes.length)
  if m.routes.length > m.options.limits.maxEdges then
    throw (.tooLarge m.options.limits.maxEdges m.routes.length)
  let bytes := m.boxes.foldl (fun n b => n + (text m b).utf8ByteSize) 0 +
    m.labels.foldl (fun n l => n + l.text.utf8ByteSize) 0
  if bytes > m.options.limits.maxTextBytes then
    throw (.tooLarge m.options.limits.maxTextBytes bytes)
  match build m with
  | .error error => throw (.geometry error)
  | .ok (scene, capped) => pure {scene := scene.projectCellAttachments (Common.routeMarkers m),budgetExhausted := capped}

end Elegant.Kinds.Architecture
