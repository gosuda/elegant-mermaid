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

def parentIndex (groups : List ModelBox) (id : String) : Except LayoutError Int :=
  if id.isEmpty then .ok (-1) else
    match groups.findIdx? (fun b => b.id == id) with
    | some i => .ok i | none => .error .domain

def configInt (m : Model) (key : String) : Option Int :=
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

/-- Every node's box must stay inside its pitch tile: the icon keeps `gutter` clearance to
the tile's side edges, and the caption may not push the box below the tile bottom minus the
port gutter. Junction icons are centered in the tile and ordinary icons sit on `pitch.top`,
so this measured bound is what keeps clauses C2, C3, C6 and C8 true. -/
def nodeTileFits (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch) (n : Grid.Architecture.Node) : Bool :=
  decide (Int.fdiv (pitch.x - n.icon.w) 2 ≥ p.gutter) &&
    decide ((if n.junction then Int.fdiv (pitch.y - n.icon.h) 2 else pitch.top) +
      n.icon.h + n.label.h + (if n.label.h > 0 then p.thickness else 0) ≤
        pitch.y - p.gutter)

def archIconWidth (m : Model) : Int :=
  match configInt m "iconSize" with
  | some px => if px > 0 then
      (if m.profile == .cell then max 1 (Int.fdiv (14*px+80) 160) else px*64)
    else LayoutConst.architecture_icon_width.get m.profile
  | none => LayoutConst.architecture_icon_width.get m.profile

def archIconHeight (m : Model) : Int :=
  match configInt m "iconSize" with
  | some px => if px > 0 then
      (if m.profile == .cell then max 1 (Int.fdiv (6*px+80) 160) else px*64)
    else LayoutConst.architecture_icon_height.get m.profile
  | none => LayoutConst.architecture_icon_height.get m.profile

def archPadding (m : Model) : Int :=
  match configInt m "padding" with
  | some px => if m.profile == .cell then Int.fdiv (2*px+20) 40 else px*64
  | none => LayoutConst.architecture_padding.get m.profile

def archParams (m : Model) : Grid.Architecture.GeometryParams :=
  let profile := m.profile
  ⟨LayoutConst.architecture_pitch_x.get profile,
    LayoutConst.architecture_pitch_y.get profile,
    LayoutConst.architecture_label_wrap.get profile, archIconWidth m,
    archIconHeight m, LayoutConst.architecture_title_inset.get profile,
    LayoutConst.line_h.get profile, LayoutConst.architecture_label_gap.get profile,
    LayoutConst.architecture_line_thickness.get profile,
    if profile == .cell then 1 else 0, LayoutConst.architecture_badge.get profile⟩

def archLineHeight (m : Model) : Int := LayoutConst.line_h.get m.profile

def archPitch (m : Model) (nodeInput : List Grid.Architecture.Node)
    (edgeLines : List (List Measure.Line)) : Grid.Architecture.Pitch :=
  Grid.Architecture.pitch (archParams m) nodeInput
    (edgeLines.map (extent (archLineHeight m)))

def build (m : Model) : Except LayoutError (Scene × Bool) := do
  let profile := m.profile
  let cell := profile == .cell
  let lh := LayoutConst.line_h.get profile
  let inset := LayoutConst.architecture_title_inset.get profile
  let border := LayoutConst.node_border.get profile
  let corner := LayoutConst.corner_radius.get profile
  let iw := archIconWidth m
  let ih := archIconHeight m
  let padding := archPadding m
  let p : Grid.Architecture.GeometryParams := archParams m
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
  let pitch := archPitch m nodeInput edgeLines
  let params : Grid.Architecture.Params := ⟨pitch.x,pitch.y,
    (LayoutConst.architecture_ring_cap.get profile).toNat, alignments nodes⟩
  let frameParams : Grid.Architecture.FrameParams := ⟨padding,inset,lh,p.badge⟩
  if nodeInput.any (fun n => !(nodeTileFits (archParams m)
      (archPitch m nodeInput edgeLines) n)) then throw .domain
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
  let scene : Scene := {kind := m.kind,profile := profile,options := m.options,canvas := ⟨width,height⟩,boxes := dumpBoxes,routes := dumpRoutes,labels := dumpLabels,items := items}
  pure (scene, placed.budgetExhausted)


private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem build_success (m : Model) (scene : Scene) (capped : Bool)
    (h : build m = .ok (scene, capped)) :
    ∃ (profile : Profile) (cell : Bool)
      (lh inset thickness border corner : Int)
      (iw ih padding : Int)
      (p : Grid.Architecture.GeometryParams)
      (groups nodes : List ModelBox)
      (metric : Measure.Metric)
      (titles captions inner : List (List Measure.Line))
      (edgeTexts : List String)
      (edgeLines : List (List Measure.Line))
      (groupInput : List Grid.Architecture.Group)
      (nodeInput : List Grid.Architecture.Node)
      (edges : List Grid.Architecture.Edge)
      (input : Grid.Architecture.Input)
      (sizes : List Size)
      (pitch : Grid.Architecture.Pitch)
      (params : Grid.Architecture.Params)
      (frameParams : Grid.Architecture.FrameParams)
      (placed : Grid.Architecture.Placement)
      (resolved : Grid.Architecture.Resolved)
      (geometry : Grid.Architecture.Geometry)
      (rawRoutes : List (List Point))
      (rawBounds bounds0 bounds : Grid.Architecture.Span)
      (margin dx dy width height : Int)
      (rawLabels : List Grid.Architecture.Span)
      (boxes icons labels frames titleRects edgeRects : List Rect)
      (routes : List (List Point))
      (dumpBoxes : List Box)
      (dumpRoutes : List Route)
      (dumpLabels : List SceneLabel)
      (items : List Elegant.Group),
      profile = m.profile ∧
      cell = (profile == .cell) ∧
      lh = LayoutConst.line_h.get profile ∧
      inset = LayoutConst.architecture_title_inset.get profile ∧
      thickness = LayoutConst.architecture_line_thickness.get profile ∧
      border = LayoutConst.node_border.get profile ∧
      corner = LayoutConst.corner_radius.get profile ∧
      iw = (match configInt m "iconSize" with
        | some px => if px > 0 then
            (if cell then max 1 (Int.fdiv (14*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_width.get profile
        | none => LayoutConst.architecture_icon_width.get profile) ∧
      ih = (match configInt m "iconSize" with
        | some px => if px > 0 then
            (if cell then max 1 (Int.fdiv (6*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_height.get profile
        | none => LayoutConst.architecture_icon_height.get profile) ∧
      padding = (match configInt m "padding" with
        | some px => if cell then Int.fdiv (2*px+20) 40 else px*64
        | none => LayoutConst.architecture_padding.get profile) ∧
      p = ⟨LayoutConst.architecture_pitch_x.get profile,
        LayoutConst.architecture_pitch_y.get profile,
        LayoutConst.architecture_label_wrap.get profile, iw, ih, inset, lh,
        LayoutConst.architecture_label_gap.get profile, thickness,
        if cell then 1 else 0, LayoutConst.architecture_badge.get profile⟩ ∧
      groups = m.boxes.filter (fun b => b.role == .group) ∧
      nodes = m.boxes.filter (fun b => b.role != .group) ∧
      Common.labelMetric profile = .ok metric ∧
      groups.mapM (fun b => lines metric I32_MAX (text m b)) = .ok titles ∧
      nodes.mapM (fun b => lines metric p.labelWrap (text m b)) = .ok captions ∧
      nodes.mapM (fun b => lines metric (max 1 (iw - 2*inset))
        (field b.shape "icontext")) = .ok inner ∧
      edgeTexts = m.routes.map (fun r =>
        ((m.labels.find? (fun l => l.owner == r.id)).map (·.text)).getD "") ∧
      edgeTexts.mapM (lines metric I32_MAX) = .ok edgeLines ∧
      (groups.zip titles).mapM (fun q => do
        let parent ← parentIndex groups q.1.parent
        let size := extent lh q.2
        pure (⟨parent, size.w, size.h,
          !(field q.1.shape "icon").isEmpty⟩ : Grid.Architecture.Group)) = .ok groupInput ∧
      ¬(groupInput.zipIdx.any (fun q =>
        decide (q.1.parent ≥ Int.ofNat q.2)) = true) ∧
      (nodes.zip captions).mapM (fun q => do
        let parent ← parentIndex groups q.1.parent
        let junction := (q.1.shape.splitOn ";").head! == "junction"
        let size := if junction then
          LayoutConst.architecture_junction_size.get profile else iw
        let height := if junction then size else ih
        pure (⟨parent, junction, ⟨size, height⟩, extent lh q.2⟩ :
          Grid.Architecture.Node)) = .ok nodeInput ∧
      m.routes.mapM (fun (r : ModelRoute) => do
        let some a := nodes.findIdx? (fun b => b.id == r.fromId) | throw LayoutError.domain
        let some b := nodes.findIdx? (fun b => b.id == r.toId) | throw LayoutError.domain
        pure (⟨a, b, side r.fromSide, side r.toSide⟩ :
          Grid.Architecture.Edge)) = (Except.ok edges :
            Except LayoutError (List Grid.Architecture.Edge)) ∧
      input = ⟨nodeInput.map (·.parent), groupInput, edges⟩ ∧
      sizes = edgeLines.map (extent lh) ∧
      pitch = Grid.Architecture.pitch p nodeInput sizes ∧
      params = ⟨pitch.x, pitch.y,
        (LayoutConst.architecture_ring_cap.get profile).toNat,
        alignments nodes⟩ ∧
      frameParams = ⟨padding, inset, lh, p.badge⟩ ∧
      ¬(nodeInput.any (fun n => !(nodeTileFits (archParams m)
          (archPitch m nodeInput edgeLines) n)) = true) ∧
      placed = Grid.Architecture.placeHierarchy input params frameParams
        (LayoutConst.architecture_bfs_cap.get profile).toNat ∧
      resolved = Grid.Architecture.resolveHierarchy input params placed ∧
      geometry = Grid.Architecture.geometry p pitch nodeInput groupInput resolved ∧
      rawRoutes = Grid.Architecture.routes p pitch nodeInput edges resolved geometry ∧
      rawBounds = Grid.Architecture.content geometry rawRoutes ∧
      bounds0 = (if rawBounds = Grid.Architecture.emptySpan then
        (⟨0, 0, 0, 0⟩ : Grid.Architecture.Span) else rawBounds) ∧
      margin = LayoutConst.canvas_margin.get profile ∧
      rawLabels = Grid.Architecture.placeLabels p margin geometry rawRoutes
        sizes bounds0 ∧
      bounds = rawLabels.foldl (fun acc r =>
        if r.x0 < r.x1 ∧ r.y0 < r.y1 then acc.union r else acc) bounds0 ∧
      dx = margin - bounds.x0 ∧
      dy = margin - bounds.y0 ∧
      width = bounds.x1 - bounds.x0 + 2 * margin ∧
      height = bounds.y1 - bounds.y0 + 2 * margin ∧
      ¬(width < 0 ∨ height < 0 ∨ COORD_LIMIT < width ∨
        COORD_LIMIT < height) ∧
      geometry.boxes.mapM (Grid.Architecture.translateRect dx dy) = .ok boxes ∧
      geometry.icons.mapM (Grid.Architecture.translateRect dx dy) = .ok icons ∧
      geometry.labels.mapM (Grid.Architecture.translateRect dx dy) = .ok labels ∧
      geometry.frames.mapM (Grid.Architecture.translateRect dx dy) = .ok frames ∧
      geometry.titles.mapM (Grid.Architecture.translateRect dx dy) = .ok titleRects ∧
      rawLabels.mapM (Grid.Architecture.translateRect dx dy) = .ok edgeRects ∧
      rawRoutes.mapM (List.mapM
        (Grid.Architecture.translatePoint dx dy)) = .ok routes ∧
      m.boxes.mapM (fun (b : ModelBox) => do
        let r ← if b.role == .group then
          match groups.findIdx? (fun q => q.id == b.id) with
          | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
          | none => throw LayoutError.domain
        else
          match nodes.findIdx? (fun q => q.id == b.id) with
          | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
          | none => throw LayoutError.domain
        pure ({
          id := b.id
          role := b.role.id
          parent := b.parent
          exclusive := b.exclusive
          rect := r } : Box)) = (Except.ok dumpBoxes : Except LayoutError (List Box)) ∧
      dumpRoutes = m.routes.zipIdx.map (fun q =>
        ({
          id := q.1.id
          fromId := q.1.fromId
          toId := q.1.toId
          orthogonal := q.1.orthogonal
          points := routes.getD q.2 [] } : Route)) ∧
      m.labels.mapM (fun (l : ModelLabel) => do
        let some i := m.routes.findIdx? (fun r => r.id == l.owner) | throw LayoutError.domain
        pure ({
          id := l.id
          owner := l.owner
          text := l.text
          rect := edgeRects.getD i ⟨0, 0, 0, 0⟩
          lines := (edgeLines.getD i []).map
            (fun line => String.ofList line.text) } : SceneLabel)) =
              (Except.ok dumpLabels : Except LayoutError (List SceneLabel)) ∧
      scene = {
        kind := m.kind
        profile := profile
        options := m.options
        canvas := ⟨width, height⟩
        boxes := dumpBoxes
        routes := dumpRoutes
        labels := dumpLabels
        items := items } ∧
      capped = placed.budgetExhausted := by
  unfold build at h
  obtain ⟨metric, hmetric, h⟩ := bind_ok h
  obtain ⟨titles, htitles, h⟩ := bind_ok h
  obtain ⟨captions, hcaptions, h⟩ := bind_ok h
  obtain ⟨inner, hinner, h⟩ := bind_ok h
  obtain ⟨edgeLines, hedgeLines, h⟩ := bind_ok h
  obtain ⟨groupInput, hgroupInput, h⟩ := bind_ok h
  by_cases hg1 : groupInput.zipIdx.any (fun q =>
      decide (q.1.parent ≥ Int.ofNat q.2)) = true
  · simp only [hg1, ite_true, Bind.bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h
    cases h
  · simp only [hg1] at h
    obtain ⟨nodeInput, hnodeInput, h⟩ := bind_ok h
    obtain ⟨edges, hedges, h⟩ := bind_ok h
    have hj : ¬(nodeInput.any (fun n => !(nodeTileFits (archParams m)
        (archPitch m nodeInput edgeLines) n)) = true) := by
      intro hat
      by_cases hc : nodeInput.any (fun n => !(nodeTileFits (archParams m)
          (archPitch m nodeInput edgeLines) n)) = true
      · simp only [hc, ite_true, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at h
        cases h
      · exact absurd hat hc
    have heq : nodeInput.any (fun n => !(nodeTileFits (archParams m)
        (archPitch m nodeInput edgeLines) n)) = false := by
      cases hb : nodeInput.any (fun n => !(nodeTileFits (archParams m)
          (archPitch m nodeInput edgeLines) n))
      · rfl
      · exact absurd hb hj
    simp only [heq] at h
    obtain ⟨boxes, hboxes, h⟩ := bind_ok h
    obtain ⟨icons, hicons, h⟩ := bind_ok h
    obtain ⟨labels, hlabels, h⟩ := bind_ok h
    obtain ⟨frames, hframes, h⟩ := bind_ok h
    obtain ⟨titleRects, htitleRects, h⟩ := bind_ok h
    obtain ⟨edgeRects, hedgeRects, h⟩ := bind_ok h
    obtain ⟨routes, hroutes, h⟩ := bind_ok h
    ·
      let profile : Profile := m.profile
      let cell : Bool := profile == .cell
      let lh : Int := LayoutConst.line_h.get profile
      let inset : Int := LayoutConst.architecture_title_inset.get profile
      let thickness : Int := LayoutConst.architecture_line_thickness.get profile
      let border : Int := LayoutConst.node_border.get profile
      let corner : Int := LayoutConst.corner_radius.get profile
      let iw : Int := match configInt m "iconSize" with
        | some px => if px > 0 then
            (if cell then max 1 (Int.fdiv (14*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_width.get profile
        | none => LayoutConst.architecture_icon_width.get profile
      let ih : Int := match configInt m "iconSize" with
        | some px => if px > 0 then
            (if cell then max 1 (Int.fdiv (6*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_height.get profile
        | none => LayoutConst.architecture_icon_height.get profile
      let padding : Int := match configInt m "padding" with
        | some px => if cell then Int.fdiv (2*px+20) 40 else px*64
        | none => LayoutConst.architecture_padding.get profile
      let p : Grid.Architecture.GeometryParams :=
        ⟨LayoutConst.architecture_pitch_x.get profile,
          LayoutConst.architecture_pitch_y.get profile,
          LayoutConst.architecture_label_wrap.get profile, iw, ih, inset, lh,
          LayoutConst.architecture_label_gap.get profile, thickness,
          if cell then 1 else 0, LayoutConst.architecture_badge.get profile⟩
      let groups : List ModelBox := m.boxes.filter (fun b => b.role == .group)
      let nodes : List ModelBox := m.boxes.filter (fun b => b.role != .group)
      let edgeTexts : List String := m.routes.map fun r =>
        ((m.labels.find? (fun l => l.owner == r.id)).map (·.text)).getD ""
      let input : Grid.Architecture.Input :=
        ⟨nodeInput.map (·.parent), groupInput, edges⟩
      let sizes : List Size := edgeLines.map (extent lh)
      let pitch : Grid.Architecture.Pitch :=
        Grid.Architecture.pitch p nodeInput sizes
      let params : Grid.Architecture.Params :=
        ⟨pitch.x, pitch.y,
          (LayoutConst.architecture_ring_cap.get profile).toNat,
          alignments nodes⟩
      let frameParams : Grid.Architecture.FrameParams :=
        ⟨padding, inset, lh, p.badge⟩
      let placed : Grid.Architecture.Placement :=
        Grid.Architecture.placeHierarchy input params frameParams
          (LayoutConst.architecture_bfs_cap.get profile).toNat
      let resolved : Grid.Architecture.Resolved :=
        Grid.Architecture.resolveHierarchy input params placed
      let geometry : Grid.Architecture.Geometry :=
        Grid.Architecture.geometry p pitch nodeInput groupInput resolved
      let rawRoutes : List (List Point) :=
        Grid.Architecture.routes p pitch nodeInput edges resolved geometry
      let rawBounds : Grid.Architecture.Span :=
        Grid.Architecture.content geometry rawRoutes
      let bounds0 : Grid.Architecture.Span :=
        if rawBounds = Grid.Architecture.emptySpan then
          (⟨0, 0, 0, 0⟩ : Grid.Architecture.Span) else rawBounds
      let margin : Int := LayoutConst.canvas_margin.get profile
      let rawLabels : List Grid.Architecture.Span :=
        Grid.Architecture.placeLabels p margin geometry rawRoutes sizes bounds0
      let bounds : Grid.Architecture.Span := rawLabels.foldl (fun acc r =>
        if r.x0 < r.x1 ∧ r.y0 < r.y1 then acc.union r else acc) bounds0
      let dx : Int := margin - bounds.x0
      let dy : Int := margin - bounds.y0
      let width : Int := bounds.x1 - bounds.x0 + 2 * margin
      let height : Int := bounds.y1 - bounds.y0 + 2 * margin
      change (if width < 0 ∨ height < 0 ∨ COORD_LIMIT < width ∨ COORD_LIMIT < height
        then _ else _) = (Except.ok (scene, capped) : Except LayoutError (Scene × Bool)) at h
      by_cases hg2 : width < 0 ∨ height < 0 ∨ COORD_LIMIT < width ∨ COORD_LIMIT < height
      · rw [ite_eq_left hg2] at h
        simp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
        cases h
      rw [ite_eq_right hg2] at h
      obtain ⟨dumpBoxes, hdumpBoxes, h⟩ := bind_ok h
      obtain ⟨dumpLabels, hdumpLabels, h⟩ := bind_ok h
      obtain ⟨items1, -, h⟩ := bind_ok h
      obtain ⟨items2, -, h⟩ := bind_ok h
      obtain ⟨items, -, h⟩ := bind_ok h
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hscene, hcapped⟩ := h
      let dumpRoutes : List Route := m.routes.zipIdx.map fun q =>
        ({ id := q.1.id, fromId := q.1.fromId, toId := q.1.toId,
           orthogonal := q.1.orthogonal,
           points := routes.getD q.2 [] } : Route)
      exact ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
        padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
        edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
        frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
        bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
        frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
        items,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        hmetric, htitles, hcaptions, hinner, rfl, hedgeLines, hgroupInput, hg1,
        hnodeInput, hedges,
        rfl, rfl, rfl, rfl, rfl,
        hj, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        hg2, hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
        hdumpBoxes, rfl, hdumpLabels, hscene.symm, hcapped.symm⟩

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
