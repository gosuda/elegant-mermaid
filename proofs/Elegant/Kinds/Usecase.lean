import Elegant.Kinds.Common
import Elegant.Layered.ExactPipeline

set_option autoImplicit false

/-! Usecase model adapter. Actors, use-case ellipses and business use cases carry a fixed size:
the label wrapped at `usecase.wrapping_width`, then the actor figure plus caption (exact), or
the label plus node padding floored by `usecase.min_node_width` (family minimum applies).
Boundaries are groups, notes size from their text. After layout an actor's caption moves below
its figure, and the label rectangle follows the first text item of every group, as the Go
adapter does. Per-kind spacing, wrap width and canvas margin come from the family's kind
parameters (`usecase.node_spacing`, `usecase.rank_spacing`, `usecase.diagram_padding`). -/

namespace Elegant
namespace Kinds
namespace Usecase

open Common

/-- The shape token without its flags: `usecaseActor:business` is `usecaseActor`. -/
def shapeId (shape : String) : String := (shape.splitOn ":").headD ""

def isActor (shape : String) : Bool := (shapeId shape).startsWith "usecaseActor"

def isSized (shape : String) : Bool :=
  isActor shape || shapeId shape == "usecaseEllipse" || shapeId shape == "usecaseBusiness"

/-- Figure width, figure height, padding and gap of an actor box. -/
def actorMetrics : Profile → Int × Int × Int × Int
  | .vector => (56 * 64, 72 * 64, 8 * 64, 8 * 64)
  | .cell => (7, 5, 1, 1)

/-- The fixed size of a sized node and whether the family must keep it exactly. -/
def nodeSize (profile : Profile) (shape text : String) (fontFamily : Bool := false) :
    Except LayoutError (Option (Size × Bool)) := do
  if !isSized shape then pure none
  else
    let metric ← labelMetric profile fontFamily
    let lines ← StyledMeasure.wrap metric (LayoutConst.usecase_wrapping_width.get profile) text.toList
    let width := widest lines
    let height ← Measure.checkedI32 ((max lines.length 1 : Nat) * LayoutConst.line_h.get profile)
    if isActor shape then
      let (figureW, figureH, padding, gap) := actorMetrics profile
      let w ← Measure.checkedI32 (max width figureW + 2 * padding)
      let h ← Measure.checkedI32 (height + figureH + gap + 2 * padding)
      pure (some (⟨w, h⟩, true))
    else
      let padX := LayoutConst.node_pad_x.get profile + LayoutConst.node_border.get profile
      let padY := LayoutConst.node_pad_y.get profile + LayoutConst.node_border.get profile
      let w ← Measure.checkedI32 (width + 2 * padX)
      let h ← Measure.checkedI32 (height + 2 * padY)
      pure (some (⟨max w (LayoutConst.usecase_min_node_width.get profile), h⟩, false))

def sizes (m : Model) : Except LayoutError (List (String × Size)) :=
  m.boxes.filterMapM fun b => do
    match ← nodeSize m.options.profile b.shape (boxText m b) m.options.fontFamily with
    | none => pure none
    | some (size, exact) =>
      pure (some (b.id, if exact then size else withFamilyMinimum m.options.profile size))

def input (m : Model) (fixed : List (String × Size)) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map fun r => edgeOptions (max r.minLength 1) r
    labels := m.labels
    fixedSizes := fixed }

/-! ### Captions and outlines

After layout, every group whose owner is a model box with a placed rectangle is redrawn as in
the Go adapter: an actor's caption moves below its figure, the label rectangle of the owner
follows the first text item, and the outline of the shape replaces every non-text item. -/

def captionRect (profile : Profile) (box text : Rect) : Rect :=
  let (top, padding) : Int × Int := match profile with
    | .vector => (88 * 64, 8 * 64)
    | .cell => (7, 1)
  ⟨box.x + padding, box.y + top, box.w - 2 * padding, text.h⟩

def firstText (items : List Primitive) : Option Rect :=
  items.findSome? fun item => match item with
    | .text t => some t.rect
    | _ => none

def moveCaption (profile : Profile) (box : Rect) : Primitive → Primitive
  | .text t => .text { t with rect := captionRect profile box t.rect }
  | item => item

def isText : Primitive → Bool
  | .text _ => true
  | _ => false

/-- The flags of a shape token: everything after its first colon. -/
def shapeFlag (shape : String) : String := ":".intercalate ((shape.splitOn ":").drop 1)

def isBusiness (shape : String) : Bool :=
  let flag := shapeFlag shape
  flag == "business" || flag.startsWith "business:"

def isPackage (shape : String) : Bool := shapeFlag shape == "package"

def hasIcon (shape : String) : Bool := shapeId shape == "usecaseActorIcon"

def inkLine : Paint := { style := "ink-line" }

/-- The actor figure: points are given in figure units (64 per unit in the vector profile). -/
structure Figure where
  origin : Point
  profile : Profile

def Figure.point (a : Figure) (x y : Int) : Except LayoutError Point := do
  let (dx, dy) : Int × Int := match a.profile with
    | .vector => (x * 64, (y + 36) * 64)
    | .cell => (Int.fdiv (x * 7) 56, Int.fdiv ((y + 36) * 5) 72)
  let px ← Measure.checkedI32 (a.origin.x + dx)
  let py ← Measure.checkedI32 (a.origin.y + dy)
  pure ⟨px, py⟩

def Figure.points (a : Figure) (path : List (Int × Int)) : Except LayoutError (List Point) :=
  path.mapM fun p => a.point p.1 p.2

def Figure.stroke (a : Figure) (path : List (Int × Int)) : Except LayoutError Primitive := do
  let points ← a.points path
  pure (.polyline points 0 inkLine)

def Figure.head (a : Figure) (c : Point) (radius : Int) : Primitive :=
  match a.profile with
  | .vector => .ellipse c.x c.y (radius * 64) (radius * 64) inkLine
  | .cell => .ellipse c.x c.y 1 1 inkLine

def hollowBody : List (Int × Int) :=
  [(-22, -10), (22, -10), (22, 0), (6, 0), (22, 17), (13, 28), (0, 13), (-13, 28), (-22, 17),
    (-6, 0), (-22, 0)]

def silhouetteBody : List (Int × Int) :=
  [(-24, 25), (-24, 7), (-14, -3), (0, -3), (14, -3), (24, 7), (24, 25), (18, 30), (-18, 30)]

def stickPaths : List (List (Int × Int)) :=
  [[(0, -12), (0, 8)], [(-17, -5), (17, -5)], [(-15, 28), (0, 8), (15, 28)]]

def Figure.silhouette (a : Figure) : Except LayoutError Primitive := do
  let p ← a.points silhouetteBody
  let pt := fun (i : Nat) => p.getD i default
  pure (.path [.M (pt 0), .C (pt 1) (pt 2) (pt 3), .C (pt 4) (pt 5) (pt 6), .L (pt 7), .L (pt 8),
    .Z] inkLine)

def Figure.body (a : Figure) (id : String) : Except LayoutError (List Primitive) :=
  match id with
  | "usecaseActorHollow" => do
    let points ← a.points hollowBody
    pure [.polygon points inkLine]
  | "usecaseActorAwesome" => do
    let silhouette ← a.silhouette
    pure [silhouette]
  | _ => stickPaths.mapM a.stroke

/-- Head centre row and radius of an actor variant. -/
def headSpec (id : String) : Int × Int :=
  match id with
  | "usecaseActorHollow" => (-23, 9)
  | "usecaseActorAwesome" => (-21, 13)
  | _ => (-24, 12)

def Figure.iconItems (a : Figure) (business : Bool) : Except LayoutError (List Primitive) := do
  let corners ← a.points [(-26, -28), (26, 24), (0, -2)]
  let topLeft := corners.getD 0 default
  let bottomRight := corners.getD 1 default
  let center := corners.getD 2 default
  let rect : Rect := ⟨topLeft.x, topLeft.y, bottomRight.x - topLeft.x, bottomRight.y - topLeft.y⟩
  let (frame, glyph) : Primitive × Primitive := match a.profile with
    | .cell => (.roundRect rect 0 inkLine, .symbolRef "unknown" center "ink-line")
    | .vector =>
      (.roundRect rect (4 * 64) inkLine,
        .text { rect := rect, role := .label, size := 24, align := .middle, style := "text",
                lines := [[⟨"?", false, false⟩]] })
  if business then
    let slash ← a.stroke [(12, -8), (26, -26)]
    pure [slash, frame, glyph]
  else pure [frame, glyph]

def Figure.items (a : Figure) (shape : String) : Except LayoutError (List Primitive) := do
  if hasIcon shape then a.iconItems (isBusiness shape)
  else
    let (y, radius) := headSpec (shapeId shape)
    let center ← a.point 0 y
    let body ← a.body (shapeId shape)
    let slash ← if isBusiness shape then
        do let s ← a.stroke [(3, y + radius), (radius, y - radius)]; pure [s]
      else pure []
    pure ([a.head center radius] ++ body ++ slash)

def Figure.of (profile : Profile) (r : Rect) : Except LayoutError Figure := do
  let x ← Measure.checkedI32 (r.x + Int.tdiv r.w 2)
  let top : Int := match profile with
    | .vector => 8 * 64
    | .cell => 1
  let y ← Measure.checkedI32 (r.y + top)
  pure ⟨⟨x, y⟩, profile⟩

def ellipseItems (id : String) (r : Rect) (style : String) :
    Except LayoutError (List Primitive) := do
  let paint : Paint := { style := style }
  let cx ← Measure.checkedI32 (r.x + Int.tdiv r.w 2)
  let cy ← Measure.checkedI32 (r.y + Int.tdiv r.h 2)
  let ellipse := Primitive.ellipse cx cy (Int.tdiv r.w 2) (Int.tdiv r.h 2) paint
  if id != "usecaseBusiness" then pure [ellipse]
  else
    let ax ← Measure.checkedI32 (cx + Int.tdiv r.w 3)
    let ay ← Measure.checkedI32 (cy + Int.tdiv r.h 4)
    let bx ← Measure.checkedI32 (cx + Int.tdiv r.w 2)
    let ey ← Measure.checkedI32 (cy + -(Int.tdiv r.h 4))
    pure [ellipse, .polyline [⟨ax, ay⟩, ⟨bx, ey⟩] 0 paint]

def outline (profile : Profile) (shape role : String) (r : Rect) :
    Except LayoutError (List Primitive) :=
  if isActor shape then do
    let figure ← Figure.of profile r
    figure.items shape
  else
    let style := if role == "group" then "group" else if shapeId shape == "note" then "note" else "node"
    if shapeId shape == "usecaseEllipse" || shapeId shape == "usecaseBusiness" then
      ellipseItems (shapeId shape) r style
    else
      let paint : Paint := { style := style }
      let tab : List Primitive :=
        if isPackage shape then
          [.rect ⟨r.x, r.y, Int.tdiv r.w 3, LayoutConst.line_h.get profile⟩ paint]
        else []
      pure (.rect r paint :: tab)

def drawStep (m : Model) (s : Scene) (acc : List Group × List SceneLabel) (group : Group) :
    Except LayoutError (List Group × List SceneLabel) :=
  match m.boxes.find? (fun b => b.id == group.owner), s.boxes.find? (fun b => b.id == group.owner) with
  | some box, some placed => do
    let profile := m.options.profile
    let moved := if isActor box.shape then group.items.map (moveCaption profile placed.rect)
      else group.items
    let labels := match firstText moved with
      | some rect => acc.2.map fun l => if l.owner == group.owner then { l with rect := rect } else l
      | none => acc.2
    let shapes ← outline profile box.shape placed.role placed.rect
    pure (acc.1 ++ [{ group with items := shapes ++ moved.filter isText }], labels)
  | _, _ => pure (acc.1 ++ [group], acc.2)

def drawShapes (m : Model) (s : Scene) : Except LayoutError Scene := do
  let result ← s.items.foldlM (drawStep m s) ([], s.labels)
  pure { s with items := result.1, labels := result.2 }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match sizes m with
  | .error e => .error (.geometry e)
  | .ok fixed =>
    match Layered.layoutFamilyB
      (Layered.PipelineImpl.layoutRecursiveX
        ((m.boxes.filter fun b => isActor b.shape).map (·.id)) (m.boxes.length + 1))
      (input m fixed) m.options with
    | .error e => .error e
    | .ok result =>
      match drawShapes m (result.scene.projectCellAttachments (routeMarkers m)) with
      | .error e => .error (.geometry e)
      | .ok scene => .ok { result with scene := scene }

end Usecase
end Kinds
end Elegant
