import Elegant.Model
import ElegantGeometry.Basic
import ElegantGeometry.Validator

namespace Elegant

inductive GroupRole where
  | decor | group | edge | node
  deriving DecidableEq, Repr

inductive TextRole where
  | title | label | body
  deriving DecidableEq, Repr

inductive Align where
  | start | middle | «end»
  deriving DecidableEq, Repr

inductive LineStyle where
  | solid | dashed | dotted | double
  deriving DecidableEq, Repr

inductive StrokeWidth where
  | normal | emphasis | units (value : Int)
  deriving DecidableEq, Repr

inductive MarkerAxis where
  | positiveX | negativeX | positiveY | negativeY
  deriving DecidableEq, Repr

structure Paint where
  style : String
  series : Fin 12 := 0
  width : StrokeWidth := .normal
  line : LineStyle := .solid
  deriving DecidableEq, Repr

inductive PathCommand where
  | M (point : Point)
  | L (point : Point)
  | C (control1 control2 point : Point)
  | A (center : Point) (radius start sweep : Int)
  | Z
  deriving DecidableEq, Repr

structure TextRun where
  text : String
  bold : Bool := false
  italic : Bool := false
  deriving DecidableEq, Repr

structure SceneText where
  rect : Rect
  role : TextRole
  size : Int
  align : Align
  style : String
  series : Fin 12 := 0
  lines : List (List TextRun)
  deriving DecidableEq, Repr

inductive Primitive where
  | rect (rect : Rect) (paint : Paint)
  | roundRect (rect : Rect) (r : Int) (paint : Paint)
  | ellipse (cx cy rx ry : Int) (paint : Paint)
  | polygon (points : List Point) (paint : Paint)
  | polyline (points : List Point) (corner : Int) (paint : Paint)
  | path (commands : List PathCommand) (paint : Paint)
  | text (value : SceneText)
  | markerRef (marker : String) (point : Point) (axis : MarkerAxis)
  | symbolRef (symbol : String) (point : Point) (style : String)
  deriving DecidableEq, Repr

structure Group where
  role : GroupRole
  owner : String
  items : List Primitive
  deriving DecidableEq, Repr

structure SceneLabel extends Label where
  text : String
  deriving DecidableEq, Repr

structure Scene where
  kind : String
  profile : Profile := .vector
  options : Options := {}
  canvas : Size
  boxes : List Box := []
  routes : List Route := []
  labels : List SceneLabel := []
  items : List Group := []
  deriving DecidableEq, Repr

def Scene.layoutDump (s : Scene) : LayoutDump :=
  ⟨s.canvas, s.boxes, s.routes, s.labels.map (·.toLabel)⟩

end Elegant
