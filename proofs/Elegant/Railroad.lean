import Elegant.Scene
import Elegant.Measure
import Elegant.Gen.Layoutconst

set_option autoImplicit false

namespace Elegant.Railroad

structure Node where
  id : String
  kind : String
  text : String
  children : List Node := []
  deriving Repr

structure Rule where
  id : String
  title : String
  root : Node
  deriving Repr

structure Shape where
  id : String
  kind : String
  text : String
  w : Int
  up : Int
  down : Int
  children : List Shape := []
  offsets : List Point := []
  deriving Repr, Inhabited

def Shape.height (s : Shape) : Int := s.up + s.down

def leaf (kind : String) : Bool :=
  kind == "terminal" || kind == "nonterminal" || kind == "special"

def constant (p : Profile) (name : String) : Int :=
  (match name with
  | "pad_x" => LayoutConst.railroad_pad_x
  | "pad_y" => LayoutConst.railroad_pad_y
  | "line_height" => LayoutConst.railroad_line_height
  | "hsep" => LayoutConst.railroad_hsep
  | "vsep" => LayoutConst.railroad_vsep
  | "arc_radius" => LayoutConst.railroad_arc_radius
  | "terminal_radius" => LayoutConst.railroad_terminal_radius
  | "marker_radius" => LayoutConst.railroad_marker_radius
  | "margin" => LayoutConst.railroad_margin
  | "rule_name_gap" => LayoutConst.railroad_rule_name_gap
  | "rule_end_gap" => LayoutConst.railroad_rule_end_gap
  | "rule_min_baseline" => LayoutConst.railroad_rule_min_baseline
  | "rule_min_height" => LayoutConst.railroad_rule_min_height
  | "empty_width" => LayoutConst.railroad_empty_width
  | "empty_height" => LayoutConst.railroad_empty_height
  | _ => ⟨0, 0⟩).get p

def sequenceOffset (up x : Int) (kid : Shape) : Point :=
  ⟨x, up - kid.up⟩

def sequenceAdvance (gap x : Int) (kid : Shape) : Int :=
  x + kid.w + gap

def choiceOffset (radius widest y : Int) (kid : Shape) : Point :=
  ⟨2 * radius + Int.fdiv (widest - kid.w) 2, y⟩

def sequenceLayout (up gap : Int) : Int → List Shape → Int × List Point
  | x, [] => (x, [])
  | x, kid :: rest =>
    let result := sequenceLayout up gap (sequenceAdvance gap x kid) rest
    (result.1, sequenceOffset up x kid :: result.2)

def choiceLayout (radius widest gap : Int) : Int → List Shape → Int × List Point
  | y, [] => (y, [])
  | kidY, kid :: rest =>
    let result := choiceLayout radius widest gap (kidY + kid.height + gap) rest
    (result.1, choiceOffset radius widest kidY kid :: result.2)

def leafShape (p : Profile) (n : Node) (width : Int) : Shape :=
  let c := constant p
  let h := c "line_height" + 2 * c "pad_y"
  ⟨n.id,n.kind,n.text,width+2*c "pad_x",Int.fdiv h 2,h-Int.fdiv h 2,[],[]⟩

def sequenceShape (p : Profile) (n : Node) (kids : List Shape) : Shape :=
  let up := kids.foldl (fun a k => max a k.up) 0
  let down := kids.foldl (fun a k => max a k.down) 0
  let result := sequenceLayout up (constant p "hsep") 0 kids
  ⟨n.id,n.kind,n.text,result.1-constant p "hsep",up,down,kids,result.2⟩

def choiceShape (p : Profile) (n : Node) (kids : List Shape) : Shape :=
  let widest := kids.foldl (fun a k => max a k.w) 0
  let result := choiceLayout (constant p "arc_radius") widest (constant p "vsep") 0 kids
  let height := result.1-constant p "vsep"
  ⟨n.id,n.kind,n.text,widest+4*constant p "arc_radius",
    Int.fdiv height 2,height-Int.fdiv height 2,kids,result.2⟩

def wrapperShape (p : Profile) (n : Node) (kid : Shape) : Shape :=
  let radius := constant p "arc_radius"
  let childY := if n.kind == "oneOrMore" then 0 else 2*radius
  let height := kid.height+2*radius + if n.kind == "zeroOrMore" then 2*radius else 0
  ⟨n.id,n.kind,n.text,kid.w+4*radius,childY+kid.up,
    height-(childY+kid.up),[kid],[⟨2*radius,childY⟩]⟩

def sizeRaw (p : Profile) (metric : Measure.Metric) (n : Node) (kids : List Shape) :
    Except LayoutError Shape :=
  if leaf n.kind then
    if !kids.isEmpty then .error .domain
    else do
      let width ← Measure.textWidth metric n.text.toList
      return leafShape p n width
  else if n.kind == "sequence" then
    if kids.length < 2 then .error .domain else .ok (sequenceShape p n kids)
  else if n.kind == "choice" then
    if kids.length < 2 then .error .domain else .ok (choiceShape p n kids)
  else if n.kind == "optional" || n.kind == "zeroOrMore" || n.kind == "oneOrMore" then
    match kids with
    | [kid] => .ok (wrapperShape p n kid)
    | _ => .error .domain
  else .error .domain

def size (p : Profile) (metric : Measure.Metric) (n : Node) (kids : List Shape) :
    Except LayoutError Shape := do
  let s ← sizeRaw p metric n kids
  if I32_MAX < s.w || I32_MAX < s.height then throw .overflow
  return s

def measure : Nat → Profile → Measure.Metric → Node → Except LayoutError Shape
  | 0, _, _, _ => .error .domain
  | fuel + 1, p, metric, n => do
    let kids ← n.children.mapM (measure fuel p metric)
    size p metric n kids

def move (p : Point) (x y : Int) : Point := ⟨p.x+x, p.y+y⟩
def sign (v : Int) : Int := if v > 0 then 1 else if v < 0 then -1 else 0

def unit (a b : Point) : Point := ⟨sign (b.x-a.x), sign (b.y-a.y)⟩
def distance (a b : Point) : Int := (b.x-a.x).natAbs + (b.y-a.y).natAbs

def quarterAngle (v : Point) : Int :=
  if v.x > 0 then 0 else if v.y > 0 then 16384 else if v.x < 0 then 32768 else 49152

def compact (ps : List Point) : List Point :=
  ps.foldl (fun out p => if out.getLast? == some p then out else out ++ [p]) []

def rounded (r : Int) (ps : List Point) : List PathCommand :=
  match ps with
  | [] => []
  | first :: _ =>
    let middle := ((List.range ps.length).filter fun k => 0 < k && k+1 < ps.length).flatMap fun k =>
      let a := ps[k-1]!
      let b := ps[k]!
      let d := ps[k+1]!
      let u := unit a b
      let v := unit b d
      let turn := u.x*v.y-u.y*v.x
      let before := distance a b
      let after := distance b d
      let radius := min r (min (if k > 1 then Int.fdiv before 2 else before)
        (if k+2 < ps.length then Int.fdiv after 2 else after))
      if turn == 0 || radius == 0 then [PathCommand.L b]
      else
        let start := Point.mk (b.x-radius*u.x) (b.y-radius*u.y)
        let center := Point.mk (start.x+radius*v.x) (start.y+radius*v.y)
        [PathCommand.L start, .A center radius (quarterAngle ⟨-v.x, -v.y⟩)
          (if turn < 0 then -16384 else 16384)]
    [.M first] ++ middle ++ [.L (ps.getLast!)]

def rail (p : Profile) (ps : List Point) : Primitive :=
  let ps := compact ps
  if p == .cell then .polyline ps 0 {style := "edge"}
  else .path (rounded (constant p "arc_radius") ps) {style := "edge"}

def rightStart (p : Profile) (s : Shape) (x : Int) : Int :=
  if p == .cell && leaf s.kind then x-1 else x

def rails (p : Profile) (s : Shape) (x y : Int) : List Primitive :=
  let r := constant p "arc_radius"
  let cy := s.up
  let polys := if s.kind == "choice" then
      (s.children.zip s.offsets).flatMap fun (kid, off) =>
        let ecy := off.y+kid.up
        let left := [Point.mk 0 cy] ++ (if ecy != cy then [⟨r,cy⟩, ⟨r,ecy⟩] else []) ++ [⟨off.x,ecy⟩]
        let right := [Point.mk (rightStart p kid (off.x+kid.w)) ecy] ++
          (if ecy != cy then [⟨s.w-r,ecy⟩, ⟨s.w-r,cy⟩] else []) ++ [⟨s.w,cy⟩]
        [left,right]
    else match s.children with
      | [kid] =>
        let forward := [[Point.mk 0 cy, ⟨2*r,cy⟩],
          [Point.mk (rightStart p kid (2*r+kid.w)) cy, ⟨s.w,cy⟩]]
        let bypass := [Point.mk 0 cy, ⟨r,cy⟩, ⟨r,0⟩, ⟨s.w-r,0⟩, ⟨s.w-r,cy⟩, ⟨s.w,cy⟩]
        let bottom := s.height - if p == .cell then 1 else 0
        let loop := [Point.mk (rightStart p kid (2*r+kid.w)) cy,
          ⟨3*r+kid.w,cy⟩, ⟨3*r+kid.w,bottom⟩, ⟨r,bottom⟩, ⟨r,cy⟩, ⟨2*r,cy⟩]
        if s.kind == "optional" then forward ++ [bypass]
        else if s.kind == "zeroOrMore" then forward ++ [loop,bypass]
        else if s.kind == "oneOrMore" then forward ++ [loop] else []
      | _ => []
  polys.map fun ps => rail p (ps.map fun pt => move pt x y)

def textItem (_p : Profile) (rect : Rect) (text : String) (align : Align) : Primitive :=
  .text {
    rect := rect, role := .label, size := 14, align := align, style := "text"
    lines := [[{text := text}]] }

structure State where
  boxes : List Box := []
  routes : List Route := []
  labels : List SceneLabel := []
  groups : List Group := []
  edges : List Group := []
  nodes : List Group := []

def shapeRect (s : Shape) (x y : Int) : Rect := ⟨x,y,s.w,s.height⟩

def joinStep (s : Shape) (x y : Int) (state : State) (i : Nat) : State :=
  let source := s.children[i]!
  let target := s.children[i+1]!
  let off := s.offsets[i]!
  let next := s.offsets[i+1]!
  let points := [Point.mk (x+off.x+source.w) (y+s.up), ⟨x+next.x,y+s.up⟩]
  let id := "e" ++ toString state.routes.length
  { state with
    routes := state.routes ++ [⟨id,source.id,target.id,true,points⟩]
    edges := state.edges ++ [⟨.edge,id,[.polyline points 0 {style := "edge"}]⟩] }

def sequenceJoins (s : Shape) (x y : Int) (state : State) : State :=
  (List.range (s.children.length-1)).foldl (joinStep s x y) state

-- Children and offsets are traversed in the declaration order of the model dump.
def placeNode : Nat → Profile → Shape → Int → Int → String → State → Except LayoutError State
  | 0, _, _, _, _, _, _ => .error .domain
  | fuel+1, p, s, x, y, parent, initial => do
    let rect := shapeRect s x y
    let isLeaf := leaf s.kind
    let state : State := { initial with boxes := initial.boxes ++
      [Box.mk s.id (if isLeaf then "node" else "group") rect parent isLeaf] }
    if isLeaf then
      let paint : Paint := {style := "node", line := if s.kind == "special" then .dashed else .solid}
      let outline := if s.kind == "terminal" then Primitive.roundRect rect (constant p "terminal_radius") paint
        else Primitive.rect rect paint
      let line := constant p "line_height"
      let textRect := Rect.mk x (y+Int.fdiv (s.height-line) 2) s.w line
      return { state with nodes := state.nodes ++
        [Group.mk .node s.id [outline,textItem p textRect s.text .middle]] }
    else
      let state : State := {state with groups := state.groups ++ [Group.mk .group s.id (rails p s x y)]}
      let state := if s.kind == "sequence" then sequenceJoins s x y state else state
      (s.children.zip s.offsets).foldlM (fun acc pair =>
        placeNode fuel p pair.1 (x+pair.2.x) (y+pair.2.y) s.id acc) state

structure RuleGeometry where
  title : Int
  nameW : Int
  defX : Int
  baseline : Int
  defY : Int
  width : Int
  height : Int

def ruleGeometry (p : Profile) (s : Shape) (title : Int) : RuleGeometry :=
  let c := constant p
  let nameW := title+c "rule_name_gap"
  let defX := nameW+c "rule_name_gap"
  let baseline := max (c "rule_min_baseline") s.up
  let defY := baseline-s.up
  ⟨title,nameW,defX,baseline,defY,defX+s.w+c "rule_end_gap"+c "marker_radius",
    max (c "rule_min_height") (defY+s.height+2*c "margin")⟩

def ruleLabelRect (p : Profile) (g : RuleGeometry) (y : Int) : Rect :=
  ⟨constant p "margin",y+g.baseline-Int.fdiv (constant p "line_height") 2,
    g.title,constant p "line_height"⟩

def ruleFrame (p : Profile) (g : RuleGeometry) (y : Int) : Rect :=
  ⟨0,y,g.width+2*constant p "margin",g.height⟩

def addRule (p : Profile) (rule : Rule) (s : Shape) (g : RuleGeometry)
    (y : Int) (state : State) : State :=
  if rule.id == "" then state
  else
    let c := constant p
    let x := c "margin"
    let base := y+g.baseline
    let right := x+g.defX+s.w
    let marker := c "marker_radius"
    let rect := ruleLabelRect p g y
    let items := [rail p [⟨x+g.nameW+marker,base⟩,⟨x+g.defX,base⟩],
      rail p [⟨rightStart p s right,base⟩,⟨right+c "rule_end_gap"-marker,base⟩],
      Primitive.ellipse (x+g.nameW) base marker marker {style := "ink"},
      Primitive.ellipse (right+c "rule_end_gap") base marker marker {style := "ink"},
      textItem p rect rule.title .start]
    { state with
      boxes := state.boxes ++ [⟨rule.id,"group",ruleFrame p g y,"",false⟩]
      labels := state.labels ++ [{
        id := rule.id++".label", owner := rule.id, rect := rect
        text := rule.title, lines := [rule.title] }]
      groups := state.groups ++ [⟨.group,rule.id,items⟩] }

structure RuleState where
  state : State := {}
  y : Int
  widest : Int := 0

def placeRule (m : Model) (metric : Measure.Metric) (before : RuleState) (rule : Rule) :
    Except LayoutError RuleState := do
  let p := m.profile
  let c := constant p
  let s ← measure (m.boxes.length+1) p metric rule.root
  let title ← Measure.textWidth metric rule.title.toList
  let g := ruleGeometry p s title
  if I32_MAX < c "margin"+g.width+c "margin" || I32_MAX < before.y+g.height then
    throw .overflow
  let state := addRule p rule s g before.y before.state
  let state ← placeNode (m.boxes.length+1) p s (c "margin"+g.defX)
    (before.y+g.defY) rule.id state
  return ⟨state,before.y+g.height+c "vsep",max before.widest g.width⟩

def metricFor : Profile → Except LayoutError Measure.Metric
  | .cell => .ok Measure.Metric.cell
  | .vector => Measure.Role.label.metric

def layout (m : Model) (rules : List Rule) : Except LayoutError Scene := do
  let p := m.profile
  let metric ← metricFor p
  let c := constant p
  let result ← rules.foldlM (placeRule m metric) {y := c "margin"}
  let width := if rules.isEmpty then c "empty_width" else result.widest+2*c "margin"
  let height := if rules.isEmpty then c "empty_height" else result.y+c "margin"
  if I32_MAX < width || I32_MAX < height then throw .overflow
  return {
    kind := m.kind, profile := p, options := m.options, canvas := ⟨width,height⟩
    boxes := result.state.boxes, routes := result.state.routes, labels := result.state.labels
    items := result.state.groups ++ result.state.edges ++ result.state.nodes }

end Elegant.Railroad
