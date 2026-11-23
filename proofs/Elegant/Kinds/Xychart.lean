
import Elegant.Kinds.Common
import Elegant.Chart.XY

set_option autoImplicit false

/-! Xychart model adapter. The model-stage dump carries the chart in three places, exactly as Go's
`xychartFromInput` reads it back: the honoured config keys in `options.config`, the axes and the
plots in the region sets (a zigzag-coded integer stream), and the titles, the categories, the
legend titles and the point labels in the label texts. The adapter decodes them into the family
input, runs the chart family under the profile of the model, and assembles the layout dump and the
scene items as Go's `layoutXY` does.

The decode is strict where Go is lenient only on inputs the Go front end never writes: a canvas
side outside `1..65536` px, a plot reserve outside `30..100` percent and a label font size outside
`1..256` are all a domain error. -/

namespace Elegant
namespace Kinds
namespace Xychart

open Common Chart.XY

def intConfig (o : Options) (key : String) : Option Int :=
  o.config.findSome? fun (k, v) =>
    match v with
    | .integer n => if k == key then some n else none
    | _ => none

def boolConfig (o : Options) (key : String) : Option Bool :=
  o.config.findSome? fun (k, v) =>
    match v with
    | .boolean b => if k == key then some b else none
    | _ => none

def inRange (lo hi : Int) : Option Int → Bool
  | none => true
  | some n => decide (lo ≤ n ∧ n ≤ hi)

def unzigzag (n : Int) : Int :=
  if 0 ≤ n ∧ n % 2 = 1 then -((n + 1) / 2) else Int.tdiv n 2

def baseInput (o : Options) : Input :=
  { horizontal := false, title := "", xTitle := "", yTitle := "", band := false, categories := [],
    xMin := 0, xMax := 0, yMin := 0, yMax := 0, plots := [],
    width := intConfig o "width", height := intConfig o "height",
    reserved := intConfig o "plotReservedSpacePercent",
    showLabel := boolConfig o "xAxis.showLabel", fontSize := intConfig o "xAxis.labelFontSize" }

def quads : Nat → List Int → List (Int × Int × Int × Int)
  | 0, _ => []
  | n + 1, a :: b :: c :: d :: rest => (a, b, c, d) :: quads n rest
  | _, _ => []

def decodePoint (q : Int × Int × Int × Int) : XPoint :=
  { present := q.1 % 2 == 1, slot := q.2.1 - 1, hasX := (q.1 / 2) % 2 == 1,
    x := unzigzag q.2.2.1, value := unzigzag q.2.2.2, label := "" }

def decodePlot (r : List Int) : XPlot :=
  { kind := ((r.getD 1 0) % 256).toNat, title := "",
    points := ((quads r.length (r.drop 3)).take (r.getD 2 0).toNat).map decodePoint }

def decodeRegion (inp : Input) (r : List Int) : Input :=
  if 7 ≤ r.length ∧ r.head? = some 0 then
    { inp with horizontal := (r.getD 1 0) % 256 == 1, band := r.getD 2 0 == 1,
               xMin := unzigzag (r.getD 3 0), xMax := unzigzag (r.getD 4 0),
               yMin := unzigzag (r.getD 5 0), yMax := unzigzag (r.getD 6 0), categories := [] }
  else if 3 ≤ r.length ∧ r.head? = some 1 then
    { inp with plots := inp.plots ++ [decodePlot r] }
  else inp

def cutFirst (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | a :: b :: rest => some (a, String.intercalate sep (b :: rest))
  | _ => none

def setPlot (inp : Input) (i : Nat) (f : XPlot → XPlot) : Input :=
  { inp with plots := inp.plots.zipIdx.map fun (pl, k) => if k == i then f pl else pl }

def legendTitle (inp : Input) (index text : String) : Input :=
  match index.toInt? with
  | some i => if 0 ≤ i ∧ i < inp.plots.length then setPlot inp i.toNat fun pl => { pl with title := text }
    else inp
  | none => inp

def pointLabel (inp : Input) (id text : String) : Input :=
  match cutFirst id ".l" with
  | none => inp
  | some (plot, point) =>
    match plot.toInt?, point.toInt? with
    | some i, some j =>
      if 0 ≤ i ∧ 0 ≤ j ∧ i < inp.plots.length ∧ j < ((inp.plots[i.toNat]?).map (·.points.length)).getD 0 then
        setPlot inp i.toNat fun pl =>
          { pl with points := pl.points.zipIdx.map fun (pt, k) =>
              if k == j.toNat then { pt with label := text } else pt }
      else inp
    | _, _ => inp

def dropN (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

def decodeLabel (inp : Input) (l : ModelLabel) : Input :=
  if l.id.startsWith "legend." then legendTitle inp (dropN l.id 7) l.text
  else if l.id.startsWith "p" then pointLabel inp (dropN l.id 1) l.text
  else if l.id == "title" then { inp with title := l.text }
  else if l.id == "x.title" then { inp with xTitle := l.text }
  else if l.id == "y.title" then { inp with yTitle := l.text }
  else if inp.band && l.id.startsWith "x.t" then { inp with categories := inp.categories ++ [l.text] }
  else inp

def configInRange (o : Options) : Bool :=
  inRange 1 65536 (intConfig o "width") && inRange 1 65536 (intConfig o "height") &&
    inRange 30 100 (intConfig o "plotReservedSpacePercent") &&
    inRange 1 256 (intConfig o "xAxis.labelFontSize")

def decode (m : Model) : Except LayoutError Input :=
  if !configInRange m.options then .error .domain
  else
    let withRegions := m.regionSets.foldl (fun inp s => decodeRegion inp s.regions) (baseInput m.options)
    .ok (m.labels.foldl decodeLabel withRegions)

def dumpBox (parent : String) (b : BoxSpec) (r : Rect) : Box :=
  ⟨b.id, "node", r, if b.isPlot then "" else parent, false⟩

def dumpLabel (it : Item) (pl : Placed) : SceneLabel :=
  { id := it.spec.id, owner := it.spec.owner, rect := pl.rect,
    lines := if pl.shown then it.box.lines.map (fun l => String.ofList l.text) else [],
    text := it.spec.text }

def sceneOf (m : Model) (r : Result) : Scene :=
  { kind := m.kind, profile := m.profile, options := { m.options with direction := .TB },
    canvas := r.canvas, boxes := (r.boxes.zip r.boxRects).map fun (b, rect) => dumpBox plotId b rect,
    routes := [], labels := (r.items.zip r.placed).map fun (it, pl) => dumpLabel it pl,
    items := r.groups }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match decode m with
  | .error e => .error (.geometry e)
  | .ok inp =>
    match Chart.XY.layout m.profile inp m.options.fontFamily with
    | .error e => .error (.geometry e)
    | .ok r =>
      .ok { scene := (sceneOf m r).projectCellAttachments (routeMarkers m),
            budgetExhausted := r.capped }

end Xychart
end Kinds
end Elegant
