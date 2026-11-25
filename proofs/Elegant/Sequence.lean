import Elegant.Model
import Elegant.Scene
import Elegant.Measure
import Elegant.StyledMeasure
import Elegant.Gen.Markers
import Elegant.SequenceConsts

set_option autoImplicit false

/-! Lean reference of the sequence layout family (`spec/layout/sequence.md`): measurement of the
actor and label text, the lifeline columns with their widening, the rows (messages, notes,
fragments, activations), the frames, and the scene. It reads the model-stage dump (boxes, routes,
labels, and the event stream that the dump carries in `regions`, model-dump-25) and computes the
same integers as the Go family `layoutSequence`. -/

namespace Elegant
namespace Sequence

/-! ### Small helpers -/

def rectZero : Rect := ⟨0, 0, 0, 0⟩

def widest (lines : List Measure.Line) : Int := lines.foldl (fun w l => max w l.width) 0

def lineTexts (lines : List Measure.Line) : List String := lines.map fun l => String.ofList l.text

def runsOf (lines : List Measure.Line) : List (List TextRun) :=
  lines.map fun l => [⟨String.ofList l.text, false, false⟩]

def sceneMarker (name : String) : String := if name == "none" then "" else name

/-! ### Wrap -/

inductive Wrap where
  | inherited | forced | suppressed
  deriving DecidableEq, Repr

def boxWrap (b : ModelBox) : Wrap :=
  if b.direction == "w" then .forced else if b.direction == "n" then .suppressed else .inherited

def wrapFromBits (bits : Nat) : Wrap :=
  if bits.testBit 4 then .forced else if bits.testBit 5 then .suppressed else .inherited

def wrapTarget (shared : Bool) (override : Wrap) (width padding : Int) : Int :=
  let wrapped := match override with | .forced => true | .suppressed => false | .inherited => shared
  if wrapped then max (width - 2 * padding) 1 else I32_MAX

def metricOf (profile : Profile) (role : Measure.Role) (fontFamily : Bool := false) :
    Except LayoutError Measure.Metric :=
  match profile with
  | .cell => pure Measure.Metric.cell
  | .vector => role.metric fontFamily

def measureLines (profile : Profile) (role : Measure.Role) (target : Int) (text : String)
    (fontFamily : Bool := false) :
    Except LayoutError (List Measure.Line) := do
  let metric ← metricOf profile role fontFamily
  StyledMeasure.wrap metric target text.toList

/-! ### The event stream -/

inductive Step where
  | message (bits : Nat) (src dst route : Nat) (destroyed : Int)
  | note (placement : Nat) (a b box : Nat)
  | fragmentStart (kind box : Nat)
  | fragmentElse (box sect : Nat)
  | fragmentEnd
  | activateStart (actor : Nat)
  | activateEnd (actor : Nat)
  deriving DecidableEq, Repr

def regionValue (r : ModelRegionSet) (i : Nat) : Int := r.regions.getD i 0

def decodeStep (r : ModelRegionSet) : Step :=
  let at_ (i : Nat) : Nat := (regionValue r i).toNat
  let tag := at_ 0
  let bits := tag - tag % 16
  match tag % 16 with
  | 0 => .message bits (at_ 1) (at_ 2) (at_ 3) (regionValue r 4)
  | 1 => .note ((bits / 256) % 4) (at_ 1) (at_ 2) (at_ 3)
  | 2 => .fragmentStart ((bits / 64) % 16) (at_ 1)
  | 3 => .fragmentElse (at_ 1) (at_ 2)
  | 4 => .fragmentEnd
  | 5 => .activateStart (at_ 1)
  | _ => .activateEnd (at_ 1)

def decodeSteps (sets : List ModelRegionSet) : List Step :=
  let ordered := sets.map fun r => (r.parent, decodeStep r)
  (ordered.mergeSort fun x y => decide (x.1 ≤ y.1)).map (·.2)

def fragmentKindRect : Nat := 1

def bitsOf (r : ModelRegionSet) : Nat := let tag := (regionValue r 0).toNat; tag - tag % 16

/-- The wrap override of a message, read from the tag bits of its route's region. -/
def messageWrap (m : Model) (owner : String) : Wrap :=
  match m.regionSets.find? fun r =>
      (regionValue r 0).toNat % 16 == 0 &&
        (match m.routes[(regionValue r 3).toNat]? with | some rt => rt.id == owner | none => false) with
  | some r => wrapFromBits (regionValue r 0).toNat
  | none => .inherited


/-! ### Lookups -/

def isActorBox (b : ModelBox) : Bool := b.role == .node && b.shape != "note"

def isParticipantBox (b : ModelBox) : Bool := b.role == .group && b.shape == ""

def fragmentKinds : List String :=
  ["loop", "rect", "opt", "alt", "par", "par_over", "critical", "break"]

def isFragmentShape (shape : String) : Bool := fragmentKinds.contains shape

def isSectionedFragment (b : ModelBox) : Bool :=
  b.role == .group && isFragmentShape b.shape && b.shape != "rect"

/-- The text of a box: its `<id>.label` label, else the text of the dump, else its id. -/
def boxText (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (fun l => l.owner == b.id && l.id == b.id ++ ".label") with
  | some l => l.text
  | none => b.text.getD b.id

def titlePos (m : Model) (boxIndex : Nat) : Option Nat :=
  match m.boxes[boxIndex]? with
  | some b => m.labels.findIdx? fun l => l.owner == b.id && l.id.endsWith ".label"
  | none => none

def routeLabelPos (m : Model) (route : Nat) : Option Nat :=
  match m.routes[route]? with
  | some r => m.labels.findIdx? fun l => l.owner == r.id
  | none => none

def labelPosById (m : Model) (id : String) : Option Nat := m.labels.findIdx? fun l => l.id == id

def ownedLabelPos (m : Model) (owner : String) : Option Nat := m.labels.findIdx? fun l => l.owner == owner

def labelIsBody (m : Model) (l : ModelLabel) : Bool :=
  m.routes.any (·.id == l.owner) ||
    (match m.boxes.find? (·.id == l.owner) with | some b => b.shape == "note" | none => false)

def labelWrap (m : Model) (l : ModelLabel) : Wrap :=
  if m.routes.any (·.id == l.owner) then messageWrap m l.owner
  else match m.boxes.find? (·.id == l.owner) with
    | some b => boxWrap b
    | none => .inherited

def sharedWrap (m : Model) : Bool :=
  m.options.config.any fun (k, v) => k == "wrap" && (v == .boolean true || v == .string "true")

/-! ### The plan: measured text and actor sizes -/

structure Plan where
  m : Model
  c : Consts
  shared : Bool
  actorBoxes : List Nat
  actorLines : List (List Measure.Line)
  labelLines : List (List Measure.Line)
  widths : List Int
  heights : List Int
  bandTop : Int
  bandHeight : Int

def Plan.linesAt (pl : Plan) (pos : Option Nat) : List Measure.Line :=
  match pos with
  | some p => pl.labelLines.getD p []
  | none => []

def Plan.titleLines (pl : Plan) (boxIndex : Nat) : List Measure.Line :=
  pl.linesAt (titlePos pl.m boxIndex)

def Plan.labelWidth (pl : Plan) (label : Option Nat) : Int := widest (pl.linesAt label)

def actorWrapped (shared : Bool) (b : ModelBox) : Bool :=
  match boxWrap b with
  | .forced => true
  | .suppressed => false
  | .inherited => shared

def actorSize (c : Consts) (shared : Bool) (b : ModelBox) (lines : List Measure.Line) : Int × Int :=
  let textH := (lines.length : Int) * c.lineHeight
  let w := if actorWrapped shared b then c.actorWidth else max c.actorWidth (widest lines + 2 * c.wrapPadding)
  (w, max c.actorHeight (textH + 2 * c.boxTextMargin))

def baseGaps (c : Consts) (widths : List Int) : List Int :=
  (List.range (widths.length - 1)).map fun i => half (widths.getD i 0 + widths.getD (i + 1) 0) + c.actorMargin

/-- The sum of the gaps `lo` to `hi - 1`. -/
def ssum (g : List Int) (lo hi : Nat) : Int := ((List.range' lo (hi - lo)).map fun k => g.getD k 0).sum

def lifelineCentres (widths gaps : List Int) : List Int :=
  match widths with
  | [] => []
  | w :: _ => (List.range widths.length).map fun i => half w + ssum gaps 0 i

def Plan.build (m : Model) : Except LayoutError Plan := do
  let c ← Consts.load m.profile
  let shared := sharedWrap m
  let actors := m.boxes.filter isActorBox
  let actorLines ← actors.mapM fun b =>
    measureLines (fontFamily := m.options.fontFamily) m.profile .label (wrapTarget shared (boxWrap b) c.actorWidth c.wrapPadding) (boxText m b)
  let labelLines ← m.labels.mapM fun l =>
    measureLines (fontFamily := m.options.fontFamily) m.profile (if labelIsBody m l then .body else .label)
      (wrapTarget shared (labelWrap m l) c.actorWidth c.wrapPadding) l.text
  let sizes := (actors.zip actorLines).map fun (b, lines) => actorSize c shared b lines
  let pl : Plan :=
    { m, c, shared
      actorBoxes := m.boxes.zipIdx.filterMap fun (b, i) => if isActorBox b then some i else none
      actorLines, labelLines
      widths := sizes.map (·.1), heights := sizes.map (·.2)
      bandTop := 0, bandHeight := 0 }
  let bandTop := m.boxes.zipIdx.foldl (fun acc (b, i) =>
    if isParticipantBox b then max acc (((pl.titleLines i).length : Int) * c.lineHeight + c.boxMargin) else acc) 0
  return { pl with bandTop, bandHeight := pl.heights.foldl max 0 }

/-! ### Columns -/


def widen (gaps : List Int) (lo hi : Nat) (need : Int) : List Int :=
  if hi ≤ lo ∨ gaps.length < hi then gaps
  else
    let extra := need - ssum gaps lo hi
    if extra ≤ 0 then gaps
    else
      let span : Int := ((hi - lo : Nat) : Int)
      let share := Int.fdiv extra span
      let rem := extra - share * span
      gaps.mapIdx fun i g =>
        if lo ≤ i ∧ i < hi then g + share + (if ((i - lo : Nat) : Int) < rem then 1 else 0) else g

def widenWhen (cond : Bool) (g : List Int) (lo hi : Nat) (need : Int) : List Int :=
  if cond then widen g lo hi need else g

def bumpGap (g : List Int) (k : Nat) (v : Int) : List Int :=
  g.mapIdx fun i x => if i == k then x + v else x

def widenForMessage (pl : Plan) (gaps : List Int) (bits : Nat) (src dst route : Nat) : List Int :=
  let c := pl.c
  let need := pl.labelWidth (routeLabelPos pl.m route) + 2 * c.wrapPadding
  let spanned :=
    if src == dst then
      widenWhen (decide (src < gaps.length)) gaps src (src + 1) (max (half need) c.selfLoopMinDx + c.actorMargin)
    else widen gaps (min src dst) (max src dst) (need + c.actorMargin)
  if bits.testBit 10 ∧ 0 < dst then bumpGap spanned (dst - 1) (half (pl.widths.getD dst 0)) else spanned

def widenForNote (pl : Plan) (gaps : List Int) (placement a b box : Nat) : List Int :=
  let c := pl.c
  let textW := widest (pl.titleLines box)
  let actorW := pl.widths.getD a 0
  let width := max actorW (textW + 2 * c.noteMargin)
  let sideNeed := half actorW + 2 * half c.actorMargin + width
  if placement == 2 ∧ a == b then
    let need := half width + c.actorMargin
    let g1 := widenWhen (decide (0 < a)) gaps (a - 1) a need
    widenWhen (decide (a < g1.length)) g1 a (a + 1) need
  else if placement == 2 then widen gaps (min a b) (max a b) (textW + 2 * c.noteMargin + c.actorMargin)
  else if placement == 1 then widenWhen (decide (a < gaps.length)) gaps a (a + 1) sideNeed
  else widenWhen (decide (0 < a)) gaps (a - 1) a sideNeed

def widenStep (pl : Plan) (g : List Int) : Step → List Int
  | .message bits src dst route _ => widenForMessage pl g bits src dst route
  | .note placement a b box => widenForNote pl g placement a b box
  | _ => g

def widenSteps (pl : Plan) (steps : List Step) (gaps : List Int) : List Int :=
  steps.foldl (widenStep pl) gaps

structure PFrame where
  first : Nat
  last : Nat
  extra : Int
  deriving DecidableEq, Repr

def memberOrdinals (pl : Plan) (id : String) : List Nat :=
  pl.actorBoxes.zipIdx.filterMap fun (at_, o) =>
    match pl.m.boxes[at_]? with
    | some b => if b.parent == id then some o else none
    | none => none

def participantFrames (pl : Plan) (centres : List Int) : List PFrame :=
  pl.m.boxes.zipIdx.filterMap fun (b, index) =>
    if isParticipantBox b then
      match memberOrdinals pl b.id with
      | [] => none
      | first :: rest =>
        let last := (first :: rest).getLast?.getD first
        let left := centres.getD first 0 - half (pl.widths.getD first 0)
        let right := centres.getD last 0 + (pl.widths.getD last 0 - half (pl.widths.getD last 0))
        let titleW := widest (pl.titleLines index)
        some ⟨first, last, max (titleW + 2 * pl.c.wrapPadding - ((right - left) + 2 * pl.c.boxTextMargin)) 0⟩
    else none

def reachRight (pl : Plan) (frames : List PFrame) (o : Nat) : Int :=
  match frames.find? (·.last == o) with
  | some f => pl.c.boxTextMargin + (f.extra - half f.extra)
  | none => 0

def reachLeft (pl : Plan) (frames : List PFrame) (o : Nat) : Int :=
  match frames.find? (·.first == o) with
  | some f => pl.c.boxTextMargin + half f.extra
  | none => 0

def widenForReach (pl : Plan) (gaps : List Int) (gap : Nat) (reach : Int) : List Int :=
  widen gaps gap (gap + 1)
    ((pl.widths.getD gap 0 - half (pl.widths.getD gap 0)) + half (pl.widths.getD (gap + 1) 0) + reach)

def reachWhen (cond : Bool) (pl : Plan) (g : List Int) (gap : Nat) (reach : Int) : List Int :=
  if cond then widenForReach pl g gap reach else g

def clearStep (pl : Plan) (frames : List PFrame) (g : List Int) (f : PFrame) : List Int :=
  let g1 := reachWhen (decide (0 < f.first)) pl g (f.first - 1)
    (reachRight pl frames (f.first - 1) + reachLeft pl frames f.first)
  reachWhen (decide (f.last + 1 < pl.widths.length)) pl g1 f.last
    (reachRight pl frames f.last + reachLeft pl frames (f.last + 1))

def clearParticipantBoxes (pl : Plan) (frames : List PFrame) (gaps : List Int) : List Int :=
  frames.foldl (clearStep pl frames) gaps

/-- The lifeline gaps after every message and note has widened them and every participant frame
has been cleared. -/
def columnGaps (pl : Plan) (steps : List Step) : List Int :=
  let widened := widenSteps pl steps (baseGaps pl.c pl.widths)
  clearParticipantBoxes pl (participantFrames pl (lifelineCentres pl.widths widened)) widened

/-- The lifeline centres of the layout. -/
def columns (pl : Plan) (steps : List Step) : List Int :=
  lifelineCentres pl.widths (columnGaps pl steps)

/-! ### Rows -/

structure Divider where
  row : Int
  label : Option Nat
  deriving DecidableEq, Repr

structure FragRun where
  box : Nat
  kind : Nat
  top : Int
  members : List Rect
  dividers : List Divider
  deriving DecidableEq, Repr

structure BarRun where
  actor : Nat
  top : Int
  x : Int
  depth : Int
  deriving DecidableEq, Repr

structure SeqMarker where
  pos : Point
  name : String
  axis : MarkerAxis
  deriving DecidableEq, Repr

structure RouteRun where
  points : List Point
  startMarker : Option SeqMarker
  endMarker : Option SeqMarker
  central : List Point
  badge : Option Point
  deriving DecidableEq, Repr

structure ClosedFrame where
  box : Nat
  dividers : List Divider
  deriving DecidableEq, Repr

structure Walk where
  cursor : Int
  bottom : Int
  boxRects : List Rect
  labelRects : List Rect
  routeRuns : List RouteRun
  fragments : List FragRun
  closed : List ClosedFrame
  openBars : List BarRun
  bars : List Rect
  barDepths : List Int
  destroyedY : List (Option Int)

/-- The height of a fragment header or section: it covers the kind box and the label of `lines` lines. -/
def sectionHeight (c : Consts) (lines : Nat) : Int :=
  max (c.boxMargin + c.boxTextMargin + c.labelBoxHeight)
    (c.boxMargin + c.boxTextMargin + (lines : Int) * c.lineHeight)

def centreLabel (pl : Plan) (ls : List Rect) (label : Option Nat) (frame : Rect) (top : Int) :
    List Rect :=
  match label with
  | none => ls
  | some p =>
    if p < pl.labelLines.length then
      let lines := pl.labelLines.getD p []
      let width := widest lines
      ls.set p ⟨frame.x + half (frame.w - width), top, width, (lines.length : Int) * pl.c.lineHeight⟩
    else ls

def rectSpan (rs : List Rect) : Int × Int :=
  match rs with
  | [] => (0, 0)
  | r :: rest =>
    (rest.foldl (fun a k => min a k.x) r.x, rest.foldl (fun a k => max a (k.x + k.w)) (r.x + r.w))

/-- The header rectangle of actor ordinal `o`. -/
def actorRect (pl : Plan) (centres : List Int) (o : Nat) : Rect :=
  ⟨centres.getD o 0 - half (pl.widths.getD o 0), pl.bandTop, pl.widths.getD o 0, pl.heights.getD o 0⟩

/-- The header rectangle of every box: the actors sit in the band, every other box starts empty. -/
def actorRects (pl : Plan) (centres : List Int) : List Rect :=
  pl.m.boxes.zipIdx.map fun (_, index) =>
    match pl.actorBoxes.findIdx? (· == index) with
    | some o => actorRect pl centres o
    | none => rectZero

/-- The frame of the participant group `b` at box index `index`, around the headers of its members. -/
def participantRect (pl : Plan) (actors : List Rect) (b : ModelBox) (index : Nat) : Rect :=
  let c := pl.c
  let kids := (pl.m.boxes.zipIdx.filter fun (o, _) => o.parent == b.id).map fun (_, i) => actors.getD i rectZero
  let (left, right) := rectSpan kids
  let lines := pl.titleLines index
  let inner := (right - left) + 2 * c.boxTextMargin
  let extra := max (widest lines + 2 * c.wrapPadding - inner) 0
  let header := (lines.length : Int) * c.lineHeight + c.boxMargin
  ⟨left - c.boxTextMargin - half extra, pl.bandTop - header, inner + extra, header + pl.bandHeight + c.boxMargin⟩

def headerRects (pl : Plan) (centres : List Int) : List Rect :=
  let actors := actorRects pl centres
  pl.m.boxes.zipIdx.map fun (b, index) =>
    if isParticipantBox b then participantRect pl actors b index else actors.getD index rectZero

def headerLabels (pl : Plan) (rects : List Rect) : List Rect :=
  pl.m.boxes.zipIdx.foldl (fun ls (b, index) =>
    if isParticipantBox b then
      let rect := rects.getD index rectZero
      centreLabel pl ls (labelPosById pl.m (b.id ++ ".label")) rect (rect.y + pl.c.boxTextMargin)
    else ls) (List.replicate pl.m.labels.length rectZero)

def placeHeaders (pl : Plan) (centres : List Int) : List Rect × List Rect :=
  let rects := headerRects pl centres
  (rects, headerLabels pl rects)

def addMember (w : Walk) (r : Rect) : Walk :=
  match w.fragments with
  | [] => w
  | f :: rest => { w with fragments := { f with members := f.members ++ [r] } :: rest }

def sequenceMarkerNames : List String :=
  ["arrowhead", "crosshead", "filled-head", "solidTopArrowHead", "solidBottomArrowHead",
   "stickTopArrowHead", "stickBottomArrowHead"]

def routeMarker (m : Model) (route : Nat) (start : Bool) : Option String :=
  match m.routes[route]? with
  | none => none
  | some r =>
    let name := if start then r.markerStart else r.markerEnd
    if name == "" || name == "none" || name == "point" || !sequenceMarkerNames.contains name then none
    else if markers.any (·.name == name) then some name else none

/-- The box of an actor that the message creates, with its box index. -/
def createdRect (pl : Plan) (cs : List Int) (bits dst : Nat) (y : Int) : Option (Nat × Rect) :=
  if bits.testBit 10 then
    match pl.actorBoxes[dst]? with
    | none => none
    | some boxIndex =>
      some (boxIndex, ⟨cs.getD dst 0 - half (pl.widths.getD dst 0), y, pl.widths.getD dst 0,
        pl.heights.getD dst 0⟩)
  else none

def createdBox (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) : Walk × Int :=
  match createdRect pl cs bits dst y with
  | some (boxIndex, rect) =>
    (addMember { w with boxRects := w.boxRects.set boxIndex rect } rect, rect.h + pl.c.boxMargin)
  | none => (w, 0)

def messageRun (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat) (y dx : Int) :
    RouteRun :=
  let c := pl.c
  let cFrom := cs.getD src 0
  let cTo := cs.getD dst 0
  let fb := w.boxRects.getD ((pl.actorBoxes[src]?).getD 0) rectZero
  let tb := w.boxRects.getD ((pl.actorBoxes[dst]?).getD 0) rectZero
  let fromBottom := fb.y + fb.h
  let points : List Point :=
    if src == dst then
      [⟨cFrom, fromBottom⟩, ⟨cFrom, y⟩, ⟨cFrom + dx, y⟩, ⟨cFrom + dx, y + c.selfLoopDepth⟩,
       ⟨cFrom, y + c.selfLoopDepth⟩, ⟨cFrom, fromBottom⟩]
    else [⟨cFrom, fromBottom⟩, ⟨cFrom, y⟩, ⟨cTo, y⟩, ⟨cTo, tb.y + tb.h⟩]
  let startAxis := if cFrom ≤ cTo then MarkerAxis.negativeX else MarkerAxis.positiveX
  let endAxis := if cFrom ≤ cTo then MarkerAxis.positiveX else MarkerAxis.negativeX
  let startMarker := (routeMarker pl.m route true).map fun name => ⟨⟨cFrom, y⟩, name, startAxis⟩
  let endMarker := (routeMarker pl.m route false).map fun name =>
    if src == dst then ⟨⟨cFrom, y + c.selfLoopDepth⟩, name, MarkerAxis.negativeX⟩
    else ⟨⟨cTo, y⟩, name, endAxis⟩
  let central := (if bits.testBit 12 then [(⟨cFrom, y⟩ : Point)] else []) ++
    (if bits.testBit 13 then [(⟨cTo, y⟩ : Point)] else [])
  let badge := if pl.m.profile == .vector ∧ bits.testBit 6 then some (⟨cFrom, y⟩ : Point) else none
  { points, startMarker, endMarker, central, badge }

/-- Advance the cursor over a row of height `rowH`. -/
def Walk.advance (w : Walk) (rowH : Int) : Walk :=
  { w with cursor := w.cursor + rowH, bottom := max w.bottom (w.cursor + rowH) }

/-- Record the row at which a destroyed actor's lifeline ends. -/
def markDestroyed (w : Walk) (bits : Nat) (destroyed y : Int) : Walk :=
  if bits.testBit 11 ∧ destroyed ≠ -1 ∧ 0 ≤ destroyed ∧ destroyed < (w.destroyedY.length : Int) then
    { w with destroyedY := w.destroyedY.set destroyed.toNat (some y) }
  else w

/-- Record the rectangle of a label. -/
def Walk.placeLabel (w : Walk) (pos : Option Nat) (r : Rect) : Walk :=
  match pos with
  | some p => { w with labelRects := w.labelRects.set p r }
  | none => w

/-- The label of a message when the plan measured it. -/
def messageLabelAt (pl : Plan) (route : Nat) : Option Nat :=
  match routeLabelPos pl.m route with
  | some p => if p < pl.labelLines.length then some p else none
  | none => none

def stepMessage (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat) (destroyed : Int) :
    Walk :=
  let c := pl.c
  let labelAt : Option Nat := messageLabelAt pl route
  let lines := pl.linesAt labelAt
  let count : Int := lines.length
  let labelW := widest lines
  let cFrom := cs.getD src 0
  let cTo := cs.getD dst 0
  let y := w.cursor + c.messageTop + count * c.lineHeight
  let rowBase := c.messageTop + count * c.lineHeight + c.boxMargin
  let dx := if src == dst then max (half (labelW + 2 * c.wrapPadding)) c.selfLoopMinDx else 0
  let rowSelf := if src == dst then rowBase + c.selfLoopDepth else rowBase
  let cb := createdBox pl cs w bits dst y
  let rowH := rowSelf + cb.2
  let w2 := markDestroyed cb.1 bits destroyed y
  let run := messageRun pl cs w2 bits src dst route y dx
  let w3 := { w2 with routeRuns := w2.routeRuns ++ [run] }
  let w4 := w3.placeLabel labelAt
    ⟨half (cFrom + cTo) - half labelW, w.cursor + c.messageTop, labelW, count * c.lineHeight⟩
  let w5 := addMember w4 ⟨min cFrom cTo - dx, w.cursor, (max cFrom cTo - min cFrom cTo) + 2 * dx, rowH⟩
  w5.advance rowH

/-- The left edge and the width of a note. -/
def noteSpan (pl : Plan) (cs : List Int) (placement a b box : Nat) : Int × Int :=
  let c := pl.c
  let textW := widest (pl.titleLines box)
  let cA := cs.getD a 0
  let cB := cs.getD b 0
  let actorW := pl.widths.getD a 0
  let width0 := max actorW (textW + 2 * c.noteMargin)
  if placement == 2 ∧ a == b then (cA - half width0, width0)
  else if placement == 2 then
    let left := min cA cB - half c.actorMargin
    let right := max cA cB + half c.actorMargin
    (left, max (right - left) (textW + 2 * c.noteMargin))
  else if placement == 1 then (cA + half actorW + half c.actorMargin, width0)
  else (cA - half actorW - half c.actorMargin - width0, width0)

/-- The height of the text of a note. -/
def noteTextHeight (pl : Plan) (box : Nat) : Int :=
  match ownedLabelPos pl.m ((pl.m.boxes[box]?.map (·.id)).getD "") with
  | some p => ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight
  | none => 0

def stepNote (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) : Walk :=
  let c := pl.c
  let pos := ownedLabelPos pl.m ((pl.m.boxes[box]?.map (·.id)).getD "")
  let textH := noteTextHeight pl box
  let span := noteSpan pl cs placement a b box
  let x := span.1
  let width := span.2
  let top := w.cursor + c.boxMargin
  let height := textH + 2 * c.noteMargin
  let rect : Rect := ⟨x, top, width, height⟩
  let w1 := addMember { w with boxRects := w.boxRects.set box rect } rect
  let w2 := w1.placeLabel pos ⟨x + c.noteMargin, top + c.noteMargin, max (width - 2 * c.noteMargin) 0, textH⟩
  w2.advance (c.boxMargin + height)

/-- The rows a fragment header takes: its kind box and title, or the margin of a `rect`. -/
def fragmentAdvance (pl : Plan) (kind box : Nat) : Int :=
  if kind == fragmentKindRect then pl.c.boxMargin
  else sectionHeight pl.c
    (pl.linesAt (labelPosById pl.m (((pl.m.boxes[box]?.map (·.id)).getD "") ++ ".label"))).length

def stepFragmentStart (pl : Plan) (w : Walk) (kind box : Nat) : Walk :=
  { w with fragments := ⟨box, kind, w.cursor, [], []⟩ :: w.fragments,
           cursor := w.cursor + fragmentAdvance pl kind box }

/-- The label of section `sect` of the fragment box `box`. -/
def sectionLabel (pl : Plan) (box sect : Nat) : Option Nat :=
  labelPosById pl.m (((pl.m.boxes[box]?.map (·.id)).getD "") ++ ".s" ++ toString sect)

def stepFragmentElse (pl : Plan) (w : Walk) (box sect : Nat) : Walk :=
  let label := sectionLabel pl box sect
  let fragments := match w.fragments with
    | [] => []
    | f :: rest => { f with dividers := f.dividers ++ [⟨w.cursor, label⟩] } :: rest
  { w with fragments, cursor := w.cursor + sectionHeight pl.c (pl.linesAt label).length }

/-- The frame width covers the natural extent, the kind box, both title measurements, and
the divider labels. -/
def fragmentWidth (pl : Plan) (run : FragRun) (natural : Int) : Except LayoutError Int :=
  if run.kind == fragmentKindRect then pure natural
  else do
    let c := pl.c
    let id := (pl.m.boxes[run.box]?.map (·.id)).getD ""
    let titleText := match pl.m.labels.find? (fun l => l.id == id ++ ".label") with
      | some l => l.text
      | none => "[]"
    let titleLines ← measureLines (fontFamily := pl.m.options.fontFamily) pl.m.profile .label I32_MAX titleText
    let placed := pl.labelWidth (labelPosById pl.m (id ++ ".label"))
    let base := max (max natural (c.labelBoxWidth + 2 * c.boxMargin))
      (max (widest titleLines) placed + 2 * c.boxMargin)
    pure (run.dividers.foldl (fun acc d => max acc (pl.labelWidth d.label + 2 * c.boxMargin)) base)

/-- The frame rectangle of a fragment that closes at the cursor of `w` with the frame width `width`. -/
def frameRect (pl : Plan) (w : Walk) (run : FragRun) (width : Int) : Rect :=
  let span := rectSpan run.members
  let natural := (span.2 - span.1) + 2 * pl.c.boxMargin
  ⟨span.1 - pl.c.boxMargin - half (width - natural), run.top, width,
    w.cursor + pl.c.boxMargin - run.top⟩

/-- The walk after a fragment closes with the frame width `width`. -/
def closeWith (pl : Plan) (w : Walk) (run : FragRun) (width : Int) : Walk :=
  let c := pl.c
  let plain := run.kind == fragmentKindRect
  let id := (pl.m.boxes[run.box]?.map (·.id)).getD ""
  let bottom := w.cursor + c.boxMargin
  let rect : Rect := frameRect pl w run width
  let titleTop := c.boxMargin + c.boxTextMargin
  let labelRects :=
    if plain then w.labelRects
    else run.dividers.foldl (fun ls d => centreLabel pl ls d.label rect (d.row + titleTop))
      (centreLabel pl w.labelRects (labelPosById pl.m (id ++ ".label")) rect (run.top + titleTop))
  let closed := w.closed ++ [(⟨run.box, run.dividers⟩ : ClosedFrame)]
  let boxRects := w.boxRects.set run.box rect
  let w1 : Walk :=
    { w with cursor := bottom, boxRects := boxRects, bottom := max w.bottom bottom,
             labelRects := labelRects, closed := closed }
  addMember w1 rect

def closeFragment (pl : Plan) (w : Walk) (run : FragRun) : Except LayoutError Walk := do
  let span := rectSpan run.members
  let natural := (span.2 - span.1) + 2 * pl.c.boxMargin
  let width ← fragmentWidth pl run natural
  return closeWith pl w run width

def stepFragmentEnd (pl : Plan) (w : Walk) : Except LayoutError Walk :=
  match w.fragments with
  | [] => pure w
  | run :: rest => closeFragment pl { w with fragments := rest } run

def stepActivateStart (pl : Plan) (cs : List Int) (w : Walk) (actor : Nat) : Walk :=
  let depth := w.barDepths.getD actor 0
  let bar : BarRun := ⟨actor, w.cursor + pl.c.activationTop,
    cs.getD actor 0 + depth * half pl.c.activationWidth, depth + 1⟩
  { w with barDepths := w.barDepths.set actor (depth + 1), openBars := bar :: w.openBars }

def extractFirst {α : Type} (p : α → Bool) : List α → Option (α × List α)
  | [] => none
  | x :: xs =>
    if p x then some (x, xs)
    else match extractFirst p xs with
      | none => none
      | some (y, ys) => some (y, x :: ys)

def barRect (pl : Plan) (cursor : Int) (bar : BarRun) : Rect :=
  ⟨bar.x, bar.top, pl.c.activationWidth, max (cursor - bar.top) 0⟩

def stepActivateEnd (pl : Plan) (w : Walk) (actor : Nat) : Walk :=
  let depth := max (w.barDepths.getD actor 0 - 1) 0
  let w1 := { w with barDepths := w.barDepths.set actor depth }
  match extractFirst (fun b => b.actor == actor && b.depth == depth + 1) w1.openBars with
  | none => w1
  | some (bar, rest) => { w1 with openBars := rest, bars := w1.bars ++ [barRect pl w1.cursor bar] }

def stepWalk (pl : Plan) (cs : List Int) (w : Walk) : Step → Except LayoutError Walk
  | .message bits src dst route destroyed => pure (stepMessage pl cs w bits src dst route destroyed)
  | .note placement a b box => pure (stepNote pl cs w placement a b box)
  | .fragmentStart kind box => pure (stepFragmentStart pl w kind box)
  | .fragmentElse box sect => pure (stepFragmentElse pl w box sect)
  | .fragmentEnd => stepFragmentEnd pl w
  | .activateStart actor => pure (stepActivateStart pl cs w actor)
  | .activateEnd actor => pure (stepActivateEnd pl w actor)

def closeAll (pl : Plan) : Walk → Nat → Except LayoutError Walk
  | w, 0 => pure w
  | w, n + 1 =>
    match w.fragments with
    | [] => pure w
    | run :: rest => do closeAll pl (← closeFragment pl { w with fragments := rest } run) n

/-- The walk before the first event: the headers are placed and the cursor is below them. -/
def initWalk (pl : Plan) (cs : List Int) : Walk :=
  let headers := placeHeaders pl cs
  let cursor := pl.bandTop + pl.bandHeight + 2 * pl.c.boxMargin
  { cursor, bottom := cursor, boxRects := headers.1, labelRects := headers.2, routeRuns := [],
    fragments := [], closed := [], openBars := [], bars := [],
    barDepths := List.replicate pl.widths.length 0,
    destroyedY := List.replicate pl.widths.length none }

def walk (pl : Plan) (cs : List Int) (steps : List Step) : Except LayoutError Walk := do
  let w1 ← steps.foldlM (stepWalk pl cs) (initWalk pl cs)
  let w2 ← closeAll pl w1 w1.fragments.length
  let barsAll := w2.bars ++ w2.openBars.map (barRect pl w2.cursor)
  return { w2 with bars := barsAll, openBars := [], bottom := w2.cursor }

/-! ### The dump -/

def extentOf (w : Walk) : Int × Int × Int :=
  let grow : Int × Int × Int → Rect → Int × Int × Int := fun a r =>
    (min a.1 r.x, max a.2.1 (r.x + r.w), max a.2.2 (r.y + r.h))
  let a1 := w.boxRects.foldl grow (0, 0, w.bottom)
  let a2 := w.routeRuns.foldl (fun acc run =>
    run.points.foldl (fun (a : Int × Int × Int) p => (min a.1 p.x, max a.2.1 p.x, max a.2.2 p.y)) acc) a1
  let a3 := w.bars.foldl grow a2
  w.labelRects.foldl (fun a r => if r.w != 0 ∨ r.h != 0 then grow a r else a) a3

structure Painter where
  pl : Plan
  w : Walk
  cs : List Int
  sx : Int
  sy : Int
  boxes : List Box
  routes : List Route
  labels : List SceneLabel

def Painter.rectOf (p : Painter) (r : Rect) : Rect := ⟨r.x + p.sx, r.y + p.sy, r.w, r.h⟩

def Painter.pointOf (p : Painter) (q : Point) : Point := ⟨q.x + p.sx, q.y + p.sy⟩

def routePoints (pl : Plan) (w : Walk) (sx sy : Int) (r : ModelRoute) (run : RouteRun) : List Point :=
  let pts := run.points.map fun q => (⟨q.x + sx, q.y + sy⟩ : Point)
  let port (id : String) : Option Int :=
    (pl.m.boxes.findIdx? (·.id == id)).map fun at_ =>
      let b := w.boxRects.getD at_ rectZero
      b.y + b.h + sy
  let first := match port r.fromId, pts with
    | some y, q :: rest => (⟨q.x, y⟩ : Point) :: rest
    | _, _ => pts
  match port r.toId, first.getLast? with
  | some y, some q => first.dropLast ++ [(⟨q.x, y⟩ : Point)]
  | _, _ => first

def mkPainter (pl : Plan) (cs : List Int) (w : Walk) : Painter :=
  let (minX, _, _) := extentOf w
  let sx := pl.c.diagramMarginX - minX
  let sy := pl.c.diagramMarginY
  let shifted := fun (r : Rect) => (⟨r.x + sx, r.y + sy, r.w, r.h⟩ : Rect)
  { pl, w, cs, sx, sy
    boxes := pl.m.boxes.zipIdx.map fun (b, i) =>
      ⟨b.id, b.role.id, shifted (w.boxRects.getD i rectZero), b.parent, b.exclusive⟩
    routes := pl.m.routes.zipIdx.map fun (r, i) =>
      ⟨r.id, r.fromId, r.toId, r.orthogonal,
        match w.routeRuns[i]? with
        | some run => routePoints pl w sx sy r run
        | none => []⟩
    labels := pl.m.labels.zipIdx.map fun (l, i) =>
      { id := l.id, owner := l.owner, rect := shifted (w.labelRects.getD i rectZero),
        lines := lineTexts (pl.labelLines.getD i []), text := l.text } }

def Painter.canvas (p : Painter) : Size :=
  let (minX, maxX, maxY) := extentOf p.w
  ⟨maxX - minX + 2 * p.pl.c.diagramMarginX, maxY + 2 * p.pl.c.diagramMarginY⟩

/-! ### The display list -/

def Painter.isCell (p : Painter) : Bool := p.pl.m.profile == .cell

def kindLabelRect (p : Painter) (frame : Rect) : Rect :=
  let inset : Int := if p.isCell then 1 else 0
  ⟨frame.x + inset, frame.y + inset, p.pl.c.labelBoxWidth, p.pl.c.labelBoxHeight⟩

def blockedRuns (p : Painter) (column : Int) : List (Int × Int) :=
  let block (r : Rect) : List (Int × Int) :=
    if 0 < r.w ∧ 0 < r.h ∧ r.x ≤ column ∧ column < r.x + r.w then [(r.y, r.y + r.h - 1)] else []
  let fromLabels := p.labels.flatMap fun l => block l.rect
  let fromKinds := (p.pl.m.boxes.zip p.boxes).flatMap fun (mb, b) =>
    if isSectionedFragment mb then block (kindLabelRect p b.rect) else []
  (fromLabels ++ fromKinds).mergeSort fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

def freeRuns (p : Painter) (column first last : Int) : List (Int × Int) :=
  if !p.isCell then [(first, last)]
  else
    let (runs, from_) := (blockedRuns p column).foldl (fun (acc : List (Int × Int) × Int) b =>
      ((if acc.2 < b.1 then acc.1 ++ [(acc.2, b.1 - 1)] else acc.1), max acc.2 (b.2 + 1))) ([], first)
    if from_ ≤ last then runs ++ [(from_, last)] else runs

def lifelineSegments (p : Painter) (centre top stop : Int) : List (List Point) :=
  ((freeRuns p centre top stop).filter fun r => r.1 < r.2).map fun r => [⟨centre, r.1⟩, ⟨centre, r.2⟩]

def textItem (rect : Rect) (role : TextRole) (style : String) (lines : List (List TextRun)) : Primitive :=
  .text { rect := rect, role := role, size := 14, align := .middle, style := style, lines := lines }

def labelItem (p : Painter) (pos : Nat) : Primitive :=
  let role := match p.pl.m.labels[pos]? with
    | some l => if labelIsBody p.pl.m l then TextRole.body else TextRole.label
    | none => TextRole.label
  textItem ((p.labels[pos]?.map (·.rect)).getD rectZero) role "text" (runsOf (p.pl.labelLines.getD pos []))

def Painter.barGroup (p : Painter) : Option Group :=
  if p.w.bars.isEmpty then none
  else
    let items := p.w.bars.flatMap fun bar =>
      let r := p.rectOf bar
      if !p.isCell then [Primitive.rect r { style := "node" }]
      else
        (freeRuns p r.x r.y (r.y + r.h - 1)).filterMap fun run =>
          if run.1 < run.2 then
            some (Primitive.polyline [⟨r.x, run.1⟩, ⟨r.x, run.2⟩] 0 { style := "node", width := .emphasis })
          else none
    some ⟨.decor, "", items⟩

def Painter.dividersOf (p : Painter) (index : Nat) : List Divider :=
  match p.w.closed.find? (·.box == index) with
  | some f => f.dividers
  | none => []

def Painter.kindBox (p : Painter) (shape : String) (r : Rect) (index : Nat) : List Primitive :=
  let position := kindLabelRect p r
  let style := if p.isCell then "text" else "text-inverse"
  let ink : List Primitive := if p.isCell then [] else [.rect position { style := "ink" }]
  let tag : Primitive := textItem position .label style [[⟨shape, false, false⟩]]
  let right := if p.isCell then r.x + r.w - 1 else r.x + r.w
  let dividerItems := (p.dividersOf index).flatMap fun d =>
    let y := d.row + p.sy
    let rule : Primitive := .polyline [⟨r.x, y⟩, ⟨right, y⟩] 0 { style := "rule", line := .dotted }
    match d.label with
    | some l => [rule, labelItem p l]
    | none => [rule]
  ink ++ [tag] ++ dividerItems

def Painter.groupFrames (p : Painter) : List Group :=
  (p.pl.m.boxes.zip p.boxes).zipIdx.filterMap fun ((mb, b), index) =>
    if mb.role != .group then none
    else
      let body : List Primitive :=
        if mb.shape == "rect" then [.rect b.rect { style := "band" }]
        else if isFragmentShape mb.shape then
          .rect b.rect { style := "group" } :: p.kindBox mb.shape b.rect index
        else [.rect b.rect { style := "group" }]
      let title := match titlePos p.pl.m index with
        | some pos => [labelItem p pos]
        | none => []
      some ⟨.group, mb.id, body ++ title⟩

def Painter.badge (p : Painter) (style : String) (q : Point) : Primitive :=
  let at_ := p.pointOf q
  .ellipse at_.x at_.y p.pl.c.autonumberRadius p.pl.c.autonumberRadius { style := style }

def Painter.edgeItems (p : Painter) (r : ModelRoute) (index : Nat) (run : RouteRun) : List Primitive :=
  let shape : Paint := { style := "edge", line := if r.stroke == "dotted" then .dotted else .solid }
  let pts := (p.routes[index]?.map (·.points)).getD []
  let drawn := if 2 < pts.length then pts.dropLast.tail else pts
  let markerItem (mk : SeqMarker) : Primitive := .markerRef mk.name (p.pointOf mk.pos) mk.axis
  let label := match ownedLabelPos p.pl.m r.id with
    | some pos => [labelItem p pos]
    | none => []
  [Primitive.polyline drawn p.pl.c.cornerRadius shape] ++
    run.central.map (p.badge "mark") ++
    (match run.badge with | some q => [p.badge "ink" q] | none => []) ++
    ((run.startMarker.map markerItem).toList ++ (run.endMarker.map markerItem).toList) ++ label

def Painter.edgeGroups (p : Painter) : List Group :=
  p.pl.m.routes.zipIdx.filterMap fun (r, index) =>
    match p.w.routeRuns[index]? with
    | some run => some ⟨.edge, r.id, p.edgeItems r index run⟩
    | none => none

def Painter.appendActor (p : Painter) (index : Nat) (r : Rect) : List Primitive :=
  let ordinal := ((p.pl.actorBoxes.findIdx? (· == index)).getD 0)
  let centre := ((p.cs[ordinal]?).getD (r.x + half r.w)) + p.sx
  let destroyed := (p.w.destroyedY[ordinal]?).getD none
  let stop := match destroyed with
    | some y => y + p.sy
    | none => p.w.bottom + p.sy
  let body : List Primitive := [.roundRect r p.pl.c.ruleRadius { style := "node" }] ++
    (lifelineSegments p centre (r.y + r.h) stop).map (fun pts => Primitive.polyline pts 0 { style := "rule" }) ++
    (match destroyed with
      | some _ => [.markerRef "crosshead" ⟨centre, stop⟩ .positiveY]
      | none => [])
  let lines := p.pl.actorLines.getD ordinal []
  if lines.isEmpty then body
  else
    let textH := (lines.length : Int) * p.pl.c.lineHeight
    body ++ [textItem ⟨r.x, r.y + half (r.h - textH), r.w, textH⟩ .label "text" (runsOf lines)]

def Painter.nodeGroups (p : Painter) : List Group :=
  (p.pl.m.boxes.zip p.boxes).zipIdx.filterMap fun ((mb, b), index) =>
    if mb.role != .node then none
    else
      let body : List Primitive :=
        if mb.shape == "note" then [.rect b.rect { style := "note" }] else p.appendActor index b.rect
      let title := match titlePos p.pl.m index with
        | some pos => [labelItem p pos]
        | none => []
      some ⟨.node, mb.id, body ++ title⟩

def Painter.groups (p : Painter) : List Group :=
  p.barGroup.toList ++ p.groupFrames ++ p.edgeGroups ++ p.nodeGroups

/-- The dump omits the shape `rect` (model-dump-03), so a `rect` fragment looks like a participant
group; the event stream names it, so the shape is restored from the `fragmentStart` steps. -/
def restoreFragmentShapes (m : Model) : Model :=
  let rects := (decodeSteps m.regionSets).filterMap fun s =>
    match s with
    | .fragmentStart kind box => if kind == fragmentKindRect then some box else none
    | _ => none
  { m with boxes := m.boxes.zipIdx.map fun (b, i) =>
      if b.role == .group ∧ b.shape == "" ∧ rects.contains i then { b with shape := "rect" } else b }

/-- The id of box `i`, or `""` when there is none. -/
def boxId (m : Model) (i : Nat) : String := (m.boxes[i]?.map (·.id)).getD ""

/-- The parent id of box `i`, or `""` when there is none. -/
def boxParent (m : Model) (i : Nat) : String := (m.boxes[i]?.map (·.parent)).getD ""

def isNoteBox (b : ModelBox) : Bool := b.role == .node && b.shape == "note"

def isFragmentBox (b : ModelBox) : Bool := b.role == .group && isFragmentShape b.shape

/-- What the event stream has done to the boxes so far: the open fragment boxes (innermost first),
the boxes that an event placed, and the count of messages. -/
structure CheckState where
  stack : List Nat
  placed : List Nat
  routes : Nat

/-- The id of the innermost open fragment, or `""` outside every fragment. -/
def topId (m : Model) (stack : List Nat) : String :=
  match stack with
  | [] => ""
  | s :: _ => boxId m s

/-- Route `route` runs between the boxes of lifelines `src` and `dst`. -/
def routeEndsOk (pl : Plan) (route src dst : Nat) : Bool :=
  match pl.m.routes[route]?, pl.actorBoxes[src]?, pl.actorBoxes[dst]? with
  | some r, some bs, some bd => r.fromId == boxId pl.m bs && r.toId == boxId pl.m bd
  | _, _, _ => false

/-- The box of lifeline `dst` when a message may create it: it is not placed yet, it is not
exclusive, and its parent is the innermost open fragment. -/
def createOk (pl : Plan) (st : CheckState) (dst : Nat) : Option Nat :=
  match pl.actorBoxes[dst]? with
  | some bi =>
    match pl.m.boxes[bi]? with
    | some b =>
      if !(st.placed.contains bi) && !b.exclusive && b.parent == topId pl.m st.stack then some bi else none
    | none => none
  | none => none

def stepCheck (pl : Plan) (st : CheckState) : Step → Option CheckState
  | .message bits src dst route _ =>
    if src < pl.actorBoxes.length && dst < pl.actorBoxes.length && route == st.routes &&
        routeEndsOk pl route src dst then
      if bits.testBit 10 then
        match createOk pl st dst with
        | some bi => some { st with placed := bi :: st.placed, routes := st.routes + 1 }
        | none => none
      else some { st with routes := st.routes + 1 }
    else none
  | .note _ _ _ box =>
    match pl.m.boxes[box]? with
    | some b =>
      if isNoteBox b && !b.exclusive && !(st.placed.contains box) && b.parent == topId pl.m st.stack then
        some { st with placed := box :: st.placed }
      else none
    | none => none
  | .fragmentStart _ box =>
    match pl.m.boxes[box]? with
    | some b =>
      if isFragmentBox b && !(st.placed.contains box) && b.parent == topId pl.m st.stack &&
          decide (st.stack.length + 1 ≤ pl.m.boxes.length) then
        some { st with stack := box :: st.stack, placed := box :: st.placed }
      else none
    | none => none
  | .fragmentElse box _ =>
    match st.stack with
    | top :: _ => if top == box then some st else none
    | [] => none
  | .fragmentEnd =>
    match st.stack with
    | _ :: rest => some { st with stack := rest }
    | [] => none
  | .activateStart _ => some st
  | .activateEnd _ => some st

/-- The lifelines of participant `id` are consecutive and there is at least one. -/
def contiguousKids (pl : Plan) (id : String) : Bool :=
  match memberOrdinals pl id with
  | [] => false
  | f :: rest => (f :: rest) == List.range' f (rest.length + 1)

/-- Some participant box has id `id`. -/
def isParticipantId (m : Model) (id : String) : Bool :=
  m.boxes.any fun p => isParticipantBox p && p.id == id

/-- The checks that run after the last event. -/
def boxFinalOk (pl : Plan) (ck : CheckState) (b : ModelBox) (i : Nat) : Bool :=
  b.id != "" &&
    (if isActorBox b then
      if b.exclusive then !(ck.placed.contains i) && (b.parent == "" || isParticipantId pl.m b.parent)
      else ck.placed.contains i
    else if isNoteBox b then !b.exclusive && ck.placed.contains i
    else if isParticipantBox b then
      !b.exclusive && b.parent == "" && contiguousKids pl b.id &&
        titlePos pl.m i == labelPosById pl.m (b.id ++ ".label")
    else if isFragmentBox b then !b.exclusive && ck.placed.contains i
    else false)

def finalOk (pl : Plan) (ck : CheckState) : Bool :=
  ck.routes == pl.m.routes.length && pl.m.boxes.zipIdx.all fun (b, i) => boxFinalOk pl ck b i

/-- The checked predicate: the plan builds, the event stream passes `stepCheck`, and the boxes and
routes that it leaves pass `finalOk`. -/
def modelOk (model : Model) : Bool :=
  let m := restoreFragmentShapes model
  match Plan.build m with
  | .error _ => false
  | .ok pl =>
    match (decodeSteps m.regionSets).foldlM (stepCheck pl) { stack := [], placed := [], routes := 0 } with
    | none => false
    | some ck => finalOk pl ck

/-- The participant frames hold their member actors and keep clear of every other participant frame
and of every actor that is not their member. The clearance is checked on the header rectangles of
the plan. -/
def headersOk (pl : Plan) (cs : List Int) : Bool :=
  let hdr := headerRects pl cs
  pl.m.boxes.zipIdx.all fun (b, i) =>
    !isParticipantBox b ||
      pl.m.boxes.zipIdx.all fun (b', j) =>
        j == i ||
          (if b'.parent == b.id then decide ((hdr.getD i rectZero).Contained (hdr.getD j rectZero))
           else !(isParticipantBox b' || isActorBox b') ||
             decide (Disjoint (hdr.getD i rectZero) (hdr.getD j rectZero)))

/-- `headersOk` is part of the gate of the sequence layout, next to `modelOk`. -/
def layoutOk (model : Model) : Bool :=
  let m := restoreFragmentShapes model
  match Plan.build m with
  | .error _ => false
  | .ok pl =>
    let steps := decodeSteps m.regionSets
    match steps.foldlM (stepCheck pl) { stack := [], placed := [], routes := 0 } with
    | none => false
    | some ck => finalOk pl ck && headersOk pl (columns pl steps)
/-- Reject inconsistent developer model dumps before the geometry walk. -/
def layout (model : Model) : Except LayoutError Scene :=
  if layoutOk model then do
    let m := restoreFragmentShapes model
    let pl ← Plan.build m
    let steps := decodeSteps m.regionSets
    let cs := columns pl steps
    let w ← walk pl cs steps
    let p := mkPainter pl cs w
    return { kind := m.kind, profile := m.profile, options := m.options, canvas := p.canvas,
             boxes := p.boxes, routes := p.routes, labels := p.labels, items := p.groups }
  else .error .domain

theorem layout_admissible {model : Model} {s : Scene} (h : layout model = .ok s) :
    layoutOk model = true := by
  unfold layout at h
  split at h
  · assumption
  · cases h

end Sequence
end Elegant
