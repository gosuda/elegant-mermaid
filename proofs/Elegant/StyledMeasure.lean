import Elegant.Formula
import Elegant.Label
import Elegant.Measure
import ElegantGeometry.Basic

set_option autoImplicit false

namespace Elegant
namespace StyledMeasure

/-- Cell profile normalizes control characters (< 32 and 127..159) to U+FFFD. -/
def normalizeCellChar (c : Char) : Char :=
  let n := c.toNat
  if n < 32 || (127 ≤ n && n ≤ 159) then '\uFFFD' else c

def normalizeCellText (cs : List Char) : List Char :=
  cs.map normalizeCellChar

/-- Plain tokens inherit m.weight, italic uses Regular (0), bold uses SemiBold (1);
italic takes priority if both. -/
def tokenWeight (m : Measure.Metric) (bold italic : Bool) : Nat :=
  if italic then 0
  else if bold then 1
  else m.weight

/-- The scalar that stands for a laid-out formula in the rendered text of a region. -/
def formulaPlaceholder : Char := '\uE000'

/-- A run positioned in the rendered text. `box` is the width of the formula box when the run
is a formula that parsed and was laid out; the rendered text then holds one placeholder. -/
structure PositionedToken where
  start : Nat
  stop : Nat
  bold : Bool
  italic : Bool
  text : List Char
  box : Option Int
deriving Repr

/-- The width of the box of a formula run under the vector profile. Cell metrics, plain runs,
and formulas with a diagnostic have no box. -/
def formulaWidthOf (m : Measure.Metric) (run : Label.Run) : Except LayoutError (Option Int) :=
  if m.profile == .cell || !run.math then pure none
  else Formula.width? ((run.text.drop 2).take (run.text.length - 4)) m.sizePx

def buildTokens (boxes : List (Option Int)) (runs : List Label.Run) : List PositionedToken :=
  go 0 (runs.zip boxes)
where
  go (offset : Nat) : List (Label.Run × Option Int) → List PositionedToken
    | [] => []
    | (r, box) :: rs =>
      let len := if box.isSome then 1 else r.text.length
      if r.text.isEmpty then
        go offset rs
      else
        ⟨offset, offset + len, r.bold, r.italic, r.text, box⟩ :: go (offset + len) rs

def renderedText (toks : List PositionedToken) : List Char :=
  (toks.map fun t => if t.box.isSome then [formulaPlaceholder] else t.text).flatten

def advanceTokens (cursor : Nat) : List PositionedToken → List PositionedToken
  | [] => []
  | tok :: rest =>
    if tok.stop ≤ cursor then
      advanceTokens cursor rest
    else
      tok :: rest

def overlappingTokens (stop : Nat) : List PositionedToken → List PositionedToken
  | [] => []
  | tok :: rest =>
    if tok.start < stop then
      tok :: overlappingTokens stop rest
    else
      []

def tokenAdvancePart (c : List Char) (cursor stop : Nat) (m : Measure.Metric) (denominator : Nat)
    (tok : PositionedToken) : Except LayoutError Int := do
  let lo := max cursor tok.start
  let hi := min stop tok.stop
  if hi ≤ lo then
    pure 0
  else
    let chars := if tok.box.isSome then [] else (c.drop (lo - cursor)).take (hi - lo)
    let w := tokenWeight m tok.bold tok.italic
    let upem ← Measure.upemOf w
    let adv := Measure.advanceSum upem w chars
    let factor : Int := (denominator / upem : Nat)
    Measure.checkedI64 ((adv : Int) * factor)

def clusterAdvanceSum (c : List Char) (cursor stop : Nat) (m : Measure.Metric) (denominator : Nat)
    (toks : List PositionedToken) : Except LayoutError Int :=
  toks.foldlM (fun acc tok => do
    let part ← tokenAdvancePart c cursor stop m denominator tok
    Measure.checkedI64 (acc + part)) 0

def clusterFormulaSum (toks : List PositionedToken) : Int :=
  toks.foldl (fun acc tok => acc + tok.box.getD 0) 0

structure ClusterSpansResult where
  spans : List (Nat × Int)
  totalUnits : Int
deriving Repr

def computeClusterSpans (m : Measure.Metric) (denominator : Nat) (clusters : List (List Char))
    (tokens : List PositionedToken) : Except LayoutError ClusterSpansResult :=
  go 0 tokens [] 0 clusters
where
  go (cursor : Nat) (curTokens : List PositionedToken) (accSpans : List (Nat × Int))
      (accTotal : Int) : List (List Char) → Except LayoutError ClusterSpansResult
    | [] => pure ⟨accSpans.reverse, accTotal⟩
    | c :: cs => do
      let curTokens' := advanceTokens cursor curTokens
      let stop := cursor + c.length
      let (span, units) ← match m.profile with
        | .cell =>
          let w := Measure.clusterWidth c
          pure ((w, (0 : Int)), (w : Int))
        | .vector => do
          let toks := overlappingTokens stop curTokens'
          let units ← clusterAdvanceSum c cursor stop m denominator toks
          if units < 0 then throw .overflow
          pure ((units.toNat, clusterFormulaSum toks), units)
      let nextTotal ← Measure.checkedI64 (accTotal + units)
      go stop curTokens' (span :: accSpans) nextTotal cs

/-- The width of a line of `units` advance units and `math` formula units: the advance part
rounds up, formula boxes add their widths, and the `fontFamily` factor applies last. -/
def lineWidth (m : Measure.Metric) (units : Nat) (math : Int) : Int :=
  match m.profile with
  | .cell => (units : Int)
  | .vector =>
    let w := Measure.ceilDiv ((units : Int) * (m.sizePx * 64)) (m.upem : Int) + math
    if m.fontFamily then Measure.fontFamilyFactor w else w

def sumSpans (ss : List (Nat × Int)) : Nat × Int :=
  (ss.foldl (fun acc s => acc + s.1) 0, ss.foldl (fun acc s => acc + s.2) 0)

/-- Rule 8, step 1: the count of leading clusters whose total width stays within `L`. -/
def fitScan (m : Measure.Metric) (L : Int) : Nat → Int → Nat → List (Nat × Int) → Nat
  | _, _, k, [] => k
  | acc, macc, k, s :: rest =>
    if lineWidth m (acc + s.1) (macc + s.2) ≤ L then
      fitScan m L (acc + s.1) (macc + s.2) (k + 1) rest
    else k

def lineLen (m : Measure.Metric) (L : Int) (ss : List (Nat × Int)) : Nat :=
  max 1 (fitScan m L 0 0 0 ss)

def mkLine (m : Measure.Metric) (cs : List (List Char)) (ss : List (Nat × Int)) (a b c d : Nat) :
    Measure.Line :=
  let sums := sumSpans (Measure.slice ss a b)
  { text := Measure.joinClusters (Measure.slice cs a b)
    sep := Measure.joinClusters (Measure.slice cs c d)
    width := lineWidth m sums.1 sums.2 }

def finalLine (m : Measure.Metric) (cs : List (List Char)) (ss : List (Nat × Int)) (n i : Nat) :
    Measure.Line :=
  let t := Measure.spaceRun (cs.drop i).reverse
  let r := if i < n - t then n - t else n
  mkLine m cs ss i r r n

def wrapLoop (m : Measure.Metric) (L : Int) (cs : List (List Char)) (ss : List (Nat × Int))
    (opps : List Measure.Opp) (n : Nat) : Nat → Nat → List Measure.Line
  | 0, _ => []
  | fuel + 1, i =>
    if i < n then
      let j := i + lineLen m L (ss.drop i)
      if j = n then [finalLine m cs ss n i]
      else
        match Measure.lastOpp i j opps with
        | some o => mkLine m cs ss i o.pos o.pos o.next :: wrapLoop m L cs ss opps n fuel o.next
        | none => mkLine m cs ss i j j j :: wrapLoop m L cs ss opps n fuel j
    else []

/-- The source text of rendered offsets `[lo, stop)`: a formula token contributes its whole
literal, any other token the slice that overlaps. -/
def lineSource (toks : List PositionedToken) (lo stop : Nat) : List Char :=
  toks.foldl (fun acc t =>
    if t.start < stop && lo < t.stop then
      match t.box with
      | some _ => acc ++ t.text
      | none =>
        let a := max lo t.start - t.start
        let b := min stop t.stop - t.start
        acc ++ (t.text.drop a).take (b - a)
    else acc) []

def restoreLines (toks : List PositionedToken) (lines : List Measure.Line) : List Measure.Line :=
  go 0 lines
where
  go (offset : Nat) : List Measure.Line → List Measure.Line
    | [] => []
    | l :: ls =>
      let stop := offset + l.text.length
      { l with text := lineSource toks offset stop } :: go (stop + l.sep.length) ls

def attachRegionSep (lines : List Measure.Line) (sep : List Char) : List Measure.Line :=
  match sep with
  | [] => lines
  | _ =>
    match lines.getLast? with
    | none => [⟨[], sep, 0⟩]
    | some l => lines.dropLast ++ [{ l with sep := l.sep ++ sep }]

def regionIsEmpty (reg : Label.Region) : Bool :=
  reg.runs.all (fun r => r.text.isEmpty)

def wrapRegion (m : Measure.Metric) (target : Int) (denominator : Nat) (reg : Label.Region) :
    Except LayoutError (List Measure.Line) := do
  let text := (reg.runs.map (·.text)).flatten
  if text.isEmpty then
    pure []
  else
    let boxes ← reg.runs.mapM (formulaWidthOf m)
    let tokens := buildTokens boxes reg.runs
    let clusters := Measure.segment (renderedText tokens)
    if clusters.isEmpty then
      pure []
    else
      let spansRes ← computeClusterSpans m denominator clusters tokens
      if m.profile == .vector then
        let _ ← Measure.checkedI64 (spansRes.totalUnits * (m.sizePx * 64))
      let mCommon : Measure.Metric := { m with upem := denominator }
      let opps := Measure.opps clusters
      let rawLines := wrapLoop mCommon target clusters spansRes.spans opps clusters.length
        clusters.length 0
      if ¬ rawLines.all (fun l => decide (I32_MIN ≤ l.width ∧ l.width ≤ I32_MAX)) then
        throw .overflow
      pure (attachRegionSep (restoreLines tokens rawLines) reg.separator)

def wrapRegions (m : Measure.Metric) (target : Int) (denominator : Nat) (regs : List Label.Region) :
    Except LayoutError (List Measure.Line) :=
  go 0 regs []
where
  go (i : Nat) (rem : List Label.Region) (accRev : List Measure.Line) :
      Except LayoutError (List Measure.Line) := do
    match rem with
    | [] => pure accRev.reverse
    | reg :: rest =>
      let isLast := i + 1 == regs.length
      let reg' :=
        if m.profile == .cell then
          { reg with runs := reg.runs.map (fun r => { r with text := normalizeCellText r.text }) }
        else reg
      if regionIsEmpty reg' then
        if isLast then
          go (i + 1) rest accRev
        else
          go (i + 1) rest (⟨[], reg.separator, 0⟩ :: accRev)
      else
        let lines ← wrapRegion m target denominator reg'
        go (i + 1) rest (lines.reverse ++ accRev)

/-- Wrap styled source text under the given metric and target width. -/
def wrap (m : Measure.Metric) (target : Int) (source : List Char) :
    Except LayoutError (List Measure.Line) := do
  if ¬ m.WF then throw .domain
  let denominator ← match m.profile with
    | .cell => pure 1
    | .vector => do
      if m.sizePx < 0 ∨ m.upem == 0 then throw .domain
      let _ ← Measure.upemOf m.weight
      let upem0 ← Measure.upemOf 0
      let upem1 ← Measure.upemOf 1
      pure ((upem0 / Nat.gcd upem0 upem1) * upem1)
  let regs := Label.regions source
  wrapRegions m target denominator regs

end StyledMeasure
end Elegant
