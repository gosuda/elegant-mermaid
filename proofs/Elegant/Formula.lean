import ElegantGeometry.Basic
import Elegant.Measure
import Elegant.Gen.Layoutconst
import Elegant.Gen.Mathgreek
import Elegant.Gen.Mathglyph

set_option autoImplicit false

/-! # Formula box widths (spec/math.md)

Lean reference of the Go twin `internal/math` (`Parse` and `Layout`) restricted to what the
measure stage reads from a formula: whether the TeX subset parses without a diagnostic, and the
width of the formula box under the vector profile. A formula that raises any diagnostic (syntax
error, unsupported command, nesting beyond 64 levels) has no box and its source text is measured
as written. Boxes carry `w`, `a` (ascent), and `d` (descent) in 1/64 px; leaves are not
modelled, because the width of a box never depends on the position of its leaves. Both phases
are total: recursion is bounded by a fuel value that exceeds the nesting limit of the grammar. -/

namespace Elegant
namespace Formula

inductive Font where
  | roman
  | italic
  | bold
deriving DecidableEq, Repr, Inhabited

inductive SymClass where
  | greek
  | ordinary
  | binary
  | relation
  | sum
  | product
  | integral
deriving DecidableEq, Repr, Inhabited

inductive Spacing where
  | thin
  | medium
  | quad
deriving DecidableEq, Repr, Inhabited

inductive Delim where
  | leftParen
  | rightParen
  | leftBracket
  | rightBracket
  | leftBrace
  | rightBrace
  | bar
  | invisible
deriving DecidableEq, Repr, Inhabited

inductive Expr where
  | row (children : List Expr)
  | group (body : Expr)
  | glyph (c : Char) (font : Font)
  | limit (font : Font)
  | symbol (c : Char) (cls : SymClass) (font : Font)
  | fraction (numerator denominator : Expr)
  | scripts (base : Expr) (sup sub : Option Expr)
  | radical (index : Option Expr) (radicand : Expr)
  | delimited (left : Delim) (body : Expr) (right : Delim)
  | styled (font : Font) (body : Expr)
  | text (body : Expr)
  | space (s : Spacing)
deriving Inhabited

/-! ### Parser -/

inductive Stop where
  | end_
  | brace
  | index
  | right
deriving DecidableEq

inductive Mode where
  | math
  | text
deriving DecidableEq

inductive Bind where
  | atom
  | group
deriving DecidableEq

def maxDepth : Nat := 64

def nested (depth : Nat) : Option Nat :=
  if depth < maxDepth then some (depth + 1) else none

def isAsciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isAsciiPunct (c : Char) : Bool :=
  let n := c.toNat
  (33 ≤ n && n ≤ 47) || (58 ≤ n && n ≤ 64) || (91 ≤ n && n ≤ 96) || (123 ≤ n && n ≤ 126)

/-- Go `unicode.IsSpace`. -/
def isSpace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || n == 32 || n == 0x85 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 || n == 0x202F ||
    n == 0x205F || n == 0x3000

def skipWs (s : Array Char) : Nat → Nat → Nat
  | 0, off => off
  | fuel + 1, off =>
    match s[off]? with
    | some c => if isSpace c then skipWs s fuel (off + 1) else off
    | none => off

def rightWord : List Char := ['\\', 'r', 'i', 'g', 'h', 't']

/-- The source at `off` starts with `\right` and the next scalar is not an ASCII letter. -/
def rightAt (s : Array Char) (off : Nat) : Bool :=
  rightWord.zipIdx.all (fun q => s[off + q.2]? == some q.1) &&
    (match s[off + 6]? with
     | none => true
     | some c => !isAsciiAlpha c)

def closes (s : Array Char) (stop : Stop) (r : Char) (off : Nat) : Bool :=
  match stop with
  | .brace => r == '}'
  | .index => r == ']'
  | .right => rightAt s off
  | .end_ => false

def rowEnd (s : Array Char) (off : Nat) (stop : Stop) (m : Mode) : Option (Bool × Nat) :=
  let off := if m == .math then skipWs s s.size off else off
  match s[off]? with
  | none => if stop != .end_ then none else some (true, off)
  | some r =>
    if closes s stop r off then some (true, off)
    else if r == '}' then none
    else if m == .math && (r == '^' || r == '_') then none
    else some (false, off)

def alphaRun (s : Array Char) : Nat → Nat → Nat
  | 0, off => off
  | fuel + 1, off =>
    match s[off]? with
    | some c => if isAsciiAlpha c then alphaRun s fuel (off + 1) else off
    | none => off

def slice (s : Array Char) (a b : Nat) : List Char := (s.extract a b).toList

def commandName (s : Array Char) (off : Nat) : List Char × Nat :=
  match s[off]? with
  | some c =>
    if isAsciiAlpha c then
      let e := alphaRun s s.size off
      (slice s off e, e)
    else ([c], off + 1)
  | none => ([], off)

def greekOf (name : String) : Option Char :=
  match mathgreek.find? (fun r => r.name == name) with
  | some r => if Nat.isValidChar r.codepoint then some (Char.ofNat r.codepoint) else none
  | none => none

def symbolOf (name : String) : Option (Char × SymClass) :=
  match name with
  | "sum" => some ('∑', .sum)
  | "prod" => some ('∏', .product)
  | "int" => some ('∫', .integral)
  | "infty" => some ('∞', .ordinary)
  | "pm" => some ('±', .binary)
  | "times" => some ('×', .binary)
  | "div" => some ('÷', .binary)
  | "cdot" => some ('⋅', .binary)
  | "le" => some ('≤', .relation)
  | "ge" => some ('≥', .relation)
  | "ne" => some ('≠', .relation)
  | "approx" => some ('≈', .relation)
  | "to" => some ('→', .relation)
  | "leftarrow" => some ('←', .relation)
  | "Rightarrow" => some ('⇒', .relation)
  | "Leftrightarrow" => some ('⇔', .relation)
  | _ => (greekOf name).map fun c => (c, .greek)

def sharedCommand (name : List Char) (font : Option Font) : Option Expr :=
  match String.ofList name with
  | "," => some (.space .thin)
  | ";" => some (.space .medium)
  | "quad" => some (.space .quad)
  | "lim" => some (.limit (font.getD .roman))
  | other =>
    match symbolOf other with
    | some (c, cls) => some (.symbol c cls (font.getD .roman))
    | none => none

def delimiter (s : Array Char) (off : Nat) : Option (Delim × Nat) :=
  let off := skipWs s s.size off
  match s[off]? with
  | some '\\' =>
    match s[off + 1]? with
    | some '{' => some (.leftBrace, off + 2)
    | some '}' => some (.rightBrace, off + 2)
    | _ => none
  | some '(' => some (.leftParen, off + 1)
  | some ')' => some (.rightParen, off + 1)
  | some '[' => some (.leftBracket, off + 1)
  | some ']' => some (.rightBracket, off + 1)
  | some '|' => some (.bar, off + 1)
  | some '.' => some (.invisible, off + 1)
  | _ => none

inductive Outcome where
  | unhandled
  | failed
  | done (e : Expr) (off : Nat)

def Outcome.ofOption : Option (Expr × Nat) → Outcome
  | none => .failed
  | some (e, off) => .done e off

mutual

def rowLoop : Nat → Array Char → Stop → Nat → Option Font → Mode → Nat → List Expr →
    Option (Expr × Nat)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, s, stop, depth, font, m, off, acc =>
    match rowEnd s off stop m with
    | none => none
    | some (true, off') => some (Expr.row acc.reverse, off')
    | some (false, off') =>
      match rowItem fuel s depth font m off' with
      | none => none
      | some (child, off'') => rowLoop fuel s stop depth font m off'' (child :: acc)

def rowItem : Nat → Array Char → Nat → Option Font → Mode → Nat → Option (Expr × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, m, off =>
    match atom fuel s depth font m off with
    | none => none
    | some (a, off') =>
      if m == .text then some (a, off') else scripts fuel s a depth font off'

def group : Nat → Array Char → Nat → Option Font → Mode → Nat → Option (Expr × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, m, off =>
    match nested depth with
    | none => none
    | some next =>
      match rowLoop fuel s .brace next font m (off + 1) [] with
      | none => none
      | some (body, o) => some (Expr.group body, o + 1)

def argument : Nat → Array Char → Nat → Option Font → Mode → Bind → Nat →
    Option (Expr × Nat)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, m, bind, off =>
    let off := skipWs s s.size off
    match s[off]? with
    | none => none
    | some '{' => group fuel s depth font m off
    | some r =>
      if r == '}' || r == '^' || r == '_' then none
      else if rightAt s off || bind == .group then none
      else
        match nested depth with
        | none => none
        | some next => atom fuel s next font m off

def scriptsLoop : Nat → Array Char → Nat → Option Font → Nat → Option Expr → Option Expr →
    Option (Option Expr × Option Expr × Nat)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, off, sup, sub =>
    let off := skipWs s s.size off
    match s[off]? with
    | some '^' =>
      if sup.isSome then none
      else
        match argument fuel s depth font .math .atom (off + 1) with
        | none => none
        | some (a, o) => scriptsLoop fuel s depth font o (some a) sub
    | some '_' =>
      if sub.isSome then none
      else
        match argument fuel s depth font .math .atom (off + 1) with
        | none => none
        | some (a, o) => scriptsLoop fuel s depth font o sup (some a)
    | _ => some (sup, sub, off)

def scripts : Nat → Array Char → Expr → Nat → Option Font → Nat → Option (Expr × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, s, base, depth, font, off =>
    match scriptsLoop fuel s depth font off none none with
    | none => none
    | some (none, none, o) => some (base, o)
    | some (sup, sub, o) => some (Expr.scripts base sup sub, o)

def atom : Nat → Array Char → Nat → Option Font → Mode → Nat → Option (Expr × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, m, off =>
    match s[off]? with
    | none => none
    | some '{' => group fuel s depth font m off
    | some r =>
      if r == '\\' then command fuel s depth font m (off + 1)
      else if r == '=' && m == .math then
        some (Expr.symbol '=' .relation (font.getD .roman), off + 1)
      else
        some (Expr.glyph r (font.getD (if isAsciiAlpha r then .italic else .roman)), off + 1)

def command : Nat → Array Char → Nat → Option Font → Mode → Nat → Option (Expr × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, m, off =>
    let (name, off') := commandName s off
    match name with
    | [] => none
    | [c] =>
      if c.toNat < 128 && isAsciiPunct c && c != ',' && c != ';' then
        some (Expr.glyph c (font.getD .roman), off')
      else commandRest fuel s depth font m name off'
    | _ => commandRest fuel s depth font m name off'

def commandRest : Nat → Array Char → Nat → Option Font → Mode → List Char → Nat →
    Option (Expr × Nat)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, s, depth, font, m, name, off =>
    let handled :=
      if m == .math then mathCommand fuel s depth font (String.ofList name) off else .unhandled
    match handled with
    | .failed => none
    | .done e o => some (e, o)
    | .unhandled =>
      match sharedCommand name font with
      | none => none
      | some e => some (e, off)

def mathCommand : Nat → Array Char → Nat → Option Font → String → Nat → Outcome
  | 0, _, _, _, _, _ => .failed
  | fuel + 1, s, depth, font, name, off =>
    match name with
    | "frac" => Outcome.ofOption (fraction fuel s depth font off)
    | "sqrt" => Outcome.ofOption (radical fuel s depth font off)
    | "left" => Outcome.ofOption (delimited fuel s depth font off)
    | "right" => .failed
    | "mathbf" => Outcome.ofOption (styled fuel s depth .bold off)
    | "mathit" => Outcome.ofOption (styled fuel s depth .italic off)
    | "mathrm" => Outcome.ofOption (styled fuel s depth .roman off)
    | "text" => Outcome.ofOption (textBody fuel s depth off)
    | _ => .unhandled

def fraction : Nat → Array Char → Nat → Option Font → Nat → Option (Expr × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, s, depth, font, off =>
    match argument fuel s depth font .math .group off with
    | none => none
    | some (numerator, o1) =>
      match argument fuel s depth font .math .group o1 with
      | none => none
      | some (denominator, o2) => some (Expr.fraction numerator denominator, o2)

def radical : Nat → Array Char → Nat → Option Font → Nat → Option (Expr × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, s, depth, font, off =>
    let off := skipWs s s.size off
    let indexed : Option (Option Expr × Nat) :=
      if s[off]? == some '[' then
        match nested depth with
        | none => none
        | some next =>
          match rowLoop fuel s .index next font .math (off + 1) [] with
          | none => none
          | some (ix, o) => some (some ix, o + 1)
      else some (none, off)
    match indexed with
    | none => none
    | some (index, o1) =>
      match argument fuel s depth font .math .group o1 with
      | none => none
      | some (radicand, o2) => some (Expr.radical index radicand, o2)

def delimited : Nat → Array Char → Nat → Option Font → Nat → Option (Expr × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, s, depth, font, off =>
    match nested depth with
    | none => none
    | some next =>
      match delimiter s off with
      | none => none
      | some (left, o1) =>
        match rowLoop fuel s .right next font .math o1 [] with
        | none => none
        | some (body, o2) =>
          match delimiter s (o2 + 6) with
          | none => none
          | some (right, o3) => some (Expr.delimited left body right, o3)

def styled : Nat → Array Char → Nat → Font → Nat → Option (Expr × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, s, depth, selected, off =>
    match argument fuel s depth (some selected) .math .group off with
    | none => none
    | some (body, o) => some (Expr.styled selected body, o)

def textBody : Nat → Array Char → Nat → Nat → Option (Expr × Nat)
  | 0, _, _, _ => none
  | fuel + 1, s, depth, off =>
    match argument fuel s depth (some .roman) .text .group off with
    | none => none
    | some (body, o) => some (Expr.text body, o)

end

/-- The parse of a formula source, `none` when any diagnostic would be raised. -/
def parse (formula : List Char) : Option Expr :=
  let s := formula.toArray
  match rowLoop (8 * s.size + 4096) s .end_ 0 none .math 0 [] with
  | some (e, _) => some e
  | none => none

/-! ### Box widths -/

structure Box where
  w : Int
  a : Int
  d : Int
deriving Repr, Inhabited

structure Consts where
  rule : Int
  axis : Int
  fracGap : Int
  supShift : Int
  subShift : Int
  scriptGap : Int
  radGap : Int
  radSignW : Int
  delimW : Int
  bigopGap : Int
  binopSpace : Int
  relopSpace : Int
  thin : Int
  medium : Int
  quad : Int
  scriptScale : Int
  bigopSize : Int

def roundHalfUp (a b : Int) : Int := Int.fdiv (2 * a + b) (2 * b)

def narrow (v : Int) : Except LayoutError Int :=
  if I32_MIN ≤ v ∧ v ≤ I32_MAX then .ok v else .error .overflow

def finish (w a d : Int) : Except LayoutError Box := do
  let w ← narrow w
  let a ← narrow a
  let d ← narrow d
  pure ⟨w, a, d⟩

def scaled (em : Int) (c : LayoutConst.Pair) : Int :=
  roundHalfUp (c.vector * em) 1000

def loadConsts (em : Int) : Consts :=
  ⟨max 1 (scaled em LayoutConst.math_rule), scaled em LayoutConst.math_axis,
    scaled em LayoutConst.math_frac_gap, scaled em LayoutConst.math_sup_shift,
    scaled em LayoutConst.math_sub_shift, scaled em LayoutConst.math_script_gap,
    scaled em LayoutConst.math_rad_gap, scaled em LayoutConst.math_rad_sign_w,
    scaled em LayoutConst.math_delim_w, scaled em LayoutConst.math_bigop_gap,
    scaled em LayoutConst.math_binop_space, scaled em LayoutConst.math_relop_space,
    scaled em LayoutConst.math_thin_space, scaled em LayoutConst.math_medium_space,
    scaled em LayoutConst.math_quad, LayoutConst.math_script_scale.vector,
    scaled em LayoutConst.math_bigop_scale⟩

def fontCodepoint (cp : Nat) : Nat :=
  match mathGlyphMappings.find? (fun r => r.codepoint == cp) with
  | some r => r.fontCodepoint
  | none => cp

def glyphBox (c : Char) (font : Font) (size : Int) : Except LayoutError Box := do
  let weight := if font == .bold then 1 else 0
  let upem ← Measure.upemOf weight
  let advance := Measure.advanceOf upem weight (fontCodepoint c.toNat)
  finish (Measure.ceilDiv ((advance : Int) * size) (upem : Int)) size 0

def horizontal (parts : List Box) (gaps : List Int) : Except LayoutError Box :=
  let cursor := (parts.zip gaps).foldl (fun acc q => acc + q.2 + q.1.w) 0
  let a := parts.foldl (fun acc p => max acc p.a) 0
  let d := parts.foldl (fun acc p => max acc p.d) 0
  finish cursor a d

def limitBox (size : Int) : Except LayoutError Box := do
  let l ← glyphBox 'l' .roman size
  let i ← glyphBox 'i' .roman size
  let m ← glyphBox 'm' .roman size
  horizontal [l, i, m] [0, 0, 0]

def spaceWidth (k : Consts) : Spacing → Int
  | .thin => k.thin
  | .medium => k.medium
  | .quad => k.quad

def symbolSpace (k : Consts) : SymClass → Int
  | .binary => k.binopSpace
  | .relation => k.relopSpace
  | _ => 0

def sideSpace (k : Consts) : Expr → Int
  | .symbol _ cls _ => symbolSpace k cls
  | .scripts base _ _ => sideSpace k base
  | _ => 0

def rowGaps : List Int → List Int
  | [] => []
  | sides => 0 :: (sides.zip sides.tail).map (fun q => q.1 + q.2)

def scriptSize (k : Consts) (size : Int) : Int := roundHalfUp (k.scriptScale * size) 1000

def isBigOp : SymClass → Bool
  | .sum => true
  | .product => true
  | .integral => true
  | _ => false

def symbolBox (c : Char) (cls : SymClass) (font : Font) (k : Consts) (size : Int) :
    Except LayoutError Box :=
  glyphBox c font (if isBigOp cls then k.bigopSize else size)

structure Script where
  box : Box
  base : Int

def attach (k : Consts) (base : Box) (scripts : List Script) : Except LayoutError Box :=
  let width := scripts.foldl (fun acc s => max acc s.box.w) 0
  let ascent := scripts.foldl (fun acc s => max acc (s.base + s.box.a)) base.a
  let descent := scripts.foldl (fun acc s => max acc (s.box.d - s.base)) base.d
  finish (base.w + k.scriptGap + width) ascent descent

def stack (base : Box) (limits : List Script) : Except LayoutError Box :=
  let width := limits.foldl (fun acc s => max acc s.box.w) base.w
  let ascent := limits.foldl (fun acc s => max acc (s.base + s.box.a)) base.a
  let descent := limits.foldl (fun acc s => max acc (s.box.d - s.base)) base.d
  finish width ascent descent

def delimiterBox (k : Consts) (d : Delim) (height : Int) (body : Box) :
    Except LayoutError Box :=
  if d == .invisible then pure ⟨0, 0, 0⟩
  else
    let extra := height - body.a - body.d
    let ascent := body.a + roundHalfUp extra 2
    finish k.delimW ascent (height - ascent)

def fuelLimit : Nat := 4096

def optBox (go : Expr → Int → Except LayoutError Box) :
    Option Expr → Int → Except LayoutError (Option Box)
  | none, _ => pure none
  | some e, size => do
    let b ← go e size
    pure (some b)

def bigopLimitsWith (k : Consts) (go : Expr → Int → Except LayoutError Box) (glyph : Box)
    (sup sub : Option Expr) : Except LayoutError Box := do
  let size := scriptSize k k.bigopSize
  let above ← optBox go sup size
  let below ← optBox go sub size
  let up := above.toList.map fun a => Script.mk a (glyph.a + k.bigopGap + a.d)
  let down := below.toList.map fun b => Script.mk b (-(k.bigopGap + b.a))
  stack glyph (up ++ down)

def limitScriptsWith (k : Consts) (go : Expr → Int → Except LayoutError Box) (b : Expr)
    (sup sub : Option Expr) (size : Int) : Except LayoutError Box := do
  let base ← go b size
  let parts ← ([sup, sub].filterMap id).mapM fun x => go x (scriptSize k size)
  let row ← horizontal parts (0 :: parts.tail.map fun _ => k.scriptGap)
  stack base [Script.mk row (-(k.bigopGap + row.a))]

def rightScriptsWith (k : Consts) (go : Expr → Int → Except LayoutError Box) (b : Expr)
    (sup sub : Option Expr) (baseSize : Int) : Except LayoutError Box := do
  let base ← go b baseSize
  let sizeS := scriptSize k baseSize
  let supBox ← optBox go sup sizeS
  let subBox ← optBox go sub sizeS
  let subBase := match supBox, subBox with
    | some su, some sb => min (-k.subShift) (k.supShift - su.d - sb.a)
    | _, _ => -k.subShift
  let up := supBox.toList.map fun su => Script.mk su k.supShift
  let down := subBox.toList.map fun sb => Script.mk sb subBase
  attach k base (up ++ down)

def box (k : Consts) (em : Int) : Nat → Expr → Int → Except LayoutError Box
  | 0, _, _ => .error .overflow
  | n + 1, e, size =>
    match e with
    | .row cs => do
      let parts ← cs.mapM (fun c => box k em n c size)
      horizontal parts (rowGaps (cs.map (sideSpace k)))
    | .group b => box k em n b size
    | .styled _ b => box k em n b size
    | .text b => box k em n b size
    | .space s => finish (spaceWidth k s) 0 0
    | .glyph c f => glyphBox c f size
    | .limit _ => limitBox size
    | .symbol c cls f => symbolBox c cls f k size
    | .fraction nu de => do
      let numerator ← box k em n nu size
      let denominator ← box k em n de size
      let width := max numerator.w denominator.w + 2 * k.scriptGap
      let barBottom := k.axis - Int.fdiv k.rule 2
      let barTop := barBottom + k.rule
      let numeratorBase := barTop + k.fracGap + numerator.d
      let denominatorBase := barBottom - k.fracGap - denominator.a
      finish width (numeratorBase + numerator.a) (denominator.d - denominatorBase)
    | .scripts b sup sub =>
      let go := fun x s => box k em n x s
      match b with
      | .symbol c cls f =>
        if cls == .sum || cls == .product then
          (symbolBox c cls f k em).bind fun glyph => bigopLimitsWith k go glyph sup sub
        else rightScriptsWith k go b sup sub (if cls == .integral then k.bigopSize else size)
      | .limit _ => limitScriptsWith k go b sup sub size
      | _ => rightScriptsWith k go b sup sub size
    | .radical index radicand => do
      let rad ← box k em n radicand size
      let ix ← optBox (fun x s => box k em n x s) index (scriptSize k size)
      let ixBox : Box := ix.getD ⟨0, 0, 0⟩
      let signX := if ix.isSome then ixBox.w + k.scriptGap else 0
      let ascent := max (rad.a + k.radGap) (k.supShift + ixBox.a)
      let descent := max (max rad.d (ixBox.d - k.supShift)) 0
      finish (signX + k.radSignW + rad.w) ascent descent
    | .delimited left body right => do
      let bodyBox ← box k em n body size
      let height := max (bodyBox.a + bodyBox.d) em
      let lb ← delimiterBox k left height bodyBox
      let rb ← delimiterBox k right height bodyBox
      let ascent := max bodyBox.a (max lb.a rb.a)
      let descent := max bodyBox.d (max lb.d rb.d)
      finish (lb.w + bodyBox.w + rb.w) ascent descent

/-- The width of the box of a parsed formula at `sizePx`, or `none` when the formula has a
diagnostic. A layout failure is an error, as in Go. -/
def width? (formula : List Char) (sizePx : Int) : Except LayoutError (Option Int) :=
  match parse formula with
  | none => pure none
  | some e =>
    if sizePx < 0 then .error .domain
    else do
      let em := sizePx * 64
      let k := loadConsts em
      let b ← box k em fuelLimit e em
      pure (some b.w)

end Formula
end Elegant
