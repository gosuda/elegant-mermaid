import Elegant.Gen.Glyphjoin
import Elegant.Gen.Cellsymbols
import Elegant.Text.Canvas

set_option autoImplicit false

/-! Glyph join of the text back end (`spec/render-cells.md`, requirements render-cells-05,
render-cells-12 to render-cells-19 and render-cells-88). The tables come from
`Elegant.Gen.Glyphjoin` and `Elegant.Gen.Cellsymbols`. -/

namespace Elegant.Text

/-- The glyph repertoire. -/
inductive Charset where
  | unicode
  | ascii
  deriving DecidableEq, Repr

/-- The charset code of the generated `glyphjoin` table. -/
def Charset.code : Charset → Nat
  | .unicode => 0
  | .ascii => 1

namespace Join

/-- The rune of the row with the given key, if the table has one. -/
def lookup (charset style mask : Nat) : Option Nat :=
  (glyphjoin.find? fun g => g.charset == charset && g.style == style && g.mask == mask).map
    (·.rune)

/-- The glyph of a line style and an arm mask. The mask is reduced to its four bits.
Unicode reads its own style; ASCII ignores style except `dotted`. A key without a row
prints as U+0020. -/
def glyph (charset : Charset) (style mask : Nat) : Nat :=
  let m := mask &&& 15
  match charset with
  | .unicode => (lookup charset.code style m).getD 32
  | .ascii => (lookup charset.code (if style == styleDotted then 1 else 0) m).getD 32

/-- The code point of a symbol name in a charset. -/
def symbol (charset : Charset) (name : String) : Option Nat :=
  (cellsymbols.find? fun s => s.name == name).map fun s =>
    match charset with
    | .unicode => s.unicode
    | .ascii => s.ascii

/-- The arm mask of each printed box-drawing glyph, written from the Unicode character
names and independent of the generated table. -/
def armTable : List (Nat × Nat) :=
  [ (0x20, 0)
  , (0x2575, bitN), (0x2576, bitE), (0x2577, bitS), (0x2574, bitW)
  , (0x2514, bitN ||| bitE), (0x2502, bitN ||| bitS), (0x250C, bitE ||| bitS)
  , (0x251C, bitN ||| bitE ||| bitS), (0x2518, bitN ||| bitW), (0x2500, bitE ||| bitW)
  , (0x2534, bitN ||| bitE ||| bitW), (0x2510, bitS ||| bitW)
  , (0x2524, bitN ||| bitS ||| bitW), (0x252C, bitE ||| bitS ||| bitW)
  , (0x253C, bitN ||| bitE ||| bitS ||| bitW)
  , (0x2579, bitN), (0x257A, bitE), (0x257B, bitS), (0x2578, bitW)
  , (0x2517, bitN ||| bitE), (0x2503, bitN ||| bitS), (0x250F, bitE ||| bitS)
  , (0x2523, bitN ||| bitE ||| bitS), (0x251B, bitN ||| bitW), (0x2501, bitE ||| bitW)
  , (0x253B, bitN ||| bitE ||| bitW), (0x2513, bitS ||| bitW)
  , (0x252B, bitN ||| bitS ||| bitW), (0x2533, bitE ||| bitS ||| bitW)
  , (0x254B, bitN ||| bitE ||| bitS ||| bitW)
  , (0x255A, bitN ||| bitE), (0x2551, bitN ||| bitS), (0x2554, bitE ||| bitS)
  , (0x2560, bitN ||| bitE ||| bitS), (0x255D, bitN ||| bitW), (0x2550, bitE ||| bitW)
  , (0x2569, bitN ||| bitE ||| bitW), (0x2557, bitS ||| bitW)
  , (0x2563, bitN ||| bitS ||| bitW), (0x2566, bitE ||| bitS ||| bitW)
  , (0x256C, bitN ||| bitE ||| bitS ||| bitW)
  , (0x2570, bitN ||| bitE), (0x256D, bitE ||| bitS), (0x256F, bitN ||| bitW)
  , (0x256E, bitS ||| bitW)
  , (0x2506, bitN ||| bitS), (0x2504, bitE ||| bitW) ]

/-- The arms of a printed glyph, from its code point; an unknown code point has no arms. -/
def arms (rune : Nat) : Nat :=
  (armTable.lookup rune).getD 0

set_option maxRecDepth 100000 in
/-- In every unicode line style the printed glyph has exactly the arms of its mask. -/
theorem join_glyph_matches_mask :
    ∀ mask, mask < 16 →
      ∀ style ∈ [styleLight, styleHeavy, styleDouble, styleRounded, styleDotted],
        arms (glyph .unicode style mask) = mask := by
  decide

end Join

end Elegant.Text
