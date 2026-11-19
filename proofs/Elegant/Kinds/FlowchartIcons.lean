import Elegant.Model
import Elegant.Scene

set_option autoImplicit false

/-! Flowchart icon drawing (spec/library-surface.md, library-surface-48 to library-surface-57).

The lean-parity gate passes no icon packs, so every icon node draws the built-in `unknown` icon:
one `symbolRef` with style `ink` at the top-centre cell of the node in the cell profile, and one
`ink` path, the Inter question-mark outline in a 1536-unit box centred on the top edge of the
node, in the vector profile. The items are inserted into the node group before its first marker,
symbol, or text item. -/

namespace Elegant
namespace Kinds
namespace Flowchart

def iconBoxUnits : Int := 1536

def iconBoxHalf : Int := 768

def glyphUnitsPerEm : Int := 2048

/-- One outline command of the Inter question mark: opcode 0 move, 1 line, 2 quadratic; the
quadratic reads both coordinate pairs, the others only the first. -/
structure GlyphCommand where
  op : Nat
  x1 : Int
  y1 : Int
  x2 : Int := 0
  y2 : Int := 0

def unknownGlyph : List GlyphCommand :=
  [⟨0, 383, 449, 0, 0⟩, ⟨1, 383, 460, 0, 0⟩, ⟨2, 383, 597, 409, 671⟩, ⟨2, 436, 746, 486, 789⟩,
   ⟨2, 536, 833, 605, 874⟩, ⟨2, 671, 914, 716, 975⟩, ⟨2, 761, 1037, 761, 1124⟩,
   ⟨2, 761, 1228, 690, 1289⟩, ⟨2, 619, 1351, 518, 1351⟩, ⟨2, 430, 1351, 355, 1295⟩,
   ⟨2, 280, 1240, 272, 1115⟩, ⟨1, 82, 1115, 0, 0⟩, ⟨2, 87, 1241, 146, 1329⟩,
   ⟨2, 206, 1417, 303, 1463⟩, ⟨2, 400, 1510, 518, 1510⟩, ⟨2, 648, 1510, 743, 1459⟩,
   ⟨2, 839, 1409, 892, 1320⟩, ⟨2, 945, 1231, 945, 1117⟩, ⟨2, 945, 996, 892, 910⟩,
   ⟨2, 839, 824, 742, 765⟩, ⟨2, 678, 726, 638, 689⟩, ⟨2, 599, 653, 581, 601⟩,
   ⟨2, 564, 549, 564, 460⟩, ⟨1, 564, 449, 0, 0⟩, ⟨1, 383, 449, 0, 0⟩, ⟨0, 476, -13, 0, 0⟩,
   ⟨2, 420, -13, 380, 26⟩, ⟨2, 341, 66, 341, 121⟩, ⟨2, 341, 177, 380, 216⟩,
   ⟨2, 420, 256, 476, 256⟩, ⟨2, 532, 256, 571, 216⟩, ⟨2, 610, 177, 610, 121⟩,
   ⟨2, 610, 66, 571, 26⟩, ⟨2, 532, -13, 476, -13⟩]

def scaleGlyph (v : Int) : Int :=
  Int.fdiv (2 * v * iconBoxUnits + glyphUnitsPerEm) (2 * glyphUnitsPerEm)

def glyphPoints (c : GlyphCommand) : List Point :=
  let first : Point := ⟨scaleGlyph c.x1, -scaleGlyph c.y1⟩
  if c.op == 2 then [first, ⟨scaleGlyph c.x2, -scaleGlyph c.y2⟩] else [first]

def allGlyphPoints : List Point := unknownGlyph.flatMap glyphPoints

def glyphMinX : Int := allGlyphPoints.foldl (fun m p => min m p.x) 0x10000000000

def glyphMaxX : Int := allGlyphPoints.foldl (fun m p => max m p.x) (-0x10000000000)

def glyphMinY : Int := allGlyphPoints.foldl (fun m p => min m p.y) 0x10000000000

def glyphMaxY : Int := allGlyphPoints.foldl (fun m p => max m p.y) (-0x10000000000)

def third (a c : Int) : Int := Int.fdiv (2 * (a + 2 * c) + 3) 6

def quadToCubic (from_ control to : Point) : PathCommand :=
  .C ⟨third from_.x control.x, third from_.y control.y⟩
    ⟨third to.x control.x, third to.y control.y⟩ to

def glyphStep (shift : Point) (state : List PathCommand × Point) (c : GlyphCommand) :
    List PathCommand × Point :=
  let points := (glyphPoints c).map fun p => (⟨p.x + shift.x, p.y + shift.y⟩ : Point)
  let first := points.headD ⟨0, 0⟩
  let last := points.getLastD ⟨0, 0⟩
  let out := state.1
  let out := if c.op == 0 ∧ out ≠ [] then out ++ [.Z] else out
  let command : PathCommand :=
    if c.op == 0 then .M first
    else if c.op == 1 then .L first
    else quadToCubic state.2 first last
  (out ++ [command], last)

def unknownGlyphPath (origin : Point) : Primitive :=
  let shift : Point :=
    ⟨origin.x + Int.fdiv (iconBoxUnits - (glyphMaxX - glyphMinX)) 2 - glyphMinX,
     origin.y + Int.fdiv (iconBoxUnits - (glyphMaxY - glyphMinY)) 2 - glyphMinY⟩
  let result := unknownGlyph.foldl (glyphStep shift) ([], (⟨0, 0⟩ : Point))
  .path (result.1 ++ [.Z]) { style := "ink" }

def iconOrigin (profile : Profile) (r : Rect) : Point :=
  match profile with
  | .cell => ⟨r.x + Int.fdiv r.w 2, r.y⟩
  | .vector => ⟨r.x + Int.fdiv r.w 2 - iconBoxHalf, r.y - iconBoxHalf⟩

def iconItems (profile : Profile) (origin : Point) : List Primitive :=
  match profile with
  | .cell => [.symbolRef "unknown" origin "ink"]
  | .vector => [unknownGlyphPath origin]

def isOverlay : Primitive → Bool
  | .markerRef _ _ _ => true
  | .symbolRef _ _ _ => true
  | .text _ => true
  | _ => false

def overlayStart (items : List Primitive) : Nat :=
  (items.takeWhile fun p => !isOverlay p).length

def insertIcon (items extra : List Primitive) : List Primitive :=
  items.take (overlayStart items) ++ extra ++ items.drop (overlayStart items)

theorem insertIcon_perm (items extra : List Primitive) :
    (insertIcon items extra).Perm (items ++ extra) := by
  unfold insertIcon
  have h := List.take_append_drop (overlayStart items) items
  calc (items.take (overlayStart items) ++ extra ++ items.drop (overlayStart items)).Perm
        (items.take (overlayStart items) ++ items.drop (overlayStart items) ++ extra) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
    _ = items ++ extra := by rw [h]

def placeIcon (s : Scene) (box : ModelBox) (groups : List Group) : List Group :=
  match s.boxes.find? (fun b => b.id == box.id) with
  | none => groups
  | some placed =>
    groups.map fun g =>
      if g.role = .node ∧ g.owner = box.id then
        { g with items := insertIcon g.items (iconItems s.profile (iconOrigin s.profile placed.rect)) }
      else g

def placeIcons (m : Model) (s : Scene) : Scene :=
  if m.kind == "flowchart" then
    { s with items := m.boxes.foldl (fun groups box =>
        if box.icon then placeIcon s box groups else groups) s.items }
  else s

theorem placeIcons_layoutDump (m : Model) (s : Scene) :
    (placeIcons m s).layoutDump = s.layoutDump := by
  unfold placeIcons
  split <;> rfl

theorem placeIcons_profile (m : Model) (s : Scene) : (placeIcons m s).profile = s.profile := by
  unfold placeIcons
  split <;> rfl

theorem placeIcons_other_kind (m : Model) (s : Scene) (h : (m.kind == "flowchart") = false) :
    placeIcons m s = s := by
  simp [placeIcons, h]

end Flowchart
end Kinds
end Elegant
