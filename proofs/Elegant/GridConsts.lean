import Elegant.Model
import Elegant.Gen.Layoutconst

set_option autoImplicit false

/-! The constants of the grid family's block kind (`spec/layout/grid.md`, grid-05 and grid-66),
read from the generated `LayoutConst` definitions, and their values under both profiles. -/

namespace Elegant
namespace Grid

structure BlockConsts where
  padding : Int
  bendCost : Int
  lineThickness : Int
  lineHeight : Int
  cornerRadius : Int
  deriving DecidableEq, Repr

def BlockConsts.load (profile : Profile) : Except LayoutError BlockConsts :=
  .ok {
    padding := LayoutConst.block_padding.get profile
    bendCost := LayoutConst.block_bend_cost.get profile
    lineThickness := LayoutConst.block_line_thickness.get profile
    lineHeight := LayoutConst.line_h.get profile
    cornerRadius := LayoutConst.corner_radius.get profile }

/-- The signs of the constants that the theorems read. -/
structure BlockConsts.Pos (c : BlockConsts) : Prop where
  padding : 0 ≤ c.padding
  bendCost : 0 ≤ c.bendCost
  lineThickness : 0 ≤ c.lineThickness
  lineHeight : 0 ≤ c.lineHeight

theorem load_vector : BlockConsts.load .vector = .ok ⟨512, 4096, 0, 1280, 512⟩ := by
  rfl

theorem load_cell : BlockConsts.load .cell = .ok ⟨1, 4, 1, 1, 0⟩ := by
  rfl

theorem load_pos {p : Profile} {c : BlockConsts} (h : BlockConsts.load p = .ok c) : c.Pos := by
  cases p with
  | vector =>
    rw [load_vector] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide⟩
  | cell =>
    rw [load_cell] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide⟩

end Grid
end Elegant
