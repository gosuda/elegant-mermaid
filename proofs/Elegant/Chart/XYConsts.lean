import Elegant.Model
import Elegant.Gen.Layoutconst

set_option autoImplicit false

/-! The constants of the xychart family (`spec/layout/charts.md`, charts-39 to charts-43), read
from the generated `LayoutConst` definitions, and their values under both profiles. -/

namespace Elegant
namespace Chart

structure XYConsts where
  width : Int
  height : Int
  reserved : Int
  barPad : Int
  barRatio : Int
  outerMax : Int
  axisLine : Int
  axisTitlePad : Int
  padX : Int
  padY : Int
  tickLen : Int
  titlePad : Int
  legendPad : Int
  legendMarker : Int
  markerGap : Int
  itemGap : Int
  pointOffset : Int
  pointSize : Int
  edge : Int
  deriving DecidableEq, Repr

def XYConsts.load (profile : Profile) : Except LayoutError XYConsts :=
  .ok {
    width := LayoutConst.xychart_width.get profile
    height := LayoutConst.xychart_height.get profile
    reserved := LayoutConst.xychart_plot_reserved_percent.get profile
    barPad := LayoutConst.xychart_bar_padding_m.get profile
    barRatio := LayoutConst.xychart_bar_width_ratio_m.get profile
    outerMax := LayoutConst.xychart_label_outer_max_m.get profile
    axisLine := LayoutConst.xychart_axis_line.get profile
    axisTitlePad := LayoutConst.xychart_axis_title_pad.get profile
    padX := LayoutConst.xychart_label_pad_x.get profile
    padY := LayoutConst.xychart_label_pad_y.get profile
    tickLen := LayoutConst.xychart_tick_length.get profile
    titlePad := LayoutConst.xychart_title_pad.get profile
    legendPad := LayoutConst.xychart_legend_pad.get profile
    legendMarker := LayoutConst.xychart_legend_marker.get profile
    markerGap := LayoutConst.xychart_legend_marker_gap.get profile
    itemGap := LayoutConst.xychart_legend_item_gap.get profile
    pointOffset := LayoutConst.xychart_point_label_offset.get profile
    pointSize := LayoutConst.xychart_point_label_size.get profile
    edge := match profile with | .cell => 1 | .vector => 0 }

/-- The signs and bounds of the constants that the theorems read. -/
structure XYConsts.Pos (c : XYConsts) : Prop where
  width : 0 < c.width
  height : 0 < c.height
  barPad : c.barPad = 50
  barRatio : c.barRatio = 700
  outerMax : c.outerMax = 200
  axisLine : 0 ≤ c.axisLine
  axisTitlePad : 0 ≤ c.axisTitlePad
  padX : 0 ≤ c.padX
  padY : 0 ≤ c.padY
  tickLen : 0 ≤ c.tickLen
  titlePad : 0 ≤ c.titlePad
  legendPad : 0 ≤ c.legendPad
  legendMarker : 0 ≤ c.legendMarker
  markerGap : 0 ≤ c.markerGap
  itemGap : 0 ≤ c.itemGap
  pointSize : 0 ≤ c.pointSize
  edge : 0 ≤ c.edge ∧ c.edge ≤ 1

theorem load_vector : XYConsts.load .vector = .ok
    ⟨44800, 32000, 50, 50, 700, 200, 128, 320, 320, 320, 320, 640, 640, 672, 314, 448, 640, 768, 0⟩ := by
  rfl

theorem load_cell : XYConsts.load .cell = .ok
    ⟨88, 32, 50, 50, 700, 200, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 768, 1⟩ := by
  rfl

theorem load_pos {p : Profile} {c : XYConsts} (h : XYConsts.load p = .ok c) : c.Pos := by
  cases p with
  | vector =>
    rw [load_vector] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩
  | cell =>
    rw [load_cell] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩

/-- The edge constant follows the profile. -/
theorem load_edge {p : Profile} {c : XYConsts} (h : XYConsts.load p = .ok c) :
    (p = .cell ∧ c.edge = 1) ∨ (p = .vector ∧ c.edge = 0) := by
  cases p with
  | vector => rw [load_vector] at h; cases h; exact Or.inr ⟨rfl, rfl⟩
  | cell => rw [load_cell] at h; cases h; exact Or.inl ⟨rfl, rfl⟩

/-- The default plot reserve is a percentage in the range that the model accepts. -/
theorem load_reserved {p : Profile} {c : XYConsts} (h : XYConsts.load p = .ok c) :
    30 ≤ c.reserved ∧ c.reserved ≤ 100 := by
  cases p with
  | vector => rw [load_vector] at h; cases h; exact ⟨by decide, by decide⟩
  | cell => rw [load_cell] at h; cases h; exact ⟨by decide, by decide⟩

end Chart
end Elegant
