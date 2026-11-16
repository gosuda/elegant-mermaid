import Elegant.Model
import Elegant.Gen.Layoutconst

set_option autoImplicit false

/-! The constants of the lanes family (`spec/layout/lanes.md`, lanes-05 and lanes-44), read from
the generated `LayoutConst` definitions, and their values under both profiles. -/

namespace Elegant
namespace Lanes

structure GitConsts where
  commitStep : Int
  lanePitch : Int
  rotationExtra : Int
  labelOffset : Int
  commitRadius : Int
  tagOffset : Int
  tagPad : Int
  labelGap : Int
  branchPadX : Int
  branchPadY : Int
  cornerRadius : Int
  canvasMargin : Int
  lineHeight : Int
  deriving DecidableEq, Repr

def GitConsts.load (profile : Profile) : Except LayoutError GitConsts :=
  .ok {
    commitStep := LayoutConst.gitgraph_commit_step.get profile
    lanePitch := LayoutConst.gitgraph_lane_pitch.get profile
    rotationExtra := LayoutConst.gitgraph_label_rotation_extra.get profile
    labelOffset := LayoutConst.gitgraph_label_offset.get profile
    commitRadius := LayoutConst.gitgraph_commit_radius.get profile
    tagOffset := LayoutConst.gitgraph_tag_offset.get profile
    tagPad := LayoutConst.gitgraph_tag_pad.get profile
    labelGap := LayoutConst.gitgraph_label_gap.get profile
    branchPadX := LayoutConst.gitgraph_branch_pad_x.get profile
    branchPadY := LayoutConst.gitgraph_branch_pad_y.get profile
    cornerRadius := LayoutConst.corner_radius.get profile
    canvasMargin := LayoutConst.canvas_margin.get profile
    lineHeight := LayoutConst.line_h.get profile }

/-- The signs of the constants that the theorems read. -/
structure GitConsts.Pos (c : GitConsts) : Prop where
  commitStep : 0 < c.commitStep
  lanePitch : 0 ≤ c.lanePitch
  rotationExtra : 0 ≤ c.rotationExtra
  labelOffset : 0 ≤ c.labelOffset
  commitRadius : 0 ≤ c.commitRadius
  tagOffset : 0 ≤ c.tagOffset
  tagPad : 0 ≤ c.tagPad
  labelGap : 0 ≤ c.labelGap
  branchPadX : 0 ≤ c.branchPadX
  branchPadY : 0 ≤ c.branchPadY
  cornerRadius : 0 ≤ c.cornerRadius
  canvasMargin : 0 ≤ c.canvasMargin
  lineHeight : 0 ≤ c.lineHeight

theorem load_vector : GitConsts.load .vector = .ok
    ⟨2560, 3200, 2560, 640, 512, 1024, 256, 1536, 768, 512, 512, 1024, 1280⟩ := by
  rfl

theorem load_cell : GitConsts.load .cell = .ok
    ⟨4, 2, 0, 1, 1, 0, 0, 2, 0, 0, 0, 1, 1⟩ := by
  rfl

theorem load_pos {p : Profile} {c : GitConsts} (h : GitConsts.load p = .ok c) : c.Pos := by
  cases p with
  | vector =>
    rw [load_vector] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩
  | cell =>
    rw [load_cell] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩

structure TimelineConsts where
  cardWidth : Int
  columnGap : Int
  eventGap : Int
  sectionGap : Int
  cardPadding : Int
  leftMargin : Int
  cornerRadius : Int
  canvasMargin : Int
  deriving DecidableEq, Repr

def TimelineConsts.load (profile : Profile) : TimelineConsts :=
  { cardWidth := LayoutConst.timeline_card_width.get profile
    columnGap := LayoutConst.timeline_column_gap.get profile
    eventGap := LayoutConst.timeline_event_gap.get profile
    sectionGap := LayoutConst.timeline_section_gap.get profile
    cardPadding := LayoutConst.timeline_card_padding.get profile
    leftMargin := LayoutConst.timeline_left_margin.get profile
    cornerRadius := LayoutConst.corner_radius.get profile
    canvasMargin := LayoutConst.canvas_margin.get profile }

theorem timeline_constants_positive (p : Profile) :
    0 < (TimelineConsts.load p).cardWidth ∧
    0 < (TimelineConsts.load p).columnGap ∧
    0 < (TimelineConsts.load p).eventGap ∧
    0 < (TimelineConsts.load p).sectionGap ∧
    0 ≤ (TimelineConsts.load p).cardPadding ∧
    0 ≤ (TimelineConsts.load p).canvasMargin := by
  cases p <;> decide

structure EventConsts where
  laneMinHeight : Int
  lanePadding : Int
  laneGap : Int
  boxPadding : Int
  boxOverlap : Int
  boxMinWidth : Int
  boxMaxWidth : Int
  boxMinHeight : Int
  boxMaxHeight : Int
  contentStartX : Int
  cornerRadius : Int
  canvasMargin : Int
  lineHeight : Int
  deriving DecidableEq, Repr

def EventConsts.load (profile : Profile) : EventConsts :=
  { laneMinHeight := LayoutConst.eventmodeling_swimlane_min_height.get profile
    lanePadding := LayoutConst.eventmodeling_swimlane_padding.get profile
    laneGap := LayoutConst.eventmodeling_swimlane_gap.get profile
    boxPadding := LayoutConst.eventmodeling_box_padding.get profile
    boxOverlap := LayoutConst.eventmodeling_box_overlap.get profile
    boxMinWidth := LayoutConst.eventmodeling_box_min_width.get profile
    boxMaxWidth := LayoutConst.eventmodeling_box_max_width.get profile
    boxMinHeight := LayoutConst.eventmodeling_box_min_height.get profile
    boxMaxHeight := LayoutConst.eventmodeling_box_max_height.get profile
    contentStartX := LayoutConst.eventmodeling_content_start_x.get profile
    lineHeight := LayoutConst.line_h.get profile
    cornerRadius := LayoutConst.corner_radius.get profile
    canvasMargin := LayoutConst.canvas_margin.get profile }

theorem event_constants_positive (p : Profile) :
    0 < (EventConsts.load p).laneMinHeight ∧
    0 ≤ (EventConsts.load p).lanePadding ∧
    0 < (EventConsts.load p).laneGap ∧
    0 < (EventConsts.load p).boxPadding ∧
    (EventConsts.load p).boxOverlap <
      (EventConsts.load p).boxMinWidth + 3 * (EventConsts.load p).boxPadding ∧
    0 ≤ (EventConsts.load p).boxMinHeight := by
  cases p <;> decide

end Lanes
end Elegant
