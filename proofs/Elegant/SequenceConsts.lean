import Elegant.Model
import Elegant.Gen.Layoutconst

set_option autoImplicit false

/-! The constants of the sequence family (`spec/layout/sequence.md`, sequence-04 and sequence-05),
read from the generated `LayoutConst` definitions, and their values under both profiles. -/

namespace Elegant
namespace Sequence

structure Consts where
  actorWidth : Int
  actorHeight : Int
  actorMargin : Int
  wrapPadding : Int
  boxTextMargin : Int
  boxMargin : Int
  noteMargin : Int
  selfLoopMinDx : Int
  selfLoopDepth : Int
  messageTop : Int
  labelBoxHeight : Int
  labelBoxWidth : Int
  activationWidth : Int
  activationTop : Int
  diagramMarginX : Int
  diagramMarginY : Int
  cornerRadius : Int
  autonumberRadius : Int
  lineHeight : Int
  ruleRadius : Int
  deriving DecidableEq, Repr

def Consts.load (profile : Profile) : Except LayoutError Consts :=
  .ok {
    actorWidth := LayoutConst.sequence_actor_width.get profile
    actorHeight := LayoutConst.sequence_actor_height.get profile
    actorMargin := LayoutConst.sequence_actor_margin.get profile
    wrapPadding := LayoutConst.sequence_wrap_padding.get profile
    boxTextMargin := LayoutConst.sequence_box_text_margin.get profile
    boxMargin := LayoutConst.sequence_box_margin.get profile
    noteMargin := LayoutConst.sequence_note_margin.get profile
    selfLoopMinDx := LayoutConst.sequence_self_loop_min_dx.get profile
    selfLoopDepth := LayoutConst.sequence_self_loop_depth.get profile
    messageTop := LayoutConst.sequence_message_top.get profile
    labelBoxHeight := LayoutConst.sequence_label_box_height.get profile
    labelBoxWidth := LayoutConst.sequence_label_box_width.get profile
    activationWidth := LayoutConst.sequence_activation_width.get profile
    activationTop := LayoutConst.sequence_activation_top.get profile
    diagramMarginX := LayoutConst.sequence_diagram_margin_x.get profile
    diagramMarginY := LayoutConst.sequence_diagram_margin_y.get profile
    cornerRadius := LayoutConst.corner_radius.get profile
    autonumberRadius := LayoutConst.sequence_autonumber_radius.get profile
    lineHeight := match profile with | .vector => 1280 | .cell => 1
    ruleRadius := match profile with | .vector => 512 | .cell => 0 }

/-- `value >> 1` on a signed integer: the floor half. -/
def half (v : Int) : Int := Int.fdiv v 2

/-- The signs of the constants that the theorems read. -/
structure Consts.Pos (c : Consts) : Prop where
  margin : 0 < c.actorMargin
  boxMargin : 0 < c.boxMargin
  messageTop : 0 < c.messageTop
  boxTextMargin : 0 ≤ c.boxTextMargin
  labelBoxHeight : 0 ≤ c.labelBoxHeight
  lineHeight : 0 ≤ c.lineHeight
  noteMargin : 0 ≤ c.noteMargin
  activationTop : 0 ≤ c.activationTop
  selfLoopDepth : 0 ≤ c.selfLoopDepth
  wrapPadding : 0 ≤ c.wrapPadding
  actorWidth : 0 < c.actorWidth
  wrapPaddingPos : 0 < c.wrapPadding
  textMargin : c.boxTextMargin ≤ c.boxMargin
  diagramMarginX : 0 ≤ c.diagramMarginX
  diagramMarginY : 0 ≤ c.diagramMarginY
  boxTextMarginPos : 0 < c.boxTextMargin

theorem load_vector : Consts.load .vector = .ok
    ⟨9600, 4160, 3200, 640, 320, 640, 640, 1920, 1920, 640, 1280, 3200, 640, 128, 3200, 640, 512, 384,
      1280, 512⟩ := by
  rfl

theorem load_cell : Consts.load .cell = .ok
    ⟨12, 3, 4, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 0, 2, 1, 0, 1, 1, 0⟩ := by
  rfl

theorem load_pos {p : Profile} {c : Consts} (h : Consts.load p = .ok c) : c.Pos := by
  cases p with
  | vector =>
    rw [load_vector] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  | cell =>
    rw [load_cell] at h
    cases h
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The nested activation bars of the vector profile step right by a positive amount. -/
theorem vector_activation_step_pos {c : Consts} (h : Consts.load .vector = .ok c) :
    0 < half c.activationWidth := by
  rw [load_vector] at h
  cases h
  decide

end Sequence
end Elegant
