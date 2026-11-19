import Elegant.Chart.WardleyScene
import Elegant.Gen.Layoutconst

set_option autoImplicit false

namespace Elegant.Chart.Wardley

def configured (m : Model) (key : String) : Option Int :=
  match m.options.config.find? (fun entry => entry.1 == key) with
  | some (_, .integer n) => some n
  | some (_, .string s) => s.toInt?
  | _ => none

private def side (profile : Profile) (n divisor : Int) : Int :=
  if profile = .cell then Int.fdiv (n + divisor - 1) divisor else n * 64

def constants (m : Model) : Constants :=
  let p := m.profile
  let width := (configured m "width").map (fun n => side p n 8)
    |>.getD (LayoutConst.wardley_width.get p)
  let height := (configured m "height").map (fun n => side p n 16)
    |>.getD (LayoutConst.wardley_height.get p)
  let padX := (configured m "padding").map (fun n => side p n 8)
    |>.getD (LayoutConst.wardley_padding_x.get p)
  let padY := (configured m "padding").map (fun n => side p n 16)
    |>.getD (LayoutConst.wardley_padding_y.get p)
  let cell := p == .cell
  let fonts : FontConstants :=
    ⟨LayoutConst.wardley_label_size.get p, LayoutConst.wardley_axis_size.get p,
      LayoutConst.wardley_note_size.get p⟩
  let labels : LabelConstants :=
    { nodeRadius := LayoutConst.wardley_node_radius.get p
      labelGap := LayoutConst.wardley_label_gap.get p
      squareSize := LayoutConst.wardley_square_size.get p
      annotationRadius := LayoutConst.wardley_annotation_radius.get p
      boxPad := LayoutConst.wardley_box_pad.get p
      linkLabelGap := LayoutConst.wardley_link_label_gap.get p
      axisGap := LayoutConst.wardley_axis_gap.get p
      stageGap := LayoutConst.wardley_stage_gap.get p
      stageHeight := XY.lineHeight cell .label (Int.fdiv fonts.axisSize 64) }
  let edge := if cell then 1 else 0
  { geometry :=
      { width, height, padX, padY, edge
        arrowWidth := LayoutConst.wardley_arrow_width.get p
        arrowShaft := LayoutConst.wardley_arrow_shaft.get p
        arrowHead := LayoutConst.wardley_arrow_head.get p
        pipelinePad := LayoutConst.wardley_pipeline_pad.get p
        pipelineHeight := LayoutConst.wardley_pipeline_height.get p
        squareSize := LayoutConst.wardley_square_size.get p }
    labels, fonts
    paint :=
      { labels, edge
        inertiaGap := LayoutConst.wardley_inertia_gap.get p
        inertiaWidth := LayoutConst.wardley_inertia_width.get p
        marketRing := LayoutConst.wardley_market_ring.get p
        marketDot := LayoutConst.wardley_market_dot.get p
        arrowTip := LayoutConst.wardley_arrow_tip.get p
        arrowShaft := LayoutConst.wardley_arrow_shaft.get p
        arrowHead := LayoutConst.wardley_arrow_head.get p } }

theorem constants_padding_nonnegative (m : Model)
    (h : ∀ n, configured m "padding" = some n → 0 ≤ n) :
    0 ≤ (constants m).geometry.padX ∧ 0 ≤ (constants m).geometry.padY := by
  cases hp : configured m "padding" with
  | none =>
      cases hprofile : m.profile <;>
        simp [constants, hp, hprofile, LayoutConst.Pair.get,
          LayoutConst.wardley_padding_x, LayoutConst.wardley_padding_y]
  | some n =>
      have hn := h n hp
      cases hprofile : m.profile
      · simp [constants, hp, hprofile, side]
        omega
      · have hy := fdiv_mono (D := 16) (t := 0) (t' := n + 15) (by decide) (by omega)
        have hx' := fdiv_mono (D := 8) (t := 0) (t' := n + 7) (by decide) (by omega)
        simp [constants, hp, hprofile, side]
        rw [show n + 8 - 1 = n + 7 by omega, show n + 16 - 1 = n + 15 by omega]
        change 0 ≤ Int.fdiv (n + 15) 16 at hy
        change 0 ≤ Int.fdiv (n + 7) 8 at hx'
        exact ⟨hx', hy⟩

end Elegant.Chart.Wardley
