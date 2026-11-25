import Elegant.Chart.XY

set_option autoImplicit false

namespace Elegant.Chart.Info

open Validator

structure Result where
  box : XY.TextBox
  rect : Rect
  canvas : Size
  size : Int

def arrange (width height textX textY : Int) (box : XY.TextBox) (size : Int) : Result :=
  let x := max 0 (textX - Int.fdiv box.w 2)
  let y := max 0 (textY - Int.fdiv box.h 2)
  ⟨box, ⟨x, y, box.w, box.h⟩, ⟨max width (x + box.w), max height (y + box.h)⟩, size⟩

def layout (profile : Profile) (text : String) (fontFamily : Bool := false) : Except LayoutError Result := do
  let size := Int.fdiv (LayoutConst.info_font_size.get profile) 64
  let box ← XY.measureText (profile == .cell) text .title size fontFamily
  let r := arrange (LayoutConst.info_width.get profile) (LayoutConst.info_height.get profile)
    (LayoutConst.info_text_x.get profile) (LayoutConst.info_text_y.get profile) box size
  if InI32 r.canvas.w ∧ InI32 r.canvas.h ∧ InI32 r.rect.x ∧ InI32 r.rect.y ∧
      InI32 r.rect.w ∧ InI32 r.rect.h then pure r else throw .overflow

def sceneOf (m : Model) (r : Result) : Scene :=
  let text := (m.labels.find? (fun l => l.id == "version")).map (·.text) |>.getD "v0.1.0"
  { kind := "info", profile := m.profile, options := { m.options with direction := .TB },
    canvas := r.canvas,
    boxes := [⟨"info", "node", ⟨0, 0, r.canvas.w, r.canvas.h⟩, "", false⟩],
    labels := [{
      id := "version"
      owner := "info"
      rect := r.rect
      text := text
      lines := r.box.lines.map (fun l => String.ofList l.text) }],
    items := [{ role := .node, owner := "info", items := [.text {
      rect := r.rect, role := .title, size := r.size, align := .middle, style := "text",
      lines := XY.runsOf r.box.lines }] }] }

theorem info_lines_in_canvas (width height textX textY : Int) (box : XY.TextBox) (size : Int) :
    let r := arrange width height textX textY box size
    Rect.Contained ⟨0, 0, r.canvas.w, r.canvas.h⟩ r.rect := by
  simp only [arrange, Rect.Contained, Int.zero_add]
  exact ⟨Int.le_max_left _ _, Int.le_max_right _ _, Int.le_max_left _ _, Int.le_max_right _ _⟩


theorem folded_width_ge_line (lines : List Measure.Line) (initial : Int)
    (line : Measure.Line) (hline : line ∈ lines) :
    line.width ≤ lines.foldl (fun w l => max w l.width) initial := by
  induction lines generalizing initial with
  | nil => simp at hline
  | cons first rest ih =>
    rcases List.mem_cons.mp hline with hfirst | hrest
    · subst line
      have hstart : max initial first.width ≤
          rest.foldl (fun w l => max w l.width) (max initial first.width) := by
        have monotone : ∀ (xs : List Measure.Line) (w : Int),
            w ≤ xs.foldl (fun v l => max v l.width) w := by
          intro xs
          induction xs with
          | nil => intro w; exact Int.le_refl _
          | cons x xs hx =>
            intro w
            exact Int.le_trans (Int.le_max_left _ _) (hx (max w x.width))
        exact monotone rest _
      exact Int.le_trans (Int.le_max_right _ _) hstart
    · exact ih (initial := max initial first.width) hrest

theorem measured_line_width_le {fontFamily : Bool} (cell : Bool) (text : String) (role : Measure.Role)
    (size : Int) (box : XY.TextBox)
    (h : XY.measureText cell text role size fontFamily = .ok box) :
    ∀ line ∈ box.lines, line.width ≤ box.w := by
  cases hm : XY.metricOf cell role size fontFamily with
  | error e => simp [XY.measureText, hm, Bind.bind, Except.bind] at h
  | ok metric =>
    cases hl : StyledMeasure.wrap metric I32_MAX text.toList with
    | error e => simp [XY.measureText, hm, hl, Bind.bind, Except.bind] at h
    | ok lines =>
      have he : (XY.TextBox.mk lines
          (lines.foldl (fun w l => max w l.width) 0)
          ((lines.length : Int) * XY.lineHeight cell role size)) = box := by
        simpa [XY.measureText, hm, hl, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using h
      cases he
      intro line hline
      exact folded_width_ge_line lines 0 line hline

theorem layout_measured_line_width_le {fontFamily : Bool} (profile : Profile) (text : String) (r : Result)
    (h : layout profile text fontFamily = .ok r) :
    ∀ line ∈ r.box.lines, line.width ≤ r.rect.w := by
  unfold layout at h
  cases hm : XY.measureText (fontFamily := fontFamily) (profile == .cell) text .title
      (Int.fdiv (LayoutConst.info_font_size.get profile) 64) with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok box =>
    simp only [hm, Bind.bind, Except.bind] at h
    split at h
    · have he : arrange (LayoutConst.info_width.get profile)
          (LayoutConst.info_height.get profile) (LayoutConst.info_text_x.get profile)
          (LayoutConst.info_text_y.get profile) box
          (Int.fdiv (LayoutConst.info_font_size.get profile) 64) = r := by
        simpa [Pure.pure, Except.pure] using h
      cases he
      exact measured_line_width_le (profile == .cell) text .title
        (Int.fdiv (LayoutConst.info_font_size.get profile) 64) box hm
    · cases h

theorem layout_lines_in_canvas {fontFamily : Bool} (profile : Profile) (text : String) (r : Result)
    (h : layout profile text fontFamily = .ok r) :
    Rect.Contained ⟨0, 0, r.canvas.w, r.canvas.h⟩ r.rect := by
  unfold layout at h
  cases hm : XY.measureText (fontFamily := fontFamily) (profile == .cell) text .title
      (Int.fdiv (LayoutConst.info_font_size.get profile) 64) with
  | error e =>
    simp [hm, Bind.bind, Except.bind] at h
  | ok box =>
    simp only [hm, Bind.bind, Except.bind] at h
    split at h
    · have he : arrange (LayoutConst.info_width.get profile)
          (LayoutConst.info_height.get profile) (LayoutConst.info_text_x.get profile)
          (LayoutConst.info_text_y.get profile) box
          (Int.fdiv (LayoutConst.info_font_size.get profile) 64) = r := by
        simpa [Pure.pure, Except.pure] using h
      cases he
      exact info_lines_in_canvas _ _ _ _ _ _
    · cases h

theorem info_valid (m : Model) (r : Result) :
    HardConstraints (sceneOf m r).layoutDump := by
  simp [HardConstraints, C1, C2, C3, C4, C5, C6, C7, C8, C8a, C8b,
    sceneOf, Scene.layoutDump, canvasRect, Rect.Contained]

end Elegant.Chart.Info
