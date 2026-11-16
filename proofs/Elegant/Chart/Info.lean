
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

theorem measured_line_width_le (cell : Bool) (text : String) (role : Measure.Role)
    (size : Int) (box : XY.TextBox)
    (h : XY.measureText cell text role size = .ok box) :
    ∀ line ∈ box.lines, line.width ≤ box.w := by
  cases hm : XY.metricOf cell role size with
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

theorem layout_measured_line_width_le (profile : Profile) (text : String) (r : Result)
    (h : layout profile text = .ok r) :
    ∀ line ∈ r.box.lines, line.width ≤ r.rect.w := by
  unfold layout at h
  cases hm : XY.measureText (profile == .cell) text .title
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

theorem layout_lines_in_canvas (profile : Profile) (text : String) (r : Result)
    (h : layout profile text = .ok r) :
    Rect.Contained ⟨0, 0, r.canvas.w, r.canvas.h⟩ r.rect := by
  unfold layout at h
  cases hm : XY.measureText (profile == .cell) text .title
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
