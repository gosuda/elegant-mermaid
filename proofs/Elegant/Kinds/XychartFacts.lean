import Elegant.Kinds.Xychart
import Elegant.Chart.XYValid

set_option autoImplicit false

/-! The validity of the xychart layout (`spec/layout/charts.md`, charts-109): the layout dump of every
xychart satisfies the hard constraints of the validator. Every box is a non-exclusive `node`, the
chart has no routes, and the boxes form one frame: the plot box lies inside the canvas and every
other box lies inside the plot box and names it as its parent. -/

namespace Elegant
namespace Kinds
namespace Xychart

open Common Chart.XY

/-! ### The options that the family reads -/

/-- Two inputs agree on the options that the family reads. -/
abbrev SameOpts (a b : Input) : Prop :=
  a.width = b.width ∧ a.height = b.height ∧ a.reserved = b.reserved ∧ a.fontSize = b.fontSize

theorem decodeRegion_same (inp : Input) (r : List Int) : SameOpts (decodeRegion inp r) inp := by
  unfold decodeRegion
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem legendTitle_same (inp : Input) (index text : String) :
    SameOpts (legendTitle inp index text) inp := by
  unfold legendTitle
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem pointLabel_same (inp : Input) (id text : String) :
    SameOpts (pointLabel inp id text) inp := by
  unfold pointLabel
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem decodeLabel_same (inp : Input) (l : ModelLabel) : SameOpts (decodeLabel inp l) inp := by
  unfold decodeLabel
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl, rfl⟩
    | exact legendTitle_same _ _ _
    | exact pointLabel_same _ _ _

theorem foldl_same {α : Type} (f : Input → α → Input) (hf : ∀ i x, SameOpts (f i x) i) :
    ∀ (l : List α) (inp : Input), SameOpts (l.foldl f inp) inp := by
  intro l
  induction l with
  | nil => intro inp; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x xs ih =>
    intro inp
    have h1 := ih (f inp x)
    have h2 := hf inp x
    simp only [List.foldl_cons]
    exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem inRange_some {lo hi n : Int} {o : Option Int} (h : inRange lo hi o = true)
    (ho : o = some n) : lo ≤ n ∧ n ≤ hi := by
  subst ho
  simpa [inRange] using h

theorem decode_inputOk {m : Model} {inp : Input} (h : decode m = .ok inp) : InputOk inp := by
  unfold decode at h
  cases hb : configInRange m.options with
  | false =>
    simp only [hb, Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    have s1 := foldl_same decodeLabel (fun i x => decodeLabel_same i x) m.labels
      (m.regionSets.foldl (fun inp s => decodeRegion inp s.regions) (baseInput m.options))
    have s2 := foldl_same (fun inp (s : _) => decodeRegion inp s.regions)
      (fun i x => decodeRegion_same i _) m.regionSets (baseInput m.options)
    unfold configInRange at hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hw, hh⟩, hr⟩, hf⟩ := hb
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
    · rw [s1.1, s2.1] at hn
      exact (inRange_some hw hn).1
    · rw [s1.2.1, s2.2.1] at hn
      exact (inRange_some hh hn).1
    · rw [s1.2.2.1, s2.2.2.1] at hn
      exact inRange_some hr hn
    · rw [s1.2.2.2, s2.2.2.2] at hn
      have := (inRange_some hf hn).1
      omega

/-! ### The frame -/

/-- A layout dump whose boxes form one frame satisfies the hard constraints: the first box `b0`
lies inside the canvas, every other box lies inside it and names it as parent, no box is exclusive
or a group, and there are no routes. -/
theorem hard_of_frame {d : LayoutDump} {b0 : Box} {tail : List Box} {plot : Rect} {pid : String}
    (hb : d.boxes = b0 :: tail) (hid : b0.id = pid) (hr : b0.rect = plot) (hp : b0.parent = "")
    (hflags : ∀ b ∈ d.boxes, b.exclusive = false ∧ b.role = "node")
    (htail : ∀ b ∈ tail, b.parent = pid ∧ plot.Contained b.rect)
    (hroutes : d.routes = []) (hc : (Validator.canvasRect d).Contained plot) :
    HardConstraints d := by
  have hfind : d.box? pid = some b0 := by
    unfold LayoutDump.box?
    rw [hb]
    exact List.find?_cons_of_pos (by simp [hid])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb'
    rw [hb] at hb'
    rcases List.mem_cons.mp hb' with rfl | hb''
    · rw [hr]
      exact hc
    · exact Rect.Contained.trans hc (htail b hb'').2
  · intro b hb' c hc' _ hex _ _
    have := (hflags b hb').1
    rw [this] at hex
    cases hex
  · intro b hb' hne p hp'
    rw [hb] at hb'
    rcases List.mem_cons.mp hb' with rfl | hb''
    · exact absurd hp hne
    · have h1 := htail b hb''
      rw [h1.1, hfind] at hp'
      cases hp'
      rw [hr]
      exact h1.2
  · intro rt hrt
    rw [hroutes] at hrt
    cases hrt
  · intro rt hrt
    rw [hroutes] at hrt
    cases hrt
  · intro rt hrt
    rw [hroutes] at hrt
    cases hrt
  · intro l _ b hb' hex
    have := (hflags b hb').1
    rw [this] at hex
    cases hex
  · refine ⟨?_, ?_⟩
    · intro g hg hrole
      have := (hflags g hg).2
      rw [this] at hrole
      exact absurd hrole (by decide)
    · intro g hg hrole
      have := (hflags g hg).2
      rw [this] at hrole
      exact absurd hrole (by decide)

theorem layout_decompose {m : Model} {r : Layered.FamilyResult} (hl : layout m = .ok r) :
    ∃ (inp : Input) (res : Chart.XY.Result), decode m = .ok inp ∧
      Chart.XY.layout m.profile inp = .ok res ∧
      r.scene = (sceneOf m res).projectCellAttachments (routeMarkers m) := by
  unfold layout at hl
  cases hd : decode m with
  | error e =>
    simp only [hd] at hl
    cases hl
  | ok inp =>
    cases hr : Chart.XY.layout m.profile inp with
    | error e =>
      simp only [hd, hr] at hl
      cases hl
    | ok res =>
      simp only [hd, hr, Except.ok.injEq] at hl
      exact ⟨inp, res, rfl, hr, by rw [← hl]⟩

/-- Every xychart layout satisfies the hard constraints of the validator. -/
theorem layout_valid {m : Model} {r : Layered.FamilyResult} (hl : layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨inp, res, hd, hres, hs⟩ := layout_decompose hl
  obtain ⟨rest, plot, restRects, hb, hnp, hr, c1, c2, c3, c4, hcont⟩ :=
    layout_frame (decode_inputOk hd) hres
  rw [hs, Scene.projectCellAttachments_layoutDump]
  have hboxes : (sceneOf m res).layoutDump.boxes =
      dumpBox plotId plotBox plot ::
        (rest.zip restRects).map (fun (b, rect) => dumpBox plotId b rect) := by
    show (res.boxes.zip res.boxRects).map _ = _
    rw [hb, hr]
    rfl
  have hmem : ∀ b ∈ (rest.zip restRects).map (fun (b, rect) => dumpBox plotId b rect),
      ∃ s rect, s ∈ rest ∧ rect ∈ restRects ∧ b = dumpBox plotId s rect := by
    intro b hb'
    obtain ⟨⟨s, rect⟩, hq, rfl⟩ := List.mem_map.mp hb'
    exact ⟨s, rect, (List.of_mem_zip hq).1, (List.of_mem_zip hq).2, rfl⟩
  refine hard_of_frame (b0 := dumpBox plotId plotBox plot) (pid := plotId) hboxes rfl rfl rfl
    ?_ ?_ rfl ?_
  · intro b hb'
    rw [hboxes] at hb'
    rcases List.mem_cons.mp hb' with rfl | hb''
    · exact ⟨rfl, rfl⟩
    · obtain ⟨s, rect, _, _, rfl⟩ := hmem b hb''
      exact ⟨rfl, rfl⟩
  · intro b hb'
    obtain ⟨s, rect, hs', hq, rfl⟩ := hmem b hb'
    refine ⟨?_, hcont rect hq⟩
    show (if s.isPlot then "" else plotId) = plotId
    rw [hnp s hs']
    rfl
  · show (⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect).Contained plot
    refine ⟨c1, ?_, c3, ?_⟩ <;> dsimp only <;> omega

theorem xychart_valid (m : Model) (result : Layered.FamilyResult)
    (_hwf : WellFormed m) (_hlim : WithinLimits m) (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  layout_valid h

end Xychart
end Kinds
end Elegant
