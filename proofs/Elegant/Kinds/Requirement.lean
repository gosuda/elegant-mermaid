import Elegant.Kinds.Common

set_option autoImplicit false

/-! Requirement model adapter. Every box label is a stack of rows (stereotype, name, fields),
one per line. The adapter sizes a box as a row table (`requirementTableSize` in Go): the widest
row plus the horizontal padding, the row heights plus the vertical padding. The family applies
its node minimum, and the table drawing replaces the plain node frame. -/

namespace Elegant
namespace Kinds
namespace Requirement

open Common

def pieces (text : String) : List String := text.splitOn "\n"

/-- The widest row and the row count of a box text. -/
def measure (profile : Profile) (text : String) : Except LayoutError (Int × Int) := do
  let metric ← labelMetric profile
  let measured ← (pieces text).mapM (unwrapped metric)
  let rows : Int := (measured.map fun ls => (max 1 ls.length : Int)).foldl (· + ·) 0
  pure (measured.foldl (fun w ls => max w (widest ls)) 0, rows)

def tableSize (profile : Profile) (text : String) : Except LayoutError Size := do
  let (width, rows) ← measure profile text
  checkSize (width + LayoutConst.requirement_padding_x.get profile)
    (rows * LayoutConst.line_h.get profile + LayoutConst.requirement_padding_y.get profile)

def sizes (m : Model) : Except LayoutError (List (String × Size)) :=
  m.boxes.mapM fun b => do
    let size ← tableSize m.options.profile (modelBoxText m b)
    pure (b.id, withFamilyMinimum m.options.profile size)

def input (m : Model) (fixed : List (String × Size)) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (modelBoxText m)
    edges := m.routes.map (edgeOptions 1)
    labels := m.labels
    fixedSizes := fixed }

/-! ### Drawing -/

/-- The wrapped lines of one row; an empty row keeps one empty line. -/
def rowLines (metric : Measure.Metric) (piece : String) :
    Except LayoutError (List (List TextRun)) := do
  let lines ← unwrapped metric piece
  pure (if lines.isEmpty then [[⟨"", false, false⟩]]
    else lines.map fun l => [⟨String.ofList l.text, false, false⟩])

/-- Space between the header rows and the field rows; the vector profile only. -/
def headerGap (profile : Profile) (rowCount : Nat) : Int :=
  if profile = .vector ∧ 2 < rowCount then Int.fdiv (LayoutConst.requirement_padding_y.get profile) 2
  else 0

def rowAlign (index : Nat) : Align := if index < 2 then .middle else .start

def rowTexts (rect : Rect) (paddingX lineH : Int) (gap : Int) :
    Nat → Int → List (List (List TextRun)) → List Primitive
  | _, _, [] => []
  | i, y, lines :: rest =>
    let y' := if i = 2 then y + gap else y
    let span := (lines.length : Int) * lineH
    .text { rect := ⟨rect.x + Int.fdiv paddingX 2, y', rect.w - paddingX, span⟩
            role := .label
            size := 14
            align := rowAlign i
            style := "text"
            lines := lines } :: rowTexts rect paddingX lineH gap (i + 1) (y' + span) rest

/-- The table of one requirement: the frame, a divider under the header rows (vector profile),
and one text per row. -/
def tablePrimitives (profile : Profile) (rect : Rect) (text : String) :
    Except LayoutError (List Primitive) := do
  let metric ← labelMetric profile
  let paddingX := LayoutConst.requirement_padding_x.get profile
  let paddingY := LayoutConst.requirement_padding_y.get profile
  let lineH := LayoutConst.line_h.get profile
  let ps := pieces text
  let rows ← ps.mapM (rowLines metric)
  let gap := headerGap profile ps.length
  let top := rect.y + Int.fdiv (paddingY - gap) 2
  let headerRows : Int := ((rows.getD 0 []).length : Int) +
    (if 1 < rows.length then ((rows.getD 1 []).length : Int) else 0)
  let divider := top + headerRows * lineH + Int.fdiv gap 2
  let rule : List Primitive :=
    if 0 < gap then
      [.polyline [⟨rect.x, divider⟩, ⟨rect.x + rect.w, divider⟩] 0 { style := "rule" }]
    else []
  pure ([.rect rect { style := "node" }] ++ rule ++ rowTexts rect paddingX lineH gap 0 top rows)

def decorateGroup (m : Model) (s : Scene) (group : Group) : Except LayoutError Group :=
  match m.boxes.find? (fun b => b.id == group.owner),
      s.boxes.find? (fun b => b.id == group.owner) with
  | some b, some placed =>
    if group.role = .node then do
      pure { group with items := ← tablePrimitives m.options.profile placed.rect (boxText m b) }
    else pure group
  | _, _ => pure group

def decorate (m : Model) (s : Scene) : Except LayoutError Scene := do
  let items ← s.items.mapM (decorateGroup m s)
  pure { s with items := items }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match sizes m with
  | .error e => .error (.geometry e)
  | .ok fixed =>
    match Layered.layoutFamily (input m fixed) m.options with
    | .error e => .error e
    | .ok result =>
      match decorate m (result.scene.projectCellAttachments (routeMarkers m)) with
      | .error e => .error (.geometry e)
      | .ok scene => .ok { result with scene := scene }

/-! ### Facts -/

/-- The drawing replacement changes the display list only. -/
theorem decorate_layoutDump {m : Model} {s s' : Scene} (h : decorate m s = .ok s') :
    s'.layoutDump = s.layoutDump := by
  unfold decorate at h
  cases hm : s.items.mapM (decorateGroup m s) with
  | error e => simp [hm, Functor.map, Except.map] at h
  | ok items =>
    simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl

theorem layout_spec {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    ∃ fixed res, sizes m = .ok fixed ∧
      Layered.layoutFamily (input m fixed) m.options = .ok res ∧
      r.scene.layoutDump = res.scene.layoutDump ∧ r.budgetExhausted = res.budgetExhausted := by
  unfold layout at h
  cases hs : sizes m with
  | error e => simp [hs] at h
  | ok fixed =>
    cases hf : Layered.layoutFamily (input m fixed) m.options with
    | error e => simp [hs, hf] at h
    | ok res =>
      cases hd : decorate m (res.scene.projectCellAttachments (routeMarkers m)) with
      | error e => simp [hs, hf, hd] at h
      | ok scene =>
        simp only [hs, hf, hd, Except.ok.injEq] at h
        subst h
        exact ⟨fixed, res, rfl, hf,
          (decorate_layoutDump hd).trans (Scene.projectCellAttachments_layoutDump _ _), rfl⟩

/-- Requirement validity reduces to the family's: the adapter changes sizes and the display
list only. -/
theorem layout_valid_of_family
    (hfam : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      Layered.layoutFamily inp o = .ok res → Validator.check res.scene.layoutDump = true)
    {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    Validator.check r.scene.layoutDump = true := by
  obtain ⟨fixed, res, _, hf, hd, _⟩ := layout_spec h
  rw [hd]
  exact hfam _ _ _ hf

end Requirement
end Kinds
end Elegant
