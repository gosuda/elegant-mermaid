import Elegant.Kinds.Common

set_option autoImplicit false

/-! ER model adapter. An entity box carries its table text in the model dump (`text`), in the
encoding the Go adapter writes: the decoded heading, a blank separator `<br/><br/>`, then one
`<br/>`-separated row per attribute with `|`-separated fields, each field escaped (`\n`, `\p`,
`\l`, `\t`, `\\`). The adapter sizes an entity as a table (`erTableSize` in Go): column widths,
row heights, the heading, the paddings, and the `er.min_*` floor. The family then applies its
own node minimum. Group boxes carry their title in the dump text and are framed by the family. -/

namespace Elegant
namespace Kinds
namespace Er

open Common

/-- Undo the field escapes of the table text; a lone trailing backslash stays. -/
def decodeField : List Char → List Char
  | [] => []
  | '\\' :: c :: rest =>
    (if c = 'n' then '\n' else if c = 't' then '\t' else if c = 'p' then '|'
     else if c = 'l' then '<' else c) :: decodeField rest
  | c :: rest => c :: decodeField rest

def decode (s : String) : String := String.ofList (decodeField s.toList)

structure Table where
  heading : String
  rows : List (List String)
deriving Repr

/-- Split a table text at its first `<br/><br/>`; no separator means no attributes. -/
def parse (text : String) : Table :=
  match text.splitOn "<br/><br/>" with
  | [] => ⟨"", []⟩
  | heading :: rest =>
    let attributes := "<br/><br/>".intercalate rest
    ⟨decode heading,
      if attributes.isEmpty then []
      else (attributes.splitOn "<br/>").map fun line => (line.splitOn "|").map decode⟩

def lineHeight (profile : Profile) : Int :=
  match profile with
  | .vector => Measure.Role.label.lineHeightPx * 64
  | .cell => 1

/-- The widest piece of a text, the pieces being its `\n`-separated parts. -/
def textWidth (metric : Measure.Metric) (text : String) : Except LayoutError Int := do
  let widths ← (text.splitOn "\n").mapM fun piece => do
    pure (widest (← unwrapped metric piece))
  Measure.checkedI32 (widths.foldl max 0)

def rowHeight (profile : Profile) (row : List String) : Except LayoutError Int :=
  Measure.checkedI32
    ((row.foldl (fun n field => max n (field.splitOn "\n").length) 1 : Nat) * lineHeight profile)

/-- Index and width of the attribute columns: the type and name columns always, the key and
comment columns only when some row fills them. At most four fields of a row count. -/
def columnWidths (metric : Measure.Metric) (rows : List (List String)) :
    Except LayoutError (List (Nat × Int)) := do
  let widths ← rows.foldlM (fun (acc : List Int) row => do
    let fieldWidths ← (row.take 4).mapM (textWidth metric)
    pure (acc.zipIdx.map fun (w, i) => max w (fieldWidths.getD i 0))) [0, 0, 0, 0]
  pure ((widths.zipIdx.filter fun (w, i) => i < 2 ∨ 0 < w).map fun (w, i) => (i, w))

def separator (profile : Profile) : Int := if profile = .cell then 1 else 0

/-- `erTableSize`: the table width and height, floored by `er.min_width` and `er.min_height`. -/
def tableSize (profile : Profile) (text : String) : Except LayoutError Size := do
  let metric ← labelMetric profile
  let table := parse text
  let columns ← columnWidths metric table.rows
  let rowHeights ← table.rows.mapM (rowHeight profile)
  let headingHeight ← rowHeight profile [table.heading]
  let headingWidth ← textWidth metric table.heading
  let paddingX := LayoutConst.er_padding_x.get profile
  let paddingY := LayoutConst.er_padding_y.get profile
  let gaps := ((columns.length - 1 : Nat) : Int) * paddingX
  let width ← Measure.checkedI32 (max ((columns.map (·.2)).sum + gaps) headingWidth + 2 * paddingX)
  let height ← Measure.checkedI32
    (headingHeight + max rowHeights.sum (lineHeight profile) + separator profile + 2 * paddingY)
  pure ⟨max width (LayoutConst.er_min_width.get profile), max height (LayoutConst.er_min_height.get profile)⟩

def isEntity (b : ModelBox) : Bool := b.shape == "erBox"

def sizes (m : Model) : Except LayoutError (List (String × Size)) :=
  (m.boxes.filter isEntity).mapM fun b => do
    let size ← tableSize m.options.profile (boxText m b)
    pure (b.id, withFamilyMinimum m.options.profile size)

def input (m : Model) (fixed : List (String × Size)) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map (edgeOptions 1)
    labels := m.labels
    fixedSizes := fixed }

/-! ### Drawing -/

/-- A text item: the wrapped lines of every `\n`-separated piece; a piece with no line keeps one
empty line. -/
def textItem (metric : Measure.Metric) (text : String) (rect : Rect) (align : Align) :
    Except LayoutError Primitive := do
  let pieces ← (text.splitOn "\n").mapM fun piece => do
    let lines ← unwrapped metric piece
    pure (if lines.isEmpty then [[⟨"", false, false⟩]]
      else lines.map fun l => [⟨String.ofList l.text, false, false⟩])
  pure (.text { rect := rect, role := .label, size := 14, align := align, style := "text",
                lines := pieces.flatten })

def rule (a b : Point) : Primitive := .polyline [a, b] 0 { style := "rule" }

/-- The cells of one attribute column, top to bottom from `y`. -/
def columnTexts (metric : Measure.Metric) (rows : List (List String)) (heights : List Int)
    (index : Nat) (x width y : Int) : Except LayoutError (List Primitive) := do
  let (_, items) ← (rows.zip heights).foldlM (fun (acc : Int × List Primitive) (q : List String × Int) => do
    let item ← textItem metric (q.1.getD index "") ⟨x, acc.1, width, q.2⟩ .start
    pure (acc.1 + q.2, acc.2 ++ [item])) (y, [])
  pure items

/-- The table of one entity: the frame, the heading rule, one rule between neighbouring columns,
then the heading and the column texts. -/
def tablePrimitives (profile : Profile) (rect : Rect) (text : String) :
    Except LayoutError (List Primitive) := do
  let metric ← labelMetric profile
  let table := parse text
  let columns ← columnWidths metric table.rows
  let heights ← table.rows.mapM (rowHeight profile)
  let headingHeight ← rowHeight profile [table.heading]
  let paddingX := LayoutConst.er_padding_x.get profile
  let paddingY := LayoutConst.er_padding_y.get profile
  let sep := separator profile
  let top := rect.y + paddingY
  let heading ← textItem metric table.heading ⟨rect.x, top, rect.w, headingHeight⟩ .middle
  let divider := top + headingHeight
  let bottom := rect.y + rect.h - sep
  let (_, shapes, texts) ← columns.zipIdx.foldlM
    (fun (acc : Int × List Primitive × List Primitive) (q : (Nat × Int) × Nat) => do
      let column := q.1
      let items ← columnTexts metric table.rows heights column.1 acc.1 column.2 (divider + sep)
      let x := acc.1 + column.2 + paddingX
      let lineX := x - Int.fdiv paddingX 2
      pure (x, if q.2 + 1 < columns.length then acc.2.1 ++ [rule ⟨lineX, divider⟩ ⟨lineX, bottom⟩]
              else acc.2.1, acc.2.2 ++ items))
    (rect.x + paddingX,
     [.rect rect { style := "node" }, rule ⟨rect.x, divider⟩ ⟨rect.x + rect.w - sep, divider⟩],
     [heading])
  pure (shapes ++ texts)

/-- Replace the drawing of every entity box by its table. -/
def decorateGroup (m : Model) (s : Scene) (group : Group) : Except LayoutError Group :=
  match m.boxes.find? (fun b => b.id == group.owner),
      s.boxes.find? (fun b => b.id == group.owner) with
  | some b, some placed =>
    if isEntity b then do
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

/-- The table replacement changes the display list only. -/
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

/-- ER validity reduces to the family's: the adapter changes sizes and the display list only. -/
theorem layout_valid_of_family
    (hfam : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      Layered.layoutFamily inp o = .ok res → Validator.check res.scene.layoutDump = true)
    {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    Validator.check r.scene.layoutDump = true := by
  obtain ⟨fixed, res, _, hf, hd, _⟩ := layout_spec h
  rw [hd]
  exact hfam _ _ _ hf

end Er
end Kinds
end Elegant
