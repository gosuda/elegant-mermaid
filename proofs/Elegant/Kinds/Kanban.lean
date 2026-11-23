import Elegant.Kinds.Common
import Elegant.StyledMeasure

set_option autoImplicit false

namespace Elegant.Kinds.Kanban

def configured (m : Model) (key : String) (fallback : Int) : Except LayoutError Int := do
  match m.options.config.find? (fun p => p.1 == key) with
  | none => pure fallback
  | some (_, .integer px) =>
    if px < 0 ∨ COORD_LIMIT < px then throw .overflow
    let v := if m.profile == .cell then Int.fdiv (px + 7) 8 else px * 64
    if COORD_LIMIT < v then throw .overflow
    pure v
  | _ => throw .overflow

private def checked (r : Rect) : Except LayoutError Rect :=
  if r.w < 0 ∨ r.h < 0 then .error .domain
  else if COORD_LIMIT < r.x + r.w ∨ COORD_LIMIT < r.y + r.h ∨
      r.x + r.w < -COORD_LIMIT ∨ r.y + r.h < -COORD_LIMIT then .error .overflow
  else .ok r

theorem checked_spec {input output : Rect} (h : checked input = .ok output) :
    output = input ∧ 0 ≤ input.w ∧ 0 ≤ input.h ∧
      -COORD_LIMIT ≤ input.x + input.w ∧ input.x + input.w ≤ COORD_LIMIT ∧
      -COORD_LIMIT ≤ input.y + input.h ∧ input.y + input.h ≤ COORD_LIMIT := by
  unfold checked at h
  split at h
  · simp at h
  · rename_i hs
    split at h
    · simp at h
    · rename_i hb
      have heq := Except.ok.inj h
      subst output
      exact ⟨rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩

def isSection (b : ModelBox) : Bool := b.role == .group || b.parent == ""

private def text (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (fun l => l.owner == b.id) with
  | some l => l.text
  | none => b.text.getD ""

private def sliceRuns (runs : List Label.Run) (offset count : Nat) : List TextRun :=
  match runs with
  | [] => []
  | r :: rs =>
    if r.text.length ≤ offset then sliceRuns rs (offset - r.text.length) count
    else
      let part := (r.text.drop offset).take count
      let tail := sliceRuns rs 0 (count - part.length)
      if part.isEmpty then tail else
        { text := String.ofList part, bold := r.bold, italic := r.italic } :: tail

private def sceneLines (profile : Profile) (source : String) (ls : List Measure.Line) : List (List TextRun) :=
  let runs := (Label.regions source.toList).flatMap fun reg =>
    let rs := if profile == .cell then
      reg.runs.map (fun r => { r with text := StyledMeasure.normalizeCellText r.text })
      else reg.runs
    rs ++ [{ text := reg.separator, bold := false, italic := false }]
  (ls.foldl (fun (state : Nat × List (List TextRun)) l =>
    (state.1 + l.text.length + l.sep.length,
      state.2 ++ [sliceRuns runs state.1 l.text.length])) (0, [])).2

private def textItem (profile : Profile) (source : String) (r : Rect) (align : Align)
    (ls : List Measure.Line) : Primitive :=
  .text { rect := r, role := .label, size := 14, align := align, style := "text", lines := sceneLines profile source ls }

def textBytes (m : Model) : Nat :=
  let bytes := m.labels.foldl (fun n l => n + l.text.utf8ByteSize) 0
  m.boxes.foldl (fun n b =>
    if m.labels.any (fun l => l.owner == b.id) then n
    else n + (b.text.getD "").utf8ByteSize) bytes

def limitFailure (m : Model) : Option LayoutFailure :=
  let l := m.options.limits
  if l.maxNodes < m.boxes.length then some (.tooLarge l.maxNodes m.boxes.length)
  else if l.maxEdges < m.routes.length then some (.tooLarge l.maxEdges m.routes.length)
  else if l.maxTextBytes < textBytes m then some (.tooLarge l.maxTextBytes (textBytes m))
  else none

/-- Advance exactly the owning column; all other column cursors are unchanged. -/
def advanceCursor (cursors : List Int) (column : Nat) (height gap band : Int) : List Int :=
  cursors.set column (cursors.getD column band + height + gap)

def cardRect (pad width gap cardWidth : Int) (column : Nat) (cursor height : Int) : Rect :=
  ⟨pad + Int.ofNat column * (width + gap) + Int.fdiv (width - cardWidth) 2,
    pad + cursor, cardWidth, height⟩

def sectionRect (pad width gap gutter band minimum minHeight cursor : Int) (index : Nat) : Rect :=
  ⟨pad + Int.ofNat index * (width + gap), pad, width,
    max (cursor - band - gap + Int.fdiv gutter 2 + 3 * gutter) minHeight + band - minimum⟩

def placedRect (placed : List (String × Rect)) (id : String) : Rect :=
  ((placed.find? (fun entry => entry.1 == id)).map (·.2)).getD ⟨0, 0, 0, 0⟩

def sceneBox (placed : List (String × Rect)) (b : ModelBox) : Box :=
  ⟨b.id, b.role.id, placedRect placed b.id, b.parent, b.exclusive⟩

def assemble (m : Model) (canvas : Size) (placed : List (String × Rect))
    (groups : List Group) : Scene :=
  let boxes := m.boxes.map (sceneBox placed)
  { kind := "kanban", profile := m.profile, options := { m.options with profile := m.profile }, canvas := canvas, boxes := boxes, items := groups }

/-- Native Kanban placement consumes the normalized boxes and their resolved label text.
The dump deliberately contains no labels: card and column captions are display primitives. -/
def scene (m : Model) : Except LayoutError Scene := do
  let p := m.profile
  let width ← configured m "sectionWidth" (LayoutConst.kanban_section_width.get p)
  let pad ← configured m "padding" (LayoutConst.kanban_padding.get p)
  let gutter := LayoutConst.kanban_gutter.get p
  let gap := LayoutConst.kanban_card_gap.get p
  let px := LayoutConst.kanban_card_pad_x.get p
  let py := LayoutConst.kanban_card_pad_y.get p
  let border := LayoutConst.node_border.get p
  let lh := LayoutConst.line_h.get p
  let minimum := LayoutConst.kanban_label_band_min.get p
  let minHeight := LayoutConst.kanban_section_min_height.get p
  let corner := LayoutConst.corner_radius.get p
  let cw := width - Int.fdiv (3 * gutter) 2
  if cw ≤ 0 then throw .domain
  let sections := m.boxes.filter isSection
  let cards := m.boxes.filter (fun b => !isSection b)
  if sections.any (fun b => b.parent != "") then throw .domain
  let metric ← Common.labelMetric p m.options.fontFamily
  let titles ← sections.mapM (fun b => StyledMeasure.wrap metric (max 1 (width - 2 * px)) (text m b).toList)
  let texts ← cards.mapM (fun b => StyledMeasure.wrap metric (max 1 (cw - 2 * px)) (text m b).toList)
  let band := titles.foldl (fun h ls => max h (Int.ofNat ls.length * lh + border)) minimum
  let mut cursors := List.replicate sections.length band
  let mut placed : List (String × Rect) := []
  let mut cardGroups : List Group := []
  for (b, ls) in cards.zip texts do
    let some s := sections.findIdx? (fun col => col.id == b.parent) | throw .domain
    let h := Int.ofNat (max 1 ls.length) * lh + 2 * py + 2 * border
    let r ← checked (cardRect pad width gap cw s (cursors.getD s band) h)
    placed := placed ++ [(b.id, r)]
    cursors := advanceCursor cursors s h gap band
    let tr : Rect := ⟨r.x + px, r.y + border + py, r.w - 2 * px, Int.ofNat ls.length * lh⟩
    cardGroups := cardGroups ++ [{ role := .node, owner := b.id, items := [.roundRect r corner { style := "node" }, textItem p (text m b) tr .start ls] }]
  let mut groups : List Group := []
  let mut right := pad
  let mut bottom := pad
  for ((b, ls), s) in (sections.zip titles).zipIdx do
    let x := pad + Int.ofNat s * (width + gap)
    let extent := cursors.getD s band - band - gap + Int.fdiv gutter 2
    let h := max (extent + 3 * gutter) minHeight + band - minimum
    let r ← checked (sectionRect pad width gap gutter band minimum minHeight (cursors.getD s band) s)
    let tr ← checked ⟨x, pad + border + Int.fdiv (band - border - Int.ofNat ls.length * lh) 2, width, Int.ofNat ls.length * lh⟩
    placed := placed ++ [(b.id, r)]
    groups := groups ++ [{ role := .group, owner := b.id, items := [.roundRect r corner { style := "group" }] ++ (if ls.isEmpty then [] else [textItem p (text m b) tr .middle ls]) }]
    right := max right (x + width)
    bottom := max bottom (pad + h)
  if COORD_LIMIT < right + pad ∨ COORD_LIMIT < bottom + pad then throw .overflow
  pure (assemble m ⟨right + pad, bottom + pad⟩ placed (groups ++ cardGroups))

/-- Kanban has no capped search phase: all three native passes traverse declaration lists. -/
def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  match limitFailure m with
  | some failure => throw failure
  | none =>
    match scene m with
    | .error error => throw (.geometry error)
    | .ok value => pure { scene := value, budgetExhausted := false }

theorem layout_spec {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    scene m = .ok result.scene ∧ result.budgetExhausted = false ∧ limitFailure m = none := by
  unfold layout at h
  cases hl : limitFailure m with
  | some failure => simp [hl] at h
  | none =>
    cases hs : scene m with
    | error error => simp [hl, hs] at h
    | ok value =>
      simp [hl, hs] at h
      change Except.ok ({ scene := value, budgetExhausted := false } : Layered.FamilyResult) = Except.ok result at h
      have heq := Except.ok.inj h
      subst result
      exact ⟨rfl, rfl, rfl⟩

end Elegant.Kinds.Kanban
