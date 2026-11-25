import Elegant.GridPacket
import Elegant.Kinds.Common

set_option autoImplicit false

namespace Elegant.Kinds.Packet
open GridPacket

structure Entry where
  box : ModelBox
  piece : Piece
  title : Bool
  lines : List Measure.Line
  textHeight : Int
  lead : Option (ModelLabel × List Measure.Line × Int)
  trail : Option (ModelLabel × List Measure.Line × Int)

private def measure (profile : Profile) (title body : Bool) (text : String)
    (fontFamily : Bool := false) :
    Except LayoutError (List Measure.Line) := do
  let metric ← if profile == .cell then pure Measure.Metric.cell
    else (if title then Measure.Role.title else if body then Measure.Role.body else Measure.Role.label).metric fontFamily
  StyledMeasure.wrap metric I32_MAX text.toList

private def width (lines : List Measure.Line) : Int := lines.foldl (fun n l => max n l.width) 0
private def lineText (l : Measure.Line) : String := String.ofList l.text

private def decode (b : ModelBox) (next : Int) : Except LayoutError (Piece × Bool) := do
  if b.role != .node then throw .domain
  if b.shape == "title" then return (⟨0, 0⟩, true)
  if b.shape.isEmpty then return (⟨next, next⟩, false)
  match b.shape.splitOn ";" with
  | ["field", a, z] =>
    if !a.startsWith "start=" || !z.startsWith "end=" then throw .domain
    match (a.drop 6).toString.toInt?, (z.drop 4).toString.toInt? with
    | some first, some last => return (⟨first, last⟩, false)
    | _, _ => throw .domain
  | _ => throw .domain

private def entries (m : Model) : Except LayoutError (List Entry) := do
  let (_, out) ← m.boxes.foldlM (fun (state : Int × List Entry) b => do
    let (piece, title) ← decode b state.1
    let caption := m.labels.find? (fun l => l.owner == b.id && l.id == b.id ++ ".label")
    let text := match caption with
      | some l => l.text
      | none => match b.text with | some t => if t.isEmpty then b.id else t | none => b.id
    let lines ← measure (fontFamily := m.options.fontFamily) m.profile title false text
    let mut lead := none
    let mut trail := none
    for l in m.labels.filter (fun l => l.owner == b.id && l.id != b.id ++ ".label") do
      if title || !(l.id.endsWith ".bit" || l.id.endsWith ".lead" || l.id.endsWith ".trail") then
        throw .domain
      let ls ← measure (fontFamily := m.options.fontFamily) m.profile false true l.text
      if l.id.endsWith ".trail" then trail := some (l, ls, width ls)
      else lead := some (l, ls, width ls)
    let lh := if m.profile == .cell then 1 else if title then 1536 else 1280
    let e : Entry := ⟨b, piece, title, lines, (lines.length : Int) * lh, lead, trail⟩
    pure (if title then state.1 else piece.last + 1, state.2 ++ [e])) (0, [])
  if m.labels.any (fun l => !m.boxes.any (fun b => b.id == l.owner)) then throw .domain
  pure out

private theorem foldlM_preserves {α β : Type} (xs : List α)
    (step : β → α → Except LayoutError β) (invariant : β → Prop)
    (initial final : β) (hinit : invariant initial)
    (hstep : ∀ state a next, invariant state →
      step state a = .ok next → invariant next)
    (hrun : xs.foldlM step initial = .ok final) : invariant final := by
  induction xs generalizing initial with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hrun
    subst final
    exact hinit
  | cons a xs ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at hrun
    cases hs : step initial a with
    | error err => simp [hs] at hrun
    | ok next =>
      simp only [hs] at hrun
      exact ih next (hstep initial a next hinit hs) hrun

private theorem decode_node (b : ModelBox) (next : Int) (piece : Piece × Bool)
    (h : decode b next = .ok piece) : b.role = .node := by
  by_cases role : b.role = .node
  · exact role
  · simp [decode, role, bind, Except.bind] at h

private def DecodedEntry (m : Model) (e : Entry) : Prop :=
  e.box.role = .node ∧
    (e.title = true → ∀ l ∈ m.labels, l.owner = e.box.id →
      l.id = e.box.id ++ ".label")

theorem entries_decoded (m : Model) (es : List Entry)
    (h : entries m = .ok es) : ∀ e ∈ es, DecodedEntry m e := by
  unfold entries at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i final hfold
    have inv : ∀ e ∈ final.2, DecodedEntry m e := by
      apply foldlM_preserves (hrun := hfold)
        (invariant := fun state => ∀ e ∈ state.2, DecodedEntry m e)
      · simp
      · intro state b next previous hs
        split at hs
        · cases hs
        · rename_i decoded hd
          have node := decode_node b state.1 decoded hd
          rcases decoded with ⟨piece, title⟩
          split at hs
          · cases hs
          · rename_i lines hlines
            have noAux : title = true →
                (m.labels.filter (fun l => l.owner == b.id &&
                  l.id != b.id ++ ".label")) = [] := by
              intro ht
              cases hl : m.labels.filter (fun l => l.owner == b.id &&
                  l.id != b.id ++ ".label") with
              | nil => rfl
              | cons l ls =>
                simp [hl, List.forIn_cons, ht, bind, Except.bind] at hs
            split at hs
            · cases hs
            · rename_i aux haux
              simp only [pure, Except.pure, Except.ok.injEq] at hs
              subst next
              intro e he
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false] at he
              rcases he with he | rfl
              · exact previous e he
              · refine ⟨node, ?_⟩
                intro ht l hl owner
                by_cases caption : l.id = b.id ++ ".label"
                · exact caption
                · have mem : l ∈ m.labels.filter (fun l => l.owner == b.id &&
                      l.id != b.id ++ ".label") := by
                    simp [List.mem_filter, hl, owner, caption]
                  rw [noAux ht] at mem
                  cases mem
    split at h
    · simp at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      cases h
      exact inv

private theorem forIn_preserves {α β : Type} (xs : List α)
    (step : α → β → Except LayoutError (ForInStep β)) (invariant : β → Prop)
    (initial final : β) (hinit : invariant initial)
    (hstep : ∀ a ∈ xs, ∀ state next, invariant state →
      step a state = .ok next → invariant next.value)
    (hrun : forIn xs initial step = .ok final) : invariant final := by
  induction xs generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hrun
    subst final
    exact hinit
  | cons a xs ih =>
    rw [List.forIn_cons] at hrun
    cases hs : step a initial with
    | error err => simp [hs, bind, Except.bind] at hrun
    | ok next =>
      have hn := hstep a (List.mem_cons_self ..) initial next hinit hs
      cases next with
      | done state =>
        simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hrun
        subst final
        exact hn
      | yield state =>
        simp only [hs, bind, Except.bind] at hrun
        exact ih state hn (fun b hb => hstep b (List.mem_cons_of_mem a hb)) hrun

theorem label_loop_origins (m : Model) (es : List Entry) (labels : List SceneLabel)
    (decoded : ∀ e ∈ es, DecodedEntry m e)
    (h : (forIn m.labels [] (fun l labels => do
      if let some e := es.find? (fun e => e.box.id == l.owner) then
        if l.id != l.owner ++ ".label" then
          let ls ← measure (fontFamily := m.options.fontFamily) m.profile false true l.text
          pure (ForInStep.yield (labels ++ [{
            id := l.id
            owner := l.owner
            rect := bitRect
              (m.options.config.foldl (configure m.profile) (defaults m.profile))
              e.piece (width ls) (l.id.endsWith ".trail")
            lines := ls.map lineText
            text := l.text
          }]))
        else pure (ForInStep.yield labels)
      else pure (ForInStep.yield labels)) : Except LayoutError (List SceneLabel)) = .ok labels) :
    ∀ l ∈ labels, ∃ e ∈ es, e.title = false ∧ ∃ w trail,
      l.rect = bitRect
        (m.options.config.foldl (configure m.profile) (defaults m.profile))
        e.piece w trail := by
  apply forIn_preserves (hrun := h)
    (invariant := fun labels => ∀ l ∈ labels, ∃ e ∈ es, e.title = false ∧
      ∃ w trail, l.rect = bitRect
        (m.options.config.foldl (configure m.profile) (defaults m.profile))
        e.piece w trail)
  · simp
  · intro l hl previous next ih hs
    cases found : es.find? (fun e => e.box.id == l.owner) with
    | none =>
      simp only [found, pure, Except.pure, Except.ok.injEq] at hs
      cases hs
      exact ih
    | some e =>
      have hem := List.mem_of_find?_eq_some found
      have owner : e.box.id = l.owner := by simpa using List.find?_some found
      by_cases caption : l.id = l.owner ++ ".label"
      · simp only [found, caption, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hs
        cases hs
        exact ih
      · have title : e.title = false := by
          cases ht : e.title with
          | false => rfl
          | true =>
            have cap := (decoded e hem).2 ht l hl owner.symm
            exact False.elim (caption (by simpa only [owner] using cap))
        have guard : (l.id != l.owner ++ ".label") = true := by
          simpa only [bne_iff_ne] using caption
        simp only [found, guard, ↓reduceIte, bind, Except.bind] at hs
        cases measured : measure (fontFamily := m.options.fontFamily) m.profile false true l.text with
        | error err =>
          simp only [measured] at hs
          cases hs
        | ok lines =>
          simp only [measured, pure, Except.pure] at hs
          cases hs
          intro label member
          rcases List.mem_append.mp member with member | member
          · exact ih label member
          · have same := List.mem_singleton.mp member
            subst label
            exact ⟨e, hem, title, width lines, l.id.endsWith ".trail", rfl⟩

private def textPrimitive (r : Rect) (role : TextRole) (align : Align)
    (style : String) (lines : List Measure.Line) : Primitive :=
  .text {
    rect := r
    role := role
    size := if role == .title then 16 else 14
    align := align
    style := style
    lines := lines.map fun l => [⟨lineText l, false, false⟩]
  }

private def checked (n : Int) : Except LayoutError Int :=
  if 0 ≤ n ∧ n ≤ COORD_LIMIT then .ok n else .error .overflow

private def fieldsDisjoint : List Entry → Bool
  | [] => true
  | e :: rest =>
    rest.all (fun f => e.title || f.title ||
      decide (e.piece.last < f.piece.first ∨ f.piece.last < e.piece.first)) &&
      fieldsDisjoint rest

theorem fieldsDisjoint_partition (es : List Entry) (h : fieldsDisjoint es = true)
    (e : Entry) (he : e ∈ es) (f : Entry) (hf : f ∈ es)
    (hne : e.box.id ≠ f.box.id) (het : e.title = false) (hft : f.title = false) :
    e.piece.last < f.piece.first ∨ f.piece.last < e.piece.first := by
  induction es with
  | nil => cases he
  | cons a rest ih =>
    simp only [fieldsDisjoint, Bool.and_eq_true] at h
    simp only [List.mem_cons] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact False.elim (hne rfl)
      · have ha := List.all_eq_true.mp h.1 f hf
        simpa [het, hft] using ha
    · rcases hf with rfl | hf
      · have ha := List.all_eq_true.mp h.1 e he
        have rev : f.piece.last < e.piece.first ∨
            e.piece.last < f.piece.first := by
          simpa [het, hft] using ha
        exact rev.symm
      · exact ih h.2 he hf

def placeBoxes (p : Params) (titleRect : Rect) : List Entry → Except LayoutError (List Box)
  | [] => pure []
  | e :: es => do
    let r := if e.title then titleRect else rect p e.piece
    let _ ← checked r.y
    let rest ← placeBoxes p titleRect es
    pure (⟨e.box.id, e.box.role.id, r, e.box.parent, e.box.exclusive⟩ :: rest)

theorem placeBoxes_metadata (p : Params) (titleRect : Rect) (es : List Entry)
    (bs : List Box) (h : placeBoxes p titleRect es = .ok bs) :
    bs.map (fun b => (b.id, b.role, b.parent, b.exclusive)) =
      es.map (fun e => (e.box.id, e.box.role.id, e.box.parent, e.box.exclusive)) := by
  induction es generalizing bs with
  | nil =>
    change Except.ok [] = Except.ok bs at h
    cases h
    rfl
  | cons e es ih =>
    simp only [placeBoxes] at h
    cases hc : checked (if e.title then titleRect else rect p e.piece).y with
    | error err =>
      rw [hc] at h
      change Except.error err = Except.ok bs at h
      cases h
    | ok y =>
      cases hr : placeBoxes p titleRect es with
      | error err =>
        rw [hc, hr] at h
        change Except.error err = Except.ok bs at h
        cases h
      | ok rest =>
        rw [hc, hr] at h
        change Except.ok
          (⟨e.box.id, e.box.role.id, if e.title then titleRect else rect p e.piece,
            e.box.parent, e.box.exclusive⟩ :: rest) = Except.ok bs at h
        cases h
        simp only [List.map_cons]
        rw [ih rest hr]

theorem placeBoxes_geometry (p : Params) (titleRect : Rect) (es : List Entry)
    (bs : List Box) (h : placeBoxes p titleRect es = .ok bs) :
    bs = es.map (fun e =>
      ⟨e.box.id, e.box.role.id, if e.title then titleRect else rect p e.piece,
        e.box.parent, e.box.exclusive⟩) := by
  induction es generalizing bs with
  | nil =>
    change Except.ok [] = Except.ok bs at h
    cases h
    rfl
  | cons e es ih =>
    simp only [placeBoxes] at h
    cases hc : checked (if e.title then titleRect else rect p e.piece).y with
    | error err =>
      rw [hc] at h
      change Except.error err = Except.ok bs at h
      cases h
    | ok y =>
      cases hr : placeBoxes p titleRect es with
      | error err =>
        rw [hc, hr] at h
        change Except.error err = Except.ok bs at h
        cases h
      | ok rest =>
        rw [hc, hr] at h
        change Except.ok
          (⟨e.box.id, e.box.role.id, if e.title then titleRect else rect p e.piece,
            e.box.parent, e.box.exclusive⟩ :: rest) = Except.ok bs at h
        cases h
        simp only [List.map_cons]
        rw [ih rest hr]

theorem placeBoxes_canvas_containment (p : Params) (titleRect : Rect)
    (es : List Entry) (bs : List Box) (h : placeBoxes p titleRect es = .ok bs)
    (canvas : Size)
    (bounds : ∀ e ∈ es, (⟨0, 0, canvas.w, canvas.h⟩ : Rect).Contained
      (if e.title then titleRect else rect p e.piece))
    (labels : List Label) :
    Validator.C1 (⟨canvas, bs, [], labels⟩ : LayoutDump) := by
  intro b hb
  rw [placeBoxes_geometry p titleRect es bs h] at hb
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
  exact bounds e he

theorem placeBoxes_root_nodes (p : Params) (titleRect : Rect) (es : List Entry)
    (bs : List Box) (h : placeBoxes p titleRect es = .ok bs)
    (roots : ∀ e ∈ es, e.box.parent = "" ∧ e.box.role = .node) :
    ∀ b ∈ bs, b.parent = "" ∧ b.role = "node" := by
  have hm := placeBoxes_metadata p titleRect es bs h
  intro b hb
  have hmem : (b.id, b.role, b.parent, b.exclusive) ∈
      es.map (fun e => (e.box.id, e.box.role.id, e.box.parent, e.box.exclusive)) := by
    rw [← hm]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  obtain ⟨e, he, eq⟩ := List.mem_map.mp hmem
  have root := roots e he
  have roleEq : e.box.role.id = "node" := by rw [root.2]; rfl
  simp only [Prod.mk.injEq] at eq
  exact ⟨eq.2.2.1.symm.trans root.1, eq.2.1.symm.trans roleEq⟩

theorem placeBoxes_structural_constraints (p : Params) (titleRect : Rect) (es : List Entry)
    (bs : List Box) (h : placeBoxes p titleRect es = .ok bs)
    (roots : ∀ e ∈ es, e.box.parent = "" ∧ e.box.role = .node)
    (canvas : Size) (labels : List Label) :
    let d : LayoutDump := ⟨canvas, bs, [], labels⟩
    Validator.C3 d ∧ Validator.C4 d ∧ Validator.C5 d ∧ Validator.C6 d ∧ Validator.C8 d := by
  have hb := placeBoxes_root_nodes p titleRect es bs h roots
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b mem ne
    exact False.elim (ne (hb b mem).1)
  · intro r mem; cases mem
  · intro r mem; cases mem
  · intro r mem; cases mem
  · constructor
    · intro g mem group
      have hn := (hb g mem).2
      simp [hn] at group
    · intro g mem group
      have hn := (hb g mem).2
      simp [hn] at group

theorem rowFold_bounds (p : Params) (es : List Entry) (n : Int) :
    n ≤ es.foldl (fun acc e => if e.title then acc else max acc (row p e.piece + 1)) n ∧
      ∀ e ∈ es, e.title = false →
        row p e.piece + 1 ≤
          es.foldl (fun acc e => if e.title then acc else max acc (row p e.piece + 1)) n := by
  induction es generalizing n with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have ht := ih (if e.title then n else max n (row p e.piece + 1))
    constructor
    · have hn : n ≤ (if e.title then n else max n (row p e.piece + 1)) := by
        split <;> omega
      exact Int.le_trans hn ht.1
    · intro f hf hfTitle
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · simp only [hfTitle, Bool.false_eq_true, ↓reduceIte] at ht
        have lower : row p f.piece + 1 ≤ max n (row p f.piece + 1) := by omega
        simpa only [hfTitle, Bool.false_eq_true, ↓reduceIte] using
          Int.le_trans lower ht.1
      · exact ht.2 f hf hfTitle

theorem entry_canvas_containment (p : Params) (es : List Entry) (e : Entry)
    (hp : p.valid) (he : e ∈ es)
    (hf : e.title = false → fits p e.piece) :
    let rows := es.foldl
      (fun n e => if e.title then n else max n (row p e.piece + 1)) 0
    let hasTitle := es.any (·.title)
    let h := rows * pitch p + padding p + if hasTitle then p.height else 0
    let titleRect : Rect := ⟨p.margin, h - p.height, p.bits * p.width, p.height⟩
    (⟨0, 0, p.bits * p.width + 2 * p.margin, h⟩ : Rect).Contained
      (if e.title then titleRect else rect p e.piece) := by
  dsimp
  have hr := rowFold_bounds p es 0
  have hpad := padding_nonneg p hp
  have hpitch := Int.le_of_lt (pitch_pos p hp)
  have hrows := Int.mul_nonneg hr.1 hpitch
  have hm := hp.2.2.2.2.2.2.1
  cases ht : e.title with
  | true =>
    have htitles : es.any (·.title) = true := List.any_eq_true.mpr ⟨e, he, ht⟩
    simp only [htitles, ↓reduceIte]
    unfold Rect.Contained
    dsimp
    omega
  | false =>
    have hfit := hf ht
    have hc := fits_coordinates p e.piece hp hfit
    have bound := rect_canvas_containment p e.piece _ hp hfit.2.1 hc.2.1
      hfit.2.2 hc.1 (hr.2 e he ht)
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold Rect.Contained at bound ⊢
    dsimp at bound ⊢
    have extra : 0 ≤ (if es.any (·.title) then p.height else 0) := by
      split <;> have hh := hp.2.2.1 <;> omega
    omega

theorem placeBoxes_bit_label_clearance (p : Params) (titleRect : Rect)
    (es : List Entry) (bs : List Box) (h : placeBoxes p titleRect es = .ok bs)
    (hp : p.valid) (canvas : Size) (labels : List Label)
    (onlyFields : ∀ e ∈ es, e.title = false)
    (bitLabels : ∀ l ∈ labels, ∃ e ∈ es, ∃ w trail,
      l.rect = bitRect p e.piece w trail) :
    Validator.C7 (⟨canvas, bs, [], labels⟩ : LayoutDump) := by
  intro l hl b hb _ _
  obtain ⟨e, _, w, trail, hrect⟩ := bitLabels l hl
  rw [placeBoxes_geometry p titleRect es bs h] at hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  simp only [onlyFields f hf, Bool.false_eq_true, ↓reduceIte]
  rw [hrect]
  exact bitRect_avoids_field p e.piece f.piece w trail hp

theorem placeBoxes_fields_separated (p : Params) (titleRect : Rect)
    (es : List Entry) (bs : List Box) (h : placeBoxes p titleRect es = .ok bs)
    (hp : p.valid) (canvas : Size) (labels : List Label)
    (onlyFields : ∀ e ∈ es, e.title = false)
    (fit : ∀ e ∈ es, fits p e.piece)
    (partition : ∀ e ∈ es, ∀ f ∈ es, e.box.id ≠ f.box.id →
      e.piece.last < f.piece.first ∨ f.piece.last < e.piece.first) :
    Validator.C2 (⟨canvas, bs, [], labels⟩ : LayoutDump) := by
  intro b hb c hc hne _ _ _
  rw [placeBoxes_geometry p titleRect es bs h] at hb hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
  have separated := rect_fields_separated p e.piece f.piece hp
    (fit e he) (fit f hf) (partition e he f hf hne)
  simpa only [onlyFields e he, onlyFields f hf, Bool.false_eq_true, ↓reduceIte]
    using separated

theorem unique_title_id (es : List Entry)
    (h : (es.filter (·.title)).length ≤ 1)
    (e : Entry) (he : e ∈ es) (het : e.title = true)
    (f : Entry) (hf : f ∈ es) (hft : f.title = true) :
    e.box.id = f.box.id := by
  induction es with
  | nil => cases he
  | cons a rest ih =>
    simp only [List.mem_cons] at he hf
    have restBound : (rest.filter (·.title)).length ≤ 1 := by
      cases ha : a.title with
      | false =>
        simpa only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte] using h
      | true =>
        have hh : (rest.filter (·.title)).length + 1 ≤ 1 := by
          simpa only [List.filter_cons, ha, ↓reduceIte, List.length_cons] using h
        omega
    have noRest (ha : a.title = true) (x : Entry) (hx : x ∈ rest)
        (hxt : x.title = true) : False := by
      have mem : x ∈ rest.filter (·.title) := List.mem_filter.mpr ⟨hx, hxt⟩
      have pos : 0 < (rest.filter (·.title)).length :=
        List.length_pos_iff.mpr (by intro hnil; rw [hnil] at mem; cases mem)
      have hh : (rest.filter (·.title)).length + 1 ≤ 1 := by
        simpa only [List.filter_cons, ha, ↓reduceIte, List.length_cons] using h
      omega
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · rfl
      · exact False.elim (noRest het f hf hft)
    · rcases hf with rfl | hf
      · exact False.elim (noRest hft e he het)
      · exact ih restBound he hf

/-- Separation includes the optional final title row. -/
theorem placeBoxes_separated (p : Params) (es : List Entry)
    (bs : List Box) (hp : p.valid)
    (fit : ∀ e ∈ es, e.title = false → fits p e.piece)
    (partition : fieldsDisjoint es = true)
    (titles : (es.filter (·.title)).length ≤ 1)
    (canvas : Size) (labels : List Label)
    (h : placeBoxes p
      ⟨p.margin,
        es.foldl (fun n e => if e.title then n else max n (row p e.piece + 1)) 0 *
          pitch p + padding p,
        p.bits * p.width, p.height⟩ es = .ok bs) :
    Validator.C2 (⟨canvas, bs, [], labels⟩ : LayoutDump) := by
  intro b hb c hc hne _ _ _
  rw [placeBoxes_geometry _ _ _ _ h] at hb hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
  have rows := rowFold_bounds p es 0
  cases het : e.title <;> cases hft : f.title
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact rect_fields_separated p e.piece f.piece hp (fit e he het) (fit f hf hft)
      (fieldsDisjoint_partition es partition e he f hf hne het hft)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact field_avoids_title p e.piece _ hp (rows.2 e he het)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro hit
    exact field_avoids_title p f.piece _ hp (rows.2 f hf hft)
      ((Rect.meetsInterior_comm _ _).mp hit)
  · exact False.elim (hne (unique_title_id es titles e he het f hf hft))

theorem placeBoxes_label_clearance (p : Params) (es : List Entry)
    (bs : List Box) (hp : p.valid) (canvas : Size) (labels : List Label)
    (bitLabels : ∀ l ∈ labels, ∃ e ∈ es, e.title = false ∧
      ∃ w trail, l.rect = bitRect p e.piece w trail)
    (h : placeBoxes p
      ⟨p.margin,
        es.foldl (fun n e => if e.title then n else max n (row p e.piece + 1)) 0 *
          pitch p + padding p,
        p.bits * p.width, p.height⟩ es = .ok bs) :
    Validator.C7 (⟨canvas, bs, [], labels⟩ : LayoutDump) := by
  intro l hl b hb _ _
  obtain ⟨e, he, het, w, trail, hrect⟩ := bitLabels l hl
  rw [placeBoxes_geometry _ _ _ _ h] at hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  rw [hrect]
  cases hft : f.title with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact bitRect_avoids_field p e.piece f.piece w trail hp
  | true =>
    simp only [↓reduceIte]
    have rows := rowFold_bounds p es 0
    exact bitRect_avoids_title p e.piece _ w trail hp rows.1 (rows.2 e he het)

theorem placeBoxes_congr_title (p : Params) (a b : Rect) (es : List Entry)
    (same : ∀ e ∈ es, (if e.title then a else rect p e.piece) =
      (if e.title then b else rect p e.piece)) :
    placeBoxes p a es = placeBoxes p b es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have head := same e (List.mem_cons_self ..)
    have tail := ih (fun f hf => same f (List.mem_cons_of_mem e hf))
    simp only [placeBoxes, head, tail]

theorem checked_value (n out : Int) (h : checked n = .ok out) :
    out = n ∧ 0 ≤ out ∧ out ≤ COORD_LIMIT := by
  unfold checked at h
  split at h
  · cases h
    exact ⟨rfl, by assumption⟩
  · cases h

/-- Assembly of the actual checked canvas and final title allocation. The
remaining decoder and label-loop invariants are independent of geometry. -/
theorem assembled_constraints (p : Params) (es : List Entry) (bs : List Box)
    (labels : List Label) (w h : Int) (hp : p.valid)
    (hw : checked (p.bits * p.width + 2 * p.margin) = .ok w)
    (hh : checked
      (es.foldl (fun n e => if e.title then n else max n (row p e.piece + 1)) 0 *
        pitch p + padding p + if es.any (·.title) then p.height else 0) = .ok h)
    (boxes : placeBoxes p ⟨p.margin, h - p.height, p.bits * p.width, p.height⟩ es =
      .ok bs)
    (roots : ∀ e ∈ es, e.box.parent = "" ∧ e.box.role = .node)
    (fit : ∀ e ∈ es, e.title = false → fits p e.piece)
    (partition : fieldsDisjoint es = true)
    (titles : (es.filter (·.title)).length ≤ 1)
    (bitLabels : ∀ l ∈ labels, ∃ e ∈ es, e.title = false ∧
      ∃ width trail, l.rect = bitRect p e.piece width trail) :
    HardConstraints (⟨⟨w, h⟩, bs, [], labels⟩ : LayoutDump) := by
  have hwv := (checked_value _ _ hw).1
  have hhv := (checked_value _ _ hh).1
  have canonical := placeBoxes_congr_title p
    ⟨p.margin, h - p.height, p.bits * p.width, p.height⟩
    ⟨p.margin,
      es.foldl (fun n e => if e.title then n else max n (row p e.piece + 1)) 0 *
        pitch p + padding p, p.bits * p.width, p.height⟩ es (by
      intro e he
      cases ht : e.title with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        have hasTitle : es.any (·.title) = true :=
          List.any_eq_true.mpr ⟨e, he, ht⟩
        simp only [↓reduceIte, hhv, hasTitle]
        congr 1 <;> omega)
  have canonicalBoxes := boxes
  rw [canonical] at canonicalBoxes
  have c1 := placeBoxes_canvas_containment p _ es bs boxes ⟨w, h⟩ (by
    intro e he
    have bound := entry_canvas_containment p es e hp he (fit e he)
    simpa only [hwv, hhv] using bound) labels
  have c2 := placeBoxes_separated p es bs hp fit partition titles
    ⟨w, h⟩ labels canonicalBoxes
  obtain ⟨c3, c4, c5, c6, c8⟩ :=
    placeBoxes_structural_constraints p _ es bs boxes roots ⟨w, h⟩ labels
  have c7 := placeBoxes_label_clearance p es bs hp ⟨w, h⟩ labels
    bitLabels canonicalBoxes
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8.1, c8.2⟩

/-- Packet model-stage inputs already contain one box per split field piece. No
additional boxes, relation ids, or semantic parents are manufactured by layout. -/
def scene (m : Model) : Except LayoutError Scene := do
  let p := m.options.config.foldl (configure m.profile) (defaults m.profile)
  if !decide p.valid then throw .domain
  let es ← entries m
  if es.any (fun e => !e.box.parent.isEmpty) then throw .domain
  if (es.filter (·.title)).length > 1 then throw .domain
  for e in es do
    if !e.title && !decide (fits p e.piece) then throw .domain
  if !fieldsDisjoint es then throw .domain
  let rows := es.foldl (fun n e => if e.title then n else max n (row p e.piece + 1)) 0
  let hasTitle := es.any (·.title)
  let w ← checked (p.bits * p.width + 2 * p.margin)
  let h ← checked (rows * pitch p + padding p + if hasTitle then p.height else 0)
  let titleRect : Rect := ⟨p.margin, h - p.height, p.bits * p.width, p.height⟩
  let boxes ← placeBoxes p titleRect es
  let mut items := []
  for e in es do
    let r := if e.title then titleRect else rect p e.piece
    let caption : Rect := ⟨r.x, r.y + Int.fdiv (r.h - e.textHeight) 2, r.w, e.textHeight⟩
    let mut ps := if !e.title && 0 < r.w then [Primitive.rect r { style := "node" }] else []
    if !e.lines.isEmpty then
      ps := ps ++ [textPrimitive caption (if e.title then .title else .label) .middle "text" e.lines]
    for (bit, trail) in [(e.lead, false), (e.trail, true)] do
      if let some (_, ls, bw) := bit then
        let br := bitRect p e.piece bw trail
        let align := if trail then Align.end else if count e.piece = 1 then .middle else .start
        ps := ps ++ [textPrimitive br .body align "text-muted" ls]
    items := items ++ [⟨.node, e.box.id, ps⟩]
  let mut labels := []
  for l in m.labels do
    if let some e := es.find? (fun e => e.box.id == l.owner) then
      if l.id != l.owner ++ ".label" then
        let ls ← measure (fontFamily := m.options.fontFamily) m.profile false true l.text
        let br := bitRect p e.piece (width ls) (l.id.endsWith ".trail")
        labels := labels ++ [{
          id := l.id
          owner := l.owner
          rect := br
          lines := ls.map lineText
          text := l.text
        }]
  return {
    kind := "packet"
    profile := m.profile
    options := { m.options with profile := m.profile }
    canvas := ⟨w, h⟩
    boxes := boxes
    labels := labels
    items := items
  }

theorem scene_params_valid (m : Model) (s : Scene) (h : scene m = .ok s) :
    (m.options.config.foldl (configure m.profile) (defaults m.profile)).valid := by
  by_cases hp :
      (m.options.config.foldl (configure m.profile) (defaults m.profile)).valid
  · exact hp
  · simp [scene, hp, bind, Except.bind] at h

theorem scene_entries_success (m : Model) (s : Scene) (h : scene m = .ok s) :
    ∃ es, entries m = .ok es := by
  cases he : entries m with
  | ok es => exact ⟨es, rfl⟩
  | error err =>
    have hp := scene_params_valid m s h
    simp [scene, hp, he, bind, Except.bind] at h

theorem scene_parent_check (m : Model) (s : Scene) (es : List Entry)
    (h : scene m = .ok s) (he : entries m = .ok es) :
    es.any (fun e => !e.box.parent.isEmpty) = false := by
  have hp := scene_params_valid m s h
  cases hc : es.any (fun e => !e.box.parent.isEmpty) with
  | false => rfl
  | true => simp [scene, hp, he, hc, bind, Except.bind] at h

theorem scene_title_count (m : Model) (s : Scene) (es : List Entry)
    (h : scene m = .ok s) (he : entries m = .ok es) :
    (es.filter (·.title)).length ≤ 1 := by
  have hp := scene_params_valid m s h
  have parents := scene_parent_check m s es h he
  by_cases count : (es.filter (·.title)).length > 1
  · simp [scene, hp, he, parents, count, bind, Except.bind] at h
  · omega

theorem scene_entry_parents (m : Model) (s : Scene) (es : List Entry)
    (h : scene m = .ok s) (he : entries m = .ok es) :
    ∀ e ∈ es, e.box.parent = "" := by
  have parents := scene_parent_check m s es h he
  intro e hem
  have entry := List.any_eq_false.mp parents e hem
  simpa using entry

/-- Successful execution of the scene's field-admission loop supplies the fit
invariant for every decoded non-title entry. -/
theorem field_loop_fits (p : Params) (es : List Entry) (out : PUnit)
    (h : (forIn es PUnit.unit (fun e _ => do
      if !e.title && !decide (fits p e.piece) then
        throw LayoutError.domain
      pure (ForInStep.yield PUnit.unit)) : Except LayoutError PUnit) = .ok out) :
    ∀ e ∈ es, e.title = false → fits p e.piece := by
  induction es with
  | nil => simp
  | cons e es ih =>
    by_cases admissible : e.title = true ∨ fits p e.piece
    · have next :
          (forIn es PUnit.unit (fun e _ => do
            if !e.title && !decide (fits p e.piece) then
              throw LayoutError.domain
            pure (ForInStep.yield PUnit.unit)) : Except LayoutError PUnit) = .ok out := by
        rcases admissible with ht | hf
        · simpa [List.forIn_cons, ht, bind, Except.bind, pure, Except.pure] using h
        · simpa [List.forIn_cons, hf, bind, Except.bind, pure, Except.pure] using h
      intro f hf hft
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases admissible with ht | hfit
        · cases ht.symm.trans hft
        · exact hfit
      · exact ih next f hf hft
    · have ht : e.title = false := by
        cases htitle : e.title with
        | false => rfl
        | true => exact False.elim (admissible (Or.inl htitle))
      have hf : ¬ fits p e.piece := fun hf => admissible (Or.inr hf)
      simp [List.forIn_cons, ht, hf, bind, Except.bind] at h

theorem scene_fields_fit (m : Model) (s : Scene) (es : List Entry)
    (h : scene m = .ok s) (he : entries m = .ok es) :
    ∀ e ∈ es, e.title = false →
      fits (m.options.config.foldl (configure m.profile) (defaults m.profile)) e.piece := by
  let p := m.options.config.foldl (configure m.profile) (defaults m.profile)
  have hp := scene_params_valid m s h
  have parents := scene_parent_check m s es h he
  have titles := scene_title_count m s es h he
  have count : ¬ (es.filter (·.title)).length > 1 := by omega
  let run : Except LayoutError PUnit :=
    forIn es PUnit.unit (fun e _ => do
      if !e.title && !decide (fits p e.piece) then throw LayoutError.domain
      pure (ForInStep.yield PUnit.unit))
  cases hr : run with
  | ok out =>
    apply field_loop_fits p es out
    change run = .ok out
    exact hr
  | error err =>
    simp only [scene, hp, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, he, bind, Except.bind, parents, count] at h
    simp only [run, p, bind, Except.bind] at hr
    rw [hr] at h
    cases h

theorem field_loop_ok (p : Params) (es : List Entry)
    (fit : ∀ e ∈ es, e.title = false → fits p e.piece) :
    (forIn es PUnit.unit (fun e _ => do
      if !e.title && !decide (fits p e.piece) then throw LayoutError.domain
      pure (ForInStep.yield PUnit.unit)) : Except LayoutError PUnit) = .ok PUnit.unit := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have tail := ih (fun f hf => fit f (List.mem_cons_of_mem e hf))
    cases ht : e.title with
    | true =>
      simpa [List.forIn_cons, ht, bind, Except.bind, pure, Except.pure] using tail
    | false =>
      have hf := fit e (List.mem_cons_self ..) ht
      simpa [List.forIn_cons, hf, bind, Except.bind, pure, Except.pure] using tail

theorem scene_fields_partition (m : Model) (s : Scene) (es : List Entry)
    (h : scene m = .ok s) (he : entries m = .ok es) :
    fieldsDisjoint es = true := by
  let p := m.options.config.foldl (configure m.profile) (defaults m.profile)
  have hp := scene_params_valid m s h
  have parents := scene_parent_check m s es h he
  have titles := scene_title_count m s es h he
  have count : ¬ (es.filter (·.title)).length > 1 := by omega
  have fit := scene_fields_fit m s es h he
  let run : Except LayoutError PUnit :=
    forIn es PUnit.unit (fun e _ => do
      if !e.title && !decide (fits p e.piece) then throw LayoutError.domain
      pure (ForInStep.yield PUnit.unit))
  have loop : run = .ok PUnit.unit := by
    exact field_loop_ok p es fit
  cases hd : fieldsDisjoint es with
  | true => rfl
  | false =>
    simp only [scene, hp, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, he, bind, Except.bind, parents, count] at h
    simp only [run, p, bind, Except.bind] at loop
    rw [loop] at h
    simp [hd, bind, Except.bind] at h

theorem scene_constraints (m : Model) (s : Scene) (h : scene m = .ok s) :
    HardConstraints s.layoutDump := by
  obtain ⟨es, he⟩ := scene_entries_success m s h
  let p := m.options.config.foldl (configure m.profile) (defaults m.profile)
  have hp := scene_params_valid m s h
  have parents := scene_parent_check m s es h he
  have titles := scene_title_count m s es h he
  have count : ¬ (es.filter (·.title)).length > 1 := by omega
  have fit := scene_fields_fit m s es h he
  have partition := scene_fields_partition m s es h he
  have decoded := entries_decoded m es he
  have roots : ∀ e ∈ es, e.box.parent = "" ∧ e.box.role = .node :=
    fun e hem => ⟨scene_entry_parents m s es h he e hem, (decoded e hem).1⟩
  have loop : (forIn es PUnit.unit (fun e _ => do
      if !e.title && !decide (fits p e.piece) then throw LayoutError.domain
      pure (ForInStep.yield PUnit.unit)) : Except LayoutError PUnit) = .ok PUnit.unit :=
    field_loop_ok p es fit
  simp only [scene, hp, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, he, bind, Except.bind, parents, count] at h
  simp only [p, bind, Except.bind] at loop
  rw [loop] at h
  simp only [partition, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i height hh
      split at h
      · cases h
      · rename_i boxes hb
        split at h
        · cases h
        · rename_i items hi
          split at h
          · cases h
          · rename_i labels hl
            simp only [pure, Except.pure, Except.ok.injEq] at h
            cases h
            apply assembled_constraints p es boxes (labels.map (·.toLabel))
              w height hp hw hh hb roots fit partition titles
            intro l member
            obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp member
            exact label_loop_origins m es labels decoded hl sl hsl

def overlappingFields : Model :=
  { kind := "packet", profile := .cell,
    options := { profile := .cell, config := [("showBits", .boolean false)] },
    boxes := [
      { id := "a", shape := "field;start=0;end=0" },
      { id := "b", shape := "field;start=0;end=0" }] }

def parentOutsideField : Model :=
  { kind := "packet", profile := .cell,
    options := { profile := .cell, config := [("showBits", .boolean false)] },
    boxes := [
      { id := "a", shape := "field;start=0;end=0" },
      { id := "b", parent := "a", shape := "field;start=1;end=1" }] }

def inputTextBytes (m : Model) : Nat :=
  let labelBytes := (m.labels.map fun l => l.text.utf8ByteSize).sum
  m.boxes.foldl (fun n b =>
    if m.labels.any (fun l => l.owner == b.id) then n
    else n + (b.text.getD "").utf8ByteSize) labelBytes

/-- Packet placement is a structural pass with no iterative budget. -/
def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if m.boxes.length > m.options.limits.maxNodes then
    throw (.tooLarge m.options.limits.maxNodes m.boxes.length)
  let bytes := inputTextBytes m
  if bytes > m.options.limits.maxTextBytes then
    throw (.tooLarge m.options.limits.maxTextBytes bytes)
  match scene m with
  | .error e => throw (.geometry e)
  | .ok s => pure { scene := s, budgetExhausted := false }

theorem packet_valid (m : Model) (result : Layered.FamilyResult)
    (_hwf : WellFormed m) (_hlim : WithinLimits m)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump := by
  simp only [layout, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i s hs
        cases h
        exact scene_constraints m s hs

def duplicateTitles : Model :=
  { kind := "packet", profile := .cell,
    options := { profile := .cell },
    boxes := [{ id := "a", shape := "title" }, { id := "b", shape := "title" }] }

def PacketValidity : Prop :=
  ∀ (m : Model) (s : Layered.FamilyResult), WellFormed m → WithinLimits m →
    layout m = .ok s → HardConstraints s.scene.layoutDump

end Elegant.Kinds.Packet
