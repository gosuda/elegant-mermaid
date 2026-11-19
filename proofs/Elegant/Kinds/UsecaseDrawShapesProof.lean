import Elegant.Kinds.Usecase
import ElegantGeometry.Validator

set_option autoImplicit false

/-! Preservation of the hard constraints across the usecase caption/outline redraw.

`Usecase.layout` runs the exact-box family entry, projects cell attachments, then
redraws captions and outlines (`drawShapes`). Cell projection preserves the dump
(`Scene.projectCellAttachments_layoutDump`); `drawShapes` keeps canvas, boxes and
routes, and only rewrites group items (invisible to the dump) and owner-label
rectangles. Clauses over boxes and routes (C1, C2, C3, C4, C5, C6, C8a) transfer by
dump equalities; the two label clauses (C7, C8b) stay residuals stated for the
executed scenes. `Validator.C1` quantifies only over boxes, so it has no label part
and transfers fully. -/

namespace Elegant
namespace Kinds
namespace Usecase

/-- `drawShapes` rebuilds only the items and the labels of the scene. -/
theorem drawShapes_eq {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') :
    ∃ items labels, s' = { s with items := items, labels := labels } := by
  unfold drawShapes at h
  cases hf : s.items.foldlM (drawStep m s) ([], s.labels) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok res =>
    simp only [hf, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨res.1, res.2, h.symm⟩

/-- The redraw keeps every box. -/
theorem drawShapes_boxes {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') : s'.boxes = s.boxes := by
  obtain ⟨items, labels, h'⟩ := drawShapes_eq h
  rw [h']

/-- The redraw keeps every route. -/
theorem drawShapes_routes {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') : s'.routes = s.routes := by
  obtain ⟨items, labels, h'⟩ := drawShapes_eq h
  rw [h']

/-- The redraw keeps the canvas. -/
theorem drawShapes_canvas {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') : s'.canvas = s.canvas := by
  obtain ⟨items, labels, h'⟩ := drawShapes_eq h
  rw [h']

/-- The dump boxes are unchanged by the redraw. -/
theorem drawShapes_dump_boxes {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') :
    s'.layoutDump.boxes = s.layoutDump.boxes := by
  simp only [Scene.layoutDump, drawShapes_boxes h]

/-- The dump routes are unchanged by the redraw. -/
theorem drawShapes_dump_routes {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') :
    s'.layoutDump.routes = s.layoutDump.routes := by
  simp only [Scene.layoutDump, drawShapes_routes h]

/-- The dump canvas is unchanged by the redraw. -/
theorem drawShapes_dump_canvas {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') :
    s'.layoutDump.canvas = s.layoutDump.canvas := by
  simp only [Scene.layoutDump, drawShapes_canvas h]

/-- The items `drawStep` inspects for the first text: captions moved below the
figure for actors, unchanged otherwise. -/
def movedItems (m : Model) (g : Group) (box : ModelBox) (placed : Box) :
    List Primitive :=
  if isActor box.shape then g.items.map (moveCaption m.options.profile placed.rect)
  else g.items

/-- `g` is the redraw witness that moves the label `rect` of `owner`: both lookups
succeed, and `rect` is the first text rectangle of the moved items. -/
def MovedBy (m : Model) (s : Scene) (g : Group) (owner : String) (rect : Rect) : Prop :=
  ∃ box : ModelBox, ∃ placed : Box,
    m.boxes.find? (·.id == g.owner) = some box ∧
    s.boxes.find? (·.id == g.owner) = some placed ∧
    g.owner = owner ∧
    ∃ r, firstText (movedItems m g box placed) = some r ∧ rect = r

/-- Caption band offset of an actor box: distance from the owner box top to the
caption, matching `captionRect` and `actorMetrics` (`figureH + gap + padding`). -/
private def ucaseDrawCaptionTop : Profile → Int
  | .vector => 88 * 64
  | .cell => 7

/-- Caption side padding of an actor box, matching `captionRect` and `actorMetrics`. -/
private def ucaseDrawCaptionPad : Profile → Int
  | .vector => 8 * 64
  | .cell => 1

/-- `captionRect` in terms of the band constants. -/
private theorem ucaseDraw_captionRect_eq (p : Profile) (box text : Rect) :
    captionRect p box text = ⟨box.x + ucaseDrawCaptionPad p,
      box.y + ucaseDrawCaptionTop p, box.w - 2 * ucaseDrawCaptionPad p, text.h⟩ := by
  cases p <;> rfl

/-- The first text of the moved items is the moved first text of the items. -/
private theorem ucaseDraw_firstText_map {p : Profile} {r : Rect}
    {items : List Primitive} {rect : Rect}
    (h : firstText (items.map (moveCaption p r)) = some rect) :
    ∃ t : SceneText, firstText items = some t.rect ∧
      rect = captionRect p r t.rect := by
  induction items with
  | nil => simp [firstText] at h
  | cons hd tl ih =>
    cases hd with
    | text t =>
      refine ⟨t, by simp [firstText], ?_⟩
      have h2 : captionRect p r t.rect = rect := by
        simpa [firstText, moveCaption] using h
      exact h2.symm
    | rect a b =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | roundRect a b c =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | ellipse a b c d e =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | polygon a b =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | polyline a b c =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | path a b =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | markerRef a b c =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩
    | symbolRef a b c =>
      have h' : firstText (tl.map (moveCaption p r)) = some rect := by
        simpa [firstText, moveCaption] using h
      obtain ⟨t, ht, hr⟩ := ih h'
      exact ⟨t, by simpa [firstText] using ht, hr⟩

/-- `l` traces back to a source label `l₀`: identity fields are kept, and the
rectangle either stays or was set by a redraw witness. -/
def TracesTo (m : Model) (s : Scene) (src : List SceneLabel) (l : SceneLabel) : Prop :=
  ∃ l₀ ∈ src, l.id = l₀.id ∧ l.owner = l₀.owner ∧ l.text = l₀.text ∧
    l.lines = l₀.lines ∧
    (l.rect = l₀.rect ∨ ∃ g ∈ s.items, MovedBy m s g l.owner l.rect)

/-- Every label traces to itself. -/
theorem tracesTo_self {m : Model} {s : Scene} {src : List SceneLabel} {l : SceneLabel}
    (h : l ∈ src) : TracesTo m s src l := by
  refine ⟨l, h, rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- Destructure a successful `Except` bind. -/
private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- `drawStep` preserves the trace property of the label list. -/
theorem drawStep_trace {m : Model} {s : Scene} {src : List SceneLabel}
    {acc : List Group × List SceneLabel} {g : Group} {acc' : List Group × List SceneLabel}
    (hg : g ∈ s.items)
    (hacc : ∀ l ∈ acc.2, TracesTo m s src l)
    (h : drawStep m s acc g = .ok acc') :
    ∀ l ∈ acc'.2, TracesTo m s src l := by
  unfold drawStep at h
  cases hf1 : m.boxes.find? (·.id == g.owner) with
  | none =>
    simp only [hf1] at h
    simp only [pure, Except.pure] at h
    injection h with h'
    subst h'
    exact hacc
  | some box =>
    cases hf2 : s.boxes.find? (·.id == g.owner) with
    | none =>
      simp only [hf1, hf2] at h
      simp only [pure, Except.pure] at h
      injection h with h'
      subst h'
      exact hacc
    | some placed =>
      simp only [hf1, hf2] at h
      obtain ⟨shapes, _hout, hres⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hres
      subst hres
      cases hft : firstText
          (if isActor box.shape then
            g.items.map (moveCaption m.options.profile placed.rect) else g.items) with
      | none =>
        intro l hl
        exact hacc l hl
      | some r =>
        intro l hl
        simp only [List.mem_map] at hl
        obtain ⟨l', hl', rfl⟩ := hl
        by_cases hown : l'.owner == g.owner
        · simp only [hown, ↓reduceIte]
          obtain ⟨l₀, hl₀, hid, hown', htext, hlines, _⟩ := hacc l' hl'
          refine ⟨l₀, hl₀, hid, hown', htext, hlines, Or.inr ⟨g, hg, box, placed,
            hf1, hf2, (beq_iff_eq.mp hown).symm, r, hft, rfl⟩⟩
        · simp only [hown]
          exact hacc l' hl'

/-- The fold preserves traces: every label of the result traces to the initial
label list, with redraw witnesses inside `s.items`. -/
theorem foldlM_trace (m : Model) (s : Scene) (src : List SceneLabel)
    (items : List Group) (acc₀ acc' : List Group × List SceneLabel)
    (hsub : ∀ g ∈ items, g ∈ s.items)
    (hf : items.foldlM (drawStep m s) acc₀ = .ok acc')
    (hacc : ∀ l ∈ acc₀.2, TracesTo m s src l) :
    ∀ l ∈ acc'.2, TracesTo m s src l := by
  induction items generalizing acc₀ acc' with
  | nil =>
    simp only [List.foldlM, pure, Except.pure] at hf
    injection hf with h'
    subst h'
    exact hacc
  | cons g gs ih =>
    simp only [List.foldlM] at hf
    cases hstep : drawStep m s acc₀ g with
    | error e => simp [hstep, bind, Except.bind] at hf
    | ok acc1 =>
      simp only [hstep, bind, Except.bind] at hf
      have hg : g ∈ s.items := hsub g (List.Mem.head gs)
      have hsub' : ∀ h ∈ gs, h ∈ s.items := fun h hh =>
        hsub h (List.mem_cons_of_mem g hh)
      have hacc1 : ∀ l ∈ acc1.2, TracesTo m s src l :=
        drawStep_trace hg hacc hstep
      exact ih acc1 acc' hsub' hf hacc1
/-- Exact label spec of the redraw: every result label keeps its identity fields
and either keeps its rectangle or was moved by a group witness. -/
theorem drawShapes_labels_spec {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') :
    ∀ l ∈ s'.labels, ∃ l₀ ∈ s.labels, l.id = l₀.id ∧ l.owner = l₀.owner ∧
      l.text = l₀.text ∧ l.lines = l₀.lines ∧
      (l.rect = l₀.rect ∨ ∃ g ∈ s.items, MovedBy m s g l.owner l.rect) := by
  unfold drawShapes at h
  cases hfold : s.items.foldlM (drawStep m s) ([], s.labels) with
  | error e => simp [hfold, bind, Except.bind] at h
  | ok res =>
    simp only [hfold, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    have hlabels : s'.labels = res.2 := by rw [← h]
    intro l hl
    rw [hlabels] at hl
    have htrace := foldlM_trace m s s.labels s.items ([], s.labels) res
      (fun g hg => hg) hfold (fun l hl => tracesTo_self hl)
    exact htrace l hl

/-- The auxiliary ancestor walk depends only on boxes. -/
theorem dump_go_congr {d₁ d₂ : LayoutDump}
    (hb : d₁.boxes = d₂.boxes) (n : Nat) (s : String) :
    LayoutDump.ancestors.go d₁ n s = LayoutDump.ancestors.go d₂ n s := by
  induction n generalizing s with
  | zero => simp only [LayoutDump.ancestors.go]
  | succ n ih =>
    simp only [LayoutDump.ancestors.go, LayoutDump.box?, hb, ih]

 /-- Ancestor walks see only boxes, so equal boxes give equal ancestors. -/
 theorem dump_ancestors_congr {d₁ d₂ : LayoutDump}
     (hb : d₁.boxes = d₂.boxes) (id : String) :
     d₁.ancestors id = d₂.ancestors id := by
  unfold LayoutDump.ancestors
  rw [hb]
  exact dump_go_congr hb _ _
 
 /-- Route scopes see only boxes, so equal boxes give equal scopes. -/
 theorem dump_routeScope_congr {d₁ d₂ : LayoutDump}
     (hb : d₁.boxes = d₂.boxes) (r : Route) :
     d₁.routeScope r = d₂.routeScope r := by
   have ha : ∀ id, d₁.ancestors id = d₂.ancestors id :=
     fun id => dump_ancestors_congr hb id
   simp only [LayoutDump.routeScope, ha]


/-- C1 (canvas containment, boxes only) survives the redraw. -/
theorem drawShapes_C1 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C1 s.layoutDump) :
    Validator.C1 s'.layoutDump := by
  have hb : s'.layoutDump.boxes = s.layoutDump.boxes := drawShapes_dump_boxes h
  have hcv : s'.layoutDump.canvas = s.layoutDump.canvas := drawShapes_dump_canvas h
  unfold Validator.C1 Validator.canvasRect at hc ⊢
  rw [hb, hcv] at ⊢
  exact hc

/-- The label-owner ancestor scope reads only routes, boxes, and the owner name;
the redraw preserves all three, so scopes of equally-owned labels agree. -/
theorem labelOwnerAnc_congr {d₁ d₂ : LayoutDump} (hr : d₁.routes = d₂.routes)
    (hb : d₁.boxes = d₂.boxes) {l₁ l₂ : Label} (ho : l₁.owner = l₂.owner) :
    d₁.labelOwnerAnc l₁ = d₂.labelOwnerAnc l₂ := by
  unfold LayoutDump.labelOwnerAnc
  rw [hr]
  have ha : ∀ id, d₁.ancestors id = d₂.ancestors id :=
    fun id => dump_ancestors_congr hb id
  simp only [ha]
  rw [ho]

/-- C2 (exclusive siblings, boxes only) survives the redraw. -/
theorem drawShapes_C2 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C2 s.layoutDump) :
    Validator.C2 s'.layoutDump := by
  have hb : s'.layoutDump.boxes = s.layoutDump.boxes := drawShapes_dump_boxes h
  unfold Validator.C2 at hc ⊢
  rw [hb] at ⊢
  exact hc

/-- C3 (parent containment, boxes only) survives the redraw. -/
theorem drawShapes_C3 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C3 s.layoutDump) :
    Validator.C3 s'.layoutDump := by
  have hb : s'.layoutDump.boxes = s.layoutDump.boxes := drawShapes_dump_boxes h
  unfold Validator.C3 LayoutDump.box? at hc ⊢
  rw [hb] at ⊢
  exact hc

/-- C4 (orthogonality, routes only) survives the redraw. -/
theorem drawShapes_C4 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C4 s.layoutDump) :
    Validator.C4 s'.layoutDump := by
  have hr : s'.layoutDump.routes = s.layoutDump.routes := drawShapes_dump_routes h
  unfold Validator.C4 at hc ⊢
  rw [hr] at ⊢
  exact hc

/-- C5 (route ports, routes and boxes) survives the redraw. -/
theorem drawShapes_C5 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C5 s.layoutDump) :
    Validator.C5 s'.layoutDump := by
  have hb : s'.layoutDump.boxes = s.layoutDump.boxes := drawShapes_dump_boxes h
  have hr : s'.layoutDump.routes = s.layoutDump.routes := drawShapes_dump_routes h
  unfold Validator.C5 LayoutDump.box? at hc ⊢
  rw [hr, hb] at ⊢
  exact hc

/-- C6 (route clearance, routes and boxes) survives the redraw. -/
theorem drawShapes_C6 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C6 s.layoutDump) :
    Validator.C6 s'.layoutDump := by
  have hb : s'.layoutDump.boxes = s.layoutDump.boxes := drawShapes_dump_boxes h
  have hr : s'.layoutDump.routes = s.layoutDump.routes := drawShapes_dump_routes h
  have hs : ∀ r, s'.layoutDump.routeScope r = s.layoutDump.routeScope r :=
    fun r => dump_routeScope_congr hb r
  unfold Validator.C6 at hc ⊢
  simp only [hr, hb, hs] at ⊢
  exact hc

/-- C8a (frame/box clearance, boxes only) survives the redraw. -/
theorem drawShapes_C8a {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s') (hc : Validator.C8a s.layoutDump) :
    Validator.C8a s'.layoutDump := by
  have hb : s'.layoutDump.boxes = s.layoutDump.boxes := drawShapes_dump_boxes h
  have ha : ∀ id, s'.layoutDump.ancestors id = s.layoutDump.ancestors id :=
    fun id => dump_ancestors_congr hb id
  unfold Validator.C8a at hc ⊢
  simp only [hb, ha] at ⊢
  exact hc

/-- Residual for C7: every label the redraw moved keeps label/box clearance.
A moved label is one whose witness group `w ∈ s.items` set its rectangle to the
first text of the moved items (`MovedBy`); that rectangle is an actor caption
below the figure, a use case label inside the ellipse, or a boundary title.
Unmoved labels are covered by the base clause, so this is the single geometric
fact still missing for the executed layout. -/
def drawShapesMovedC7 (m : Model) (s s' : Scene) : Prop :=
  ∀ l ∈ s'.labels, ∀ b ∈ s'.layoutDump.boxes, b.exclusive = true →
    (∃ w ∈ s.items, MovedBy m s w l.owner l.rect) →
    b.id ∉ s'.layoutDump.labelOwnerAnc (SceneLabel.toLabel l) →
    ¬ l.rect.meetsInterior b.rect

/-- Residual for C8b: every label the redraw moved keeps frame/label clearance.
Same moved-label positions as `drawShapesMovedC7`; unmoved labels are covered by
the base clause. -/
def drawShapesMovedC8b (m : Model) (s s' : Scene) : Prop :=
  ∀ g ∈ s'.layoutDump.boxes, g.role = "group" →
    ∀ l ∈ s'.labels, (∃ w ∈ s.items, MovedBy m s w l.owner l.rect) →
      Disjoint g.rect l.rect ∨ g.rect.StrictInside l.rect

/-- The adapter's size equation for executed scenes: every actor box is placed
with exactly the dimensions `nodeSize` computes (figure plus caption, exact),
and every first text of an actor group fits the caption band below the figure.
`Usecase.sizes` emits exactly these `nodeSize` entries with `exact = true`, so
this is the executed-scene form of that equation. -/
def ActorCaptionFit (m : Model) (s : Scene) : Prop :=
  ∀ box : ModelBox, box ∈ m.boxes → isActor box.shape = true →
    ∀ placed : Box, s.boxes.find? (fun b => b.id == box.id) = some placed →
      ∃ sz : Size, nodeSize m.options.profile box.shape (Common.boxText m box) =
          .ok (some (sz, true)) ∧
        placed.rect.w = sz.w ∧ placed.rect.h = sz.h ∧
        ∀ g ∈ s.items, g.owner = box.id →
          ∀ t : SceneText, firstText g.items = some t.rect →
            t.rect.h + ucaseDrawCaptionTop m.options.profile +
              ucaseDrawCaptionPad m.options.profile ≤ sz.h

/-- A moved actor caption lands strictly inside its owner placed box: the band
offset and padding are positive, and the size equation reserves room for the
figure plus the caption text. -/
theorem movedCaption_insideOwner {m : Model} {s : Scene} {g : Group}
    {rect : Rect} {box : ModelBox} {placed : Box}
    (hboxmem : box ∈ m.boxes)
    (hactor : isActor box.shape = true)
    (hplaced : s.boxes.find? (fun b => b.id == box.id) = some placed)
    (hg : g ∈ s.items) (hgown : g.owner = box.id)
    (hft : firstText (movedItems m g box placed) = some rect)
    (hfit : ActorCaptionFit m s) :
    placed.rect.StrictInside rect := by
  have hmoved : movedItems m g box placed =
      g.items.map (moveCaption m.options.profile placed.rect) := by
    simp [movedItems, hactor]
  rw [hmoved] at hft
  obtain ⟨t, ht, hrect⟩ := ucaseDraw_firstText_map hft
  obtain ⟨sz, _hns, hwd, hht, htxt⟩ := hfit box hboxmem hactor placed hplaced
  have hineq := htxt g hg hgown t ht
  rw [hrect, ucaseDraw_captionRect_eq]
  have hpad : 0 < ucaseDrawCaptionPad m.options.profile := by
    cases m.options.profile <;> decide
  have htop : 0 < ucaseDrawCaptionTop m.options.profile := by
    cases m.options.profile <;> decide
  simp only [Rect.StrictInside]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- C7 survives the redraw: unmoved labels reuse the base clause through the
label-scope congruence; moved labels are exactly `drawShapesMovedC7`. -/
theorem drawShapes_C7 {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s')
    (hc7 : drawShapesMovedC7 m s s') (hc : Validator.C7 s.layoutDump) :
    Validator.C7 s'.layoutDump := by
  intro l' hl' b hb' hex hnotin
  have hlabels : s'.layoutDump.labels = s'.labels.map (·.toLabel) := rfl
  rw [hlabels] at hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  have hb2 : b ∈ s.layoutDump.boxes := by
    rw [← drawShapes_dump_boxes h]; exact hb'
  have hspec := drawShapes_labels_spec h l hl
  obtain ⟨l₀, hl₀, _hid, hown, _htext, _hlines, hrect⟩ := hspec
  have hAnc : s'.layoutDump.labelOwnerAnc (SceneLabel.toLabel l) =
      s.layoutDump.labelOwnerAnc (SceneLabel.toLabel l₀) :=
    labelOwnerAnc_congr (drawShapes_dump_routes h) (drawShapes_dump_boxes h) hown
  have hnotinP : b.id ∉ s.layoutDump.labelOwnerAnc (SceneLabel.toLabel l₀) := by
    rw [← hAnc]; exact hnotin
  have hl₀' : SceneLabel.toLabel l₀ ∈ s.layoutDump.labels := by
    show SceneLabel.toLabel l₀ ∈ s.labels.map (·.toLabel)
    exact List.mem_map.mpr ⟨l₀, hl₀, rfl⟩
  rcases hrect with heq | hmv
  · have hthis := hc (SceneLabel.toLabel l₀) hl₀' b hb2 hex hnotinP
    intro hmeet
    apply hthis
    rw [heq] at hmeet
    exact hmeet
  · exact hc7 l hl b hb' hex hmv hnotin

/-- C8b survives the redraw: unmoved labels reuse the base clause; moved labels
are exactly `drawShapesMovedC8b`. -/
theorem drawShapes_C8b {m : Model} {s s' : Scene}
    (h : drawShapes m s = .ok s')
    (hc8b : drawShapesMovedC8b m s s') (hc : Validator.C8b s.layoutDump) :
    Validator.C8b s'.layoutDump := by
  intro g hg hrole l' hl'
  have hlabels : s'.layoutDump.labels = s'.labels.map (·.toLabel) := rfl
  rw [hlabels] at hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  have hg2 : g ∈ s.layoutDump.boxes := by
    rw [← drawShapes_dump_boxes h]; exact hg
  have hspec := drawShapes_labels_spec h l hl
  obtain ⟨l₀, hl₀, _hid, _hown, _htext, _hlines, hrect⟩ := hspec
  have hl₀' : SceneLabel.toLabel l₀ ∈ s.layoutDump.labels := by
    show SceneLabel.toLabel l₀ ∈ s.labels.map (·.toLabel)
    exact List.mem_map.mpr ⟨l₀, hl₀, rfl⟩
  rcases hrect with heq | hmv
  · have hthis := hc g hg2 hrole (SceneLabel.toLabel l₀) hl₀'
    rw [← heq] at hthis
    exact hthis
  · exact hc8b g hg hrole l hl hmv

/-- The usecase caption/outline redraw keeps the hard constraints: the family scene
`base`, the projected scene `proj`, and the redrawn scene `drawn` are the equations
of the executed `Usecase.layout`; label clauses come from the executed residuals. -/
theorem drawShapes_hardConstraints {m : Model} {base proj drawn : Scene}
    (hproj : base.projectCellAttachments (Common.routeMarkers m) = proj)
    (hdraw : drawShapes m proj = .ok drawn)
    (hbase : HardConstraints base.layoutDump)
    (hc7 : drawShapesMovedC7 m proj drawn)
    (hc8b : drawShapesMovedC8b m proj drawn) :
    HardConstraints drawn.layoutDump := by
  have hpd : proj.layoutDump = base.layoutDump := by
    rw [← hproj, Scene.projectCellAttachments_layoutDump]
  have hpbase : HardConstraints proj.layoutDump := by
    rw [hpd]
    exact hbase
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7p, hc8⟩ := hpbase
  obtain ⟨hc8a, hc8bp⟩ := hc8
  exact ⟨drawShapes_C1 hdraw hc1, drawShapes_C2 hdraw hc2, drawShapes_C3 hdraw hc3,
    drawShapes_C4 hdraw hc4, drawShapes_C5 hdraw hc5, drawShapes_C6 hdraw hc6,
    drawShapes_C7 hdraw hc7 hc7p, drawShapes_C8a hdraw hc8a,
    drawShapes_C8b hdraw hc8b hc8bp⟩

end Usecase
end Kinds
end Elegant
