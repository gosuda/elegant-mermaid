import Elegant.Model
import ElegantGeometry.Basic
import ElegantGeometry.Validator

namespace Elegant

inductive GroupRole where
  | decor | group | edge | node
  deriving DecidableEq, Repr

inductive TextRole where
  | title | label | body
  deriving DecidableEq, Repr

inductive Align where
  | start | middle | «end»
  deriving DecidableEq, Repr

inductive LineStyle where
  | solid | dashed | dotted | double
  deriving DecidableEq, Repr

inductive StrokeWidth where
  | normal | emphasis | units (value : Int)
  deriving DecidableEq, Repr

inductive MarkerAxis where
  | positiveX | negativeX | positiveY | negativeY
  deriving DecidableEq, Repr

structure Paint where
  style : String
  series : Fin 12 := 0
  width : StrokeWidth := .normal
  line : LineStyle := .solid
  deriving DecidableEq, Repr

inductive PathCommand where
  | M (point : Point)
  | L (point : Point)
  | C (control1 control2 point : Point)
  | A (center : Point) (radius start sweep : Int)
  | Z
  deriving DecidableEq, Repr

structure TextRun where
  text : String
  bold : Bool := false
  italic : Bool := false
  deriving DecidableEq, Repr

structure SceneText where
  rect : Rect
  role : TextRole
  size : Int
  align : Align
  style : String
  series : Fin 12 := 0
  lines : List (List TextRun)
  deriving DecidableEq, Repr

inductive Primitive where
  | rect (rect : Rect) (paint : Paint)
  | roundRect (rect : Rect) (r : Int) (paint : Paint)
  | ellipse (cx cy rx ry : Int) (paint : Paint)
  | polygon (points : List Point) (paint : Paint)
  | polyline (points : List Point) (corner : Int) (paint : Paint)
  | path (commands : List PathCommand) (paint : Paint)
  | text (value : SceneText)
  | markerRef (marker : String) (point : Point) (axis : MarkerAxis)
  | symbolRef (symbol : String) (point : Point) (style : String)
  deriving DecidableEq, Repr

structure Group where
  role : GroupRole
  owner : String
  items : List Primitive
  deriving DecidableEq, Repr

structure SceneLabel extends Label where
  text : String
  deriving DecidableEq, Repr

/-- Ephemeral semantic marker attribution supplied during scene assembly. -/
structure RouteMarkers where
  owner : String
  startMarker : String
  endMarker : String
  deriving DecidableEq, Repr

structure Scene where
  kind : String
  profile : Profile := .vector
  options : Options := {}
  canvas : Size
  boxes : List Box := []
  routes : List Route := []
  labels : List SceneLabel := []
  items : List Group := []
  deriving DecidableEq, Repr

def Scene.layoutDump (s : Scene) : LayoutDump :=
  ⟨s.canvas, s.boxes, s.routes, s.labels.map (·.toLabel)⟩

namespace Scene

/-- Project a closed geometric attachment onto the last painted cell of its box. -/
private def attachment (s : Scene) (id : String) (p : Point) : Point :=
  match s.boxes.find? (fun b => b.id == id) with
  | none => p
  | some b =>
    let r := b.rect
    if 0 < r.w ∧ 0 < r.h ∧ r.x ≤ p.x ∧ p.x ≤ r.x + r.w ∧
        r.y ≤ p.y ∧ p.y ≤ r.y + r.h then
      ⟨if p.x = r.x + r.w then p.x - 1 else p.x,
       if p.y = r.y + r.h then p.y - 1 else p.y⟩
    else p

/-- Append a distinct point, keeping zero-length segments out of the drawing. -/
private def appendPoint (ps : List Point) (p : Point) : List Point :=
  if ps.getLast? = some p then ps else ps ++ [p]

/-- Keep the endpoint-adjacent direction; the one-point tie is horizontal first. -/
private def projectLine (ps : List Point) (a b : Point) : List Point :=
  let count := max 2 ps.length
  ((List.range (count - 1)).foldl (fun out j =>
    let i := j + 1
    let prev := (out.getLast?).getD a
    let oldA := (ps[i - 1]?).getD b
    let oldB := (ps[min i (ps.length - 1)]?).getD oldA
    let next := if i = count - 1 then b else oldB
    let horizontal := oldA.y == oldB.y
    let horizontal := if i = count - 1 ∧ i ≠ 1 then !horizontal else horizontal
    let out := if (oldA.x = oldB.x ∨ oldA.y = oldB.y) ∧
        prev.x ≠ next.x ∧ prev.y ≠ next.y then
      appendPoint out (if horizontal then ⟨next.x, prev.y⟩ else ⟨prev.x, next.y⟩)
      else out
    appendPoint out next) [a])

/-- Only a full route polyline in its owning edge group is projected. -/
private def projectPrimitive (s : Scene) (markers : List RouteMarkers) (grp : Group) (index : Nat) (p : Primitive) : Primitive :=
  if grp.role ≠ .edge then p else
  match s.routes.find? (fun r => r.id == grp.owner) with
  | none => p
  | some r =>
    match r.points.head?, r.points.getLast? with
    | some first, some last =>
      let a := attachment s r.fromId first
      let b := attachment s r.toId last
      match p with
      | .polyline ps corner paint =>
        if ps.head? = some first ∧ ps.getLast? = some last ∧
            (a ≠ first ∨ b ≠ last) then .polyline (projectLine ps a b) corner paint else p
      | .markerRef name pos axis =>
        let metadata := markers.find? (fun m => m.owner == r.id)
        let earlier := (grp.items.take index).any (fun item =>
          match item with | .markerRef _ _ _ => true | _ => false)
        let target : Bool := match metadata with
          | some m => m.endMarker == name && (m.startMarker != name || earlier)
          | none => earlier
        let attachment := if pos = first ∧ pos = last then (if target then b else a)
          else if pos = first then a else if pos = last then b else pos
        .markerRef name attachment axis
      | _ => p
    | _, _ => p

/-- Project attachments once, after the complete family scene has been assembled.
Canonical geometry remains closed; only the cell display list changes. -/
def projectCellAttachments (s : Scene) (markers : List RouteMarkers) : Scene :=
  if s.profile = .cell then
    { s with items := s.items.map fun grp =>
        { grp with items := grp.items.zipIdx.map fun (p, i) => projectPrimitive s markers grp i p } }
  else s

theorem projectCellAttachments_layoutDump (s : Scene) (markers : List RouteMarkers) :
    (projectCellAttachments s markers).layoutDump = s.layoutDump := by
  unfold projectCellAttachments
  split <;> rfl

theorem projectCellAttachments_profile (s : Scene) (markers : List RouteMarkers) :
    (projectCellAttachments s markers).profile = s.profile := by
  unfold projectCellAttachments
  split <;> rfl

theorem projectCellAttachments_canvas (s : Scene) (markers : List RouteMarkers) :
    (projectCellAttachments s markers).canvas = s.canvas := by
  unfold projectCellAttachments
  split <;> rfl

theorem projectCellAttachments_options (s : Scene) (markers : List RouteMarkers) :
    (projectCellAttachments s markers).options = s.options := by
  unfold projectCellAttachments
  split <;> rfl

theorem projectCellAttachments_vector (s : Scene) (markers : List RouteMarkers)
    (h : s.profile ≠ .cell) : projectCellAttachments s markers = s := by
  simp [projectCellAttachments, h]

theorem projectCellAttachments_items (s : Scene) (markers : List RouteMarkers)
    (h : s.profile = .cell) :
    (projectCellAttachments s markers).items =
      s.items.map (fun grp =>
        { grp with items := grp.items.zipIdx.map (fun (p, i) => projectPrimitive s markers grp i p) }) := by
  simp [projectCellAttachments, h]

#guard projectLine [⟨4, 4⟩] ⟨3, 4⟩ ⟨4, 3⟩ =
  [⟨3, 4⟩, ⟨4, 4⟩, ⟨4, 3⟩]
#guard projectLine [⟨0, 0⟩, ⟨0, 4⟩] ⟨0, 0⟩ ⟨0, 3⟩ =
  [⟨0, 0⟩, ⟨0, 3⟩]

private def projectionScene : Scene :=
  { kind := "test", profile := .cell, canvas := ⟨8, 8⟩
    boxes := [⟨"a", "node", ⟨1, 1, 3, 3⟩, "", true⟩,
      ⟨"b", "node", ⟨4, 4, 2, 2⟩, "", true⟩]
    routes := [⟨"e", "a", "b", true, [⟨4, 4⟩]⟩]
    }

#guard attachment projectionScene "a" ⟨4, 4⟩ = ⟨3, 3⟩
#guard attachment projectionScene "b" ⟨4, 4⟩ = ⟨4, 4⟩
#guard attachment projectionScene "a" ⟨1, 1⟩ = ⟨1, 1⟩
#guard attachment projectionScene "a" ⟨4, 2⟩ = ⟨3, 2⟩
#guard attachment projectionScene "a" ⟨2, 4⟩ = ⟨2, 3⟩
#guard projectPrimitive projectionScene [⟨"e", "", "point"⟩] ⟨.edge, "e", []⟩ 0
    (.markerRef "point" ⟨4, 4⟩ .positiveX) =
  .markerRef "point" ⟨4, 4⟩ .positiveX
#guard projectPrimitive projectionScene [⟨"e", "point", ""⟩]
    ⟨.edge, "e", []⟩ 0 (.markerRef "point" ⟨4, 4⟩ .positiveX) =
  .markerRef "point" ⟨3, 3⟩ .positiveX
#guard projectPrimitive projectionScene [⟨"e", "", "point"⟩] ⟨.decor, "e", []⟩ 0
    (.polyline [⟨4, 4⟩] 0 { style := "edge" }) =
  .polyline [⟨4, 4⟩] 0 { style := "edge" }


end Scene

/-- Cell geometry uses half-open extents: a point names a cell, not a rectangle edge. -/
def Size.containsCell (extent : Size) (p : Point) : Bool :=
  decide (0 ≤ p.x ∧ p.x < extent.w ∧ 0 ≤ p.y ∧ p.y < extent.h)

def Size.containsCellRect (extent : Size) (r : Rect) : Bool :=
  decide (0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧
    r.x + r.w ≤ extent.w ∧ r.y + r.h ≤ extent.h)

/-- A conservative bound for curved geometry includes its control hull. Arc commands include
the whole circle, so a partial arc cannot evade the check through its endpoints. -/
def PathCommand.cellBounds (extent : Size) : PathCommand → Bool
  | .M p | .L p => Size.containsCell extent p
  | .C a b p => Size.containsCell extent a && Size.containsCell extent b && Size.containsCell extent p
  | .A c r _ _ => decide (0 ≤ r) &&
      Size.containsCell extent ⟨c.x - r, c.y - r⟩ &&
      Size.containsCell extent ⟨c.x + r, c.y + r⟩
  | .Z => true

/-- Bounds of actual scene primitives, including decor items absent from `layoutDump`.
Markers and symbols occupy their anchor cell in the cell renderer. Rectangles use cell
counts; polygon and path coordinates name cells and therefore require strict upper bounds. -/
def Primitive.cellBounds (extent : Size) : Primitive → Bool
  | .rect r _ | .roundRect r _ _ => Size.containsCellRect extent r
  | .ellipse cx cy rx ry _ =>
      decide (0 ≤ rx ∧ 0 ≤ ry) &&
      Size.containsCell extent ⟨cx - rx, cy - ry⟩ &&
      Size.containsCell extent ⟨cx + rx, cy + ry⟩
  | .polygon ps _ | .polyline ps _ _ => ps.all (Size.containsCell extent)
  | .path cs _ => cs.all (PathCommand.cellBounds extent)
  | .text t => Size.containsCellRect extent t.rect
  | .markerRef _ p _ | .symbolRef _ p _ => Size.containsCell extent p

/-- Executable scene invariant, independent of the relation-only dump validator.
Every group participates, regardless of role or ownership. -/
def Scene.primitiveBoundsCheck (s : Scene) : Bool :=
  decide (0 ≤ s.canvas.w ∧ 0 ≤ s.canvas.h) &&
    s.items.all (fun group => group.items.all (Primitive.cellBounds s.canvas))

def Scene.PrimitiveBounds (s : Scene) : Prop :=
  s.primitiveBoundsCheck = true

/-- The invariant checks actual items, not a separately authored list of bounding boxes. -/
theorem Scene.primitiveBounds_item {s : Scene} (h : s.PrimitiveBounds)
    {group : Group} (hg : group ∈ s.items) {item : Primitive} (hi : item ∈ group.items) :
    item.cellBounds s.canvas = true := by
  have hs : s.items.all (fun group => group.items.all (Primitive.cellBounds s.canvas)) = true := by
    simp only [Scene.PrimitiveBounds, Scene.primitiveBoundsCheck,
      Bool.and_eq_true_iff] at h
    exact h.2
  exact (List.all_eq_true.mp (List.all_eq_true.mp hs group hg)) item hi

namespace Scene

private theorem mem_of_head? {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    simp only [List.head?, Option.some.injEq] at h
    subst h
    exact List.Mem.head xs

private theorem mem_of_mem_zipIdx {α : Type} {l : List α} {x : α} {i : Nat} (h : (x, i) ∈ l.zipIdx) :
    x ∈ l :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp h)

private theorem containsCell_mix (extent : Size) (p1 p2 : Point)
    (h1 : Size.containsCell extent p1 = true) (h2 : Size.containsCell extent p2 = true) :
    Size.containsCell extent ⟨p1.x, p2.y⟩ = true := by
  unfold Size.containsCell at *
  simp only [decide_eq_true_iff] at *
  omega

private theorem appendPoint_mem (ps : List Point) (p q : Point) :
    q ∈ appendPoint ps p ↔ q ∈ ps ∨ q = p := by
  unfold appendPoint
  split
  · rename_i heq
    have hq_in : p ∈ ps := List.mem_of_getLast? heq
    constructor
    · intro hq
      exact Or.inl hq
    · intro hq
      rcases hq with h | rfl
      · exact h
      · exact hq_in
  · simp only [List.mem_append, List.mem_singleton]

private theorem appendPoint_containsCell {extent : Size} {ps : List Point} {p : Point}
    (hps : ∀ q ∈ ps, Size.containsCell extent q = true)
    (hp : Size.containsCell extent p = true) :
    ∀ q ∈ appendPoint ps p, Size.containsCell extent q = true := by
  intro q hq
  rw [appendPoint_mem] at hq
  rcases hq with h | rfl
  · exact hps q h
  · exact hp

private theorem containsCell_mix_ite {extent : Size} {p1 p2 : Point} {h : Bool}
    (h1 : Size.containsCell extent p1 = true) (h2 : Size.containsCell extent p2 = true) :
    Size.containsCell extent (if h then ⟨p1.x, p2.y⟩ else ⟨p2.x, p1.y⟩) = true := by
  cases h with
  | false => exact containsCell_mix extent p2 p1 h2 h1
  | true => exact containsCell_mix extent p1 p2 h1 h2

private theorem ite_appendPoint_containsCell {extent : Size} {out : List Point} {bend : Point} {cond : Prop} [Decidable cond]
    (hout : ∀ p ∈ out, Size.containsCell extent p = true)
    (hbend : Size.containsCell extent bend = true) :
    ∀ p ∈ (if cond then appendPoint out bend else out), Size.containsCell extent p = true := by
  intro p hp
  by_cases h : cond
  · rw [ite_eq_left h] at hp
    rw [appendPoint_mem] at hp
    rcases hp with hp | rfl
    · exact hout p hp
    · exact hbend
  · rw [ite_eq_right h] at hp
    exact hout p hp

private theorem foldl_projectLine_step_containsCell (ps : List Point) (a b : Point) (count : Nat) (extent : Size)
    (ha : Size.containsCell extent a = true)
    (hb : Size.containsCell extent b = true)
    (hps : ∀ p ∈ ps, Size.containsCell extent p = true)
    (l : List Nat) (out : List Point)
    (hout : ∀ p ∈ out, Size.containsCell extent p = true) :
    ∀ p ∈ l.foldl (fun out j =>
      let i := j + 1
      let prev := (out.getLast?).getD a
      let oldA := (ps[i - 1]?).getD b
      let oldB := (ps[min i (ps.length - 1)]?).getD oldA
      let next := if i = count - 1 then b else oldB
      let horizontal := oldA.y == oldB.y
      let horizontal := if i = count - 1 ∧ i ≠ 1 then !horizontal else horizontal
      let out := if (oldA.x = oldB.x ∨ oldA.y = oldB.y) ∧
          prev.x ≠ next.x ∧ prev.y ≠ next.y then
        appendPoint out (if horizontal then ⟨next.x, prev.y⟩ else ⟨prev.x, next.y⟩)
        else out
      appendPoint out next) out, Size.containsCell extent p = true := by
  induction l generalizing out with
  | nil =>
    intro p hp
    exact hout p hp
  | cons j js ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [Nat.add_sub_cancel]
    intro p hp
    have hprev : Size.containsCell extent ((out.getLast?).getD a) = true := by
      cases hg : out.getLast? with
      | none => simp only [Option.getD_none]; exact ha
      | some q =>
        simp only [Option.getD_some]
        exact hout q (List.mem_of_getLast? hg)
    have holdA : Size.containsCell extent ((ps[j]?).getD b) = true := by
      cases hopt : ps[j]? with
      | none => simp only [Option.getD_none]; exact hb
      | some pt =>
        simp only [Option.getD_some]
        exact hps pt (List.mem_of_getElem? hopt)
    have holdB : Size.containsCell extent ((ps[min (j + 1) (ps.length - 1)]?).getD ((ps[j]?).getD b)) = true := by
      cases hopt : ps[min (j + 1) (ps.length - 1)]? with
      | none => simp only [Option.getD_none]; exact holdA
      | some pt =>
        simp only [Option.getD_some]
        exact hps pt (List.mem_of_getElem? hopt)
    have hnext : Size.containsCell extent (if j + 1 = count - 1 then b else ((ps[min (j + 1) (ps.length - 1)]?).getD ((ps[j]?).getD b))) = true := by
      split
      · exact hb
      · exact holdB
    exact appendPoint_containsCell
      (ite_appendPoint_containsCell hout (containsCell_mix_ite hnext hprev))
      hnext p hp

private theorem projectLine_mem_containsCell (ps : List Point) (a b : Point) (extent : Size)
    (ha : Size.containsCell extent a = true)
    (hb : Size.containsCell extent b = true)
    (hps : ∀ p ∈ ps, Size.containsCell extent p = true) :
    ∀ p ∈ projectLine ps a b, Size.containsCell extent p = true := by
  unfold projectLine
  dsimp only
  apply foldl_projectLine_step_containsCell ps a b (max 2 ps.length) extent ha hb hps
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  exact ha

theorem projectLine_cellBounds (ps : List Point) (a b : Point) (extent : Size)
    (ha : Size.containsCell extent a = true)
    (hb : Size.containsCell extent b = true)
    (hps : ps.all (Size.containsCell extent) = true) :
    (projectLine ps a b).all (Size.containsCell extent) = true := by
  rw [List.all_eq_true]
  have hps_mem : ∀ p ∈ ps, Size.containsCell extent p = true := by
    rw [← List.all_eq_true]
    exact hps
  exact projectLine_mem_containsCell ps a b extent ha hb hps_mem

theorem attachment_containsCell (s : Scene) (hc1 : Validator.C1 s.layoutDump)
    (id : String) (p : Point) (hp : Size.containsCell s.canvas p = true) :
    Size.containsCell s.canvas (attachment s id p) = true := by
  unfold attachment
  cases hbox : s.boxes.find? (fun b => b.id == id) with
  | none => exact hp
  | some b =>
    dsimp only
    split
    · rename_i hcond
      have hmem : b ∈ s.layoutDump.boxes := List.mem_of_find?_eq_some hbox
      have hcont := hc1 b hmem
      dsimp [Validator.canvasRect, Rect.Contained, Scene.layoutDump] at hcont
      unfold Size.containsCell at hp ⊢
      simp only [decide_eq_true_iff] at hp ⊢
      obtain ⟨hw_pos, hh_pos, hx_lo, hx_hi, hy_lo, hy_hi⟩ := hcond
      obtain ⟨hbx_ge, hbx_le, hby_ge, hby_le⟩ := hcont
      split <;> split <;> omega
    · exact hp

theorem projectPrimitive_cellBounds (s : Scene) (markers : List RouteMarkers)
    (hc1 : Validator.C1 s.layoutDump)
    (grp : Group) (index : Nat) (p : Primitive)
    (hp : p.cellBounds s.canvas = true) :
    (projectPrimitive s markers grp index p).cellBounds s.canvas = true := by
  unfold projectPrimitive
  split
  · exact hp
  · cases hroute : s.routes.find? (fun r => r.id == grp.owner) with
    | none => exact hp
    | some r =>
      dsimp only
      cases hfirst : r.points.head? with
      | none =>
        dsimp only
        exact hp
      | some first =>
        cases hlast : r.points.getLast? with
        | none =>
          dsimp only
          exact hp
        | some last =>
          dsimp only
          cases p with
          | rect r paint => exact hp
          | roundRect r rad paint => exact hp
          | ellipse cx cy rx ry paint => exact hp
          | polygon ps paint => exact hp
          | polyline ps corner paint =>
            dsimp only
            by_cases hcond : ps.head? = some first ∧ ps.getLast? = some last ∧
                (attachment s r.fromId first ≠ first ∨ attachment s r.toId last ≠ last)
            · simp only [hcond]
              dsimp only [Primitive.cellBounds]
              obtain ⟨hhead, hlast_pt, _⟩ := hcond
              have hfirst_in : first ∈ ps := mem_of_head? hhead
              have hlast_in : last ∈ ps := List.mem_of_getLast? hlast_pt
              have hp_all : ps.all (Size.containsCell s.canvas) = true := hp
              have hps_all : ∀ pt ∈ ps, Size.containsCell s.canvas pt = true := by
                rw [← List.all_eq_true]
                exact hp_all
              have hfirst_cell : Size.containsCell s.canvas first = true := hps_all first hfirst_in
              have hlast_cell : Size.containsCell s.canvas last = true := hps_all last hlast_in
              have ha_cell := attachment_containsCell s hc1 r.fromId first hfirst_cell
              have hb_cell := attachment_containsCell s hc1 r.toId last hlast_cell
              exact projectLine_cellBounds ps _ _ s.canvas ha_cell hb_cell hp_all
            · simp only [hcond]
              exact hp
          | path cs paint => exact hp
          | text t => exact hp
          | markerRef name pos axis =>
            dsimp only [Primitive.cellBounds]
            have hp_cell : Size.containsCell s.canvas pos = true := hp
            by_cases hfl : pos = first ∧ pos = last
            · rw [ite_eq_left hfl]
              obtain ⟨hfirst, hlast⟩ := hfl
              have hlast_cell : Size.containsCell s.canvas last = true := by
                rw [← hlast]
                exact hp_cell
              have hfirst_cell : Size.containsCell s.canvas first = true := by
                rw [← hfirst]
                exact hp_cell
              have hb_cell := attachment_containsCell s hc1 r.toId last hlast_cell
              have ha_cell := attachment_containsCell s hc1 r.fromId first hfirst_cell
              split <;> split <;> assumption
            · rw [ite_eq_right hfl]
              by_cases hfirst' : pos = first
              · rw [ite_eq_left hfirst']
                have hfirst_cell : Size.containsCell s.canvas first = true := by
                  rw [← hfirst']
                  exact hp_cell
                exact attachment_containsCell s hc1 r.fromId first hfirst_cell
              · rw [ite_eq_right hfirst']
                by_cases hlast' : pos = last
                · rw [ite_eq_left hlast']
                  have hlast_cell : Size.containsCell s.canvas last = true := by
                    rw [← hlast']
                    exact hp_cell
                  exact attachment_containsCell s hc1 r.toId last hlast_cell
                · rw [ite_eq_right hlast']
                  exact hp_cell
          | symbolRef sym pt st => exact hp

theorem projectCellAttachments_primitiveBounds_of_c1 (s : Scene) (markers : List RouteMarkers)
    (hc1 : Validator.C1 s.layoutDump) (hp : s.PrimitiveBounds) :
    (projectCellAttachments s markers).PrimitiveBounds := by
  unfold Scene.PrimitiveBounds Scene.primitiveBoundsCheck at hp ⊢
  simp only [Bool.and_eq_true_iff, decide_eq_true_iff] at hp ⊢
  obtain ⟨hcanvas, hitems⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [projectCellAttachments_canvas]
    exact hcanvas
  · by_cases hprof : s.profile = .cell
    · rw [projectCellAttachments_items s markers hprof]
      rw [List.all_eq_true] at hitems ⊢
      intro grp hgrp
      simp only [List.mem_map] at hgrp
      obtain ⟨origGrp, horigGrp, rfl⟩ := hgrp
      simp only [List.all_eq_true]
      intro item hitem
      simp only [List.mem_map] at hitem
      obtain ⟨⟨p, idx⟩, hzip, rfl⟩ := hitem
      have hp_mem : p ∈ origGrp.items := mem_of_mem_zipIdx hzip
      have hp_bounds : p.cellBounds s.canvas = true := by
        have := hitems origGrp horigGrp
        rw [List.all_eq_true] at this
        exact this p hp_mem
      have hprim := projectPrimitive_cellBounds s markers hc1 origGrp idx p hp_bounds
      rw [projectCellAttachments_canvas]
      exact hprim
    · rw [projectCellAttachments_vector s markers hprof]
      exact hitems

theorem projectCellAttachments_primitiveBounds (s : Scene) (markers : List RouteMarkers)
    (hhc : HardConstraints s.layoutDump) (hp : s.PrimitiveBounds) :
    (projectCellAttachments s markers).PrimitiveBounds :=
  projectCellAttachments_primitiveBounds_of_c1 s markers hhc.1 hp

theorem projectCellAttachments_primitiveBounds_of_check (s : Scene) (markers : List RouteMarkers)
    (hcheck : Validator.check s.layoutDump = true) (hp : s.PrimitiveBounds) :
    (projectCellAttachments s markers).PrimitiveBounds :=
  projectCellAttachments_primitiveBounds s markers ((Validator.check_iff s.layoutDump).mp hcheck) hp

end Scene

def softCost (scene : Scene) : Except LayoutError Int := do
  let allRects := scene.boxes.map (·.rect) ++ scene.labels.map (·.rect)
  if !allRects.all (fun r => decide r.Valid) then throw .domain
  let real := scene.boxes.filter (fun b => b.role == "node")
  let count := max 1 (real.length : Int)
  let sum := real.foldl (fun n b => n + Int.fdiv (b.rect.w + b.rect.h) 2) 0
  if 9223372036854775807 < sum then throw .overflow
  let mean := max 1 (Int.fdiv sum count)
  let routes := scene.routes.map (fun r => { r with points :=
    (r.points.foldr (fun p ps => if ps.head? == some p then ps else p :: ps) []) })
  let segments := routes.map (fun r => r.points.zip r.points.tail)
  let allPoints := routes.flatMap (·.points)
  if !allPoints.all (fun p => decide (InI32 p.x ∧ InI32 p.y)) then throw .overflow
  if !segments.all (fun ss => ss.all (fun segment =>
      allPoints.all (safeSide segment.1 segment.2))) then throw .overflow
  if !segments.all (fun ss => ss.all (fun a =>
      segments.all (fun ts => ts.all (safePair a)))) then throw .overflow
  let crossings := (segments.zipIdx.flatMap fun a =>
    (segments.drop (a.2 + 1)).flatMap fun bs =>
      a.1.flatMap fun x => bs.map fun y => if properCross x y then (1 : Int) else 0).foldl (· + ·) 0
  let bends := routes.foldl (fun n r =>
    n + ((r.points.zip r.points.tail).zip r.points.tail.tail).foldl (fun k q =>
      let a := q.1.1
      let b := q.1.2
      let c := q.2
      let ux := b.x - a.x
      let uy := b.y - a.y
      let vx := c.x - b.x
      let vy := c.y - b.y
      k + if ux * vy - uy * vx ≠ 0 ∨ ux * vx + uy * vy < 0 then 1 else 0) 0) 0
  let against := routes.foldl (fun n r =>
    match scene.boxes.find? (fun b => b.id == r.fromId),
        scene.boxes.find? (fun b => b.id == r.toId) with
    | some a, some b =>
      let delta : Int := match scene.options.direction with
        | .TB => 2 * b.rect.y + b.rect.h - (2 * a.rect.y + a.rect.h)
        | .BT => 2 * a.rect.y + a.rect.h - (2 * b.rect.y + b.rect.h)
        | .LR => 2 * b.rect.x + b.rect.w - (2 * a.rect.x + a.rect.w)
        | .RL => 2 * a.rect.x + a.rect.w - (2 * b.rect.x + b.rect.w)
      n + if delta < 0 then 1 else 0
    | _, _ => n) 0
  let length ← segments.foldlM (fun n ss =>
    ss.foldlM (fun total segment => do
      let dx := segment.2.x - segment.1.x
      let dy := segment.2.y - segment.1.y
      let squared := dx * dx + dy * dy
      if 9223372036854775807 < squared then throw .overflow
      let distance ← Rect.isqrt squared
      let next := total + distance
      if 9223372036854775807 < next then throw .overflow
      pure next) n) 0
  let rects := scene.boxes.map (·.rect) ++ scene.labels.map (·.rect)
  let points := rects.flatMap (fun r => [⟨r.x, r.y⟩, ⟨r.x + r.w, r.y + r.h⟩]) ++
    routes.flatMap (·.points)
  let area := match points with
    | [] => 0
    | p :: ps =>
      let bounds := ps.foldl (fun b q =>
        (min b.1 q.x, max b.2.1 q.x, min b.2.2.1 q.y, max b.2.2.2 q.y))
        (p.x, p.x, p.y, p.y)
      (bounds.2.1 - bounds.1) * (bounds.2.2.2 - bounds.2.2.1)
  let denominator := mean * mean * count
  if 9223372036854775807 < area ∨ 9223372036854775807 < denominator then throw .overflow
  let cost := 10 * crossings + 2 * bends + 5 * against +
    Int.fdiv length mean + Int.fdiv area denominator
  if 9223372036854775807 < cost then throw .overflow
  pure cost
where
  safe (n : Int) : Bool := decide (-9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807)
  safeSide (a b p : Point) : Bool :=
    let x := (b.x - a.x) * (p.y - a.y)
    let y := (b.y - a.y) * (p.x - a.x)
    safe x && safe y && safe (x - y)
  safePair (a b : Point × Point) : Bool :=
    let ux := a.2.x - a.1.x
    let uy := a.2.y - a.1.y
    let vx := b.2.x - b.1.x
    let vy := b.2.y - b.1.y
    safe (ux * vx) && safe (uy * vy) && safe (ux * vy) && safe (uy * vx) &&
      safe (ux * vx + uy * vy) && safe (ux * vy - uy * vx)
  side (a b p : Point) : Int :=
    Int.sign ((b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x))
  properCross (a b : Point × Point) : Bool :=
    side a.1 a.2 b.1 * side a.1 a.2 b.2 == -1 &&
    side b.1 b.2 a.1 * side b.1 b.2 a.2 == -1

private theorem cost_fold_nonneg {α : Type} (xs : List α) (f : Int → α → Int)
    (step : ∀ n x, 0 ≤ n → x ∈ xs → 0 ≤ f n x) (n : Int) (hn : 0 ≤ n) :
    0 ≤ xs.foldl f n := by
  induction xs generalizing n with
  | nil => exact hn
  | cons x xs ih =>
    exact ih (fun n y h hy => step n y h (by simp [hy]))
      (f n x) (step n x hn (by simp))

private theorem cost_foldM_nonneg {α : Type} (xs : List α)
    (f : Int → α → Except LayoutError Int)
    (step : ∀ n x out, 0 ≤ n → f n x = .ok out → 0 ≤ out)
    (n out : Int) (hn : 0 ≤ n) (h : xs.foldlM f n = .ok out) : 0 ≤ out := by
  induction xs generalizing n with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst out
    exact hn
  | cons x xs ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hx : f n x with
    | error e => simp [hx] at h
    | ok next =>
      simp only [hx] at h
      exact ih next (step n x next hn hx) h

private theorem cost_bounds_ordered (ps : List Point) (b : Int × Int × Int × Int)
    (hb : b.1 ≤ b.2.1 ∧ b.2.2.1 ≤ b.2.2.2) :
    let out := ps.foldl (fun b q =>
      (min b.1 q.x, max b.2.1 q.x, min b.2.2.1 q.y, max b.2.2.2 q.y)) b
    out.1 ≤ out.2.1 ∧ out.2.2.1 ≤ out.2.2.2 := by
  induction ps generalizing b with
  | nil => exact hb
  | cons p ps ih =>
    apply ih
    simp only
    constructor <;> omega

private theorem cost_area_nonneg (ps : List Point) :
    (0 : Int) ≤ (match ps with
      | [] => (0 : Int)
      | p :: rest =>
        let b := rest.foldl (fun b q =>
          (min b.1 q.x, max b.2.1 q.x, min b.2.2.1 q.y, max b.2.2.2 q.y))
          (p.x, p.x, p.y, p.y)
        (b.2.1 - b.1) * (b.2.2.2 - b.2.2.1)) := by
  cases ps with
  | nil => exact Int.le_refl _
  | cons p ps =>
    have hb := cost_bounds_ordered ps (p.x, p.x, p.y, p.y) ⟨Int.le_refl _, Int.le_refl _⟩
    exact Int.mul_nonneg (by omega) (by omega)

private theorem cost_lengths_nonneg (segments : List (List (Point × Point))) (out : Int)
    (h : segments.foldlM (fun n ss =>
      ss.foldlM (fun (total : Int) (segment : Point × Point) => do
        let dx := segment.2.x - segment.1.x
        let dy := segment.2.y - segment.1.y
        let squared := dx * dx + dy * dy
        if 9223372036854775807 < squared then throw LayoutError.overflow
        let distance ← Rect.isqrt squared
        let next := total + distance
        if 9223372036854775807 < next then throw LayoutError.overflow
        pure next) n) (0 : Int) = .ok out) : 0 ≤ out := by
  apply cost_foldM_nonneg segments _ _ 0 out (by decide) h
  intro n ss result hn hs
  apply cost_foldM_nonneg ss _ _ n result hn hs
  intro total segment result ht hr
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
  split at hr
  · cases hr
  · cases hd : Rect.isqrt ((segment.2.x - segment.1.x) * (segment.2.x - segment.1.x) +
        (segment.2.y - segment.1.y) * (segment.2.y - segment.1.y)) with
    | error e => rw [hd] at hr; cases hr
    | ok distance =>
      rw [hd] at hr
      have hdist := (Rect.isqrt_spec hd).1
      by_cases hb : 9223372036854775807 < total + distance
      · simp [hb] at hr
      · simp only [hb, ↓reduceIte, Except.ok.injEq] at hr
        omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem softCost_nonneg {scene : Scene} {cost : Int}
    (h : softCost scene = .ok cost) : 0 ≤ cost := by
  unfold softCost at h
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  generalize scene.routes.map (fun r => { r with points :=
    (r.points.foldr (fun p ps => if ps.head? == some p then ps else p :: ps) []) }) = routes at h
  generalize routes.map (fun r => r.points.zip r.points.tail) = segments at h
  generalize scene.boxes.map (·.rect) ++ scene.labels.map (·.rect) = rects at h
  generalize rects.flatMap (fun r => [Point.mk r.x r.y, Point.mk (r.x + r.w) (r.y + r.h)]) ++
    routes.flatMap (·.points) = points at h
  generalize scene.boxes.filter (fun b => b.role == "node") = real at h
  generalize real.foldl (fun n b => n + Int.fdiv (b.rect.w + b.rect.h) 2) 0 = sum at h
  have hc : 0 ≤ (segments.zipIdx.flatMap fun a =>
      (segments.drop (a.2 + 1)).flatMap fun bs =>
        a.1.flatMap fun x => bs.map fun y =>
          if softCost.properCross x y then (1 : Int) else 0).foldl (· + ·) 0 := by
    apply cost_fold_nonneg
    · intro n x hn hx
      simp only [List.mem_flatMap, List.mem_map] at hx
      obtain ⟨a, _, bs, _, edge, _, other, _, rfl⟩ := hx
      split <;> omega
    · omega
  have hb : (0 : Int) ≤ routes.foldl (fun n r =>
      n + ((r.points.zip r.points.tail).zip r.points.tail.tail).foldl (fun k q =>
        k + if (q.1.2.x - q.1.1.x) * (q.2.y - q.1.2.y) -
            (q.1.2.y - q.1.1.y) * (q.2.x - q.1.2.x) ≠ 0 ∨
          (q.1.2.x - q.1.1.x) * (q.2.x - q.1.2.x) +
            (q.1.2.y - q.1.1.y) * (q.2.y - q.1.2.y) < 0 then 1 else 0) 0) 0 := by
    apply cost_fold_nonneg
    · intro n r hn _
      apply Int.add_nonneg hn
      apply cost_fold_nonneg
      · intro k q hk _
        split <;> omega
      · omega
    · omega
  have ha : (0 : Int) ≤ routes.foldl (fun (n : Int) r =>
      match scene.boxes.find? (fun b => b.id == r.fromId),
          scene.boxes.find? (fun b => b.id == r.toId) with
      | some a, some b =>
        n + if (match scene.options.direction with
          | .TB => 2 * b.rect.y + b.rect.h - (2 * a.rect.y + a.rect.h)
          | .BT => 2 * a.rect.y + a.rect.h - (2 * b.rect.y + b.rect.h)
          | .LR => 2 * b.rect.x + b.rect.w - (2 * a.rect.x + a.rect.w)
          | .RL => 2 * a.rect.x + a.rect.w - (2 * b.rect.x + b.rect.w)) < (0 : Int) then 1 else 0
      | _, _ => n) 0 := by
    apply cost_fold_nonneg
    · intro n r hn _
      split <;> try exact hn
      all_goals repeat' split
      all_goals omega
    · omega
  generalize hcross : (segments.zipIdx.flatMap fun a =>
    (segments.drop (a.2 + 1)).flatMap fun bs =>
      a.1.flatMap fun x => bs.map fun y =>
        if softCost.properCross x y then (1 : Int) else 0).foldl (· + ·) 0 = crossings at h hc
  generalize hbend : routes.foldl (fun n r =>
    n + ((r.points.zip r.points.tail).zip r.points.tail.tail).foldl (fun k q =>
      k + if (q.1.2.x - q.1.1.x) * (q.2.y - q.1.2.y) -
          (q.1.2.y - q.1.1.y) * (q.2.x - q.1.2.x) ≠ 0 ∨
        (q.1.2.x - q.1.1.x) * (q.2.x - q.1.2.x) +
          (q.1.2.y - q.1.1.y) * (q.2.y - q.1.2.y) < 0 then 1 else 0) 0) (0 : Int) = bends at h hb
  generalize hagainst : routes.foldl (fun n r =>
    match scene.boxes.find? (fun b => b.id == r.fromId),
        scene.boxes.find? (fun b => b.id == r.toId) with
    | some a, some b =>
      n + if (match scene.options.direction with
        | .TB => 2 * b.rect.y + b.rect.h - (2 * a.rect.y + a.rect.h)
        | .BT => 2 * a.rect.y + a.rect.h - (2 * b.rect.y + b.rect.h)
        | .LR => 2 * b.rect.x + b.rect.w - (2 * a.rect.x + a.rect.w)
        | .RL => 2 * a.rect.x + a.rect.w - (2 * b.rect.x + b.rect.w)) < (0 : Int) then 1 else 0
    | _, _ => n) (0 : Int) = against at h ha
  have harea := cost_area_nonneg points
  repeat' (split at h <;> try contradiction)
  all_goals
    have lengthNonneg := cost_lengths_nonneg segments _ (by assumption)
    simp only [Except.ok.injEq] at h
    subst cost
    apply Int.add_nonneg
    · apply Int.add_nonneg
      · omega
      · exact Int.fdiv_nonneg lengthNonneg (by omega)
    · apply Int.fdiv_nonneg
      · simpa only using harea
      · exact Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)

end Elegant
