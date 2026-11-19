import Elegant.Scene
import Elegant.Measure
import Elegant.Gen.Layoutconst
import Elegant.Kinds.FlowchartIcons

namespace Elegant.Treeview

structure Metrics where
  rowIndent : Int
  paddingX : Int
  paddingY : Int
  textHeight : Int
  iconSize : Int
  iconGap : Int
  descGap : Int
  thickness : Int
  margin : Int
  deriving Repr

def configured (m : Model) (key : String) (fallback : Int) : Except LayoutError Int :=
  if m.profile = .cell then pure fallback else
  match m.options.config.find? (fun c => c.1 == key) with
  | none => pure fallback
  | some (_, .integer n) =>
    let u := Int.fdiv (2 * n * 64 + 1000) 2000
    if n < 0 ∨ n > 536870912 ∨ u > 536870912 then .error .overflow else pure u
  | _ => .error .domain

def metrics (m : Model) : Except LayoutError Metrics := do
  let ri := LayoutConst.treeview_row_indent.get m.profile
  let px := LayoutConst.treeview_padding_x.get m.profile
  let py := LayoutConst.treeview_padding_y.get m.profile
  let th := LayoutConst.treeview_line_thickness.get m.profile
  return ⟨← configured m "rowIndent" ri, ← configured m "paddingX" px,
    ← configured m "paddingY" py, LayoutConst.line_h.get m.profile,
    LayoutConst.treeview_icon_size.get m.profile,
    LayoutConst.treeview_icon_gap.get m.profile,
    LayoutConst.treeview_desc_gap.get m.profile, ← configured m "lineThickness" th,
    LayoutConst.canvas_margin.get m.profile⟩

def flat (s : String) : String := String.ofList (s.toList.map fun c => if c = '\n' then ' ' else c)

structure Row where
  source : ModelBox
  parent : Option Nat
  depth : Nat
  name : String
  desc : String
  icon : String
  className : String
  labelWidth : Int
  descWidth : Int
  guidePrefix : String := ""
  trunk : String := ""
  deriving Repr

def field (m : Model) (b : ModelBox) (suffix fallback : String) : String :=
  m.labels.foldl (fun value l => if l.owner == b.id && l.id.endsWith suffix then l.text else value) fallback

def measureWidth (p : Profile) (role : Measure.Role) (s : String) : Except LayoutError Int := do
  if p = .cell then
    Measure.textWidth ⟨.cell, 14, 0, 2048, false⟩ s.toList
  else
    let metric ← role.metric
    Measure.textWidth metric s.toList

theorem measureWidth_nonnegative {p : Profile} {role : Measure.Role}
    {s : String} {w : Int} (h : measureWidth p role s = .ok w) :
    0 ≤ w := by
  unfold measureWidth at h
  split at h
  · exact Measure.textWidth_nonneg h
  · cases hm : role.metric with
    | error e => simp [hm, Bind.bind, Except.bind] at h
    | ok metric =>
      simp only [hm, Bind.bind, Except.bind] at h
      exact Measure.textWidth_nonneg h

/-- A preorder may attach the next row only to the previous row or an open ancestor. -/
def openAncestor (rs : Array Row) (wanted : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, current =>
    if wanted == current then true else
      match rs[current]? with
      | none => false
      | some r => match r.parent with
        | none => false
        | some parent => openAncestor rs wanted fuel parent

def parentIndex (m : Model) (b : ModelBox) (i : Nat) :
    Except LayoutError (Option Nat) :=
  match m.routes.filter (fun r => r.toId == b.id) with
  | [] => if i = 0 then pure none else throw .domain
  | [r] => match m.boxes.findIdx? (fun a => a.id == r.fromId) with
    | some j => if j < i then pure (some j) else throw .domain
    | none => throw .domain
  | _ => throw .domain

theorem parentIndex_backward {m : Model} {b : ModelBox} {i parent : Nat}
    (h : parentIndex m b i = .ok (some parent)) : parent < i := by
  unfold parentIndex at h
  split at h
  · split at h <;> simp_all [pure, Except.pure, throw]
  · split at h
    · split at h <;> simp_all [pure, Except.pure, throw]
    · simp [throw] at h
  · simp [throw] at h

def checkOpenParent (out : Array Row) (i : Nat) (parent : Option Nat) :
    Except LayoutError Unit :=
  match parent with
  | none => pure ()
  | some j => if !(openAncestor out j out.size (i - 1)) then throw .domain else pure ()

def pushRow (m : Model) (entry : ModelBox × Nat) (out : Array Row) :
    Except LayoutError (ForInStep (Array Row)) := do
  let (b, i) := entry
  let parent ← parentIndex m b i
  let _ ← checkOpenParent out i parent
  let depth := match parent with | none => 0 | some j => ((out[j]?).map (·.depth)).getD 0 + 1
  let name := flat (field m b ".label" b.id)
  let name := if m.profile = .cell ∧ b.shape = "directory" ∧ parent.isSome then name ++ "/" else name
  let desc := flat (field m b ".desc" "")
  let icon := field m b ".icon" ""
  let icon := if icon == "none" then "" else icon
  let role := if b.shape == "directory" then Measure.Role.label else .body
  let lw ← measureWidth m.profile role name
  let dw ← measureWidth m.profile .body desc
  let last := !(m.routes.any fun r => r.fromId == (match parent with
    | none => "" | some j => ((m.boxes[j]?).map (·.id)).getD "") &&
    (match m.boxes.findIdx? (fun a => a.id == r.toId) with | some j => j > i | none => false))
  let trunk := match parent with | none => "" | some j => ((out[j]?).map (·.trunk)).getD ""
  return .yield (out.push { source := b, parent := parent, depth := depth, name := name, desc := desc, icon := icon, className := field m b ".class" "", labelWidth := lw, descWidth := dw, guidePrefix := if parent.isSome then trunk ++ (if last then "└── " else "├── ") else "", trunk := if parent.isSome then trunk ++ (if last then "    " else "│   ") else "" })

def rows (m : Model) : Except LayoutError (List Row) := do
  if m.boxes.isEmpty then throw .domain
  let out ← forIn m.boxes.zipIdx #[] (pushRow m)
  return out.toList

def rowHeight (p : Metrics) : Int := p.textHeight + 2 * p.paddingY

def indent (p : Metrics) (depth : Nat) : Int := (depth : Int) * (p.rowIndent + p.paddingX)

def slot (p : Metrics) (r : Row) : Int := if r.icon.isEmpty then 0 else p.iconSize + p.iconGap

def width (p : Metrics) (r : Row) : Int := max (r.labelWidth + 2 * p.paddingX + slot p r) 1

def labelX (p : Metrics) (r : Row) : Int := indent p r.depth + p.paddingX + slot p r

def rowRect (p : Metrics) (i : Nat) (r : Row) : Rect :=
  ⟨indent p r.depth + p.margin, (i : Int) * rowHeight p + p.margin, width p r, rowHeight p⟩

def routePoints (p : Metrics) (rs : Array Row) (i : Nat) (r : Row) : List Point :=
  match r.parent with
  | none => []
  | some j =>
    let spine := indent p (((rs[j]?).map (·.depth)).getD 0) + p.paddingX + p.margin
    let bottom := ((j : Int) + 1) * rowHeight p + p.margin
    let mid := (i : Int) * rowHeight p + p.margin + Int.fdiv (rowHeight p) 2
    let tail := [⟨spine, mid⟩, ⟨indent p r.depth + p.margin, mid⟩]
    if bottom = mid then tail else ⟨spine, bottom⟩ :: tail

def text (r : Rect) (role : TextRole) (style value : String) (italic : Bool := false) : Primitive :=
  .text { rect := r, role := role, size := 14, align := .start, style := style, lines := [[{ text := value, italic := italic }]] }

def nodeItems (profile : Profile) (p : Metrics) (right descX : Int) (i : Nat) (r : Row) : List Primitive :=
  let rect := rowRect p i r
  let y := rect.y + p.paddingY
  let band := if profile = .vector ∧ r.className = "highlight" then
    [Primitive.rect { rect with w := right + p.margin - rect.x } { style := "band" }] else []
  let iconX := indent p r.depth + p.paddingX + p.margin
  let origin : Point := if profile = .cell then ⟨iconX, rect.y⟩ else
    ⟨iconX + Int.fdiv p.iconSize 2 - 768, rect.y + Int.fdiv rect.h 2 - 768⟩
  let icons := if r.icon.isEmpty then [] else Kinds.Flowchart.iconItems profile origin
  let guides := if profile = .cell ∧ r.guidePrefix ≠ "" then
    [text ⟨p.margin, y, 4 * (r.depth : Int), p.textHeight⟩ .body "text" r.guidePrefix] else []
  let name := text ⟨labelX p r + p.margin, y, r.labelWidth, p.textHeight⟩
    (if r.source.shape == "directory" then .label else .body) "text" r.name
  let desc := if r.desc.isEmpty then [] else
    [text ⟨descX + p.margin, y, r.descWidth, p.textHeight⟩ .body "text-muted" r.desc true]
  band ++ icons ++ guides ++ [name] ++ desc

def makeRoute (m : Model) (p : Metrics) (rs : List Row)
    (route : ModelRoute) : Except LayoutError Route := do
  let some i := m.boxes.findIdx? (fun b => b.id == route.toId) | throw .domain
  let some r := rs[i]? | throw .domain
  return { id := route.id, fromId := route.fromId, toId := route.toId, orthogonal := route.orthogonal, points := routePoints p rs.toArray i r }

def assemble (m : Model) (p : Metrics) (rs : List Row)
    (descX right : Int) (routes : List Route) : Scene :=
  let boxes := rs.zipIdx.map fun (r, i) =>
    ({ id := r.source.id, role := r.source.role.id, parent := r.source.parent, exclusive := r.source.exclusive, rect := rowRect p i r } : Box)
  let edges := routes.map fun r =>
    ({ role := .edge, owner := r.id, items := if m.profile = .cell then [] else [.polyline r.points 0 { style := "rule", width := .units p.thickness }] } : Group)
  let nodes := rs.zipIdx.map fun (r, i) =>
    ({ role := .node, owner := r.source.id, items := nodeItems m.profile p right descX i r } : Group)
  { kind := m.kind, profile := m.profile, options := m.options,
    canvas := ⟨right + 2 * p.margin, (rs.length : Int) * rowHeight p + 2 * p.margin⟩,
    boxes := boxes, routes := routes, items := edges ++ nodes }

def layout (m : Model) : Except LayoutError Scene := do
  if m.boxes.any (fun b => b.parent != "") then throw .domain
  let p ← metrics m
  if p.textHeight < 1 ∨ p.paddingX < 0 ∨ p.paddingY < 0 ∨ p.rowIndent < 0 then throw .domain
  let rs ← rows m
  let descX := rs.foldl (fun x r => max x (labelX p r + r.labelWidth + p.descGap)) 0
  let right := rs.foldl (fun x r => max x (indent p r.depth + width p r)) 0
  let right := rs.foldl (fun x r => if r.desc.isEmpty then x else max x (descX + r.descWidth + p.paddingX)) right
  let w := right + 2 * p.margin
  let h := (rs.length : Int) * rowHeight p + 2 * p.margin
  if w > 536870912 ∨ h > 536870912 then throw .overflow
  let routes ← m.routes.mapM (makeRoute m p rs)
  return assemble m p rs descX right routes

/-- Row indices are the declaration/preorder indices handed off by the model. -/
theorem treeview_rows_preorder (p : Metrics) (i : Nat) (r : Row) :
    (rowRect p i r).y = (i : Int) * rowHeight p + p.margin := rfl

theorem treeview_indent_step (p : Metrics) (d : Nat) :
    indent p (d + 1) = indent p d + (p.rowIndent + p.paddingX) := by
  simp [indent, Int.natCast_add, Int.add_mul]

theorem treeview_rows_disjoint (p : Metrics) (i j : Nat) (a b : Row)
    (h : 0 ≤ rowHeight p) (hij : i < j) :
    (rowRect p i a).y + (rowRect p i a).h ≤ (rowRect p j b).y := by
  have hn : (i : Int) + 1 ≤ (j : Int) := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hn h
  simp only [rowRect]
  simp only [Int.add_mul, Int.one_mul] at hm
  omega

theorem treeview_rows_no_interior_overlap (p : Metrics) (i j : Nat) (a b : Row)
    (h : 0 ≤ rowHeight p) (hij : i < j) :
    ¬ (rowRect p i a).meetsInterior (rowRect p j b) := by
  have sep := treeview_rows_disjoint p i j a b h hij
  unfold Rect.meetsInterior
  intro overlap
  have lower := Int.le_max_right (rowRect p i a).y (rowRect p j b).y
  have upper := Int.min_le_left ((rowRect p i a).y + (rowRect p i a).h)
    ((rowRect p j b).y + (rowRect p j b).h)
  omega

theorem treeview_name_inside_row (p : Metrics) (r : Row)
    (px : 0 ≤ p.paddingX) (ss : 0 ≤ slot p r) :
    indent p r.depth ≤ labelX p r ∧
      labelX p r + r.labelWidth ≤ indent p r.depth + width p r := by
  have hw := Int.le_max_left (r.labelWidth + 2 * p.paddingX + slot p r) 1
  unfold labelX width
  omega

theorem treeview_row_height_positive (p : Metrics)
    (ht : 1 ≤ p.textHeight) (hy : 0 ≤ p.paddingY) : 1 ≤ rowHeight p := by
  unfold rowHeight
  omega

theorem treeview_icon_slot_preserved (p : Metrics) (r : Row)
    (hi : r.icon.isEmpty = false) :
    labelX p r = indent p r.depth + p.paddingX + p.iconSize + p.iconGap := by
  simp [labelX, slot, hi, Int.add_assoc]

theorem treeview_row_inside_canvas (p : Metrics) (r : Row) (i n : Nat) (right : Int)
    (hm : 0 ≤ p.margin) (hh : 0 ≤ rowHeight p)
    (hx : 0 ≤ indent p r.depth)
    (hr : indent p r.depth + width p r ≤ right) (hi : i < n) :
    Rect.Contained ⟨0, 0, right + 2 * p.margin, (n : Int) * rowHeight p + 2 * p.margin⟩
      (rowRect p i r) := by
  have ii : 0 ≤ (i : Int) := Int.natCast_nonneg i
  have iy := Int.mul_nonneg ii hh
  have step : (i : Int) + 1 ≤ (n : Int) := by omega
  have top := Int.mul_le_mul_of_nonneg_right step hh
  simp only [Int.add_mul, Int.one_mul] at top
  unfold Rect.Contained rowRect
  dsimp only
  omega

/-- The route-parent relation, independent of containment metadata and coordinates. -/
inductive RouteAncestor (rs : Array Row) (ancestor : Nat) : Nat → Prop where
  | self : RouteAncestor rs ancestor ancestor
  | parent {child parent : Nat} {r : Row} :
      rs[child]? = some r → r.parent = some parent →
      RouteAncestor rs ancestor parent → RouteAncestor rs ancestor child

/-- The admission walk follows actual stored route parents, not just row depths. -/
theorem openAncestor_sound (rs : Array Row) (wanted fuel current : Nat)
    (h : openAncestor rs wanted fuel current = true) :
    RouteAncestor rs wanted current := by
  induction fuel generalizing current with
  | zero => simp [openAncestor] at h
  | succ fuel ih =>
    by_cases heq : wanted = current
    · subst current
      exact .self
    · cases hr : rs[current]? with
      | none => simp [openAncestor, heq, hr] at h
      | some r =>
        cases hp : r.parent with
        | none => simp [openAncestor, heq, hr, hp] at h
        | some parent =>
          apply RouteAncestor.parent hr hp
          apply ih
          simpa [openAncestor, heq, hr, hp] using h

theorem treeview_indent_nonnegative (p : Metrics) (depth : Nat)
    (hi : 0 ≤ p.rowIndent) (hp : 0 ≤ p.paddingX) :
    0 ≤ indent p depth := by
  exact Int.mul_nonneg (Int.natCast_nonneg depth) (by omega)

/-- The vertical route spine stays to the left of every deeper row, even when
    the configured indentation is zero. -/
theorem treeview_spine_left_of_deeper_row (p : Metrics) (parent child : Row)
    (i : Nat) (hdepth : parent.depth < child.depth)
    (hi : 0 ≤ p.rowIndent) (hp : 0 ≤ p.paddingX) :
    indent p parent.depth + p.paddingX + p.margin ≤ (rowRect p i child).x := by
  have hstep : (parent.depth : Int) + 1 ≤ (child.depth : Int) := by omega
  have hmul := Int.mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ p.rowIndent + p.paddingX by omega)
  simp only [Int.add_mul, Int.one_mul] at hmul
  dsimp only [indent, rowRect]
  omega

theorem treeview_width_positive (p : Metrics) (r : Row) :
    1 ≤ width p r := by
  exact Int.le_max_right _ _

/-- The canvas extent fold retains each row's complete right edge. -/
theorem treeview_right_fold_lower (rs : List Row) (p : Metrics) (initial : Int) :
    initial ≤ rs.foldl (fun x r => max x (indent p r.depth + width p r)) initial := by
  induction rs generalizing initial with
  | nil => exact Int.le_refl initial
  | cons r rs ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem treeview_right_fold_member (rs : List Row) (p : Metrics) (initial : Int)
    (r : Row) (hr : r ∈ rs) :
    indent p r.depth + width p r ≤
      rs.foldl (fun x r => max x (indent p r.depth + width p r)) initial := by
  induction rs generalizing initial with
  | nil => simp at hr
  | cons a rs ih =>
    simp only [List.mem_cons] at hr
    simp only [List.foldl_cons]
    rcases hr with heq | hr
    · subst a
      exact Int.le_trans (Int.le_max_right _ _) (treeview_right_fold_lower rs p _)
    · exact ih _ hr

/-- The second width fold can only enlarge the already established row bound. -/
theorem treeview_description_fold_lower (rs : List Row) (p : Metrics)
    (descX initial : Int) :
    initial ≤ rs.foldl (fun x r =>
      if r.desc.isEmpty then x else max x (descX + r.descWidth + p.paddingX)) initial := by
  induction rs generalizing initial with
  | nil => exact Int.le_refl initial
  | cons r rs ih =>
    simp only [List.foldl_cons]
    split
    · exact ih initial
    · exact Int.le_trans (Int.le_max_left _ _) (ih _)

/-- Exact canvas containment follows from the two executed width folds. -/
theorem treeview_row_inside_fold_canvas (rs : List Row) (p : Metrics)
    (descX : Int) (r : Row) (i : Nat)
    (hr : r ∈ rs) (hi : i < rs.length)
    (hm : 0 ≤ p.margin) (ht : 1 ≤ p.textHeight)
    (hx : 0 ≤ p.paddingX) (hy : 0 ≤ p.paddingY)
    (hind : 0 ≤ p.rowIndent) :
    let right := rs.foldl (fun x r => max x (indent p r.depth + width p r)) 0
    let finalRight := rs.foldl (fun x r =>
      if r.desc.isEmpty then x else max x (descX + r.descWidth + p.paddingX)) right
    Rect.Contained
      ⟨0, 0, finalRight + 2 * p.margin,
        (rs.length : Int) * rowHeight p + 2 * p.margin⟩
      (rowRect p i r) := by
  dsimp only
  apply treeview_row_inside_canvas p r i rs.length _ hm
    (by have := treeview_row_height_positive p ht hy; omega)
    (treeview_indent_nonnegative p r.depth hind hx) _ hi
  exact Int.le_trans (treeview_right_fold_member rs p 0 r hr)
    (treeview_description_fold_lower rs p descX _)

/-- Every finite route-ancestor chain is accepted with a sufficiently large walk budget. -/
theorem RouteAncestor.openAncestor_complete {rs : Array Row} {ancestor current : Nat}
    (h : RouteAncestor rs ancestor current) :
    ∃ fuel, openAncestor rs ancestor fuel current = true := by
  induction h with
  | self =>
    exact ⟨1, by simp [openAncestor]⟩
  | @parent child parent r hr hp _ ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    by_cases heq : ancestor = child
    · exact ⟨1, by simp [openAncestor, heq]⟩
    · exact ⟨fuel + 1, by simp [openAncestor, heq, hr, hp, hfuel]⟩

theorem openAncestor_iff_routeAncestor (rs : Array Row) (ancestor current : Nat) :
    (∃ fuel, openAncestor rs ancestor fuel current = true) ↔
      RouteAncestor rs ancestor current := by
  constructor
  · rintro ⟨fuel, h⟩
    exact openAncestor_sound rs ancestor fuel current h
  · exact RouteAncestor.openAncestor_complete

theorem treeview_route_last (p : Metrics) (rs : Array Row) (i j : Nat) (r : Row)
    (hp : r.parent = some j) :
    (routePoints p rs i r).getLast? =
      some ⟨(rowRect p i r).x,
        (rowRect p i r).y + Int.fdiv (rowHeight p) 2⟩ := by
  simp only [routePoints, hp, rowRect]
  split <;> simp

theorem treeview_route_first (p : Metrics) (rs : Array Row) (i j : Nat)
    (r parent : Row) (hp : r.parent = some j) (hj : rs[j]? = some parent) :
    (routePoints p rs i r).head? =
      some ⟨indent p parent.depth + p.paddingX + p.margin,
        (rowRect p j parent).y + (rowRect p j parent).h⟩ := by
  simp only [routePoints, hp, hj, Option.map_some, Option.getD_some]
  split
  · rename_i heq
    simp only [List.head?, Option.some.injEq, Point.mk.injEq, rowRect]
    constructor
    · trivial
    · simp only [Int.add_mul, Int.one_mul] at heq
      omega
  · simp [rowRect, Int.add_mul, Int.one_mul, Int.add_assoc, Int.add_comm,
      Int.add_left_comm]

/-- Successful execution supplies the measured metrics and admitted row fold. -/
theorem successful_layout_rows {m : Model} {s : Scene} (h : layout m = .ok s) :
    ∃ p rs, metrics m = .ok p ∧ rows m = .ok rs ∧
      1 ≤ p.textHeight ∧ 0 ≤ p.paddingX ∧ 0 ≤ p.paddingY ∧ 0 ≤ p.rowIndent := by
  have hempty : m.boxes.any (fun b => b.parent != "") = false := by
    cases hp : m.boxes.any (fun b => b.parent != "") with
    | false => rfl
    | true => simp [layout, hp, Bind.bind, Except.bind] at h
  simp only [layout, hempty, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind] at h
  cases hm : metrics m with
  | error e => simp [hm] at h
  | ok p =>
    simp only [hm] at h
    by_cases hmetric : p.textHeight < 1 ∨ p.paddingX < 0 ∨
        p.paddingY < 0 ∨ p.rowIndent < 0
    · simp [hmetric] at h
    · simp only [hmetric, ↓reduceIte] at h
      cases hr : rows m with
      | error e => simp [hr] at h
      | ok rs => exact ⟨p, rs, rfl, rfl, by omega, by omega, by omega, by omega⟩

theorem treeview_route_orthogonal (p : Metrics) (rs : Array Row) (i : Nat) (r : Row) :
    Polyline.isOrthogonal (routePoints p rs i r) = true := by
  cases hp : r.parent with
  | none => simp [routePoints, hp, Polyline.isOrthogonal]
  | some j =>
    simp only [routePoints, hp]
    split <;> simp [Polyline.isOrthogonal]

theorem treeview_source_boundary (p : Metrics) (j : Nat) (parent : Row)
    (hpx : 0 ≤ p.paddingX) (hh : 0 ≤ rowHeight p)
    (hlw : 0 ≤ parent.labelWidth) (hslot : 0 ≤ slot p parent) :
    Validator.onBoundary
      ⟨indent p parent.depth + p.paddingX + p.margin,
        (rowRect p j parent).y + (rowRect p j parent).h⟩
      (rowRect p j parent) := by
  have hw := Int.le_max_left
    (parent.labelWidth + 2 * p.paddingX + slot p parent) 1
  dsimp only [Validator.onBoundary, rowRect]
  refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩ <;>
    (try dsimp only [width]) <;> omega

theorem treeview_target_boundary (p : Metrics) (i : Nat) (r : Row)
    (hh : 0 ≤ rowHeight p) :
    Validator.onBoundary
      ⟨(rowRect p i r).x,
        (rowRect p i r).y + Int.fdiv (rowHeight p) 2⟩
      (rowRect p i r) := by
  have hw := treeview_width_positive p r
  have hhalf : 0 ≤ Int.fdiv (rowHeight p) 2 ∧
      Int.fdiv (rowHeight p) 2 ≤ rowHeight p := by
    rw [Measure.fdiv_of_nonneg (by omega)]
    omega
  dsimp only [Validator.onBoundary, rowRect]
  refine ⟨?_, ?_, ?_, ?_, Or.inl rfl⟩ <;> omega

theorem RouteAncestor.trans {rs : Array Row} {a b c : Nat}
    (hab : RouteAncestor rs a b) (hbc : RouteAncestor rs b c) :
    RouteAncestor rs a c := by
  induction hbc with
  | self => exact hab
  | parent hr hp _ ih => exact .parent hr hp ih

/-- Every new parent is still on the preceding row's route-ancestor stack. -/
def OpenParentOrder (rs : Array Row) : Prop :=
  ∀ (child : Nat) (r : Row) (parent : Nat),
    rs[child]? = some r → r.parent = some parent →
      RouteAncestor rs parent (child - 1)

theorem routeAncestor_previous {rs : Array Row} (horder : OpenParentOrder rs)
    {ancestor child : Nat} (h : RouteAncestor rs ancestor child)
    (hlt : ancestor < child) :
    RouteAncestor rs ancestor (child - 1) := by
  cases h with
  | self => omega
  | parent hr hp hancestor =>
    exact hancestor.trans (horder _ _ _ hr hp)

/-- Descendants cannot resume after leaving their declaration-order interval. -/
theorem treeview_descendant_interval {rs : Array Row} (horder : OpenParentOrder rs)
    {ancestor last middle : Nat} (hlast : RouteAncestor rs ancestor last)
    (hleft : ancestor ≤ middle) (hright : middle ≤ last) :
    RouteAncestor rs ancestor middle := by
  induction last using Nat.strongRecOn with
  | ind last ih =>
    by_cases heq : middle = last
    · subst middle
      exact hlast
    · have hlt : ancestor < last := by omega
      have hprev := routeAncestor_previous horder hlast hlt
      exact ih (last - 1) (by omega) hprev (by omega)

theorem RouteAncestor.push {rs : Array Row} {ancestor child : Nat}
    (h : RouteAncestor rs ancestor child) (r : Row) :
    RouteAncestor (rs.push r) ancestor child := by
  induction h with
  | self => exact .self
  | @parent child parent old hr hp _ ih =>
    apply RouteAncestor.parent (r := old) (parent := parent) _ hp ih
    obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hr
    rw [Array.getElem?_push_lt hlt]
    simpa only [Array.getElem?_eq_getElem hlt] using hr

private theorem row_bind_success {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases hx : x with
  | error e => simp [hx, Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Bind.bind, Except.bind] using h⟩

theorem successful_metrics_fixed_nonnegative {m : Model} {p : Metrics}
    (h : metrics m = .ok p) :
    0 ≤ p.margin ∧ 0 ≤ p.iconSize ∧ 0 ≤ p.iconGap := by
  unfold metrics at h
  obtain ⟨rowIndent, _, h⟩ := row_bind_success h
  obtain ⟨paddingX, _, h⟩ := row_bind_success h
  obtain ⟨paddingY, _, h⟩ := row_bind_success h
  obtain ⟨thickness, _, h⟩ := row_bind_success h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst p
  change 0 ≤ LayoutConst.canvas_margin.get m.profile ∧
    0 ≤ LayoutConst.treeview_icon_size.get m.profile ∧
    0 ≤ LayoutConst.treeview_icon_gap.get m.profile
  cases m.profile <;> decide

theorem successful_metrics_slot_nonnegative {m : Model} {p : Metrics}
    (h : metrics m = .ok p) (r : Row) : 0 ≤ slot p r := by
  obtain ⟨_, hs, hg⟩ := successful_metrics_fixed_nonnegative h
  unfold slot
  split <;> omega

theorem pushRow_evidence {m : Model} {b : ModelBox} {i : Nat}
    {out : Array Row} {next : ForInStep (Array Row)}
    (hsize : i = out.size) (h : pushRow m (b, i) out = .ok next) :
    ∃ r, next = .yield (out.push r) ∧
      r.source = b ∧ 0 ≤ r.labelWidth ∧ 0 ≤ r.descWidth ∧
      (∀ parent, r.parent = some parent →
        parent < i ∧ openAncestor out parent out.size (out.size - 1) = true) := by
  unfold pushRow at h
  obtain ⟨parent, hp, h⟩ := row_bind_success h
  obtain ⟨checked, hguard, h⟩ := row_bind_success h
  obtain ⟨lw, hlw, h⟩ := row_bind_success h
  obtain ⟨dw, hdw, h⟩ := row_bind_success h
  have hl := measureWidth_nonnegative hlw
  have hd := measureWidth_nonnegative hdw
  have hparent : ∀ j, parent = some j →
      j < i ∧ openAncestor out j out.size (out.size - 1) = true := by
    intro j hj
    subst parent
    refine ⟨parentIndex_backward hp, ?_⟩
    by_cases hg : openAncestor out j out.size (i - 1) = true
    · simpa [hsize] using hg
    · simp [checkOpenParent, hg] at hguard
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨_, h.symm, rfl, hl, hd, hparent⟩
/-- The actual push preserves the interval invariant after the admission guard succeeds. -/
theorem openParentOrder_push {rs : Array Row} (horder : OpenParentOrder rs)
    (r : Row)
    (hnew : ∀ parent, r.parent = some parent →
      openAncestor rs parent rs.size (rs.size - 1) = true) :
    OpenParentOrder (rs.push r) := by
  intro child found parent hfound hparent
  by_cases heq : child = rs.size
  · subst child
    have heqrow : r = found := by
      simpa only [Array.getElem?_push_size, Option.some.injEq] using hfound
    subst found
    exact (openAncestor_sound rs parent rs.size (rs.size - 1)
      (hnew parent hparent)).push r
  · have hold : rs[child]? = some found := by
      simpa only [Array.getElem?_push, heq, ↓reduceIte] using hfound
    exact (horder child found parent hold hparent).push r

def RowsInvariant (rs : Array Row) : Prop :=
  OpenParentOrder rs ∧
    ∀ r ∈ rs.toList, 0 ≤ r.labelWidth ∧ 0 ≤ r.descWidth

theorem pushRow_invariant {m : Model} {b : ModelBox} {i : Nat}
    {out : Array Row} {next : ForInStep (Array Row)}
    (hi : i = out.size) (hinv : RowsInvariant out)
    (h : pushRow m (b, i) out = .ok next) :
    ∃ r, next = .yield (out.push r) ∧ RowsInvariant (out.push r) := by
  obtain ⟨r, hn, _, hl, hd, hp⟩ := pushRow_evidence hi h
  refine ⟨r, hn, openParentOrder_push hinv.1 r (fun j hj => (hp j hj).2), ?_⟩
  intro found hfound
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hfound
  rcases hfound with hold | heq
  · exact hinv.2 found hold
  · subst found
    exact ⟨hl, hd⟩

theorem rows_loop_invariant (m : Model) (inputs : List ModelBox)
    (start : Nat) (out final : Array Row)
    (hsize : out.size = start) (hinv : RowsInvariant out)
    (hrun : forIn (inputs.zipIdx start) out (pushRow m) = .ok final) :
    RowsInvariant final := by
  induction inputs generalizing start out with
  | nil =>
    have heq : out = final := by
      simpa only [List.zipIdx_nil, List.forIn_nil, pure, Except.pure,
        Except.ok.injEq] using hrun
    simpa only [← heq] using hinv
  | cons b inputs ih =>
    rw [List.zipIdx_cons, List.forIn_cons] at hrun
    cases hs : pushRow m (b, start) out with
    | error e => simp [hs, Bind.bind, Except.bind] at hrun
    | ok next =>
      obtain ⟨r, hn, hnext⟩ := pushRow_invariant hsize.symm hinv hs
      subst next
      have htail : forIn (inputs.zipIdx (start + 1)) (out.push r)
          (pushRow m) = .ok final := by
        simpa [hs, Bind.bind, Except.bind] using hrun
      exact ih (start + 1) (out.push r) (by simp [hsize]) hnext htail

def ParentDepthOrder (rs : Array Row) : Prop :=
  ∀ (child : Nat) (r : Row) (parent : Nat),
    rs[child]? = some r → r.parent = some parent →
      ∃ pr : Row, rs[parent]? = some pr ∧ parent < child ∧ r.depth = pr.depth + 1

theorem pushRow_parent_data {m : Model} {b : ModelBox} {i : Nat}
    {out : Array Row} {next : ForInStep (Array Row)}
    (h : pushRow m (b, i) out = .ok next) :
    ∃ r, next = .yield (out.push r) ∧ parentIndex m r.source i = .ok r.parent ∧
      ∀ j, r.parent = some j →
        j < i ∧ r.depth = ((out[j]?).map (·.depth)).getD 0 + 1 := by
  unfold pushRow at h
  obtain ⟨parent, hp, h⟩ := row_bind_success h
  obtain ⟨checked, _, h⟩ := row_bind_success h
  obtain ⟨lw, _, h⟩ := row_bind_success h
  obtain ⟨dw, _, h⟩ := row_bind_success h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨_, h.symm, hp, ?_⟩
  intro j hj
  change parent = some j at hj
  refine ⟨parentIndex_backward (by simpa only [hj] using hp), ?_⟩
  simp only [hj]

theorem parentDepthOrder_push {out : Array Row} {r : Row}
    (hinv : ParentDepthOrder out)
    (hnew : ∀ j, r.parent = some j →
      ∃ pr, out[j]? = some pr ∧ j < out.size ∧ r.depth = pr.depth + 1) :
    ParentDepthOrder (out.push r) := by
  intro child found parent hfound hp
  by_cases heq : child = out.size
  · subst child
    have hrow : r = found := by
      simpa only [Array.getElem?_push_size, Option.some.injEq] using hfound
    subst found
    obtain ⟨pr, hpr, hj, hd⟩ := hnew parent hp
    refine ⟨pr, ?_, hj, hd⟩
    simpa only [Array.getElem?_push, Nat.ne_of_lt hj, ↓reduceIte] using hpr
  · have hold : out[child]? = some found := by
      simpa only [Array.getElem?_push, heq, ↓reduceIte] using hfound
    obtain ⟨pr, hpr, hj, hd⟩ := hinv child found parent hold hp
    have hc : child < out.size := (Array.getElem?_eq_some_iff.mp hold).1
    have hparent : parent ≠ out.size := by omega
    refine ⟨pr, ?_, hj, hd⟩
    simpa only [Array.getElem?_push, hparent, ↓reduceIte] using hpr

theorem rows_loop_parent_depth (m : Model) (inputs : List ModelBox)
    (start : Nat) (out final : Array Row) (hsize : out.size = start)
    (hinv : ParentDepthOrder out)
    (hrun : forIn (inputs.zipIdx start) out (pushRow m) = .ok final) :
    ParentDepthOrder final := by
  induction inputs generalizing start out with
  | nil =>
    have heq : out = final := by
      simpa only [List.zipIdx_nil, List.forIn_nil, pure, Except.pure,
        Except.ok.injEq] using hrun
    simpa only [← heq] using hinv
  | cons b inputs ih =>
    rw [List.zipIdx_cons, List.forIn_cons] at hrun
    cases hs : pushRow m (b, start) out with
    | error e => simp [hs, Bind.bind, Except.bind] at hrun
    | ok next =>
      obtain ⟨r, hn, _, hd⟩ := pushRow_parent_data hs
      subst next
      have hnext : ParentDepthOrder (out.push r) := by
        apply parentDepthOrder_push hinv
        intro j hj
        obtain ⟨hlt, hdepth⟩ := hd j hj
        have hbound : j < out.size := by omega
        refine ⟨out[j], Array.getElem?_eq_getElem hbound, hbound, ?_⟩
        simpa only [Array.getElem?_eq_getElem hbound, Option.map_some,
          Option.getD_some] using hdepth
      have htail : forIn (inputs.zipIdx (start + 1)) (out.push r)
          (pushRow m) = .ok final := by
        simpa [hs, Bind.bind, Except.bind] using hrun
      exact ih (start + 1) (out.push r) (by simp [hsize]) hnext htail

theorem successful_rows_parent_depth {m : Model} {rs : List Row}
    (h : rows m = .ok rs) : ParentDepthOrder rs.toArray := by
  unfold rows at h
  by_cases hempty : m.boxes.isEmpty = true
  · simp [hempty, Bind.bind, Except.bind] at h
  · simp only [hempty] at h
    obtain ⟨out, hout, heq⟩ := row_bind_success h
    have hinit : ParentDepthOrder #[] := by
      intro child r parent hr
      simp at hr
    have hinv := rows_loop_parent_depth m m.boxes 0 #[] out rfl hinit hout
    have hrs : out.toList = rs := by
      simpa only [pure, Except.pure, Except.ok.injEq] using heq
    simpa only [← hrs, Array.toArray_toList] using hinv

theorem RouteAncestor.depth_order {rs : Array Row} (horder : ParentDepthOrder rs)
    {ancestor child : Nat} (h : RouteAncestor rs ancestor child) :
    ∀ r, rs[child]? = some r →
      ∃ ar, rs[ancestor]? = some ar ∧ ar.depth ≤ r.depth ∧
        (ancestor < child → ar.depth < r.depth) := by
  induction h with
  | self =>
    intro r hr
    exact ⟨r, hr, Nat.le_refl _, by omega⟩
  | @parent child parent old hr hp hancestor ih =>
    intro r hrow
    have heq : old = r := Option.some.inj (hr.symm.trans hrow)
    subst r
    obtain ⟨pr, hpr, _, hd⟩ := horder child old parent hr hp
    obtain ⟨ar, har, hle, _⟩ := ih pr hpr
    exact ⟨ar, har, by omega, by omega⟩

def ParentIndexOrder (m : Model) (rs : Array Row) : Prop :=
  ∀ (i : Nat) (r : Row), rs[i]? = some r →
    parentIndex m r.source i = .ok r.parent

theorem parentIndexOrder_push {m : Model} {out : Array Row} {r : Row}
    (hinv : ParentIndexOrder m out)
    (hnew : parentIndex m r.source out.size = .ok r.parent) :
    ParentIndexOrder m (out.push r) := by
  intro i found hfound
  by_cases heq : i = out.size
  · subst i
    have hrow : r = found := by
      simpa only [Array.getElem?_push_size, Option.some.injEq] using hfound
    subst found
    exact hnew
  · have hold : out[i]? = some found := by
      simpa only [Array.getElem?_push, heq, ↓reduceIte] using hfound
    exact hinv i found hold

theorem rows_loop_parent_indices (m : Model) (inputs : List ModelBox)
    (start : Nat) (out final : Array Row) (hsize : out.size = start)
    (hinv : ParentIndexOrder m out)
    (hrun : forIn (inputs.zipIdx start) out (pushRow m) = .ok final) :
    ParentIndexOrder m final := by
  induction inputs generalizing start out with
  | nil =>
    have heq : out = final := by
      simpa only [List.zipIdx_nil, List.forIn_nil, pure, Except.pure,
        Except.ok.injEq] using hrun
    simpa only [← heq] using hinv
  | cons b inputs ih =>
    rw [List.zipIdx_cons, List.forIn_cons] at hrun
    cases hs : pushRow m (b, start) out with
    | error e => simp [hs, Bind.bind, Except.bind] at hrun
    | ok next =>
      obtain ⟨r, hn, hindex, _⟩ := pushRow_parent_data hs
      subst next
      have hnext : ParentIndexOrder m (out.push r) :=
        parentIndexOrder_push hinv (by simpa only [hsize] using hindex)
      have htail : forIn (inputs.zipIdx (start + 1)) (out.push r)
          (pushRow m) = .ok final := by
        simpa [hs, Bind.bind, Except.bind] using hrun
      exact ih (start + 1) (out.push r) (by simp [hsize]) hnext htail

theorem successful_rows_parent_indices {m : Model} {rs : List Row}
    (h : rows m = .ok rs) : ParentIndexOrder m rs.toArray := by
  unfold rows at h
  by_cases hempty : m.boxes.isEmpty = true
  · simp [hempty, Bind.bind, Except.bind] at h
  · simp only [hempty] at h
    obtain ⟨out, hout, heq⟩ := row_bind_success h
    have hinit : ParentIndexOrder m #[] := by
      intro i r hr
      simp at hr
    have hinv := rows_loop_parent_indices m m.boxes 0 #[] out rfl hinit hout
    have hrs : out.toList = rs := by
      simpa only [pure, Except.pure, Except.ok.injEq] using heq
    simpa only [← hrs, Array.toArray_toList] using hinv

theorem rows_loop_sources (m : Model) (inputs : List ModelBox)
    (start : Nat) (out final : Array Row) (hsize : out.size = start)
    (hrun : forIn (inputs.zipIdx start) out (pushRow m) = .ok final) :
    final.toList.map (·.source) = out.toList.map (·.source) ++ inputs := by
  induction inputs generalizing start out with
  | nil =>
    have heq : out = final := by
      simpa only [List.zipIdx_nil, List.forIn_nil, pure, Except.pure,
        Except.ok.injEq] using hrun
    simp [← heq]
  | cons b inputs ih =>
    rw [List.zipIdx_cons, List.forIn_cons] at hrun
    cases hs : pushRow m (b, start) out with
    | error e => simp [hs, Bind.bind, Except.bind] at hrun
    | ok next =>
      obtain ⟨r, hn, hsource, _, _, _⟩ := pushRow_evidence hsize.symm hs
      subst next
      have htail : forIn (inputs.zipIdx (start + 1)) (out.push r)
          (pushRow m) = .ok final := by
        simpa [hs, Bind.bind, Except.bind] using hrun
      have hrest := ih (start + 1) (out.push r) (by simp [hsize]) htail
      simpa [Array.toList_push, List.map_append, hsource, List.append_assoc] using hrest

theorem successful_rows_sources {m : Model} {rs : List Row}
    (h : rows m = .ok rs) : rs.map (·.source) = m.boxes := by
  unfold rows at h
  by_cases hempty : m.boxes.isEmpty = true
  · simp [hempty, Bind.bind, Except.bind] at h
  · simp only [hempty] at h
    obtain ⟨out, hout, heq⟩ := row_bind_success h
    have hsources := rows_loop_sources m m.boxes 0 #[] out rfl hout
    have hrs : out.toList = rs := by
      simpa only [pure, Except.pure, Except.ok.injEq] using heq
    simpa [hrs] using hsources

theorem successful_rows_invariant {m : Model} {rs : List Row}
    (h : rows m = .ok rs) : RowsInvariant rs.toArray := by
  unfold rows at h
  by_cases hempty : m.boxes.isEmpty = true
  · simp [hempty, Bind.bind, Except.bind] at h
  · simp only [hempty] at h
    obtain ⟨out, hout, heq⟩ := row_bind_success h
    have hinit : RowsInvariant #[] := by
      constructor
      · intro child r parent hr
        simp at hr
      · simp
    have hinv := rows_loop_invariant m m.boxes 0 #[] out rfl hinit hout
    have hrs : out.toList = rs := by
      simpa only [pure, Except.pure, Except.ok.injEq] using heq
    simpa only [← hrs, Array.toArray_toList] using hinv

theorem successful_rows_descendant_interval {m : Model} {rs : List Row}
    (h : rows m = .ok rs) {ancestor last middle : Nat}
    (hlast : RouteAncestor rs.toArray ancestor last)
    (hleft : ancestor ≤ middle) (hright : middle ≤ last) :
    RouteAncestor rs.toArray ancestor middle :=
  treeview_descendant_interval (successful_rows_invariant h).1 hlast hleft hright

theorem successful_rows_widths {m : Model} {rs : List Row}
    (h : rows m = .ok rs) (r : Row) (hr : r ∈ rs) :
    0 ≤ r.labelWidth ∧ 0 ≤ r.descWidth := by
  apply (successful_rows_invariant h).2 r
  simpa only [List.toList_toArray] using hr

/-- Successful admission preserves the supplied containment metadata unchanged:
    it must already be empty, independently of the route ancestry. -/
theorem successful_layout_empty_parents {m : Model} {s : Scene}
    (h : layout m = .ok s) :
    m.boxes.any (fun b => b.parent != "") = false := by
  cases hp : m.boxes.any (fun b => b.parent != "") with
  | false => rfl
  | true => simp [layout, hp, Bind.bind, Except.bind] at h

/-- The descendants of each row form a declaration-order interval: once a
    traversal leaves that interval, no later declaration can re-enter it. -/
theorem treeview_no_descendant_reentry {rs : Array Row}
    (horder : OpenParentOrder rs) {ancestor middle last : Nat}
    (hleft : ancestor ≤ middle) (hright : middle ≤ last)
    (houtside : ¬ RouteAncestor rs ancestor middle) :
    ¬ RouteAncestor rs ancestor last := by
  intro hlast
  exact houtside (treeview_descendant_interval horder hlast hleft hright)

/-- Both ends of the constructed polyline lie on their actual row boxes. -/
theorem treeview_route_boundary_endpoints (p : Metrics) (rs : Array Row)
    (i j : Nat) (r parent : Row)
    (hp : r.parent = some j) (hj : rs[j]? = some parent)
    (hpx : 0 ≤ p.paddingX) (hh : 0 ≤ rowHeight p)
    (hlw : 0 ≤ parent.labelWidth) (hslot : 0 ≤ slot p parent) :
    (∃ first, (routePoints p rs i r).head? = some first ∧
      Validator.onBoundary first (rowRect p j parent)) ∧
    (∃ last, (routePoints p rs i r).getLast? = some last ∧
      Validator.onBoundary last (rowRect p i r)) := by
  constructor
  · exact ⟨_, treeview_route_first p rs i j r parent hp hj,
      treeview_source_boundary p j parent hpx hh hlw hslot⟩
  · exact ⟨_, treeview_route_last p rs i j r hp,
      treeview_target_boundary p i r hh⟩

theorem successful_assembly {m : Model} {s : Scene} (h : layout m = .ok s) :
    ∃ p rs routes,
      metrics m = .ok p ∧ rows m = .ok rs ∧
      m.routes.mapM (makeRoute m p rs) = .ok routes ∧
      s = assemble m p rs
        (rs.foldl (fun x r => max x (labelX p r + r.labelWidth + p.descGap)) 0)
        (rs.foldl (fun x r => if r.desc.isEmpty then x else max x
          (rs.foldl (fun x r => max x (labelX p r + r.labelWidth + p.descGap)) 0 +
            r.descWidth + p.paddingX))
          (rs.foldl (fun x r => max x (indent p r.depth + width p r)) 0))
        routes := by
  obtain ⟨p, rs, hp, hr, ht, hx, hy, hi⟩ := successful_layout_rows h
  have hparents := successful_layout_empty_parents h
  have hmetric : ¬ (p.textHeight < 1 ∨ p.paddingX < 0 ∨
      p.paddingY < 0 ∨ p.rowIndent < 0) := by omega
  simp only [layout, hparents, Bool.false_eq_true, ↓reduceIte,
    hp, hr, Bind.bind, Except.bind, hmetric] at h
  split at h
  · simp [throw] at h
  · cases hrt : m.routes.mapM (makeRoute m p rs) with
    | error e => simp [hrt] at h
    | ok routes =>
      refine ⟨p, rs, routes, hp, hr, hrt, ?_⟩
      symm
      simpa [hrt, pure, Except.pure] using h

theorem assemble_boxes_disjoint (m : Model) (p : Metrics) (rs : List Row)
    (descX right : Int) (routes : List Route) (hh : 0 ≤ rowHeight p) :
    ∀ a ∈ (assemble m p rs descX right routes).boxes,
      ∀ b ∈ (assemble m p rs descX right routes).boxes,
      a.id ≠ b.id → Disjoint a.rect b.rect := by
  intro a ha b hb hne
  dsimp only [assemble] at ha hb
  obtain ⟨⟨ra, i⟩, hai, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨rb, j⟩, hbj, rfl⟩ := List.mem_map.mp hb
  have hri := List.mem_zipIdx_iff_getElem?.mp hai
  have hrj := List.mem_zipIdx_iff_getElem?.mp hbj
  have hij : i ≠ j := by
    intro heq
    subst j
    have heqr : ra = rb := Option.some.inj (hri.symm.trans hrj)
    subst rb
    exact hne rfl
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact treeview_rows_no_interior_overlap p i j ra rb hh hlt
  · exact (Disjoint.comm _ _).mpr
      (treeview_rows_no_interior_overlap p j i rb ra hh hgt)

theorem assemble_canvas (m : Model) (p : Metrics) (rs : List Row)
    (routes : List Route) (hm : 0 ≤ p.margin) (ht : 1 ≤ p.textHeight)
    (hx : 0 ≤ p.paddingX) (hy : 0 ≤ p.paddingY) (hind : 0 ≤ p.rowIndent) :
    let descX := rs.foldl
      (fun x r => max x (labelX p r + r.labelWidth + p.descGap)) 0
    let right := rs.foldl (fun x r => if r.desc.isEmpty then x else
      max x (descX + r.descWidth + p.paddingX))
      (rs.foldl (fun x r => max x (indent p r.depth + width p r)) 0)
    Validator.C1 (assemble m p rs descX right routes).layoutDump := by
  dsimp only
  intro b hb
  dsimp only [Scene.layoutDump, assemble] at hb
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := List.mem_map.mp hb
  apply treeview_row_inside_fold_canvas rs p _ r i
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri))
    (List.mem_zipIdx' hri).1 hm ht hx hy hind

theorem successful_metric_bounds {m : Model} {s : Scene} {p : Metrics}
    (h : layout m = .ok s) (hp : metrics m = .ok p) :
    1 ≤ p.textHeight ∧ 0 ≤ p.paddingX ∧ 0 ≤ p.paddingY ∧ 0 ≤ p.rowIndent := by
  obtain ⟨actual, rs, ha, _, ht, hx, hy, hi⟩ := successful_layout_rows h
  rw [hp] at ha
  cases ha
  exact ⟨ht, hx, hy, hi⟩

theorem successful_canvas {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C1 s.layoutDump := by
  obtain ⟨p, rs, routes, hp, _, _, hs⟩ := successful_assembly h
  obtain ⟨ht, hx, hy, hi⟩ := successful_metric_bounds h hp
  have hm := (successful_metrics_fixed_nonnegative hp).1
  rw [hs]
  exact assemble_canvas m p rs routes hm ht hx hy hi

theorem successful_boxes_disjoint {m : Model} {s : Scene} (h : layout m = .ok s) :
    ∀ a ∈ s.boxes, ∀ b ∈ s.boxes, a.id ≠ b.id → Disjoint a.rect b.rect := by
  obtain ⟨p, rs, routes, hp, _, _, hs⟩ := successful_assembly h
  obtain ⟨ht, _, hy, _⟩ := successful_metric_bounds h hp
  have hh : 0 ≤ rowHeight p := by
    have := treeview_row_height_positive p ht hy
    omega
  rw [hs]
  exact assemble_boxes_disjoint m p rs _ _ routes hh

theorem successful_no_labels {m : Model} {s : Scene} (h : layout m = .ok s) :
    s.labels = [] := by
  obtain ⟨p, rs, routes, hp, hr, hrt, hs⟩ := successful_assembly h
  rw [hs]
  rfl

theorem successful_C2 {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C2 s.layoutDump := by
  intro a ha b hb hne _ _ _
  exact successful_boxes_disjoint h a ha b hb hne

theorem successful_C7 {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C7 s.layoutDump := by
  intro l hl
  simp [Scene.layoutDump, successful_no_labels h] at hl

theorem successful_C8 {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C8 s.layoutDump := by
  constructor
  · intro a ha _ b hb hne _ _
    exact successful_boxes_disjoint h a ha b hb (fun heq => hne heq.symm)
  · intro g hg hgroup l hl
    simp [Scene.layoutDump, successful_no_labels h] at hl

theorem successful_box_parents {m : Model} {s : Scene} (h : layout m = .ok s) :
    ∀ b ∈ s.boxes, b.parent = "" := by
  have hm : ∀ b ∈ m.boxes, b.parent = "" := by
    simpa using successful_layout_empty_parents h
  obtain ⟨p, rs, routes, hp, hr, hrt, hs⟩ := successful_assembly h
  rw [hs]
  intro b hb
  dsimp only [assemble] at hb
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := List.mem_map.mp hb
  have hrmem := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  have hsource : r.source ∈ rs.map (·.source) := List.mem_map.mpr ⟨r, hrmem, rfl⟩
  rw [successful_rows_sources hr] at hsource
  exact hm r.source hsource

theorem successful_C3 {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C3 s.layoutDump := by
  intro b hb hparent
  exact False.elim (hparent (successful_box_parents h b hb))

private theorem row_mapM_member {α β : Type} {inputs : List α}
    {f : α → Except LayoutError β} {out : List β} {b : β}
    (h : inputs.mapM f = .ok out) (hb : b ∈ out) :
    ∃ a ∈ inputs, f a = .ok b := by
  induction inputs generalizing out with
  | nil =>
    have heq : ([] : List β) = out := by
      simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using h
    simp [← heq] at hb
  | cons a inputs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨first, hf, h⟩ := row_bind_success h
    obtain ⟨rest, hr, h⟩ := row_bind_success h
    have heq : first :: rest = out := by
      simpa only [pure, Except.pure, Except.ok.injEq] using h
    rw [← heq] at hb
    simp only [List.mem_cons] at hb
    rcases hb with hfirst | hrest
    · subst b
      exact ⟨a, by simp, hf⟩
    · obtain ⟨a', ha', heq'⟩ := ih hr hrest
      exact ⟨a', by simp [ha'], heq'⟩

theorem makeRoute_evidence {m : Model} {p : Metrics} {rs : List Row}
    {source : ModelRoute} {out : Route} (h : makeRoute m p rs source = .ok out) :
    ∃ i r, m.boxes.findIdx? (fun b => b.id == source.toId) = some i ∧
      rs[i]? = some r ∧
      out = { id := source.id, fromId := source.fromId, toId := source.toId, orthogonal := source.orthogonal, points := routePoints p rs.toArray i r } := by
  unfold makeRoute at h
  cases hi : m.boxes.findIdx? (fun b => b.id == source.toId) with
  | none => simp [hi, throw] at h
  | some i =>
    simp only [hi] at h
    cases hr : rs[i]? with
    | none => simp [hr, throw] at h
    | some r =>
      refine ⟨i, r, rfl, hr, ?_⟩
      symm
      simpa only [hr, pure, Except.pure, Except.ok.injEq] using h

theorem successful_C4 {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C4 s.layoutDump := by
  obtain ⟨p, rs, routes, hp, hr, hrt, hs⟩ := successful_assembly h
  rw [hs]
  intro route hroute _
  obtain ⟨source, _, hsource⟩ := row_mapM_member hrt hroute
  obtain ⟨i, r, _, _, heq⟩ := makeRoute_evidence hsource
  rw [heq]
  exact treeview_route_orthogonal p rs.toArray i r

theorem successful_row_route_clearance {m : Model} {rs : List Row}
    (hrows : rows m = .ok rs) (p : Metrics)
    (ht : 1 ≤ p.textHeight) (hy : 0 ≤ p.paddingY)
    (hind : 0 ≤ p.rowIndent) (hpx : 0 ≤ p.paddingX)
    {i j k : Nat} {r parent foreign : Row}
    (hri : rs.toArray[i]? = some r) (hp : r.parent = some j)
    (hj : rs.toArray[j]? = some parent) (hk : rs.toArray[k]? = some foreign)
    (hki : k ≠ i) (hkj : k ≠ j) :
    ¬ Polyline.hitsRect (routePoints p rs.toArray i r) (rowRect p k foreign) := by
  have horder := successful_rows_parent_depth hrows
  obtain ⟨actualParent, hactual, hji, _⟩ := horder i r j hri hp
  have hheight := treeview_row_height_positive p ht hy
  have hh : 0 ≤ rowHeight p := by omega
  have hhalf : 0 ≤ Int.fdiv (rowHeight p) 2 ∧
      Int.fdiv (rowHeight p) 2 ≤ rowHeight p := by
    rw [Measure.fdiv_of_nonneg (by omega)]
    omega
  let x := indent p parent.depth + p.paddingX + p.margin
  let bottom := ((j : Int) + 1) * rowHeight p + p.margin
  let mid := (i : Int) * rowHeight p + p.margin + Int.fdiv (rowHeight p) 2
  have hbm : bottom ≤ mid := by
    have hs := treeview_rows_disjoint p j i parent r hh hji
    dsimp only [rowRect] at hs
    dsimp only [bottom, mid]
    have heq : ((j : Int) + 1) * rowHeight p =
        (j : Int) * rowHeight p + rowHeight p := by
      simp only [Int.add_mul, Int.one_mul]
    omega
  have horizontal : Polyline.segMisses
      ⟨x, mid⟩ ⟨indent p r.depth + p.margin, mid⟩ (rowRect p k foreign) := by
    by_cases hlt : k < i
    · have hs := treeview_rows_disjoint p k i foreign r hh hlt
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      dsimp only [rowRect] at hs ⊢
      dsimp only [mid]
      simp only [Int.min_self]
      omega
    · have hlt : i < k := by omega
      have hs := treeview_rows_disjoint p i k r foreign hh hlt
      refine Or.inr (Or.inr (Or.inl ?_))
      dsimp only [rowRect] at hs ⊢
      dsimp only [mid]
      simp only [Int.max_self]
      omega
  have vertical : Polyline.segMisses
      ⟨x, bottom⟩ ⟨x, mid⟩ (rowRect p k foreign) := by
    by_cases hleft : k < j
    · have hs := treeview_rows_disjoint p k j foreign parent hh hleft
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      dsimp only [rowRect] at hs ⊢
      dsimp only [bottom]
      have heq : ((j : Int) + 1) * rowHeight p =
          (j : Int) * rowHeight p + rowHeight p := by
        simp only [Int.add_mul, Int.one_mul]
      omega
    · by_cases hright : i < k
      · have hs := treeview_rows_disjoint p i k r foreign hh hright
        refine Or.inr (Or.inr (Or.inl ?_))
        dsimp only [rowRect] at hs ⊢
        dsimp only [mid]
        omega
      · have hjk : j < k := by omega
        have hkit : k < i := by omega
        have hancestor : RouteAncestor rs.toArray j i := .parent hri hp .self
        have hdesc := successful_rows_descendant_interval hrows hancestor
          (show j ≤ k by omega) (show k ≤ i by omega)
        obtain ⟨pr, hpr, _, hdepth⟩ := hdesc.depth_order horder foreign hk
        have heq : pr = parent := Option.some.inj (hpr.symm.trans hj)
        subst pr
        have hx := treeview_spine_left_of_deeper_row p parent foreign k
          (hdepth hjk) hind hpx
        exact Or.inl (by simpa only [Int.max_self] using hx)
  simp only [routePoints, hp, hj, Option.map_some, Option.getD_some]
  split
  · exact Polyline.not_hits_of_allMiss ⟨horizontal, trivial⟩
  · exact Polyline.not_hits_of_allMiss ⟨vertical, horizontal, trivial⟩

theorem source_id_at_index {m : Model} {rs : List Row} (hrows : rows m = .ok rs)
    {id : String} {i : Nat} {r : Row}
    (hi : m.boxes.findIdx? (fun b => b.id == id) = some i)
    (hr : rs[i]? = some r) : r.source.id = id := by
  have hbox : m.boxes[i]? = some r.source := by
    rw [← successful_rows_sources hrows]
    simp only [List.getElem?_map, hr, Option.map_some]
  have hfound := List.of_findIdx?_eq_some hi
  simpa only [hbox, beq_iff_eq] using hfound

theorem parentIndex_of_route {m : Model} {b : ModelBox} {i : Nat}
    {parent : Option Nat} {route : ModelRoute}
    (hp : parentIndex m b i = .ok parent)
    (hroute : route ∈ m.routes) (hid : b.id = route.toId) :
    ∃ j, parent = some j ∧
      m.boxes.findIdx? (fun a => a.id == route.fromId) = some j := by
  have hin : route ∈ m.routes.filter (fun r => r.toId == b.id) := by
    exact List.mem_filter.mpr ⟨hroute, by simp [hid]⟩
  unfold parentIndex at hp
  cases he : m.routes.filter (fun r => r.toId == b.id) with
  | nil => simp [he] at hin
  | cons edge rest =>
    cases rest with
    | cons edge2 rest => simp [he, throw] at hp
    | nil =>
      have heq : route = edge := by simpa only [he, List.mem_singleton] using hin
      subst edge
      simp only [he] at hp
      cases hj : m.boxes.findIdx? (fun a => a.id == route.fromId) with
      | none => simp [hj, throw] at hp
      | some j =>
        simp only [hj] at hp
        by_cases hji : j < i
        · have heq : some j = parent := by
            simpa only [hji, ↓reduceIte, pure, Except.pure, Except.ok.injEq] using hp
          exact ⟨j, heq.symm, rfl⟩
        · simp [hji, throw] at hp

theorem successful_route_data {m : Model} {rs : List Row}
    (hrows : rows m = .ok rs) {source : ModelRoute} {p : Metrics} {out : Route}
    (hsource : source ∈ m.routes) (hmake : makeRoute m p rs source = .ok out) :
    ∃ i j r parent, rs[i]? = some r ∧ rs[j]? = some parent ∧
      r.parent = some j ∧
      m.boxes.findIdx? (fun b => b.id == source.toId) = some i ∧
      m.boxes.findIdx? (fun b => b.id == source.fromId) = some j ∧
      out = { id := source.id, fromId := source.fromId, toId := source.toId, orthogonal := source.orthogonal, points := routePoints p rs.toArray i r } := by
  obtain ⟨i, r, hi, hr, hout⟩ := makeRoute_evidence hmake
  have hid := source_id_at_index hrows hi hr
  have hindex := successful_rows_parent_indices hrows i r
    (by simpa only [List.getElem?_toArray] using hr)
  obtain ⟨j, hp, hj⟩ := parentIndex_of_route hindex hsource hid
  obtain ⟨hjbound, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
  have hlen := congrArg List.length (successful_rows_sources hrows)
  simp only [List.length_map] at hlen
  have hrowbound : j < rs.length := by omega
  exact ⟨i, j, r, rs[j], hr, List.getElem?_eq_getElem hrowbound, hp, hi, hj, hout⟩

private theorem box_id_injective {boxes : List Box}
    (hn : (boxes.map (·.id)).Nodup) {a b : Box}
    (ha : a ∈ boxes) (hb : b ∈ boxes) (hid : a.id = b.id) : a = b := by
  induction boxes with
  | nil => simp at ha
  | cons first rest ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact False.elim (hn'.1 (List.mem_map.mpr ⟨b, hb, hid.symm⟩))
    · rcases hb with rfl | hb
      · exact False.elim (hn'.1 (List.mem_map.mpr ⟨a, ha, hid⟩))
      · exact ih hn'.2 ha hb

private theorem box_find_of_mem {boxes : List Box}
    (hn : (boxes.map (·.id)).Nodup) {b : Box} (hb : b ∈ boxes) :
    boxes.find? (fun a => a.id == b.id) = some b := by
  cases hf : boxes.find? (fun a => a.id == b.id) with
  | none =>
    have hfalse := (List.find?_eq_none.mp hf) b hb
    simp at hfalse
  | some a =>
    have hid : a.id = b.id := by simpa using List.find?_some hf
    have heq := box_id_injective hn (List.mem_of_find?_eq_some hf) hb hid
    exact congrArg some heq

theorem assemble_box_lookup {m : Model} {rs : List Row}
    (hwf : WellFormed m) (hrows : rows m = .ok rs)
    (p : Metrics) (descX right : Int) (routes : List Route)
    {id : String} {i : Nat} {r : Row}
    (hi : m.boxes.findIdx? (fun b => b.id == id) = some i)
    (hr : rs[i]? = some r) :
    (assemble m p rs descX right routes).layoutDump.box? id =
      some { id := r.source.id, role := r.source.role.id, parent := r.source.parent, exclusive := r.source.exclusive, rect := rowRect p i r } := by
  have hids : (assemble m p rs descX right routes).boxes.map (·.id) =
      m.boxes.map (·.id) := by
    have hfst := congrArg (List.map fun row : Row => row.source.id)
      (List.zipIdx_map_fst 0 rs)
    have hsource := congrArg (List.map fun b : ModelBox => b.id)
      (successful_rows_sources hrows)
    dsimp only [assemble]
    simp only [List.map_map, Function.comp_def] at hfst hsource ⊢
    exact hfst.trans hsource
  have hn : ((assemble m p rs descX right routes).boxes.map (·.id)).Nodup := by
    rw [hids]
    exact Model.boxIds_nodup hwf
  have hmem :
      ({ id := r.source.id, role := r.source.role.id, parent := r.source.parent, exclusive := r.source.exclusive, rect := rowRect p i r } : Box) ∈
        (assemble m p rs descX right routes).boxes := by
    exact List.mem_map.mpr ⟨(r, i), List.mem_zipIdx_iff_getElem?.mpr hr, rfl⟩
  have hid := source_id_at_index hrows hi hr
  unfold LayoutDump.box?
  change (assemble m p rs descX right routes).boxes.find? (fun b => b.id == id) = _
  rw [← hid]
  exact box_find_of_mem hn hmem

theorem successful_C5 {m : Model} {s : Scene}
    (hwf : WellFormed m) (h : layout m = .ok s) : Validator.C5 s.layoutDump := by
  obtain ⟨p, rs, routes, hp, hr, hrt, hs⟩ := successful_assembly h
  obtain ⟨ht, hx, hy, hi⟩ := successful_metric_bounds h hp
  have hh : 0 ≤ rowHeight p := by
    have := treeview_row_height_positive p ht hy
    omega
  rw [hs]
  intro route hroute
  obtain ⟨source, hsource, hmake⟩ := row_mapM_member hrt hroute
  obtain ⟨i, j, r, parent, hri, hpj, hparent, hto, hfrom, hout⟩ :=
    successful_route_data hr hsource hmake
  obtain ⟨hfirst, hlast⟩ := treeview_route_boundary_endpoints p rs.toArray i j r parent
    hparent (by simpa only [List.getElem?_toArray] using hpj) hx hh
    (successful_rows_widths hr parent (List.mem_of_getElem? hpj)).1
    (successful_metrics_slot_nonnegative hp parent)
  obtain ⟨first, hfirst, hfirstBoundary⟩ := hfirst
  obtain ⟨last, hlast, hlastBoundary⟩ := hlast
  rw [hout]
  exact ⟨first, last, _, _, hfirst, hlast,
    assemble_box_lookup hwf hr p _ _ routes hfrom hpj,
    assemble_box_lookup hwf hr p _ _ routes hto hri,
    hfirstBoundary, hlastBoundary⟩

theorem successful_C6 {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C6 s.layoutDump := by
  obtain ⟨p, rs, routes, hp, hr, hrt, hs⟩ := successful_assembly h
  obtain ⟨ht, hx, hy, hi⟩ := successful_metric_bounds h hp
  rw [hs]
  intro route hroute b hb _ hscope
  obtain ⟨source, hsource, hmake⟩ := row_mapM_member hrt hroute
  obtain ⟨i, j, r, parent, hri, hpj, hparent, hto, hfrom, hout⟩ :=
    successful_route_data hr hsource hmake
  dsimp only [assemble, Scene.layoutDump] at hb
  obtain ⟨⟨foreign, k⟩, hfk, rfl⟩ := List.mem_map.mp hb
  have hforeign := List.mem_zipIdx_iff_getElem?.mp hfk
  have hidTo := source_id_at_index hr hto hri
  have hidFrom := source_id_at_index hr hfrom hpj
  have hnotTo : foreign.source.id ≠ source.toId := by
    intro heq
    apply hscope
    rw [hout]
    simp [LayoutDump.routeScope, heq]
  have hnotFrom : foreign.source.id ≠ source.fromId := by
    intro heq
    apply hscope
    rw [hout]
    simp [LayoutDump.routeScope, heq]
  have hki : k ≠ i := by
    intro heq
    subst k
    have heqrow : foreign = r := Option.some.inj (hforeign.symm.trans hri)
    subst foreign
    exact hnotTo hidTo
  have hkj : k ≠ j := by
    intro heq
    subst k
    have heqrow : foreign = parent := Option.some.inj (hforeign.symm.trans hpj)
    subst foreign
    exact hnotFrom hidFrom
  rw [hout]
  exact successful_row_route_clearance hr p ht hy hi hx
    (by simpa only [List.getElem?_toArray] using hri) hparent
    (by simpa only [List.getElem?_toArray] using hpj)
    (by simpa only [List.getElem?_toArray] using hforeign) hki hkj

/-- Original full-kind contract, retained without strengthening model admission. -/
theorem treeview_valid {m : Model} {s : Scene} (hwf : WellFormed m)
    (_limits : WithinLimits m) (h : layout m = .ok s) : HardConstraints s.layoutDump :=
  ⟨successful_canvas h, successful_C2 h, successful_C3 h, successful_C4 h,
    successful_C5 hwf h, successful_C6 h, successful_C7 h, successful_C8 h⟩

/-- An executable non-preorder developer model: its last guide crosses n2. -/
def nonPreorderWitness : Model :=
  { kind := "treeview", boxes := [
      { id := "n0", shape := "file" }, { id := "n1", shape := "file" },
      { id := "n2", shape := "file" }, { id := "n3", shape := "file" }],
    routes := [{ id := "e0", fromId := "n0", toId := "n1" },
      { id := "e1", fromId := "n0", toId := "n2" },
      { id := "e2", fromId := "n1", toId := "n3" }],
    labels := [ { id := "n0.label", owner := "n0", text := "x" },
      { id := "n1.label", owner := "n1", text := "x" },
      { id := "n2.label", owner := "n2", text := "x" },
      { id := "n3.label", owner := "n3", text := "x" }] }

/-- Box containment metadata is independent of the preorder route relation. -/
def containmentWitness : Model :=
  { kind := "treeview", boxes := [{ id := "n0", parent := "n1", shape := "file" }, { id := "n1", shape := "file" }], routes := [{ id := "e0", fromId := "n0", toId := "n1" }], labels := [{ id := "n0.label", owner := "n0", text := "x" }, { id := "n1.label", owner := "n1", text := "x" }] }

/-- The same routed tree with no independent containment relation. -/
def containmentControl : Model :=
  { containmentWitness with
    boxes := [{ id := "n0", shape := "file" }, { id := "n1", shape := "file" }] }

end Elegant.Treeview
