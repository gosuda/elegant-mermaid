import Elegant.Kinds.Common
import Elegant.Layered.RegionPipeline

set_option autoImplicit false

/-! Divider painting for concurrent regions (Go's `paintRegions`). Every region group loses
its items; between consecutive regions of a set a dashed rule is inserted into the composite
group's items ahead of its first non-shape primitive. -/

namespace Elegant
namespace Kinds
namespace StateRegions

open Common

def groupBoxes (m : Model) : List ModelBox := m.boxes.filter fun b => b.role == .group

def boxRect (s : Scene) (id : String) : Except LayoutError Rect :=
  match s.boxes.find? fun b => b.id == id with
  | some b => pure b.rect
  | none => throw .domain

def stateCoord (v : Int) : Except LayoutError Int :=
  if I32_MIN ≤ v ∧ v ≤ I32_MAX then pure v else throw .overflow

/-- Go's `regionGap`: the middle of the gap when two spans are disjoint. -/
def regionGap (aStart aSize bStart bSize : Int) : Except LayoutError (Option Int) := do
  let aEnd ← stateCoord (aStart + aSize)
  let bEnd ← stateCoord (bStart + bSize)
  if aEnd ≤ bStart then pure (some (Int.fdiv (aEnd + bStart) 2))
  else if bEnd ≤ aStart then pure (some (Int.fdiv (bEnd + aStart) 2))
  else pure none

/-- The adjacent regions' cross-axis envelope clipped to the parent's inset. -/
def clippedSpan (parentStart parentEnd aStart aEnd bStart bEnd : Int) : Int × Int :=
  ⟨max parentStart (min aStart bStart), min parentEnd (max aEnd bEnd)⟩

theorem clippedSpan_parent_bounds (parentStart parentEnd aStart aEnd bStart bEnd : Int) :
    parentStart ≤ (clippedSpan parentStart parentEnd aStart aEnd bStart bEnd).1 ∧
    (clippedSpan parentStart parentEnd aStart aEnd bStart bEnd).2 ≤ parentEnd := by
  exact ⟨Int.le_max_left _ _, Int.min_le_left _ _⟩

theorem clippedSpan_body_bounds (parentStart parentEnd aStart aEnd bStart bEnd : Int) :
    min aStart bStart ≤ (clippedSpan parentStart parentEnd aStart aEnd bStart bEnd).1 ∧
    (clippedSpan parentStart parentEnd aStart aEnd bStart bEnd).2 ≤ max aEnd bEnd := by
  exact ⟨Int.le_max_right _ _, Int.min_le_right _ _⟩

/-- A separator clipped to both child bodies starts after any title ending before them. -/
theorem clippedSpan_title_clearance
    {parentStart parentEnd aStart aEnd bStart bEnd titleEnd : Int}
    (ha : titleEnd ≤ aStart) (hb : titleEnd ≤ bStart) :
    titleEnd ≤ (clippedSpan parentStart parentEnd aStart aEnd bStart bEnd).1 := by
  exact Int.le_trans (Int.le_min.mpr ⟨ha, hb⟩) (Int.le_max_right _ _)

/-- Keep the gap midpoint only when it lies inside the clipped region envelope. -/
def separatorSegment (left top right bottom : Int) (vertical : Bool) (middle : Int) :
    Except LayoutError (Point × Point) :=
  if vertical then
    if left ≤ middle ∧ middle ≤ right then .ok (⟨middle, top⟩, ⟨middle, bottom⟩)
    else .error .domain
  else
    if top ≤ middle ∧ middle ≤ bottom then .ok (⟨left, middle⟩, ⟨right, middle⟩)
    else .error .domain

/-- Both endpoints of an accepted divider lie within its ordered clipped bounds. -/
theorem separatorSegment_contained {left top right bottom middle : Int}
    {vertical : Bool} {p q : Point} (hwidth : left ≤ right) (hheight : top ≤ bottom)
    (h : separatorSegment left top right bottom vertical middle = .ok (p, q)) :
    (left ≤ p.x ∧ p.x ≤ right ∧ top ≤ p.y ∧ p.y ≤ bottom) ∧
    (left ≤ q.x ∧ q.x ≤ right ∧ top ≤ q.y ∧ q.y ≤ bottom) := by
  cases vertical with
  | false =>
    by_cases hmiddle : top ≤ middle ∧ middle ≤ bottom
    · simp only [separatorSegment, Bool.false_eq_true, ↓reduceIte, hmiddle] at h
      rcases h with ⟨rfl, rfl⟩
      dsimp only
      omega
    · simp [separatorSegment, hmiddle] at h
  | true =>
    by_cases hmiddle : left ≤ middle ∧ middle ≤ right
    · simp only [separatorSegment, ↓reduceIte, hmiddle] at h
      rcases h with ⟨rfl, rfl⟩
      dsimp only
      omega
    · simp [separatorSegment, hmiddle] at h

/-- The midpoint guard also protects a title above the clipped envelope. -/
theorem separatorSegment_title_clearance {left top right bottom middle titleEnd : Int}
    {vertical : Bool} {p q : Point} (hwidth : left ≤ right) (hheight : top ≤ bottom)
    (htitle : titleEnd ≤ top)
    (h : separatorSegment left top right bottom vertical middle = .ok (p, q)) :
    titleEnd ≤ p.y ∧ titleEnd ≤ q.y := by
  have bounds := separatorSegment_contained hwidth hheight h
  exact ⟨Int.le_trans htitle bounds.1.2.2.1, Int.le_trans htitle bounds.2.2.2.1⟩

def regionSeparator (parent a b : Rect) (inset : Int) :
    Except LayoutError (Point × Point) := do
  let parentLeft ← stateCoord (parent.x + inset)
  let parentTop ← stateCoord (parent.y + inset)
  let parentRight ← stateCoord (parent.x + parent.w - inset)
  let parentBottom ← stateCoord (parent.y + parent.h - inset)
  let aRight ← stateCoord (a.x + a.w)
  let bRight ← stateCoord (b.x + b.w)
  let aBottom ← stateCoord (a.y + a.h)
  let bBottom ← stateCoord (b.y + b.h)
  let (left, right) := clippedSpan parentLeft parentRight a.x aRight b.x bRight
  let (top, bottom) := clippedSpan parentTop parentBottom a.y aBottom b.y bBottom
  if inset < 0 ∨ left > right ∨ top > bottom ∨ a.w ≤ 0 ∨ a.h ≤ 0 ∨ b.w ≤ 0 ∨ b.h ≤ 0 then
    throw .domain
  match ← regionGap a.x a.w b.x b.w with
  | some x => separatorSegment left top right bottom true x
  | none =>
    match ← regionGap a.y a.h b.y b.h with
    | some y => separatorSegment left top right bottom false y
    | none => throw .domain

-- Adjacent bodies begin below the parent's title; their divider must do so too.
#guard (regionSeparator ⟨0, 0, 30, 20⟩ ⟨3, 6, 8, 8⟩ ⟨15, 7, 7, 6⟩ 1).toOption =
  some (⟨13, 6⟩, ⟨13, 14⟩)
#guard (regionSeparator ⟨0, 0, 30, 20⟩ ⟨15, 7, 7, 6⟩ ⟨3, 6, 8, 8⟩ 1).toOption =
  some (⟨13, 6⟩, ⟨13, 14⟩)
#guard (regionSeparator ⟨0, 0, 30, 30⟩ ⟨5, 7, 7, 5⟩ ⟨4, 17, 10, 6⟩ 1).toOption =
  some (⟨4, 14⟩, ⟨14, 14⟩)
#guard match regionSeparator ⟨0, 0, 20, 20⟩ ⟨-10, 3, 2, 4⟩ ⟨-5, 3, 10, 4⟩ 1 with
  | .error .domain => true
  | _ => false
#guard match regionSeparator ⟨I32_MAX, 0, 1, 20⟩ ⟨0, 0, 2, 2⟩ ⟨4, 0, 2, 2⟩ 0 with
  | .error .overflow => true
  | _ => false

def isShapePrimitive : Primitive → Bool
  | .rect _ _ | .roundRect _ _ _ | .ellipse _ _ _ _ _ | .polygon _ _
  | .polyline _ _ _ | .path _ _ => true
  | _ => false

def dividerPaint : Paint := { style := "rule", line := .dashed }

/-- Go inserts the dividers ahead of the first non-shape primitive of the composite group. -/
def insertDividers (dividers : List Primitive) (g : Group) : Group :=
  let cut := (g.items.findIdx? fun item => !isShapePrimitive item).getD g.items.length
  { g with items := g.items.take cut ++ dividers ++ g.items.drop cut }

def paintRegionSet (m : Model) (s : Scene) (set : ModelRegionSet)
    (inset : Int) : Except LayoutError Scene := do
  let groups := groupBoxes m
  let idAt (i : Int) : Except LayoutError String :=
    if 0 ≤ i ∧ i < groups.length then
      match groups[i.toNat]? with
      | some b => pure b.id
      | none => throw .domain
    else throw .domain
  let rectAt (i : Int) : Except LayoutError Rect := do
    let id ← idAt i
    boxRect s id
  let groupAt (i : Int) : Except LayoutError String := do
    let id ← idAt i
    if s.items.any fun g => g.role == .group && g.owner == id then pure id
    else throw .domain
  let parentRect ← rectAt set.parent
  let regionOwners ← set.regions.mapM groupAt
  let cleared : Scene := { s with
    items := s.items.map fun g =>
      if g.role == .group && regionOwners.contains g.owner then { g with items := [] }
      else g }
  let parentOwner ← groupAt set.parent
  let dividers ← (set.regions.zip set.regions.tail).mapM fun pair => do
    let a ← rectAt pair.1
    let b ← rectAt pair.2
    let (p, q) ← regionSeparator parentRect a b inset
    pure (.polyline [p, q] 0 dividerPaint : Primitive)
  pure { cleared with
    items := cleared.items.map fun g =>
      if g.role == .group && g.owner == parentOwner then
        insertDividers dividers g
      else g }

/-- Go's `paintRegions`: nothing to do without region sets. -/
def paintRegions (m : Model) (s : Scene) : Except LayoutError Scene :=
  if m.regionSets.isEmpty then pure s
  else
    let inset := LayoutConst.cluster_pad.get m.options.profile
    m.regionSets.foldlM (fun s set => paintRegionSet m s set inset) s

end StateRegions
end Kinds
end Elegant
