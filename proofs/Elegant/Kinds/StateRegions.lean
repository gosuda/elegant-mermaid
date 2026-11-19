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

def regionSeparator (parent a b : Rect) (inset : Int) :
    Except LayoutError (Point × Point) := do
  let left ← stateCoord (parent.x + inset)
  let top ← stateCoord (parent.y + inset)
  let right ← stateCoord (parent.x + parent.w - inset)
  let bottom ← stateCoord (parent.y + parent.h - inset)
  if inset < 0 ∨ left > right ∨ top > bottom ∨ a.w ≤ 0 ∨ a.h ≤ 0 ∨ b.w ≤ 0 ∨ b.h ≤ 0 then
    throw .domain
  match ← regionGap a.x a.w b.x b.w with
  | some x => pure (⟨x, top⟩, ⟨x, bottom⟩)
  | none =>
    match ← regionGap a.y a.h b.y b.h with
    | some y => pure (⟨left, y⟩, ⟨right, y⟩)
    | none => throw .domain

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
