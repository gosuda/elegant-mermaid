import Elegant.Layered.SelectFacts
import Elegant.Layered.CoordGraph

set_option autoImplicit false

/-!
# C1 and C3 through `expandChild` and `layoutRecursive`

`expandChild` merges a successfully laid-out child scene into its parent scene:
every child box is shifted by `(dx, dy)` and child boxes whose parent was the
child root get `group.id` as their new parent. This file proves that the merge
preserves validator clauses C1 (canvas containment) and C3 (parent containment)
when both input scenes satisfy them, provided the shifted child canvas fits
inside the group frame, box lookups transport to the result, and parent
pointers stay inside their own scene.

`layoutRecursive_c1_c3_of_flat` lifts the same two clauses through the
recursive subdivision: the leaf case is a hypothesis function so the flat
layout theorems of other workers plug in directly, and the recursive case
consumes `expandChild_c1_c3` together with a second hypothesis function that
supplies the fit and lookup facts for each expansion.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-- `Rect.Contained` is invariant under a common translation. -/
theorem contained_shiftRect {a b : Rect} (dx dy : Int) :
    (shiftRect dx dy a).Contained (shiftRect dx dy b) ↔ a.Contained b := by
  simp only [shiftRect, Rect.Contained]
  omega

/-- The image of a child box inside the expanded scene: shifted by `(dx, dy)`,
with the child root parent rewritten to `group.id`. -/
def embedBox (groupId : String) (dx dy : Int) (box : Box) : Box :=
  { box with
    rect := shiftRect dx dy box.rect,
    parent := (if box.parent == "" then groupId else box.parent) }
/-- Sources of a successful `expandChild`: the frame lookup, the measured title
lines, the shift offsets, and the box/canvas equations of the result scene. -/
theorem expandChild_sources {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ (frame : Box) (metric : Measure.Metric) (titleLines : List Measure.Line)
      (lines : List (List Measure.Line)) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      metricOf o.profile = .ok metric ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        inp = .ok lines ∧
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let inset := childInset group.direction P.clusterPad titleWidth titleHeight
      dx = frame.rect.x + inset.x - P.canvasMargin ∧
      dy = frame.rect.y + inset.y - P.canvasMargin ∧
      res.scene.canvas = parent.scene.canvas ∧
      res.scene.boxes = inp.boxes.filterMap (fun model =>
        ((child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes).find? (fun box => box.id == model.id)) := by
  unfold expandChild at h
  cases hf : parent.scene.boxes.find? (fun box => box.id == group.id) with
  | none => simp [hf] at h; contradiction
  | some frame =>
    simp only [hf] at h
    obtain ⟨frame', hframe', h⟩ := bind_ok' h
    have heframe : frame = frame' := Except.ok.inj hframe'
    subst frame'
    obtain ⟨metric, hmetric, h⟩ := bind_ok' h
    obtain ⟨titleLines, htitle, h⟩ := bind_ok' h
    obtain ⟨itemMetric, hitemMetric, h⟩ := bind_ok' h
    have hemetric : itemMetric = metric := Except.ok.inj (hitemMetric.symm.trans hmetric)
    subst itemMetric
    obtain ⟨lines, hlines, h⟩ := bind_ok' h
    have he := Except.ok.inj h
    subst res
    exact ⟨frame, metric, titleLines, lines,
      frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x - P.canvasMargin,
      frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y - P.canvasMargin,
      rfl, hmetric, htitle, hlines, rfl, rfl, rfl, rfl⟩

/-- The executed title fact: `titleLines` is the wrapped group title the
expansion itself measured (the run's own metric and wrap target applied to
the group's text), exactly the equation `expandChild_sources` exposes as
`htitle`.  It is a needed premise of the step shapes: without it they are
unsatisfiable, because `childInset` for direction `"LR"` adds the title
width to the frame offset, so a caller list with a different foldl width
satisfies the `dx`/`dy` equations at an offset the merged scene never
stored, and any other width also moves the caption rect, whose `w` field is
that width. -/
def ExpandChildTitleWrapped (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) : Prop :=
  ∃ metric : Measure.Metric,
    metricOf o.profile = .ok metric ∧
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
        group.id).toList = .ok titleLines

/-- The geometric and lookup premises `expandChild` needs for C1 and C3: for
the located frame, the child canvas shifted by the computed offsets stays
inside the frame, every child box lookup lands on its shifted image in the
result, and every parent box lookup lands on itself. -/
def ExpandChildFits (P : Params) (_inp : Input) (_o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    frame.rect.Contained
        (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)) ∧
    (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      result.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box)) ∧
    (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      result.scene.layoutDump.box? box.id = some box)

/-- Every nonempty parent pointer of a scene box names another box of the same
scene. -/
def SceneParentClosed (scene : Scene) : Prop :=
  ∀ b ∈ scene.boxes, b.parent = "" ∨ ∃ p ∈ scene.boxes, p.id = b.parent

/-- `expandChild` preserves C1 and C3. Parent-scene boxes keep their containment
in the unchanged canvas; shifted child boxes land inside the group frame, which
itself lies in the parent canvas. Rewritten child roots are contained in the
frame by the canvas-fit premise; deeper child boxes keep their shifted parent
containment. -/
theorem expandChild_c1_c3 {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (hparentC1 : Validator.C1 parent.scene.layoutDump)
    (hchildC1 : Validator.C1 child.scene.layoutDump)
    (hparentC3 : Validator.C3 parent.scene.layoutDump)
    (hchildC3 : Validator.C3 child.scene.layoutDump)
    (hfit : ExpandChildFits P inp o group titleHeight parent child result)
    (hparentClosed : SceneParentClosed parent.scene)
    (hchildClosed : SceneParentClosed child.scene)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C1 result.scene.layoutDump ∧ Validator.C3 result.scene.layoutDump := by
  obtain ⟨frame, _metric, titleLines, _lines, dx, dy, hframe, _hmetric, _htitle,
    _hlines, hdx, hdy, hcanvas, hboxes⟩ := expandChild_sources h
  have hframeMem : frame ∈ parent.scene.boxes := List.mem_of_find?_eq_some hframe
  have hfit' := hfit frame titleLines dx dy hframe hdx hdy
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hcanvasRect : Validator.canvasRect result.scene.layoutDump =
      Validator.canvasRect parent.scene.layoutDump := by
    unfold Validator.canvasRect
    have : result.scene.layoutDump.canvas = parent.scene.layoutDump.canvas := hcanvas
    rw [this]
  have hframeC1 : (Validator.canvasRect result.scene.layoutDump).Contained frame.rect := by
    rw [hcanvasRect]
    exact hparentC1 frame hframeMem
  constructor
  · intro b hb
    have hbMem : b ∈ result.scene.layoutDump.boxes := hb
    simp only [Scene.layoutDump] at hbMem
    change b ∈ result.scene.boxes at hbMem
    rw [hboxes] at hbMem
    obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hbMem
    have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes := List.mem_of_find?_eq_some hfind
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbc
      have hshift : (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
          (shiftRect dx dy c.rect) := (contained_shiftRect dx dy).mpr (hchildC1 c hc)
      exact Rect.Contained.trans hframeC1 (Rect.Contained.trans hfit'.1 hshift)
    · rw [hcanvasRect]
      exact hparentC1 b hbp
  · intro b hb hne p hp
    simp only [Scene.layoutDump] at hb
    change b ∈ result.scene.boxes at hb
    rw [hboxes] at hb
    obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hb
    have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes := List.mem_of_find?_eq_some hfind
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨c, hc, hbEq⟩ := List.mem_map.mp hbc
      by_cases hcRoot : c.parent = ""
      · have hbParent : b.parent = group.id := by
          have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
            rw [← hbEq]; rfl
          rw [hproj]
          simp [hcRoot]
        have hframeSelf : parent.scene.layoutDump.box? frame.id = some frame := by
          rw [hframeId]
          exact hframe
        have hresultLookup := hfit'.2.2 frame hframeSelf
        rw [hframeId] at hresultLookup
        rw [hbParent] at hp
        rw [hresultLookup] at hp
        have hpEq : frame = p := Option.some.inj hp
        subst hpEq
        have hshift : (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
            (shiftRect dx dy c.rect) := (contained_shiftRect dx dy).mpr (hchildC1 c hc)
        rw [← hbEq]
        exact Rect.Contained.trans hfit'.1 hshift
      · have hbParent : b.parent = c.parent := by
          have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
            rw [← hbEq]; rfl
          rw [hproj]
          simp [hcRoot]
        rcases hchildClosed c hc with hcpEmpty | ⟨p', hp'mem, hp'id⟩
        · exact absurd hcpEmpty hcRoot
        · have hfindNe : child.scene.boxes.find? (fun candidate => candidate.id == c.parent) ≠ none := by
            intro hnone
            rw [List.find?_eq_none] at hnone
            exact absurd (hnone p' hp'mem) (by simp [hp'id])
          cases hfind2 : child.scene.boxes.find? (fun candidate => candidate.id == c.parent) with
          | none => exact absurd hfind2 hfindNe
          | some p'' =>
            have hchildLookup : child.scene.layoutDump.box? c.parent = some p'' := hfind2
            have hp''cont := hchildC3 c hc hcRoot p'' hchildLookup
            have hp''id : p''.id = c.parent := by simpa using List.find?_some hfind2
            have hp''self : child.scene.layoutDump.box? p''.id = some p'' := by
              rw [hp''id]; exact hchildLookup
            have hchildLookup' := hfit'.2.1 p'' hp''self
            rw [hp''id] at hchildLookup'
            rw [hbParent] at hp
            rw [hchildLookup'] at hp
            have hpEq : embedBox group.id dx dy p'' = p := Option.some.inj hp
            subst hpEq
            have hshift : (shiftRect dx dy p''.rect).Contained (shiftRect dx dy c.rect) :=
              (contained_shiftRect dx dy).mpr hp''cont
            rw [← hbEq]
            exact hshift
    · rcases hparentClosed b hbp with hbEmpty | ⟨p', hp'mem, hp'id⟩
      · exact absurd hbEmpty hne
      · have hfindNe : parent.scene.boxes.find? (fun candidate => candidate.id == b.parent) ≠ none := by
          intro hnone
          rw [List.find?_eq_none] at hnone
          exact absurd (hnone p' hp'mem) (by simp [hp'id])
        cases hfind2 : parent.scene.boxes.find? (fun candidate => candidate.id == b.parent) with
        | none => exact absurd hfind2 hfindNe
        | some p'' =>
          have hparentLookup : parent.scene.layoutDump.box? b.parent = some p'' := hfind2
          have hp''cont := hparentC3 b hbp hne p'' hparentLookup
          have hp''id : p''.id = b.parent := by simpa using List.find?_some hfind2
          have hp''self : parent.scene.layoutDump.box? p''.id = some p'' := by
            rw [hp''id]; exact hparentLookup
          have hparentLookup' := hfit'.2.2 p'' hp''self
          rw [hp''id] at hparentLookup'
          rw [hparentLookup'] at hp
          have hpEq : p'' = p := Option.some.inj hp
          subst hpEq
          exact hp''cont

/-- `layoutRecursive` preserves C1 and C3, given the flat-layout clauses for the
leaf case and, for every `expandChild` call the recursion performs, the frame
fit, lookup transport, and parent-closure facts. -/
theorem layoutRecursive_c1_c3_of_flat
    (hflat : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      layout inp o = .ok res →
      Validator.C1 res.scene.layoutDump ∧ Validator.C3 res.scene.layoutDump)
    (hgeo : ∀ (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      ExpandChildFits P inp o group titleHeight parent child res ∧
      SceneParentClosed parent.scene ∧ SceneParentClosed child.scene) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res →
      Validator.C1 res.scene.layoutDump ∧ Validator.C3 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res h
      exact hflat inp o res h
  | succ fuel ih =>
      intro inp o res h
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, P, metric, child, titleLines, parent, _hgroup, _hP, _hm, hchild, _hwrap,
          hparent, hexpand⟩
      · exact hflat inp o res hlayout
      · have hc := ih _ _ _ hchild
        have hp := ih _ _ _ hparent
        have hcl := hgeo P inp o group _ parent child res hexpand
        exact expandChild_c1_c3 hp.1 hc.1 hp.2 hc.2 hcl.1 hcl.2.1 hcl.2.2 hexpand

end Elegant.Layered.PipelineImpl
