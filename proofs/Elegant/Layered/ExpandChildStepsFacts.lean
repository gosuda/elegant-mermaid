import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.RecursiveC78
import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC6
import Elegant.Layered.SelectFacts
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.Assembly

set_option autoImplicit false

/-!
# Per-expansion facts of the recursive lifts

For one `expandChild` call inside `layoutRecursive`, the recursive lifts
`layoutRecursive_c8a_of_flat`, `layoutRecursive_c8b_of_flat`, and
`layoutRecursive_c7_of_flat` consume a per-expansion step package
(`ExpandChildC8aStep`, `ExpandChildC8bStep`, `ExpandChildC7Step`).  Each
step splits into:

* a **geometric remainder** — frame containment of shifted child boxes and
  the cross-scene `Disjoint`/`StrictInside`/`meetsInterior` clearance pairs —
  packaged here as `ExpandChildC8aGeometry`, `ExpandChildC8bGeometry`, and
  `ExpandChildC7Geometry`.  These are the facts the family seam owns;
* a **structural remainder** — box-lookup transport, scene-size bounds, the
  frame's group role, child/group isolation, ancestor and owner-scope
  anchors, and the label classifications — packaged here as
  `ExpandChildC8aStructure`, `ExpandChildC8bStructure`, and
  `ExpandChildC7Structure`.

`expandChild_c8a_step_of_geometry`, `expandChild_c8b_step_of_geometry`, and
`expandChild_c7_step_of_geometry` assemble each step package from its two
named remainders.  The structural remainders are hypotheses of these
theorems, not conjuncts of the geometry definitions: they are the facts the
expansion's assembly (`expandChild_sources`, `expandChild_assembly_sources`,
`layoutRecursive_ids`, `recursive_selected_box_ids_disjoint`) and the
label-owner pipeline invariant (`ExpandChildLabelOwners`) are expected to
discharge at the family seam.
-/

namespace Elegant.Layered.PipelineImpl

/-! ### Keyed-list injectivity -/

/-- Two members of a list with nodup keys that carry equal keys are equal. -/
theorem expandChild_nodup_map_inj {α : Type} (f : α → String) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha (by simp)
  | x :: xs, hnd, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exfalso
        exact hnd.1 (he ▸ List.mem_map_of_mem hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exfalso
        exact hnd.1 (he ▸ List.mem_map_of_mem ha')
      · exact expandChild_nodup_map_inj f hnd.2 ha' hb' he

/-! ### The label-owner pipeline invariant -/

/-- A scene label and an input label with the same id carry the same owner:
`layout` emits labels from the input labels, so ids and owners travel
together through every stage, and the two recursive sub-scenes inherit the
property the same way. -/
def ExpandChildLabelOwners (inp : Input) (parent child : FamilyResult) : Prop :=
  (∀ cl ∈ child.scene.labels, ∀ m ∈ inp.labels, m.id = cl.id → m.owner = cl.owner) ∧
  (∀ pl ∈ parent.scene.labels, ∀ m ∈ inp.labels, m.id = pl.id → m.owner = pl.owner)

/-! ### Proved structural facts of one expansion -/

/-- The offset-independent structural facts of one `expandChild` call: the
two scene-size bounds and the child/group id isolation.  Discharged from
the expansion's id equations (`expandChild_ids`, `layoutRecursive_ids`),
the `selectInput` id/filter lemmas, route coverage transported through
`independent_inside`, and `recursive_selected_box_ids_disjoint`.

The box-lookup transports are deliberately NOT proved here: `hctx` never
pins `titleLines` to the lines `expandChild` wraps internally, so the
step's `dx dy` may differ from the offsets the merged scene actually used,
making a transport stated at the step's `dx dy` unprovable in general.
They remain in the structure hypotheses. -/
theorem expandChild_merge_bounds
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    child.scene.boxes.length ≤ res.scene.boxes.length ∧
    parent.scene.boxes.length ≤ res.scene.boxes.length ∧
    (∀ (frame : Box), parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hchildCov : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hparentCov : RoutesCovered (parentSubInput inp group P titleLines child) :=
    selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hchildIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hchildCov hchild
  have hparentIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hparentCov hparent
  have hdisjoint := recursive_selected_box_ids_disjoint hchild hparent
  -- every input box id is emitted by exactly one sub-scene
  have hbox : ∀ b ∈ inp.boxes, ∃ x ∈ child.scene.boxes ++ parent.scene.boxes, x.id = b.id := by
    intro b hb
    by_cases hi : Compound.inside inp.boxes group.id b.id = true
    · obtain ⟨cb, _hcbmem, hcbid, _⟩ := selectInput_box_exists inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id hb hi
      have hcid : child.scene.boxes.map (·.id) =
          (inp.boxes.filter
            (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
        have hsel : (childSubInput inp group).boxes.map (·.id) =
            (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
          show (selectInput inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
              (·.id) =
            (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id)
          rw [selectInput_box_ids]
        rw [hchildIds.1, hsel]
      have hmem : b.id ∈ child.scene.boxes.map (·.id) := by
        rw [hcid]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hi⟩, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
      exact ⟨x, List.mem_append_left _ hx, hxid⟩
    · have hninside : (!Compound.inside inp.boxes group.id b.id) = true := by
        rw [Bool.not_eq_true']; exact Bool.of_not_eq_true hi
      obtain ⟨pb, _hpbmem, hpbid, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hb hninside
      have hpid : parent.scene.boxes.map (·.id) =
          (inp.boxes.filter
            (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
        have hboxes : (parentSubInput inp group P titleLines child).boxes =
            (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
        rw [hparentIds.1, hboxes, selectInput_box_ids]
      have hmem : b.id ∈ parent.scene.boxes.map (·.id) := by
        rw [hpid]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hninside⟩, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
      exact ⟨x, List.mem_append_right _ hx, hxid⟩
  -- every input route id is emitted by exactly one sub-scene: the group's
  -- independence keeps both endpoints on the same side of the split
  have hroute : ∀ r ∈ inp.routes,
      ∃ x ∈ child.scene.routes ++ parent.scene.routes, x.id = r.id := by
    intro r hr
    obtain ⟨⟨bf, hbf, hbfid⟩, ⟨bt, hbt, hbtid⟩⟩ := hcovered r hr
    have hIndep : Compound.independent inp.boxes inp.routes group = true := by
      have hfind := List.find?_some hgroup
      simp only [Bool.and_eq_true] at hfind
      exact hfind.1
    have hsame := independent_inside hIndep r hr
    by_cases hi : Compound.inside inp.boxes group.id r.fromId = true
    · have hti : Compound.inside inp.boxes group.id r.toId = true := by
        rw [← hsame]; exact hi
      obtain ⟨bf', hbf'mem, hbf'id, _⟩ := selectInput_box_exists inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id hbf
        (by rw [hbfid]; exact hi)
      obtain ⟨bt', hbt'mem, hbt'id, _⟩ := selectInput_box_exists inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id hbt
        (by rw [hbtid]; exact hti)
      have hmem : r ∈ (childSubInput inp group).routes := by
        exact (selectInput_route_mem inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id r).mpr
          ⟨hr, by
            rw [List.any_eq_true]
            exact ⟨bf', hbf'mem, by simp [hbf'id, hbfid]⟩,
          by
            rw [List.any_eq_true]
            exact ⟨bt', hbt'mem, by simp [hbt'id, hbtid]⟩⟩
      have hcr : child.scene.routes.map (·.id) =
          (childSubInput inp group).routes.map (·.id) := hchildIds.2
      have hmid : r.id ∈ child.scene.routes.map (·.id) := by
        rw [hcr]
        exact List.mem_map.mpr ⟨r, hmem, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmid
      exact ⟨x, List.mem_append_left _ hx, hxid⟩
    · have hfi : Compound.inside inp.boxes group.id r.fromId = false :=
        Bool.of_not_eq_true hi
      have hft : Compound.inside inp.boxes group.id r.toId = false := by
        have := hsame
        rw [hfi] at this
        exact this.symm
      obtain ⟨bf', hbf'mem, hbf'id, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hbf
        (by rw [hbfid]; rw [Bool.not_eq_true']; exact hfi)
      obtain ⟨bt', hbt'mem, hbt'id, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hbt
        (by rw [hbtid]; rw [Bool.not_eq_true']; exact hft)
      have hmem : r ∈ (parentSubInput inp group P titleLines child).routes := by
        have hsel := (selectInput_route_mem inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" r).mpr
          ⟨hr, by
            rw [List.any_eq_true]
            exact ⟨bf', hbf'mem, by simp [hbf'id, hbfid]⟩,
          by
            rw [List.any_eq_true]
            exact ⟨bt', hbt'mem, by simp [hbt'id, hbtid]⟩⟩
        have hroutes : (parentSubInput inp group P titleLines child).routes =
            (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := rfl
        rwa [hroutes]
      have hpr : parent.scene.routes.map (·.id) =
          (parentSubInput inp group P titleLines child).routes.map (·.id) := hparentIds.2
      have hmid : r.id ∈ parent.scene.routes.map (·.id) := by
        rw [hpr]
        exact List.mem_map.mpr ⟨r, hmem, rfl⟩
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmid
      exact ⟨x, List.mem_append_right _ hx, hxid⟩
  obtain ⟨hboxIds, hroutesIds⟩ := expandChild_ids hexpand hbox hroute
  have hresLen : res.scene.boxes.length = inp.boxes.length := by
    have h := congrArg List.length hboxIds
    simp only [List.length_map] at h
    exact h
  have hchildLen : child.scene.boxes.length = (childSubInput inp group).boxes.length := by
    have h := congrArg List.length hchildIds.1
    simpa using h
  have hparentLen : parent.scene.boxes.length =
      (parentSubInput inp group P titleLines child).boxes.length := by
    have h := congrArg List.length hparentIds.1
    simpa using h
  have hsubC : (childSubInput inp group).boxes.length ≤ inp.boxes.length := by
    show (((inp.boxes.zipIdx 0).filter
      fun q => Compound.inside inp.boxes group.id q.1.id).map
        fun q => if q.1.parent == group.id then { q.1 with parent := "" } else q.1).length ≤
      inp.boxes.length
    simp only [List.length_map]
    have h := List.length_filter_le
      (fun q => Compound.inside inp.boxes group.id q.1.id) (inp.boxes.zipIdx 0)
    rw [List.length_zipIdx] at h
    exact h
  have hsubP : (parentSubInput inp group P titleLines child).boxes.length ≤
      inp.boxes.length := by
    have hboxes : (parentSubInput inp group P titleLines child).boxes =
        (selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
    rw [hboxes]
    show (((inp.boxes.zipIdx 0).filter
      fun q => (!Compound.inside inp.boxes group.id q.1.id)).map
        fun q => if q.1.parent == "" then { q.1 with parent := "" } else q.1).length ≤
      inp.boxes.length
    simp only [List.length_map]
    have h := List.length_filter_le
      (fun q => !Compound.inside inp.boxes group.id q.1.id) (inp.boxes.zipIdx 0)
    rw [List.length_zipIdx] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hchildLen, hresLen]; exact Nat.le_trans hsubC (Nat.le_refl _)
  · rw [hparentLen, hresLen]; exact Nat.le_trans hsubP (Nat.le_refl _)
  · intro frame hframe cb hcb hEq
    have hcbId : cb.id ∈ child.scene.boxes.map (·.id) := List.mem_map.mpr ⟨cb, hcb, rfl⟩
    have hframeMem : frame ∈ parent.scene.boxes := List.mem_of_find?_eq_some hframe
    have hfid : frame.id = group.id := by simpa using List.find?_some hframe
    have hparentId : group.id ∈ parent.scene.boxes.map (·.id) :=
      List.mem_map.mpr ⟨frame, hframeMem, hfid⟩
    exact hdisjoint group.id (hEq ▸ hcbId) hparentId

/-! ### The named geometric remainder of each step -/

/-- The genuinely geometric remainder of `ExpandChildC8aStep`: every shifted
child box lies inside the located frame.  Box-lookup transport, scene sizes,
the frame's group role, child/group isolation, and the ancestor anchors are
structural and live in `ExpandChildC8aStructure`. -/
def ExpandChildC8aGeometry (P : Params) (group : ModelBox)
    (titleHeight : Int) (parent child _result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ∀ cb ∈ child.scene.boxes, frame.rect.Contained (shiftRect dx dy cb.rect)

/-- The genuinely geometric remainder of `ExpandChildC8bStep`: the four
cross-scene clearance pairs (parent groups vs child labels, child groups vs
parent labels, child groups vs the caption, and parent groups vs the
caption).  The label classification is structural and lives in
`ExpandChildC8bStructure`. -/
def ExpandChildC8bGeometry (P : Params) (group : ModelBox)
    (titleHeight : Int) (parent child _result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    (∀ g ∈ parent.scene.boxes, g.role = "group" → ∀ cl ∈ child.scene.labels,
        Disjoint g.rect (shiftRect dx dy cl.rect) ∨
          g.rect.StrictInside (shiftRect dx dy cl.rect)) ∧
    (∀ cg ∈ child.scene.boxes, cg.role = "group" → ∀ pl ∈ parent.scene.labels,
        Disjoint (shiftRect dx dy cg.rect) pl.rect ∨
          (shiftRect dx dy cg.rect).StrictInside pl.rect) ∧
    (∀ cg ∈ child.scene.boxes, cg.role = "group" →
        Disjoint (shiftRect dx dy cg.rect)
          (groupTitleRectC8 group P titleLines titleHeight frame) ∨
        (shiftRect dx dy cg.rect).StrictInside
          (groupTitleRectC8 group P titleLines titleHeight frame)) ∧
    (∀ g ∈ parent.scene.boxes, g.role = "group" →
        Disjoint g.rect (groupTitleRectC8 group P titleLines titleHeight frame) ∨
        g.rect.StrictInside (groupTitleRectC8 group P titleLines titleHeight frame))

/-- The genuinely geometric remainder of `ExpandChildC7Step`: the four
cross-scene interior-clearance pairs.  Box-lookup transport, scene sizes,
the label classification, and the owner-scope transports are structural and
live in `ExpandChildC7Structure`. -/
def ExpandChildC7Geometry (P : Params) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    (∀ cl ∈ child.scene.labels, cl.owner ≠ group.id →
        ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
          pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
          ¬ (shiftRect dx dy cl.rect).meetsInterior pb.rect) ∧
    (∀ cb ∈ child.scene.boxes, cb.exclusive = true →
        ∀ rl ∈ result.scene.layoutDump.labels, rl.owner = group.id →
          ¬ rl.rect.meetsInterior (shiftRect dx dy cb.rect)) ∧
    (∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        ∀ cb ∈ child.scene.boxes, cb.exclusive = true →
          ¬ pl.rect.meetsInterior (shiftRect dx dy cb.rect)) ∧
    (∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        ∀ rl ∈ result.scene.layoutDump.labels, rl.owner = group.id →
          ¬ rl.rect.meetsInterior pb.rect)

/-! ### The named structural remainder of each step -/

/-- The structural remainder of `ExpandChildC8aStep`: box-lookup transport
for both merged scenes, scene-size bounds, the frame's `"group"` role, the
child/group id isolation, the scope anchors `{group.id} ++ ancestors
group.id` of every embedded box, and the isolation of the group's ancestor
chain from other parent boxes.  These are proved from the expansion's
assembly sources and the recursive id lemmas, not from geometry. -/
def ExpandChildC8aStructure (P : Params) (_inp : Input) (_o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
    (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some b) ∧
    child.scene.boxes.length ≤ result.scene.boxes.length ∧
    parent.scene.boxes.length ≤ result.scene.boxes.length ∧
    frame.role = "group" ∧
    (∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) ∧
    (∀ cb ∈ child.scene.boxes,
        ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
          x ∈ result.scene.layoutDump.ancestors cb.id) ∧
    (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
        group.id ∉ parent.scene.layoutDump.ancestors pb.id)

/-- The structural remainder of `ExpandChildC8bStep`: the label
classification `ExpandChildLabelClassesC8`.  The four cross-scene
clearance pairs are geometric and live in `ExpandChildC8bGeometry`. -/
def ExpandChildC8bStructure (P : Params) (_inp : Input) (_o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildLabelClassesC8 P group titleLines titleHeight frame dx dy parent child result

/-- The structural remainder of `ExpandChildC7Step`: box-lookup transport,
scene-size bounds, the label classification `ExpandChildLabelClasses`, and
the owner-scope transports for child and parent labels plus the scope
anchors of every merged label.  The four cross-scene clearance pairs are
geometric and live in `ExpandChildC7Geometry`. -/
def ExpandChildC7Structure (P : Params) (_inp : Input) (_o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
    (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some b) ∧
    child.scene.boxes.length ≤ result.scene.boxes.length ∧
    parent.scene.boxes.length ≤ result.scene.boxes.length ∧
    ExpandChildLabelClasses P group titleLines titleHeight frame dx dy parent child result ∧
    (∀ cl ∈ child.scene.labels, ∀ rl ∈ result.scene.layoutDump.labels, rl.id = cl.id →
        ∀ x ∈ child.scene.layoutDump.labelOwnerAnc cl.toLabel,
          x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
    (∀ pl ∈ parent.scene.labels, ∀ rl ∈ result.scene.layoutDump.labels, rl.id = pl.id →
        ∀ x ∈ parent.scene.layoutDump.labelOwnerAnc pl.toLabel,
          x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
    (∀ rl ∈ result.scene.layoutDump.labels,
        ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
          x ∈ result.scene.layoutDump.labelOwnerAnc rl)

/-! ### Step assembly -/

/-- The `hgeo` shape `layoutRecursive_c8a_of_flat` consumes: every
`expandChild` call `layoutRecursive` performs satisfies `ExpandChildC8aStep`,
discharged from the named geometric and structural remainders. -/
theorem expandChild_c8a_step_of_geometry
    (hgeoC8a : ∀ (P : Params) (group : ModelBox) (titleHeight : Int)
      (parent child result : FamilyResult),
      ExpandChildC8aGeometry P group titleHeight parent child result)
    (hstructC8a : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aStructure P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
  intro frame tl dx dy hframe hdx hdy
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    hstructC8a fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx frame tl dx dy hframe hdx hdy
  exact ⟨s1, s2, s3, s4, s5, s6,
    hgeoC8a P group titleHeight parent child res frame tl dx dy hframe hdx hdy,
    s7, s8⟩

/-- The `hgeo` shape `layoutRecursive_c8b_of_flat` consumes. -/
theorem expandChild_c8b_step_of_geometry
    (hgeoC8b : ∀ (P : Params) (group : ModelBox) (titleHeight : Int)
      (parent child result : FamilyResult),
      ExpandChildC8bGeometry P group titleHeight parent child result)
    (hstructC8b : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8bStructure P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8bStep P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
  intro frame tl dx dy hframe hdx hdy
  obtain ⟨g1, g2, g3, g4⟩ :=
    hgeoC8b P group titleHeight parent child res frame tl dx dy hframe hdx hdy
  exact ⟨hstructC8b fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx frame tl dx dy hframe hdx hdy, g1, g2, g3, g4⟩

/-- The `hgeo` shape `layoutRecursive_c7_of_flat` consumes. -/
theorem expandChild_c7_step_of_geometry
    (hgeoC7 : ∀ (P : Params) (group : ModelBox) (titleHeight : Int)
      (parent child result : FamilyResult),
      ExpandChildC7Geometry P group titleHeight parent child result)
    (hstructC7 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC7Structure P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC7Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
  intro frame tl dx dy hframe hdx hdy
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    hstructC7 fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx frame tl dx dy hframe hdx hdy
  obtain ⟨g1, g2, g3, g4⟩ :=
    hgeoC7 P group titleHeight parent child res frame tl dx dy hframe hdx hdy
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, g1, g2, g3, g4⟩

/-! ### Generic lookup and id-partition helpers -/

/-- A keyed `filterMap` finds `y` when some source element maps to it, and
every source element that maps to a `key`-matching result maps to `y`. -/
theorem expandChild_find?_filterMap_eq_some {α β : Type} (f : α → Option β) (key : β → String)
    {l : List α} {s : String} {y : β}
    (hy : ∃ x ∈ l, f x = some y) (hkey : key y = s)
    (huniq : ∀ x ∈ l, ∀ z, f x = some z → key z = s → z = y) :
    (l.filterMap f).find? (fun z => key z == s) = some y := by
  have hmem : y ∈ l.filterMap f := List.mem_filterMap.mpr hy
  have hp : (key y == s) = true := by simp [hkey]
  cases hf : (l.filterMap f).find? (fun z => key z == s) with
  | none =>
    exact absurd hp (List.find?_eq_none.mp hf y hmem)
  | some z =>
    have hzmem : z ∈ l.filterMap f := List.mem_of_find?_eq_some hf
    have hpz : (key z == s) = true :=
      List.find?_some (p := fun z => key z == s) hf
    obtain ⟨x, hx, hxz⟩ := List.mem_filterMap.mp hzmem
    have hzy : z = y := huniq x hx z hxz (by simpa using hpz)
    rw [hzy]

/-- Filtering a keyed-nodup list keeps the keys nodup. -/
theorem expandChild_nodup_filter_map {α : Type} (f : α → String) (keep : α → Bool)
    {l : List α} (h : (l.map f).Nodup) :
    ((l.filter keep).map f).Nodup :=
  h.sublist ((List.filter_sublist (p := keep)).map f)

/-- The child/parent scene id lists of one expansion, as the two disjoint
halves of the input ids. -/
theorem expandChild_selected_ids
    {fuel : Nat} {inp : Input} {o : Options} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent) :
    child.scene.boxes.map (·.id) =
      (inp.boxes.filter (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) ∧
    parent.scene.boxes.map (·.id) =
      (inp.boxes.filter (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) ∧
    ((inp.boxes.filter (fun box => Compound.inside inp.boxes group.id box.id)).map
      (·.id)).Nodup ∧
    ((inp.boxes.filter (fun box => !Compound.inside inp.boxes group.id box.id)).map
      (·.id)).Nodup ∧
    ∀ id : String,
      id ∈ (inp.boxes.filter (fun box => Compound.inside inp.boxes group.id box.id)).map
        (·.id) →
      id ∈ (inp.boxes.filter (fun box => !Compound.inside inp.boxes group.id box.id)).map
        (·.id) → False := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hchildCov : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hparentCov : RoutesCovered (parentSubInput inp group P titleLines child) :=
    selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hchildIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hchildCov hchild
  have hparentIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hparentCov hparent
  refine ⟨?_, ?_, expandChild_nodup_filter_map _ _ hnodup,
    expandChild_nodup_filter_map _ _ hnodup, ?_⟩
  · rw [hchildIds.1]
    show (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map (·.id) = _
    rw [selectInput_box_ids]
  · rw [hparentIds.1]
    show (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id) = _
    rw [selectInput_box_ids]
  · intro id hidC hidP
    obtain ⟨m1, hmemC1, hid1⟩ := List.mem_map.mp hidC
    obtain ⟨m2, hmemC2, hid2⟩ := List.mem_map.mp hidP
    obtain ⟨_hm1, hin1⟩ := List.mem_filter.mp hmemC1
    obtain ⟨_hm2, hin2⟩ := List.mem_filter.mp hmemC2
    have heq : m1 = m2 := expandChild_nodup_map_inj (·.id) hnodup
      (List.mem_filter.mp hmemC1).1 (List.mem_filter.mp hmemC2).1 (hid1.trans hid2.symm)
    rw [heq] at hin1
    exact absurd hin2 (fun hc => by
      have hbad : ¬ ((!Compound.inside inp.boxes group.id m2.id) = true) := by
        rw [hin1]; simp
      exact hbad hc)


/-! ### Box-lookup transport of one expansion -/

/-- The merged scene resolves every child box to its embedded image and every
parent box to itself.  The offsets are the ones `expandChild` actually used
(`expandChild_sources`): the merged boxes are stored at exactly those
offsets, and the child/parent id lists are the two disjoint halves of the
input ids. -/
theorem expandChild_boxLookup_transport
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin ∧
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin ∧
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        res.scene.layoutDump.box? b.id = some b) := by
  obtain ⟨frame, _metric, tl, _lines, dx, dy, hframe, _hmetric, _htitle,
    _hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ :=
    expandChild_selected_ids hwf hchild hparent
  refine ⟨frame, tl, dx, dy, hframe, hdx, hdy, ?_, ?_⟩
  · intro b hb
    have hbMem : b ∈ child.scene.boxes := List.mem_of_find?_eq_some hb
    have hidC : b.id ∈ (inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hcid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidC
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hchildFirst : ∀ (cb : Box), cb ∈ child.scene.boxes → cb.id = b.id → cb = b := by
      intro cb hcbmem hcbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hcid]; exact hnC) hcbmem hbMem hcbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some (embedBox group.id dx dy b)
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := embedBox group.id dx dy b) (s := b.id)
      ⟨m, hmin, ?_⟩ rfl ?_
    · have hcf : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = some (embedBox group.id dx dy b) := by
        rw [List.find?_map]
        have hinside : (child.scene.boxes.find?
            ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy)) = some b := by
          have hpred : ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy) =
              (fun cb => cb.id == b.id) := by
            funext cb
            simp only [Function.comp_apply, embedBox]
            rw [hmid]
          rw [hpred]
          exact hb
        rw [hinside]
        rfl
      rw [List.find?_append]
      rw [hcf]
      rfl
    · intro m' hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        rw [hchildFirst cb hcb hcbkey]
      · exfalso
        exact hdisj z.id
          (by rw [hzid, ← hcid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
          (by rw [← hpid]; exact List.mem_map.mpr ⟨z, hzp, rfl⟩)
  · intro b hb
    have hbMem : b ∈ parent.scene.boxes := List.mem_of_find?_eq_some hb
    have hidP : b.id ∈ (inp.boxes.filter
        (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hpid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidP
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hparentFirst : ∀ (pb : Box), pb ∈ parent.scene.boxes → pb.id = b.id → pb = b := by
      intro pb hpmem hpbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hpid]; exact hnP) hpmem hbMem hpbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some b
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := b) (s := b.id) ⟨m, hmin, ?_⟩ rfl ?_
    · have hcfNone : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = none := by
        rw [List.find?_eq_none]
        intro cb hcb hp
        obtain ⟨cd, hcd, hcdrfl⟩ := List.mem_map.mp hcb
        subst hcdrfl
        have hkey : (embedBox group.id dx dy cd).id = m.id := beq_iff_eq.mp hp
        rw [show (embedBox group.id dx dy cd).id = cd.id from rfl] at hkey
        exact hdisj cd.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cd, hcd, rfl⟩)
          (by rw [hkey]; exact List.mem_map.mpr ⟨m, hmf, rfl⟩)
      have hcfP : parent.scene.boxes.find? (fun box => box.id == m.id) = some b := by
        show parent.scene.layoutDump.box? m.id = some b
        rw [hmid]
        exact hb
      rw [List.find?_append, hcfNone, hcfP]
      rfl
    · intro m' hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        exfalso
        exact hdisj cb.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cb, hcb, rfl⟩)
          (by rw [hcbkey, ← hpid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
      · rw [hparentFirst z hzp hzid]

end Elegant.Layered.PipelineImpl
