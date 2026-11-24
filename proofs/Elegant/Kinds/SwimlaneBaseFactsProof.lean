import Elegant.Kinds.Swimlane
import Elegant.Layered.Pipeline
import Elegant.Layered.SelectFacts
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CgShape
import Elegant.Layered.PartFrameWitnessProof
import Elegant.Layered.InputFixedFit
import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneBands

set_option autoImplicit false

/-! Executed-scene facts for the swimlane adapter (scratch lane file for
`SwimlaneBaseFactsProof`; the parent gates and wires it).

`Swimlane.input` supplies no fixed sizes, and the layered family keeps every
scene box on a measured floor or a positive group frame: an executed
`layoutFamily (Swimlane.input m) m.options` scene therefore has strictly
positive box rects in both dimensions. That single fact yields both
`boxNonneg` (the cross-axis length of every executed box rect is `0 ≤`) and
`basePos` (`ExclusivePositive` of the executed dump).

`orthoAll` is NOT kept: the executed family scene replays the model's
per-route `orthogonal` flag (`sceneOf` builds the scene route as
`⟨q.1.id, q.1.fromId, q.1.toId, q.1.orthogonal, …⟩`; `selectInput` keeps the
model records verbatim and `expandChild` only shifts points), so the field
body fails on the concrete counterexample model `orthoAllWitness`, whose only
route carries `orthogonal := false`. The witness passes every gate the other
fields' theorems use (well-formedness, layered admission, lane nesting,
spacing); only the executed-run equation itself stays probe-class, exactly
like the `endsSplit` refutation receipts, because `decide` diverges on the
layout fold. -/

namespace Elegant
namespace Kinds

/-- `Swimlane.input` supplies no fixed sizes: the adapter record leaves the
`fixedSizes` field at its `[]` default. -/
theorem swimlane_input_fixedSizes (m : Model) :
    (Swimlane.input m).fixedSizes = [] := rfl

/-- Fixed-size positivity is therefore vacuous for the swimlane input. -/
theorem swimlane_input_fixedSizesPositive (m : Model) :
    Layered.PipelineImpl.FixedSizesPositive (Swimlane.input m) := by
  intro entry hmem
  rw [swimlane_input_fixedSizes] at hmem
  simp at hmem

end Kinds

namespace Layered
namespace PipelineImpl

/-- Positivity of the frame behind one scene box: the input box index sits in
some placed component, its local frame is a measured node above the profile
minima (border 0) or a group top with its title reservation (border -2), and
both shapes are strictly positive. -/
private theorem swf_part_frame_pos_of_node {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res) (hfix : FixedSizesPositive inp)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = 0 ∨ node.border = -2) :
    ∃ part : List Nat × Part, part ∈ execution.componentsAcc.parts ∧
      ∃ pdx pdy : Int, ∃ frame : Rect,
        0 < frame.w ∧ 0 < frame.h ∧
        execution.packedAcc.rects.getD key default = shiftRect pdx pdy frame := by
  have hkeyGraphLt : key < execution.graph.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  obtain ⟨comp, hcompMem, hkeyComp⟩ :=
    components_cover hkeyGraphLt (sceneExecution_edges_bounded execution)
  obtain ⟨hparts, _⟩ :=
    actual_components_parts_geometry (by rfl) execution.components_eq
  have hcompPart : comp ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcompMem
  obtain ⟨part, hpartMem, hpartComp⟩ := List.mem_map.mp hcompPart
  have hkeyIn : key ∈ part.1 := by
    rw [hpartComp]
    exact hkeyComp
  obtain ⟨position, hposKey⟩ := List.mem_iff_getElem?.mp hkeyIn
  have hposLt : position < part.1.length := (List.getElem?_eq_some_iff.mp hposKey).1
  obtain ⟨index, run, _dx, _dy, hcompIn, hrun, hframes⟩ :=
    execution.part_frame_rects hpartMem
  have hcgLen : (componentCandidate execution.graph part.1 index).nodes.length =
      part.1.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hlocalNode : (componentCandidate execution.graph part.1 index).nodes[position]? =
      some node := candidate_node_of_part_key hposKey hnode
  have hposLt2 : position <
      (componentCandidate execution.graph part.1 index).nodes.length := by
    rw [hcgLen]
    exact hposLt
  have hframe := hframes hposLt2
  have hstrict : 0 < (frameRect execution.params
      (componentCandidate execution.graph part.1 index) run position).w ∧
      0 < (frameRect execution.params
      (componentCandidate execution.graph part.1 index) run position).h := by
    rcases hborder with hb | hb
    · exact plain_frame_pos execution hcompIn hrun hlocalNode hb hposKey hsource hfix
    · exact top_frame_pos execution hcompIn hrun hlocalNode hb
  have hposFrame : 0 < (shiftRect _dx _dy
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run position)).w ∧
      0 < (shiftRect _dx _dy
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run position)).h := by
    simp only [shiftRect]
    exact hstrict
  have hkeySize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨pdx, pdy, hpackedShift⟩ := execution.packed_part_rect_shift hpartMem
  refine ⟨part, hpartMem, pdx, pdy, _, hposFrame.1, hposFrame.2, ?_⟩
  exact hpackedShift hposKey hframe hkeySize

/-- Executed flat layouts place every input box with a strictly positive
rect: plain boxes sit on measured floors above the profile minima, group
tops reserve the title band, and fixed sizes (when present) must be
positive. -/
theorem swf_scene_boxes_pos {inp : Input} {o : Options} {res : FamilyResult}
    (hfix : FixedSizesPositive inp)
    (h : layout inp o = .ok res) :
    ∀ b ∈ res.scene.boxes, 0 < b.rect.w ∧ 0 < b.rect.h := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  have hsceneLen : res.scene.boxes.length = inp.boxes.length := by
    rw [execution.boxes_eq_map]
    simp [List.length_map, List.length_zipIdx]
  intro b hb
  obtain ⟨key, hkb⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hkb
  have hkeyLt : key < inp.boxes.length := by omega
  rw [execution.boxes_eq_map, List.getElem?_map, List.getElem?_zipIdx] at hkb
  cases hboxes : inp.boxes[key]? with
  | none => simp [hboxes] at hkb
  | some source =>
    simp only [hboxes, Option.map_some, Nat.zero_add] at hkb
    have hrec : b = Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)))
        source.parent source.exclusive := (Option.some.inj hkb).symm
    by_cases hgf : source.role = .group ∧
        (inp.fixedSizes.any fun fixed => fixed.1 == source.id) = false
    · obtain ⟨node, hnode, hborder, _⟩ :=
        execution.nonfixed_group_graph_node hboxes hgf.1 hgf.2
      obtain ⟨part, hpartMem, pdx, pdy, frame, hfw, hfh, hpackedEq⟩ :=
        swf_part_frame_pos_of_node execution hfix hboxes hnode (Or.inr hborder)
      have hrect : b.rect = shiftRect execution.params.canvasMargin
          execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect pdx pdy frame)) := by
        rw [hrec, hpackedEq]
      rw [hrect]
      cases o.direction with
      | TB => simp only [shiftRect, orientRect]; omega
      | BT => simp only [shiftRect, orientRect]; omega
      | LR => simp only [shiftRect, orientRect]; omega
      | RL => simp only [shiftRect, orientRect]; omega
    · obtain ⟨node, hnode, hb0, _, _⟩ := execution.plain_graph_node hboxes hgf
      obtain ⟨part, hpartMem, pdx, pdy, frame, hfw, hfh, hpackedEq⟩ :=
        swf_part_frame_pos_of_node execution hfix hboxes hnode (Or.inl hb0)
      have hrect : b.rect = shiftRect execution.params.canvasMargin
          execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect pdx pdy frame)) := by
        rw [hrec, hpackedEq]
      rw [hrect]
      cases o.direction with
      | TB => simp only [shiftRect, orientRect]; omega
      | BT => simp only [shiftRect, orientRect]; omega
      | LR => simp only [shiftRect, orientRect]; omega
      | RL => simp only [shiftRect, orientRect]; omega

/-- Strict box positivity lifts through the recursive subdivision: the child
and parent sub-inputs carry fixed-size positivity (the added group frame is
positive because the executed child canvas clears both margins), and
`expandChild` only shifts box rects. -/
theorem swf_layoutRecursive_boxes_pos :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      FixedSizesPositive inp →
      layoutRecursive fuel inp o = .ok res →
      ∀ b ∈ res.scene.boxes, 0 < b.rect.w ∧ 0 < b.rect.h := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hfix h
    exact swf_scene_boxes_pos hfix h
  | succ fuel ih =>
    intro inp o res hfix h
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨group, P, _metric, child, titleLines, parent, _hg, hP, _hm, hc, _ht, hp, hexp⟩
    · exact swf_scene_boxes_pos hfix hlayout
    · have hcm := layoutRecursive_canvas_margins fuel hc
      have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
        rw [checkedParams_canvasMargin hP]
        exact hcm.1
      have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
        rw [checkedParams_canvasMargin hP]
        exact hcm.2
      have hfixChild : FixedSizesPositive (childSubInput inp group) :=
        FixedSizesPositive.childSubInput hfix group
      have hfixParent : FixedSizesPositive
          (parentSubInput inp group P titleLines child) :=
        FixedSizesPositive.parentSubInput hfix hP hcw hch
      obtain ⟨_frame, _metric', _titleLines', _lines, dx, dy, _hframe, _hmetric',
        _htitle', _hlines', _hdxdy, _hcanvas, hboxeseq⟩ := expandChild_sources hexp
      intro b hb
      rw [hboxeseq.2] at hb
      obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hb
      have hmemB : b ∈ child.scene.boxes.map (embedBox group.id dx dy) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hmemB with hchild | hparentBox
      · obtain ⟨cb, hcbMem, hcbEq⟩ := List.mem_map.mp hchild
        subst hcbEq
        have hcb := ih (childSubInput inp group) (childSubOptions o group) child
          hfixChild hc cb hcbMem
        simpa only [embedBox, shiftRect] using hcb
      · exact ih _ _ _ hfixParent hp b hparentBox

end PipelineImpl
end Layered

namespace Kinds

/-- Executed swimlane family scenes: every scene box is strictly positive in
both dimensions. `Swimlane.input` supplies no fixed sizes, so the fixed-size
positivity premise is vacuous. -/
theorem swimlane_boxes_pos {m : Model} {base : Layered.FamilyResult}
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    ∀ b ∈ base.scene.boxes, 0 < b.rect.w ∧ 0 < b.rect.h :=
  Layered.PipelineImpl.swf_layoutRecursive_boxes_pos
    ((Swimlane.input m).boxes.length + 1) (Swimlane.input m) m.options base
    (swimlane_input_fixedSizesPositive m)
    (Layered.layoutFamily_geometry_ok hfam)

/-- `boxNonneg` field body: the cross-axis length of every executed box rect
is nonnegative. With strict positivity in both dimensions this holds for
either axis choice. -/
theorem swimlane_boxNonneg {m : Model} {base : Layered.FamilyResult}
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    ∀ b ∈ base.scene.boxes,
      0 ≤ (Layered.LaneBands.Axis.ofDirection m.options.direction).length b.rect := by
  intro b hb
  cases m.options.direction with
  | TB =>
    have h := (swimlane_boxes_pos hfam b hb).1
    show 0 ≤ b.rect.w
    omega
  | BT =>
    have h := (swimlane_boxes_pos hfam b hb).1
    show 0 ≤ b.rect.w
    omega
  | LR =>
    have h := (swimlane_boxes_pos hfam b hb).2
    show 0 ≤ b.rect.h
    omega
  | RL =>
    have h := (swimlane_boxes_pos hfam b hb).2
    show 0 ≤ b.rect.h
    omega

/-- `basePos` field body: the executed dump is `ExclusivePositive` — in fact
every executed scene box is positive, exclusive or not. -/
theorem swimlane_basePos {m : Model} {base : Layered.FamilyResult}
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    Layered.LaneBands.ExclusivePositive base.scene.layoutDump := by
  intro b hb _
  exact swimlane_boxes_pos hfam b hb

/-! ### `orthoAll`: not kept — counterexample -/

private def swLane (id : String) : ModelBox :=
  { id := id, role := .group, parent := "", exclusive := false }

private def swNode (id parent : String) : ModelBox :=
  { id := id, role := .node, parent := parent, exclusive := true }

/-- Counterexample model for the `orthoAll` field: structurally identical to
the executed `endsSplitWitnessG2G` probe model, with the single route's
`orthogonal` flag set to `false`. The flag is not an input to any layout
decision (it travels in `ModelRoute`, not in `EdgeOptions`), so the executed
`layoutFamily` run of this model behaves exactly like the probed
`endsSplitWitnessG2G` run (`proofs/wip/Probe/SwimlaneEndsAboveTProbe.lean`,
`g2g … layout-ok fam-ok`), and `sceneOf` replays the flag verbatim into the
scene route (`Route.mk`/anonymous-route construction copies `q.1.orthogonal`;
`selectInput` keeps records and `expandChild` only shifts points). No new
admission restriction is involved. -/
def orthoAllWitness : Model :=
  { kind := "swimlane"
    boxes := [swLane "A", swNode "a1" "A", swLane "B", swNode "b1" "B"]
    routes := [{ id := "e0", fromId := "A", toId := "B", orthogonal := false }]
    labels := [] }

/-- Every gate of the field except the executed-run equation is
kernel-checked: the witness is well formed, passes the layered admission,
nests in its lanes, and admits a spacing. The executed-run equation stays
probe-class because `decide` diverges on the layout fold (the same
limitation documented for the `endsSplit` refutation). -/
theorem orthoAllWitness_gates :
    WellFormed orthoAllWitness = true ∧
      Layered.layeredAdmissibleB (Swimlane.input orthoAllWitness) = true ∧
      Swimlane.nestedInLaneB orthoAllWitness.boxes = true ∧
      ∃ sp : Layered.LaneBands.Spacing,
        Layered.LaneBands.spacingOf orthoAllWitness.options.profile = .ok sp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact ⟨_, rfl⟩

end Kinds
end Elegant
