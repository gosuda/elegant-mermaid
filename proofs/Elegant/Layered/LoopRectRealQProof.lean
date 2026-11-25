import Elegant.Layered.LoopRectPlainSourceProof
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Model
import Elegant.Layered.SizingFacts
import Elegant.Layered.RunStageChainKeys
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.PartFrameCoresProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Real-part loop rect: transport cancellation and the emission bridge

`LoopRectPlainSourceProof` leaves five residuals, each about an exclusive
scene box `b` whose rect equals the transported `frameRect` of a real node `v`
of the run of a real packed part `q`. This module proves the two reductions
every case shares, then closes the group-top member sub-case:

* Transport cancellation (`loopTransport_cancel`): the full placement
  transport (shelf shift, bounds shift, orientation, margin shift) is
  injective, so equal transported rects give equal source rects. Proved once
  from `shiftRect_inj` and `orientRect_inj`.
* Emission bridge (`loopRect_exclusive_witness`, `loopRect_box_origin`,
  `loopRect_samePart_frameEq`): an exclusive scene box comes from one model
  box whose packed rect equals the transported `frameRect` of one run node
  `w` of the same part (adapted from the `FlatC6ScopeBridgeProof` argument,
  which also supplies the `w` border-`0` conclusion here). Hence, when the
  box source lies in the selected part, `frameRect w = frameRect v` in one
  run; otherwise the source key is foreign to the part.
* Frame shape (`frameRect_of_border_zero`): a non-top candidate frame is its
  node rect.
* Group-top member sub-case (`loopRectTop_strictInside_case`): a member `w`
  of the group sits strictly inside the group-top frame, so the frame
  equation is impossible. The non-member sub-case stays open as
  `LoopRectTopForeignReal`.
-/

/-- Orientations are injective on rectangles. -/
theorem orientRect_inj {d : Direction} {Ht : Int} {r1 r2 : Rect}
    (h : orientRect d Ht r1 = orientRect d Ht r2) : r1 = r2 := by
  obtain ⟨x1, y1, w1, h1⟩ := r1
  obtain ⟨x2, y2, w2, h2⟩ := r2
  cases d with
  | TB =>
    simpa only [orientRect] using h
  | BT =>
    simp only [orientRect] at h
    injection h with hx hy hw hh
    subst hx
    subst hw
    subst hh
    have e : y1 = y2 := by omega
    subst e
    rfl
  | LR =>
    simp only [orientRect] at h
    injection h with hx hy hw hh
    subst hx
    subst hy
    subst hw
    subst hh
    rfl
  | RL =>
    simp only [orientRect] at h
    injection h with hx hy hw hh
    subst hy
    subst hw
    subst hh
    have e : y1 = y2 := by omega
    subst e
    rfl

/-- The full placement transport cancels: equal transported rects come from
equal source rects. This is the reduction every real-part loop case shares. -/
theorem loopTransport_cancel {M Ht qx qy lx ly : Int} {d : Direction}
    {r1 r2 : Rect}
    (h : shiftRect M M (orientRect d Ht (shiftRect qx qy (shiftRect lx ly r1))) =
         shiftRect M M (orientRect d Ht (shiftRect qx qy (shiftRect lx ly r2)))) :
    r1 = r2 := by
  have h1 := shiftRect_inj h
  have h2 := orientRect_inj h1
  have h3 := shiftRect_inj h2
  exact shiftRect_inj h3

/-- Transported positivity: with a positive scene rect and the rect equation,
the run frame is positive. Shifts preserve size and orientation swaps width
and height (`shiftRect_dims`, `orientRect_dims`). This replaces the non-fixed
floor (`exclusiveBox_frame_pos`) wherever the def premise supplies `b.rect`
positivity. -/
theorem loopRect_frame_pos_of_rectEq
    {M Ht qx qy lx ly : Int} {d : Direction}
    {fr : Rect} {b : Rect}
    (hrect : b = shiftRect M M (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr))))
    (hw : 0 < b.w) (hh : 0 < b.h) :
    0 < fr.w ∧ 0 < fr.h := by
  have e1 : (shiftRect M M (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr)))).w =
      (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr))).w := rfl
  have e2 : (shiftRect M M (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr)))).h =
      (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr))).h := rfl
  have hwO : 0 < (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr))).w := by
    rw [← e1, ← hrect]
    exact hw
  have hhO : 0 < (orientRect d Ht (shiftRect qx qy (shiftRect lx ly fr))).h := by
    rw [← e2, ← hrect]
    exact hh
  have hs := (orientRect_dims d Ht _).mp ⟨hwO, hhO⟩
  exact (shiftRect_dims lx ly fr).mp ((shiftRect_dims qx qy _).mp hs)

/-- A candidate frame at a `border = 0` position is its node rect. -/
theorem frameRect_of_border_zero {P : Params} {cg : Graph} {run : Run}
    {v : Nat} {node : Node}
    (hget : cg.nodes.getD v default = node) (hb : node.border = 0) :
    frameRect P cg run v = nodeRect cg run v := by
  unfold frameRect
  simp only []
  rw [hget, hb]
  rfl

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`:
a candidate graph has exactly the component's nodes. -/
private theorem candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Same-part witness: an exclusive scene box whose source key lies in the
selected part's component is the transported `frameRect` of the real run node
at the key's local position, and that node is a plain (`border = 0`) node.
This adapts the `FlatC6ScopeBridgeProof` exclusive-box argument to the
loop-case context (which needs no `componentLoops` hypothesis). -/
theorem loopRect_exclusive_witness
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {key : Nat} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source)
    (hexcl : source.exclusive = true)
    (hmem : key ∈ q.1.1) :
    ∃ w : Nat,
      q.1.1[w]? = some key ∧ source.role = BoxRole.node ∧
      w < (componentCandidate execution.graph q.1.1 candidate).nodes.length ∧
      RouteImpl.IsReal run.proper w ∧
      ((componentCandidate execution.graph q.1.1 candidate).nodes.getD w default).border = 0 ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default))) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run w)))) := by
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
  have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
    rw [candidate_nodes_length]
    exact (List.getElem?_eq_some_iff.mp hv).1
  have hkeylen : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hentry := chosen_part_frame_entry hpart hv
  dsimp only at hentry
  have hval := actual_components_packed_rect_value (by rfl) execution.components_eq
    execution.packed_eq packed hpack hselected hentry hkeysize default
  have hgraphlen : key < execution.graph.nodes.length :=
    sceneExecution_graph_len execution hkeylen
  have hgraphnode : execution.graph.nodes[key]? =
      some (execution.graph.nodes[key]'hgraphlen) := List.getElem?_eq_getElem hgraphlen
  have hreal := componentRun_source_isReal hrun (candidate_node_of_part_key hv hgraphnode)
  obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
  have hnode : source.role = BoxRole.node := by
    have hnotgroup : source.role ≠ BoxRole.group := by
      intro hg
      have := hgroups source (List.mem_of_getElem? hsource) hg
      rw [this] at hexcl
      exact Bool.noConfusion hexcl
    cases hr : source.role with
    | node => rfl
    | group => exact absurd hr hnotgroup
  have hborder :=
    candidateBorderZeroOfNonGroup execution (comp := q.1.1) (candidate := candidate)
      (v := v) (key := key) (src := source) hv hsource
      (by intro hcon; rw [hnode] at hcon; cases hcon)
  refine ⟨v, hv, hnode, hvlen, hreal, hborder, ?_⟩
  exact congrArg (fun r => shiftRect execution.params.canvasMargin
    execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH r)) hval

/-- Reverse scene-box lookup: every scene box comes from one model box whose
exclusive flag it carries and whose packed rect it transports. -/
theorem loopRect_box_origin
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {b : Box} (hbmem : b ∈ res.scene.boxes) :
    ∃ key source, inp.boxes[key]? = some source ∧ source.exclusive = b.exclusive ∧
      b.rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)) := by
  rw [execution.boxes_eq_map] at hbmem
  obtain ⟨pair, hpair, hboxeq⟩ := List.mem_map.mp hbmem
  have hsource : inp.boxes[pair.2]? = some pair.1 :=
    List.mem_zipIdx_iff_getElem?.mp hpair
  refine ⟨pair.2, pair.1, hsource, ?_, ?_⟩
  · exact congrArg Box.exclusive hboxeq
  · exact (congrArg Box.rect hboxeq).symm

/-- Same-part reduction: an exclusive scene box satisfying a real-part rect
equation either comes from a plain run node `w` of the same part with
`frameRect w = frameRect v` (transports cancelled), or its source key is
foreign to the part. -/
theorem loopRect_samePart_frameEq
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {v : Nat} {b : Box}
    (_hreal : RouteImpl.IsReal run.proper v)
    (hbmem : b ∈ res.scene.boxes) (hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v))))) :
    (∃ w key source, q.1.1[w]? = some key ∧ inp.boxes[key]? = some source ∧
      source.role = BoxRole.node ∧
      w < (componentCandidate execution.graph q.1.1 candidate).nodes.length ∧
      RouteImpl.IsReal run.proper w ∧
      ((componentCandidate execution.graph q.1.1 candidate).nodes.getD w default).border = 0 ∧
      frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run w =
        frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v) ∨
    (∃ key source, inp.boxes[key]? = some source ∧ source.exclusive = true ∧
      b.rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)) ∧
      key ∉ q.1.1) := by
  obtain ⟨key, source, hsource, hboxexcl, hboxrect⟩ :=
    loopRect_box_origin execution hbmem
  have hexcl' : source.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : key ∈ q.1.1
  · obtain ⟨w, hw, hroleW, hwlen, hrealw, hbord0, hpackeq⟩ :=
      loopRect_exclusive_witness execution hwf packed hpack hselected hrun hpart
        hsource hexcl' hmem
    refine Or.inl ⟨w, key, source, hw, hsource, hroleW, hwlen, hrealw, hbord0, ?_⟩
    have hww : shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run w)))) =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (0 - (placeBounds execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
      rw [← hpackeq, ← hboxrect, hrect]
    exact loopTransport_cancel hww
  · exact Or.inr ⟨key, source, hsource, hexcl', hboxrect, hmem⟩

/-- Strict containment is irreflexive: a strictly inside rect differs from
its outer rect. -/
theorem loopRect_strictInside_ne {r1 r2 : Rect} (h : r1.StrictInside r2)
    (heq : r1 = r2) : False := by
  subst heq
  unfold Rect.StrictInside at h
  omega

/-- Group-top member sub-case: a plain member `w` of the group sits strictly
inside the group-top frame, so the same-part frame equation is impossible. -/
theorem loopRectTop_strictInside_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true)
    (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run memberIndex =
      frameRect execution.params (componentCandidate execution.graph comp candidate) run index) :
    False := by
  have hsi := execution.component_member_strictInside' hwf hcomp hrun hnode hgroup
    hmember hplain hinside
  exact loopRect_strictInside_ne hsi hframe.symm

/-- Residual (real-part group-top foreign sub-case): a same-part plain run
node `w` outside the group whose frame equals the group-top frame. It rests
on the open foreign-span seams. -/
def LoopRectTopForeignReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = -2 →
      ∀ {w : Nat} {key : Nat} {member : Node},
        q.1.1[w]? = some key →
        ((componentCandidate execution.graph q.1.1 candidate).nodes.getD w default).border = 0 →
        (componentCandidate execution.graph q.1.1 candidate).nodes[w]? = some member →
        member.border = 0 →
        member.clusterPath.contains node.decl = false →
        frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run w =
          frameRect execution.params
            (componentCandidate execution.graph q.1.1 candidate) run v →
        False

/-- Floor of a measured node: `sizedNode` takes the max with the profile
minima, so every measured node is at least `nodeMinW` by `nodeMinH`. -/
theorem sizedNode_min_floor {P : Params} {decl : Nat} {lines : List Measure.Line}
    {n : Node} (h : sizedNode P decl lines = .ok n) :
    P.nodeMinW ≤ n.w ∧ P.nodeMinH ≤ n.h := by
  unfold sizedNode at h
  obtain ⟨size, hs, he⟩ := bind_ok h
  have hn := Except.ok.inj he
  subst n
  unfold nodeSize at hs
  dsimp only at hs
  split at hs
  · simp at hs
  · have heq := Except.ok.inj hs
    subst size
    dsimp only
    exact ⟨Int.le_max_right _ _, Int.le_max_right _ _⟩

/-- Graph floor for a non-fixed node-role box: the measured graph keeps the
oriented `sizedNode` dimensions for non-fixed boxes (`prepare` only rewrites
cluster paths), so the node clears the profile minima up to orientation. -/
theorem graphNode_min_floor
    {profile : Profile} {kind : String} {P : Params}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)} {g : Graph}
    (_hp : checkedParams profile kind = .ok P)
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box) (hrole : box.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false) :
    ∃ node, g.nodes[i]? = some node ∧ node.decl = i ∧
      min P.nodeMinW P.nodeMinH ≤ node.w ∧ min P.nodeMinW P.nodeMinH ≤ node.h := by
  have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  subst g
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, hsized, hbefore⟩ := hinit i (ls, i)
    (by simp only [List.getElem?_zipIdx, hline, Option.map_some, Nat.zero_add])
  have hfloor := sizedNode_min_floor hsized
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ := hprocessed i (orientNode o.direction before, i)
    (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
      Option.map_some, Nat.zero_add])
  have hprepared := prepare_node_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) P.clusterPad
      (lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * P.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      { nodes := nodes, edges := edges, slot := P.slot }
      hafter (by simp only [List.getElem?_map, hbox, Option.map_some,
        hfixed, Bool.false_eq_true, ↓reduceIte]) hrole
  have hbefore_decl : before.decl = i := by
    unfold sizedNode at hsized
    cases hns : nodeSize P ls with
    | error e =>
      rw [hns] at hsized
      change Except.error e = Except.ok before at hsized
      cases hsized
    | ok size =>
      rw [hns] at hsized
      simp only [bind, Except.bind, pure, Except.pure] at hsized
      have hb := Except.ok.inj hsized
      subst before
      rfl
  refine ⟨_, hprepared, ?_, ?_, ?_⟩
  all_goals
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hstep
    simp [hfind, hbox, hrole] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        have hh := Int.le_max_left (orientNode o.direction before).h
          (Loops.requiredHeight P.slot (loopSizes edges labels i P.slot))
        cases hd : o.direction <;> simp only [hd, orientNode] at * <;> omega

/-- Every executed layout measures one line block per input box. -/
theorem loopRect_lines_get {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat}
    (hkey : key < inp.boxes.length) :
    ∃ ls, execution.lines[key]? = some ls := by
  have hlen : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx
  have hlt : key < execution.lines.length := by omega
  exact ⟨_, List.getElem?_eq_getElem hlt⟩

/-- Positivity, once: the frame of a plain (border-0, non-fixed source) run
node is positive. The frame is the node rect; proper dims cover graph dims;
graph dims clear the profile minima, which are positive in both profiles.
The non-fixed premise is load-bearing: fixed sizes replace measured dims
with unchecked user values. -/
theorem exclusiveBox_frame_pos
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    {w : Nat} {nodeW : Node}
    (hnodeW : (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW)
    (hbW : nodeW.border = 0)
    {key : Nat} {source : ModelBox} {ls : List Measure.Line}
    (hkey : comp[w]? = some key)
    (hsource : inp.boxes[key]? = some source)
    (hline : execution.lines[key]? = some ls)
    (hrole : source.role = .node)
    (hnf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w).w ∧
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w).h := by
  obtain ⟨out, hout, _, _, hwle, hheq⟩ :=
    componentRun_original_node_dims hrun hnodeW hbW
  have hkeylen : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hgbound : key < execution.graph.nodes.length :=
    sceneExecution_graph_len execution hkeylen
  have hmap : (componentCandidate execution.graph comp candidate).nodes =
      comp.map fun k => execution.graph.nodes.getD k default := by
    rw [componentCandidate_nodes]
    simp only [componentGraph]
  have hsame : execution.graph.nodes.getD key default = nodeW := by
    have e3 : ((comp.map fun k => execution.graph.nodes.getD k default)[w]? =
        some nodeW) := by
      rw [← hmap]
      exact hnodeW
    rw [List.getElem?_map, hkey, Option.map_some] at e3
    exact Option.some.inj e3
  have hgn : execution.graph.nodes[key]? = some nodeW := by
    have h1 : execution.graph.nodes[key]? =
        some (execution.graph.nodes[key]'hgbound) :=
      List.getElem?_eq_getElem hgbound
    have h2 : execution.graph.nodes[key]'hgbound = nodeW := by
      have h3 := hsame
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgbound,
        Option.getD_some] at h3
    rwa [h2] at h1
  obtain ⟨gnode, hgnode, _, hgw, hgh⟩ :=
    graphNode_min_floor execution.checked execution.graph_eq hline hsource hrole hnf
  rw [hgn] at hgnode
  have heq : gnode = nodeW := Option.some.inj hgnode.symm
  rw [heq] at hgw hgh
  have hminW := nodeMinW_pos execution.checked
  have hminH := nodeMinH_pos execution.checked
  have hget : (componentCandidate execution.graph comp candidate).nodes.getD w default =
      nodeW := by
    rw [List.getD_eq_getElem?_getD, hnodeW, Option.getD_some]
  have hrect : nodeRect (componentCandidate execution.graph comp candidate) run w =
      ⟨run.xs.getD w 0 - Int.fdiv out.node.w 2, run.ys.getD w 0,
        out.node.w, out.node.h⟩ := by
    simp [nodeRect, hout]
  rw [frameRect_of_border_zero hget hbW, hrect]
  show (0 : Int) < out.node.w ∧ 0 < out.node.h
  omega
/-- A positive rectangle meets its own interior. -/
theorem loopRect_meetsInterior_refl {r : Rect} (hw : 0 < r.w) (hh : 0 < r.h) :
    r.meetsInterior r := by
  unfold Rect.meetsInterior
  omega

/-- Equal positive rects are not disjoint. -/
theorem loopRect_frameNe_of_disjoint {r1 r2 : Rect} (hdis : Disjoint r1 r2)
    (heq : r1 = r2) (hw : 0 < r1.w) (hh : 0 < r1.h) : False := by
  subst heq
  exact hdis (loopRect_meetsInterior_refl hw hh)

/-- A range-degenerate node (beyond both the candidate and the proper run)
has the default degenerate frame. -/
theorem loopRect_rangeDeg_frame {P : Params} {cg : Graph} {run : Run} {v : Nat}
    (hn : cg.nodes[v]? = none) (hp : run.proper.nodes[v]? = none) :
    frameRect P cg run v = ⟨run.xs.getD v 0, run.ys.getD v 0, 0, 0⟩ := by
  have hc : cg.nodes.getD v default = default := by
    rw [List.getD_eq_getElem?_getD, hn, Option.getD_none]
  have hpd : run.proper.nodes.getD v default = default := by
    rw [List.getD_eq_getElem?_getD, hp, Option.getD_none]
  have hb0 : (default : Node).border = 0 := rfl
  have hw0 : (default : Node).w = 0 := rfl
  have hh0 : (default : Node).h = 0 := rfl
  have hnw : (default : ProperNode).node = default := rfl
  have hframe : frameRect P cg run v = nodeRect cg run v :=
    frameRect_of_border_zero hc hb0
  rw [hframe]
  unfold nodeRect
  simp only []
  rw [hpd, hnw, hw0, hh0, show Int.fdiv 0 2 = 0 from by decide, Int.sub_zero]

/-- Bottom same-part case: the bottom-marker frame is degenerate in height
(`bottomMarker_frame_disjoint` against the plain node), while the plain
node frame is positive. -/
theorem loopRectBottom_samePart
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    {v : Nat} {nodeV : Node}
    (hnodeV : (componentCandidate execution.graph comp candidate).nodes[v]? = some nodeV)
    (hbV : nodeV.border = 2)
    {w : Nat} {nodeW : Node}
    (_hnodeW : (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW)
    (_hbW : nodeW.border = 0)
    (hpos : 0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).w ∧
      0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).h)
    (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run w =
      frameRect execution.params (componentCandidate execution.graph comp candidate) run v) :
    False := by
  have hdis := bottomMarker_frame_disjoint hrun hnodeV hbV w
  exact loopRect_frameNe_of_disjoint hdis hframe hpos.1 hpos.2

/-- Range-degenerate same-part case: the out-of-range frame is the default
degenerate rect, while the plain node frame is positive. -/
theorem loopRectRangeDeg_samePart
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {run : Run}
    (_hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    {v : Nat}
    (hn : (componentCandidate execution.graph comp candidate).nodes[v]? = none)
    (hp : run.proper.nodes[v]? = none)
    {w : Nat} {nodeW : Node}
    (_hnodeW : (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW)
    (_hbW : nodeW.border = 0)
    (hpos : 0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).w ∧
      0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).h)
    (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run w =
      frameRect execution.params (componentCandidate execution.graph comp candidate) run v) :
    False := by
  have hdeg : frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v =
      ⟨run.xs.getD v 0, run.ys.getD v 0, 0, 0⟩ :=
    loopRect_rangeDeg_frame hn hp
  rw [hdeg] at hframe
  have hw0 : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w).w = 0 :=
    congrArg Rect.w hframe
  have hh0 : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w).h = 0 :=
    congrArg Rect.h hframe
  omega

/-- Fixed distinct-positions sub-case: two distinct border-0 nodes of one run
have disjoint frames, contradicting the frame equation with positivity. -/
theorem loopRectFixed_samePart_ne
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    {v : Nat} {nodeV : Node}
    (hnodeV : (componentCandidate execution.graph comp candidate).nodes[v]? = some nodeV)
    (hbV : nodeV.border = 0)
    {w : Nat} {nodeW : Node}
    (hnodeW : (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW)
    (hbW : nodeW.border = 0)
    (hne : v ≠ w)
    (hpos : 0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).w ∧
      0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).h)
    (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run w =
      frameRect execution.params (componentCandidate execution.graph comp candidate) run v) :
    False := by
  have hdis := componentRun_positions_disjoint execution.graph_eq hcomp hrun
    hnodeW hnodeV hbW hbV (Ne.symm hne)
  exact loopRect_frameNe_of_disjoint hdis hframe hpos.1 hpos.2

/-- Fixed same-position sub-case: at the same position the witness key and
source discharge the fixed residual's existential directly. -/
theorem loopRectFixed_samePart_refl
    {inp : Input} {q : (List Nat × Part) × Rect}
    {v w : Nat} {key : Nat} {source : ModelBox}
    (hw : q.1.1[w]? = some key)
    (hsource : inp.boxes[key]? = some source)
    (hrole : source.role = .node)
    (hv_eq_w : v = w) :
    ∃ key' src', q.1.1[v]? = some key' ∧ inp.boxes[key']? = some src' ∧
      src'.role ≠ .group := by
  refine ⟨key, source, ?_, hsource, ?_⟩
  · rw [hv_eq_w]
    exact hw
  · intro hcon
    rw [hrole] at hcon
    cases hcon
end Elegant.Layered.PipelineImpl
