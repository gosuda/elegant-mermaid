import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.PartFrameWitnessProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.SizingFacts
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.RunStageChainKeys
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactSeamClosureGlue
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.CgShape
import Elegant.Layered.ExactCaptionSelfNarrowProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Part width and height dominate any frame rect in the placement bounds. -/
private theorem xpp_placeComponentExact_size {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {r0 : Rect} (hr0 : r0 ∈ (List.range cg.nodes.length).map (frameRect P cg run)) :
    r0.w ≤ (placeComponentExact P cg run cursor labels loops).width ∧
      r0.h ≤ (placeComponentExact P cg run cursor labels loops).height := by
  have hmem : r0 ∈ (List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
          ⟨q.1.x + q.1.w, q.1.y,
            if run.exact.contains q.2 then
              Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
            else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
            if run.exact.contains q.2 then
              max q.1.h
                (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                  Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
            else q.1.h⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2) :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl hr0)))))
  have hb : boundsOf
      ((List.range cg.nodes.length).map (frameRect P cg run) ++
        ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
          ⟨q.1.x + q.1.w, q.1.y,
            if run.exact.contains q.2 then
              Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
            else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
            if run.exact.contains q.2 then
              max q.1.h
                (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                  Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
            else q.1.h⟩) ++
        labelBounds P cg run labels ++
        (componentTitles P cg run).map (·.2))
      (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) =
    placeBoundsX P cg run labels loops := rfl
  have h1 := rect_right_le_boundsOf_right _
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) r0 hmem
  have h2 := boundsOf_minX_le_rect_x _
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) r0 hmem
  have h3 := rect_bottom_le_boundsOf_bottom _
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) r0 hmem
  have h4 := boundsOf_minY_le_rect_y _
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) r0 hmem
  rw [hb] at h1 h2 h3 h4
  simp only [placeComponentExact]
  rw [hb]
  exact ⟨by omega, by omega⟩

/-- `markOne` with an out-of-range box returns the input node. -/
private theorem xpp_markOne_none_eq {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {m : Node} {i : Nat} (hpb : boxes[i]? = none) :
    markOne boxes pad titles (m, i) = m := by
  unfold markOne
  dsimp only
  simp [hpb]

/-- `markOne` on a group-role box stores border `-2` at the box index. -/
private theorem xpp_markOne_group_border {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {m : Node} {i : Nat} {box : ModelBox}
    (hpb : boxes[i]? = some box) (hcond : (box.role == .group) = true) :
    (markOne boxes pad titles (m, i)).border = -2 := by
  unfold markOne
  dsimp only
  simp [hpb, hcond]

/-- `markOne` on a non-group-role box only rewrites the cluster path. -/
private theorem xpp_markOne_plain_eq {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {m : Node} {i : Nat} {box : ModelBox}
    (hpb : boxes[i]? = some box) (hcond : ¬((box.role == .group) = true)) :
    markOne boxes pad titles (m, i) =
      { m with clusterPath := Compound.path boxes box } := by
  unfold markOne
  dsimp only
  simp [hpb, hcond]

/-- A border-`0` node of the measured graph sits at its own declaration index
and its box is either a plain `.node` role or carries a fixed-size entry. -/
private theorem xpp_graph0_border0_facts {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} {n : Node} (hn : g.nodes[i]? = some n) (hb : n.border = 0) :
    n.decl = i ∧ i < lines.length ∧
      ∀ box : ModelBox, inp.boxes[i]? = some box →
        box.role = .node ∨
          ∃ entry : String × Size, entry ∈ inp.fixedSizes ∧ entry.1 == box.id := by
  obtain ⟨nodes, _edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source hg
  rw [hprepared] at hn
  simp only [Compound.prepare_nodes] at hn
  by_cases hi : i < nodes.length
  · rw [markNodes_eq] at hn
    rw [List.getElem?_append_left (by
      simp only [List.length_map, List.length_zipIdx]
      exact hi)] at hn
    simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add] at hn
    obtain ⟨m, hm⟩ : ∃ m, nodes[i]? = some m :=
      ⟨nodes[i]'hi, List.getElem?_eq_getElem hi⟩
    rw [hm] at hn
    simp only [Option.map_some] at hn
    have hnm : n = markOne
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
        P.clusterPad titles (m, i) := Option.some.inj hn.symm
    rw [hnm] at hb
    have hmeta := hmetadata i m hm
    have hilen : i < lines.length :=
      Nat.lt_of_lt_of_le hi (Nat.le_of_eq hlength)
    have hboxi : inp.boxes[i]? = none ∨ ∃ b : ModelBox, inp.boxes[i]? = some b := by
      cases hx : inp.boxes[i]? with
      | none => exact Or.inl rfl
      | some b => exact Or.inr ⟨b, rfl⟩
    rcases hboxi with hbnone | ⟨box, hboxi⟩
    · have hpl := xpp_markOne_none_eq (boxes :=
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box))
        (pad := P.clusterPad) (titles := titles) (m := m) (i := i)
        (by simp [List.getElem?_map, hbnone])
      refine ⟨?_, hilen, ?_⟩
      · rw [hnm]
        rw [hpl]
        exact hmeta.1
      · intro box' hbx'
        rw [hbnone] at hbx'
        exact absurd hbx' (by simp)
    · let demote (b : ModelBox) : ModelBox :=
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b
      have hpb : (inp.boxes.map demote)[i]? = some (demote box) := by
        simp [List.getElem?_map, hboxi]
      by_cases hgrp : ((demote box).role == .group) = true
      · have hb2 := xpp_markOne_group_border
          (pad := P.clusterPad) (titles := titles) (m := m) hpb hgrp
        rw [hb] at hb2
        exact absurd hb2 (by decide)
      · have hdeclm := xpp_markOne_plain_eq
          (pad := P.clusterPad) (titles := titles) (m := m) hpb hgrp
        refine ⟨?_, hilen, ?_⟩
        · rw [hnm]
          rw [hdeclm]
          exact hmeta.1
        · intro box' hbx'
          have hbx'eq : box' = box := Option.some.inj (hbx'.symm.trans hboxi)
          rw [hbx'eq]
          by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
          · right
            obtain ⟨entry, hemem, heq⟩ := List.any_eq_true.mp hf
            exact ⟨entry, hemem, heq⟩
          · left
            have hfb : demote box = box := by simp [demote, hf]
            have hfr : box.role ≠ .group := by
              intro hcon
              rw [hfb, hcon] at hgrp
              simp at hgrp
            cases hr : box.role with
            | node => rfl
            | group => exact absurd hr hfr
  · have hb2 := (Compound.markNodes_getElem?_bottom
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      P.clusterPad titles nodes i (by omega) hn).1
    omega

/-- The exact execution's `lines` cover every box. -/
private theorem xpp_exec_lines_length {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have hle := execution.lines_eq
  unfold boxLines at hle
  have h := (mapM_getElem? _ _ _ hle).1
  rw [h]
  simp

/-- A border-`0` measured-graph node at a box index has positive dimensions. -/
private theorem xpp_graph0_node_dims_positive {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hg0 : measuredGraph P inp o lines = .ok g0)
    (hlines : lines.length = inp.boxes.length)
    (hfix : FixedSizesPositive inp)
    {key : Nat} {nd0 : Node} (h0 : g0.nodes[key]? = some nd0) (hb0 : nd0.border = 0) :
    0 < nd0.w ∧ 0 < nd0.h := by
  obtain ⟨_hdecl, hkey_lt, hrole⟩ := xpp_graph0_border0_facts hg0 h0 hb0
  have hkey_boxes : key < inp.boxes.length := by omega
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[key]? = some box :=
    ⟨inp.boxes[key]'hkey_boxes, List.getElem?_eq_getElem hkey_boxes⟩
  obtain ⟨ls, hline⟩ : ∃ ls, lines[key]? = some ls :=
    ⟨lines[key]'hkey_lt, List.getElem?_eq_getElem hkey_lt⟩
  cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
  | none =>
    have hrolebox : box.role = .node := by
      rcases hrole box hbox with h | ⟨entry, hemem, heq⟩
      · exact h
      · exfalso
        have h1 := List.find?_eq_none.mp hfind entry hemem
        rw [heq] at h1
        exact h1 rfl
    have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false := by
      rw [List.any_eq_false]
      intro e he hpe
      exact List.find?_eq_none.mp hfind e he hpe
    obtain ⟨node2, hnode2, _, hminw, hminh⟩ :=
      graphNode_min_floor hp hg0 hline hbox hrolebox hany
    have hnd2 : node2 = nd0 := Option.some.inj (hnode2.symm.trans h0)
    subst hnd2
    have h1 := nodeMinW_pos hp
    have h2 := nodeMinH_pos hp
    omega
  | some entry =>
    obtain ⟨node2, hnode2, _, _, hw, hh⟩ :=
      measuredGraph_fixed_node_dims hg0 hline hbox hfind
    have hnd2 : node2 = nd0 := Option.some.inj (hnode2.symm.trans h0)
    subst hnd2
    have hpos := hfix entry (List.mem_of_find?_eq_some hfind)
    cases hd : o.direction <;> simp only [hd] at hw hh <;> omega

/-- `exactGraph` turns a positive-dimension node into a positive-dimension
node of the exact graph. -/
private theorem xpp_exactGraph_dims_positive {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (hg : exactGraph P exactIds inp o measured g0 = .ok g)
    (hfix : FixedSizesPositive inp)
    {key : Nat} {nd0 : Node} (h0 : g0.nodes[key]? = some nd0)
    (hpos0 : 0 < nd0.w ∧ 0 < nd0.h) :
    ∃ nd, g.nodes[key]? = some nd ∧ 0 < nd.w ∧ 0 < nd.h := by
  obtain ⟨nd, hnd, _, _, _⟩ := exactGraph_node_key hg h0
  refine ⟨nd, hnd, ?_⟩
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, h⟩ := bind_ok hg
  have he := Except.ok.inj h
  subst he
  have hnd' : nodes[key]? = some nd := hnd
  obtain ⟨out, hout, hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 key nd0 h0
  have hndeq : nd = out := Option.some.inj (hnd'.symm.trans hmem)
  subst hndeq
  cases hbox : inp.boxes[nd0.decl]? with
  | none =>
    simp only [hbox, pure, Except.pure] at hout
    have h1 := Except.ok.inj hout
    subst h1
    exact hpos0
  | some box =>
    simp only [hbox] at hout
    split at hout
    · simp only [pure, Except.pure] at hout
      have h1 := Except.ok.inj hout
      subst h1
      exact hpos0
    · cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
      | none =>
        simp only [hfind, throw, throwThe, MonadExceptOf.throw] at hout
        cases hout
      | some fixed =>
        simp only [hfind] at hout
        split at hout
        · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hout
          cases hout
        · split at hout
          · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
              at hout
            cases hout
          · simp only [pure, Except.pure] at hout
            have h1 := Except.ok.inj hout
            subst h1
            have hposf := hfix fixed (List.mem_of_find?_eq_some hfind)
            cases o.direction <;>
              first | exact hposf | exact ⟨hposf.2, hposf.1⟩

theorem X6_PartPosW_of_fixedSizesPositive (exactIds : List String) :
    X6_PartPosW exactIds := by
  intro inp o res execution hfix _hwf _hfp packed _hpacked c q hsel candidate i edge hedge
  obtain ⟨part, _rect⟩ := q
  dsimp only
  have hmem : part ∈ execution.componentsAcc.parts :=
    List.mem_iff_getElem?.mpr ⟨c, (List.getElem?_zip_eq_some.mp hsel).1⟩
  obtain ⟨hmap, hgeom⟩ :=
    actual_components_parts_geometryX (by rfl) execution.components_eq
  obtain ⟨index, _chosen, run, loops, _area, _hindex, _hchosen, _hvalue, hrun,
    _hloops, hpartdef⟩ := hgeom part hmem
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨part, hmem, rfl⟩
  obtain ⟨r, hreq⟩ := mem_components_eq hcomp
  by_cases hsel0 : ∃ j key : Nat, part.1[j]? = some key ∧
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.border = 0
  · obtain ⟨j, key, hkey, node, hnode, hborder⟩ := hsel0
    have hkeymem : key ∈ part.1 := List.mem_iff_getElem?.mpr ⟨j, hkey⟩
    have hkeylt : key < execution.graph.nodes.length := by
      rw [hreq] at hkeymem
      exact (mem_componentOf.mp hkeymem).1
    have hlen0 : execution.graph.nodes.length = execution.graph0.nodes.length :=
      exactGraph_length execution.graph_eq
    have hkeylt0 : key < execution.graph0.nodes.length := by omega
    obtain ⟨nd0, h0⟩ : ∃ nd0, execution.graph0.nodes[key]? = some nd0 :=
      ⟨execution.graph0.nodes[key]'hkeylt0, List.getElem?_eq_getElem hkeylt0⟩
    obtain ⟨nd', hnd', hb', _, _⟩ := exactGraph_node_key execution.graph_eq h0
    have hb0 : nd0.border = 0 := by
      have hndeq : nd' = node := Option.some.inj (hnd'.symm.trans hnode)
      rw [hndeq] at hb'
      omega
    have hlines_len := xpp_exec_lines_length execution
    have hdims0 := xpp_graph0_node_dims_positive execution.checked
      execution.graph0_eq hlines_len hfix h0 hb0
    obtain ⟨nd, hnd, hwN, hhN⟩ :=
      xpp_exactGraph_dims_positive execution.graph_eq hfix h0 hdims0
    have hnde : nd = node := Option.some.inj (hnd.symm.trans hnode)
    subst hnde
    have hjlen : j < (componentCandidate execution.graph part.1 index).nodes.length := by
      have h1 : (componentCandidate execution.graph part.1 index).nodes =
          part.1.map (fun v => execution.graph.nodes.getD v default) := by
        rw [componentCandidate_nodes]
        rfl
      rw [h1, List.length_map]
      exact (List.getElem?_eq_some_iff.mp hkey).1
    have hr0mem : frameRect execution.params
        (componentCandidate execution.graph part.1 index) run j ∈
        (List.range (componentCandidate execution.graph part.1 index).nodes.length).map
          (frameRect execution.params
            (componentCandidate execution.graph part.1 index) run) :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr hjlen, rfl⟩
    obtain ⟨hWrect, hHrect⟩ := xpp_placeComponentExact_size
      (labels := execution.measured) (loops := loops) (cursor := 0) hr0mem
    have hcrectEq : part.2.rects[j]? = some (shiftRect
        (0 - (placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run j)) := by
      rw [hpartdef]
      unfold placeComponentExact placeBoundsX
      simp only [List.getElem?_map, List.getElem?_range hjlen, Option.map_some]
    have hmin := SceneExecutionX.component_rect_minimum_dims execution hmem hkey
      hnode hborder hcrectEq
    have hwS : (shiftRect
        (0 - (placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run j)).w =
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run j).w := rfl
    have hhS : (shiftRect
        (0 - (placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run j)).h =
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run j).h := rfl
    rw [hwS, hhS] at hmin
    rw [hpartdef]
    exact ⟨Int.lt_of_lt_of_le hwN (Int.le_trans hmin.1 hWrect),
      Int.lt_of_lt_of_le hhN (Int.le_trans hmin.2 hHrect)⟩
  · have htail := (candidate_edge_endpoints_bounded_general execution.graph part.1
      candidate hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)).1
    have hlength (k : Nat) :
        (componentCandidate execution.graph part.1 k).nodes.length = part.1.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    have htailPart : edge.tail < part.1.length := by simpa only [hlength] using htail
    obtain ⟨key, hkey⟩ : ∃ key : Nat, part.1[edge.tail]? = some key :=
      ⟨_, List.getElem?_eq_getElem htailPart⟩
    have hkeymem : key ∈ part.1 := List.mem_of_getElem? hkey
    have hkeylt : key < execution.graph.nodes.length := by
      rw [hreq] at hkeymem
      exact (mem_componentOf.mp hkeymem).1
    obtain ⟨source, hsource⟩ : ∃ node : Node, execution.graph.nodes[key]? = some node :=
      ⟨_, List.getElem?_eq_getElem hkeylt⟩
    have hlocal := candidate_node_of_part_key (index := index) hkey hsource
    let cg := componentCandidate execution.graph part.1 index
    obtain ⟨j, top, htop, hgroup⟩ :
        ∃ (j : Nat) (top : Node), cg.nodes[j]? = some top ∧ top.border = -2 := by
      rcases (X_componentCandidate_marker_shape
        execution.graph0_eq execution.graph_eq hlocal).1 with hplain | hgroup | hbottom
      · exact (hsel0 ⟨edge.tail, key, hkey, source, hsource, hplain⟩).elim
      · exact ⟨edge.tail, source, hlocal, hgroup⟩
      · obtain ⟨entry, hentry⟩ := X_componentRun_cg_top_of_bottom execution.graph0_eq
          execution.graph_eq (xpp_exec_lines_length execution) hcomp hlocal hbottom
        have htest := List.find?_some hentry
        change (entry.1.border == -2 && entry.1.clusterPath == source.clusterPath) =
          true at htest
        have hb := (Bool.and_eq_true_iff.mp htest).1
        exact ⟨entry.2, entry.1, List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hentry),
          by simpa only [beq_iff_eq] using hb⟩
    have hpos := componentRunX_group_frame_dims_pos execution hcomp hrun htop hgroup
    have hframe : frameRect execution.params cg run j ∈
        (List.range cg.nodes.length).map (frameRect execution.params cg run) :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr ((List.getElem?_eq_some_iff.mp htop).1), rfl⟩
    have hbounds := xpp_placeComponentExact_size
      (labels := execution.measured) (loops := loops) (cursor := 0) hframe
    rw [hpartdef]
    exact ⟨Int.lt_of_lt_of_le hpos.1 hbounds.1, Int.lt_of_lt_of_le hpos.2 hbounds.2⟩
end PipelineImpl
end Layered
end Elegant
