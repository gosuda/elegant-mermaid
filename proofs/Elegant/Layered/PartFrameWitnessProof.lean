import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SizingFacts
import Elegant.Layered.PlainNodeSizingFacts
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.Compound
import Elegant.Layered.RunStageChainKeys
import Elegant.Layered.RunStageChainKeysResiduals
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.LabelsC8bFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Every fixed-size override has positive width and height. The open
`PartFrameWitness` is false without this: two plain boxes with `⟨0,0⟩` fixed
sizes and a route between them execute successfully with all frames `(1024,0)`
(`PartFrameWitnessTProbe` / `PartFrameWitnessTFalsify`:
`doubleFixedZero` has `wit=false` for every candidate while `modelWellFormed`
and `framedParents` hold and `layout` succeeds). -/
def FixedSizesPositive (inp : Input) : Prop :=
  ∀ f ∈ inp.fixedSizes, 0 < f.2.w ∧ 0 < f.2.h

/-- `List.idxOf` inverts membership (copy of the private helper elsewhere). -/
private theorem comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- Candidate nodes are the global nodes mapped over the component. -/
private theorem cand_nodes_len (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  simp [componentCandidate_nodes, componentGraph]

/-- Candidate node lookup is the global lookup at the mapped key. -/
private theorem cand_node_global {g : Graph} {comp : List Nat} {index v key : Nat}
    {node : Node} (hcomp : comp[v]? = some key)
    (hnode : (componentCandidate g comp index).nodes[v]? = some node) :
    g.nodes.getD key default = node := by
  have h := hnode
  simp only [componentCandidate_nodes, componentGraph, List.getElem?_map, hcomp,
    Option.map_some] at h
  exact Option.some.inj h

/-- Endpoint case split (copy of the private helper elsewhere): an aliased
endpoint is either the box index itself or the bottom marker of a group. -/
private theorem alias_endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases hbj : boxes[j]? with
    | none => exact Or.inl rfl
    | some target =>
      dsimp only
      by_cases hc : (box.role != .group || i == j) = true
      · rw [ite_eq_left hc]
        exact Or.inl rfl
      · rw [ite_eq_right hc]
        by_cases hd : (s == Compound.inside boxes box.id target.id) = true
        · rw [ite_eq_left hd]
          exact Or.inl rfl
        · rw [ite_eq_right hd]
          refine Or.inr ⟨rfl, ?_⟩
          intro box' hb'
          have heq : box' = box := (Option.some.inj hb').symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl


/-- Candidate lookup upgrades a mapped global `getD` to `getElem?`. -/
private theorem cand_global_lookup {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate v key : Nat} {node : Node}
    (hkey : comp[v]? = some key)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node) :
    execution.graph.nodes[key]? = some node := by
  have hlt : key < execution.graph.nodes.length :=
    comp_mem_lt hcomp (List.mem_of_getElem? hkey)
  have hgetD := cand_node_global hkey hnode
  rw [List.getD_eq_getElem?_getD] at hgetD
  cases h2 : execution.graph.nodes[key]? with
  | none =>
    exfalso
    rw [List.getElem?_eq_none_iff] at h2
    omega
  | some n =>
    rw [h2, Option.getD_some] at hgetD
    exact congrArg some hgetD
/-- A fold of nonnegative maxima from `0` stays nonnegative. -/
private theorem fold_max_width_nonneg_aux (ls : List Measure.Line) :
    ∀ acc : Int, 0 ≤ acc →
      0 ≤ ls.foldl (fun w line => max w line.width) acc := by
  intro acc ha
  induction ls generalizing acc with
  | nil => simpa using ha
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    exact ih _ (Int.le_trans ha (Int.le_max_left _ _))

private theorem fold_max_width_nonneg (ls : List Measure.Line) :
    0 ≤ ls.foldl (fun w line => max w line.width) 0 :=
  fold_max_width_nonneg_aux ls 0 (Int.le_refl _)

/-- Frame positivity for a border-0 candidate node. Non-fixed node-role boxes
use the measured floor; fixed boxes use their override dims with `FixedPos`. -/
theorem plain_frame_pos {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {v key : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hb : node.border = 0)
    (hkey : comp[v]? = some key)
    {box : ModelBox} (hbox : inp.boxes[key]? = some box)
    (hfix : FixedSizesPositive inp) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w ∧
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h := by
  obtain ⟨ls, hline⟩ :=
    loopRect_lines_get execution ((List.getElem?_eq_some_iff.mp hbox).1)
  cases hfind : inp.fixedSizes.find? (fun fixed : String × Size => fixed.1 == box.id) with
  | some entry =>
    obtain ⟨gnode, hgnode, _, _, hw, hh⟩ :=
      measuredGraph_fixed_node_dims execution.graph_eq hline hbox hfind
    have hgn := cand_global_lookup execution hcomp hkey hnode
    have heq : gnode = node := Option.some.inj (hgnode.symm.trans hgn)
    rw [heq] at hw hh
    obtain ⟨hew, heh⟩ := hfix _ (List.mem_of_find?_eq_some hfind)
    have hposW : 0 < node.w := by
      cases hdir : o.direction <;> simp only [hdir] at hw ⊢ <;> omega
    have hposH : 0 < node.h := by
      cases hdir : o.direction <;> simp only [hdir] at hh ⊢ <;> omega
    obtain ⟨out, hout, _, _, hwle, hheq⟩ :=
      componentRun_original_node_dims hrun hnode hb
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD v default =
        node := by
      rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
    have hrect : nodeRect (componentCandidate execution.graph comp candidate) run v =
        ⟨run.xs.getD v 0 - Int.fdiv out.node.w 2, run.ys.getD v 0,
          out.node.w, out.node.h⟩ := by
      simp [nodeRect, hout]
    rw [frameRect_of_border_zero hget hb, hrect]
    exact ⟨Int.lt_of_lt_of_le hposW hwle, by rw [hheq]; exact hposH⟩
  | none =>
    have hnf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
      List.any_eq_false.mpr (List.find?_eq_none.mp hfind)
    have hrole : box.role = .node := by
      cases hr : box.role with
      | node => rfl
      | group =>
        exfalso
        obtain ⟨gnode, hgn, hb2, _⟩ :=
          execution.nonfixed_group_graph_node hbox hr hnf
        have hgn2 := cand_global_lookup execution hcomp hkey hnode
        have heq := Option.some.inj (hgn.symm.trans hgn2)
        rw [← heq] at hb
        omega
    exact exclusiveBox_frame_pos execution hrun hnode hb hkey hbox hline hrole hnf

/-- Frame positivity for a group-top candidate node: height from the title
reservation, width from the side borders. -/
theorem top_frame_pos {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hb : node.border = -2) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w ∧
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h := by
  obtain ⟨orig, horig, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, _, _, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph_eq hsource hb
  have hself : node.clusterPath.contains node.decl = true := by rw [hpath]; simp
  have howner : node.clusterPath.getLast? = some node.decl := by rw [hpath]; simp
  have hkeyD : comp.getD v 0 = orig := by simp [List.getD, horig]
  obtain ⟨_, capH⟩ := actual_title_caption_fit execution.graph_eq hnode hb
  rw [hkeyD] at capH
  have hpad : 0 < execution.params.clusterPad :=
    checkedParams_clusterPad_pos execution.checked
  have hlineH : 0 < execution.params.lineH :=
    checkedParams_lineH_pos execution.checked
  have hnodepos : 0 < node.h := by
    cases hdir : o.direction with
    | TB =>
      simp only [hdir] at capH
      have h1 : (1 : Int) ≤ max 1 (((execution.lines.getD orig []).length : Int)) :=
        Int.le_max_left _ _
      have h2 : (1 : Int) * execution.params.lineH ≤
          max 1 (((execution.lines.getD orig []).length : Int)) *
            execution.params.lineH :=
        Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hlineH)
      omega
    | BT =>
      simp only [hdir] at capH
      have h1 : (1 : Int) ≤ max 1 (((execution.lines.getD orig []).length : Int)) :=
        Int.le_max_left _ _
      have h2 : (1 : Int) * execution.params.lineH ≤
          max 1 (((execution.lines.getD orig []).length : Int)) *
            execution.params.lineH :=
        Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hlineH)
      omega
    | LR =>
      simp only [hdir] at capH
      have hf := fold_max_width_nonneg (execution.lines.getD orig [])
      omega
    | RL =>
      simp only [hdir] at capH
      have hf := fold_max_width_nonneg (execution.lines.getD orig [])
      omega
  have hge := componentRun_group_frame_height_ge hrun hnode hb hself
    (th := node.h - execution.params.clusterPad) (by omega)
  have hle : node.h ≤ (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h := by omega
  have hposH : 0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h :=
    Int.lt_of_lt_of_le hnodepos hle
  obtain ⟨_, left, right, _, hleft, hright, _, _⟩ :=
    measured_component_caption_border_interval execution.graph_eq hcomp hrun hnode hb
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some node.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mem_zipIdx_iff_getElem?.mpr hleft, ?_⟩
    simp [titleF, hb, howner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, right), List.mem_zipIdx_iff_getElem?.mpr hright, ?_⟩
    simp [titleF, hb, howner]
  have hframeW : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w =
      (boundsOf borders []).right - (boundsOf borders []).minX :=
    frameRect_group_width_eq_horizontal_span hnode hb
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hwR : (Labels.rectAt run.proper run.xs run.ys right).w =
      execution.params.clusterBorderW := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeW, hright,
      OrderImpl.borderRight]
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have hposW : 0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w := by
    rw [hframeW]
    omega
  exact ⟨hposW, hposH⟩

private theorem nodup_getElem_unique {α : Type} {l : List α} (hnd : l.Nodup) :
    ∀ {i j : Nat} {a : α}, l[i]? = some a → l[j]? = some a → i = j := by
  intro i j a hi hj
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have hx : x = a := Option.some.inj (by simpa using hi)
        have hmem : a ∈ xs := List.mem_of_getElem? hj
        have hnn : x ∉ xs := (List.nodup_cons.mp hnd).1
        rw [← hx] at hmem
        exact absurd hmem hnn
    | succ i =>
      cases j with
      | zero =>
        have hx : x = a := Option.some.inj (by simpa using hj)
        have hmem : a ∈ xs := List.mem_of_getElem? hi
        have hnn : x ∉ xs := (List.nodup_cons.mp hnd).1
        rw [← hx] at hmem
        exact absurd hmem hnn
      | succ j =>
        have hnd' := (List.nodup_cons.mp hnd).2
        have hi' : xs[i]? = some a := by simpa using hi
        have hj' : xs[j]? = some a := by simpa using hj
        exact congrArg Nat.succ (ih hnd' hi' hj')

private theorem exec_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  have hlen := (mapM_getElem? _ _ _ h).1
  simpa [List.length_zipIdx] using hlen

/-- Prepared-graph nodes below the box count are never bottom markers. -/
private theorem marked_nonbottom {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {j : Nat} (hj : j < inp.boxes.length)
    {node : Node} (hnode : execution.graph.nodes[j]? = some node) :
    node.border ≠ 2 := by
  obtain ⟨ls, hline⟩ := loopRect_lines_get execution hj
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[j]? = some box :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  cases hfind : inp.fixedSizes.find? (fun fixed : String × Size => fixed.1 == box.id) with
  | some entry =>
    obtain ⟨gnode, hgnode, _, hb0, _, _⟩ :=
      measuredGraph_fixed_node_dims execution.graph_eq hline hbox hfind
    have heq : gnode = node := Option.some.inj (hgnode.symm.trans hnode)
    rw [heq] at hb0
    omega
  | none =>
    have hnf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
      List.any_eq_false.mpr (List.find?_eq_none.mp hfind)
    cases hr : box.role with
    | node =>
      obtain ⟨gnode, hgnode, _, hb0⟩ :=
        measuredGraph_node_border_zero execution.checked execution.graph_eq
          hline hbox hr hnf
      have heq : gnode = node := Option.some.inj (hgnode.symm.trans hnode)
      rw [heq] at hb0
      omega
    | group =>
      obtain ⟨gnode, hgn, hb2, _⟩ :=
        execution.nonfixed_group_graph_node hbox hr hnf
      have heq : gnode = node := Option.some.inj (hgn.symm.trans hnode)
      rw [heq] at hb2
      omega

/-- Positions at or beyond the box count are bottom markers. -/
private theorem bottom_of_ge {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {j : Nat} (hj : inp.boxes.length ≤ j)
    {node : Node} (hnode : execution.graph.nodes[j]? = some node) :
    node.border = 2 := by
  obtain ⟨ns, es, titles, hprep, hlen, _⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length :=
    exec_lines_len execution
  have hle : ns.length ≤ j := by omega
  rw [hprep] at hnode
  exact (Compound.prepare_bottom_of_index _ _ _ _ _ hle hnode).1

/-- Two bottom markers with the same declaration are the same pair. -/
private theorem bottom_match_unique {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {i1 i2 : Nat} {n1 n2 : Node} {D : Nat}
    (h1 : execution.graph.nodes[i1]? = some n1)
    (hb1 : n1.border = 2) (hd1 : n1.decl = D)
    (h2 : execution.graph.nodes[i2]? = some n2)
    (hb2 : n2.border = 2) (hd2 : n2.decl = D) :
    (n1, i1) = (n2, i2) := by
  obtain ⟨ns, es, titles, hprep, hlen, _⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length :=
    exec_lines_len execution
  have hnn1 : ¬ i1 < inp.boxes.length := by
    intro hlt
    exact absurd hb1 (marked_nonbottom execution hlt h1)
  have hnn2 : ¬ i2 < inp.boxes.length := by
    intro hlt
    exact absurd hb2 (marked_nonbottom execution hlt h2)
  have hnodes : (Compound.prepare
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles
      { nodes := ns, edges := es, slot := execution.params.slot }).nodes =
      (ns.zipIdx.map (markOne
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
        execution.params.clusterPad titles)) ++
      markExtras
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) := rfl
  have hmlen : (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length = inp.boxes.length := by
    simp only [List.length_map, List.length_zipIdx, hlen, hlines]
  rw [hprep, hnodes] at h1 h2
  have hg1 : (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length ≤ i1 := by omega
  have hg2 : (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length ≤ i2 := by omega
  rw [List.getElem?_append_right hg1] at h1
  rw [List.getElem?_append_right hg2] at h2
  have hd1' : ((markExtras
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)).map (·.decl))[i1 - (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length]? = some D := by
    rw [List.getElem?_map, h1, Option.map_some]
    exact congrArg some hd1
  have hd2' : ((markExtras
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)).map (·.decl))[i2 - (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length]? = some D := by
    rw [List.getElem?_map, h2, Option.map_some]
    exact congrArg some hd2
  have hkk : i1 - (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length =
      i2 - (ns.zipIdx.map (markOne
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles)).length :=
    nodup_getElem_unique (markExtras_decl_nodup _) hd1' hd2'
  have hii : i1 = i2 := by omega
  subst hii
  have heq := Option.some.inj (h1.symm.trans h2)
  subst heq
  rfl

/-- The bottom-marker lookup finds a given matching bottom. -/
private theorem bottom_find_eq {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {bj : Nat} {bot : Node} {D : Nat}
    (hj : execution.graph.nodes[bj]? = some bot)
    (hb : bot.border = 2) (hd : bot.decl = D) :
    (execution.graph.nodes.zipIdx.find? fun e =>
      e.1.border == 2 && e.1.decl == D) = some (bot, bj) := by
  cases hfind : execution.graph.nodes.zipIdx.find? (fun e =>
      e.1.border == 2 && e.1.decl == D) with
  | none =>
    exfalso
    have hmem : (bot, bj) ∈ execution.graph.nodes.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hj
    have hpred : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == D) (bot, bj)) = true := by
      simp [hb, hd]
    have hne := List.find?_eq_none.mp hfind _ hmem
    simp [hpred] at hne
  | some gb =>
    obtain ⟨a, b⟩ := gb
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true] at hpred
    obtain ⟨hbb, hbd⟩ := hpred
    have hgbot : a.border = 2 := by simpa using hbb
    have hgdecl : a.decl = D := by simpa using hbd
    have hlook : execution.graph.nodes[b]? = some a :=
      List.mem_zipIdx_iff_getElem?.mp hmem
    have heq := bottom_match_unique execution hlook hgbot hgdecl hj hb hd
    exact congrArg some heq

end PipelineImpl
end Layered
end Elegant
