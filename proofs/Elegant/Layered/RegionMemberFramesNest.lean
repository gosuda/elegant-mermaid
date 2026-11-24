import Elegant.Layered.RegionFlatC3
import Elegant.Layered.RegionPlacement
import Elegant.Layered.RegionPipeline
import Elegant.Layered.RegionModel
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.CgShape
 import Elegant.Layered.Compound
 import Elegant.Layered.CoordGraph
 import Elegant.Layered.ComponentCoverage
set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region member-frame nesting (`R_MemberFramesNestR`).

Proves `R_memberFramesNestR_holds`: the region analogue of `exactMemberInFrame'`
(`ExactRunFrameNestingProof.lean`), from one narrower named residual
`R_RegionNestResidual` about the region coordinate allocation.

Truth note (probe `proofs/wip/Probe/RegionFlatC3Probe.lean`): `nest=true` on the
three executed inputs (two-region, nested, titled-group); the R2/R4
fixed-parent inputs are counterexamples without `framedParents`, so the
`WellFormed` / `framedParents` premises mirror `exactMemberInFrame'`.

Split of the exact-twin proof:
- Ordering / rank structure replays here: `measuredGraph` and `exactGraph`
  construction is shared between `SceneExecutionX` and `SceneExecutionR`, so
  the graph-side transfer (`rmfn_revKey`, `rmfn_borderSplit`, `rmfn_plainPath`)
  and the input-level assembly (`framedParents_parent`, `boxIds_nodup`,
  `path_of_parent`, paired markers) replay verbatim.
- Coordinate step stays open: `crossCoordsR` (`RegionPlacement.lean`)
  replaces `crossCoordsClusterWith` with pinned layers, `allocatePl` shifts,
  and `regionFrames` border placement. The residual keeps exactly that part:
  conjunct one is the horizontal bracketing of a plain member rect plus the
  proper-node correspondence at the same index (the `proxyWidths` /
  `dropSynthetic` stages shared with the exact run preserve indices); the
  vertical half is then closed in-file with the generic hull lemmas
  `frameRect_member_vertical` / `frameRect_side_marker_contained`.
  Conjunct two is child-group nesting, whose both-axis argument needs the
  region allocation and the region proper-node scoping.
-/
 /-- Region nesting residual: the `crossCoordsR` coordinate-allocation remainder.
 
 Conjunct one covers plain members: the proper node at the same index carries
 the member path, and the parent frame brackets the member rect in `x`. This is
 the horizontal half of nesting; the matching vertical half is proved from the
 generic hull lemmas once this correspondence is available. Conjunct two covers
 child groups in full: their both-axis nesting needs the region allocation.
 Together this is strictly narrower than `R_MemberFramesNestR` (plain members
 lack the vertical half here), and it holds on the three probe inputs (see the
 `#eval` checks below). -/
 def R_RegionNestResidual (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   (∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
     (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
     (run : Run) (orderOptions : OrderOptions),
     comp ∈ components execution.graph →
     componentRunR execution.params (exactDecls exactIds inp) spec' inp
       (componentCandidateR spec' execution.graph comp candidate) execution.measured
       orderOptions = .ok (cg', run) →
     ∀ (index memberIndex : Nat) (node member : Node),
       (componentCandidateR spec' execution.graph comp candidate).nodes[index]? =
         some node →
       node.border = -2 →
       (componentCandidateR spec' execution.graph comp candidate).nodes[memberIndex]? =
         some member →
       member.border = 0 → member.clusterPath.contains node.decl = true →
       ∃ actual : ProperNode, run.proper.nodes[memberIndex]? = some actual ∧
         actual.node.clusterPath = member.clusterPath ∧
         (frameRect execution.params
           (componentCandidateR spec' execution.graph comp candidate)
           run index).x ≤
           (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
         (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
           (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
           (frameRect execution.params
             (componentCandidateR spec' execution.graph comp candidate)
             run index).x +
           (frameRect execution.params
             (componentCandidateR spec' execution.graph comp candidate)
             run index).w) ∧
   (∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
     (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
     (run : Run) (orderOptions : OrderOptions),
     comp ∈ components execution.graph →
     componentRunR execution.params (exactDecls exactIds inp) spec' inp
       (componentCandidateR spec' execution.graph comp candidate) execution.measured
       orderOptions = .ok (cg', run) →
     ∀ (parentIndex childIndex : Nat) (parent child : Node),
       (componentCandidateR spec' execution.graph comp candidate).nodes[parentIndex]? =
         some parent →
       parent.border = -2 →
       (componentCandidateR spec' execution.graph comp candidate).nodes[childIndex]? =
         some child →
       child.border = -2 →
       ∀ (parentBox childBox : ModelBox),
         inp.boxes[parent.decl]? = some parentBox →
         inp.boxes[child.decl]? = some childBox →
         childBox.parent = parentBox.id → childBox.parent ≠ "" →
         (frameRect execution.params
           (componentCandidateR spec' execution.graph comp candidate)
           run parentIndex).Contained
           (frameRect execution.params
             (componentCandidateR spec' execution.graph comp candidate)
             run childIndex))
 /-! ## Probe evidence for the residual.

 Executable copies of the three `RegionFlatC3Probe` inputs plus the real
 `layoutRIds` prefix. The `#eval` checks after the checker evaluate the
 decidable form of both residual conjuncts on every executed component run.
 -/
 private def rmfn_o : Options := { profile := .vector, direction := .TB }

 private def rmfn_nBox (id parent : String) : ModelBox :=
   { id := id, parent := parent, exclusive := false }

 private def rmfn_gBox (id parent : String) : ModelBox :=
   { id := id, role := .group, parent := parent, exclusive := false }

 private def rmfn_rt (id fromId toId : String) : ModelRoute :=
   { id := id, fromId := fromId, toId := toId }

 private def rmfn_inp2 : Input := { kind := "state", boxes := [rmfn_gBox "G1" "", rmfn_gBox "A" "G1", rmfn_gBox "B" "G1", rmfn_gBox "G2" "", rmfn_gBox "C" "G2", rmfn_gBox "D" "G2"], routes := [rmfn_rt "e1" "A" "B", rmfn_rt "e2" "C" "D"], texts := ["G1", "A", "B", "G2", "C", "D"], edges := [.plain], labels := [] }

 private def rmfn_sets2 : List ModelRegionSet :=
   [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]

 private def rmfn_inpN : Input := { kind := "state", boxes := [rmfn_gBox "G" "", rmfn_gBox "H" "G", rmfn_gBox "J" "H", rmfn_nBox "a" "J", rmfn_nBox "b" "G"], routes := [rmfn_rt "e1" "b" "a"], texts := ["G", "H", "J", "a", "b"], edges := [.plain], labels := [] }

 private def rmfn_setsN : List ModelRegionSet :=
   [{ parent := 0, regions := [1] }, { parent := 1, regions := [2] }]

 private def rmfn_inpT : Input := { kind := "state", boxes := [rmfn_gBox "T" "", rmfn_gBox "G1" "T", rmfn_gBox "A" "G1", rmfn_gBox "B" "G1", rmfn_nBox "a1" "A", rmfn_nBox "b1" "B"], routes := [rmfn_rt "e1" "a1" "b1"], texts := ["T", "G1", "A", "B", "a1", "b1"], edges := [.plain], labels := [] }

 private def rmfn_setsT : List ModelRegionSet :=
   [{ parent := 1, regions := [2, 3] }]

 /-- Real prefix of `layoutRIds`: params, exact graph, measured labels, spec. -/
 private def rmfn_prefix (inp : Input) (sets : List ModelRegionSet) :
     Except LayoutError (Params × Graph × List MeasuredLabel × Option RegionSpec) := do
   let P ← checkedParams .vector inp.kind
   let m ← metricOf .vector
   let target := Measure.wrapTarget m.profile P.wrapWidth 0
   let lines ← boxLines m target inp
   let measured ← measureLabels P m target inp .TB
   let g0 ← measuredGraph P inp rmfn_o lines
   let g ← exactGraph P [] inp rmfn_o measured g0
   let idSets ← graphRegions inp sets
   let titles := lines.map fun ls =>
     let width := ls.foldl (fun w line => max w line.width) 0
     let height := (max 1 ls.length : Int) * P.lineH
     (width, height)
   pure (P, g, measured, if idSets.isEmpty then none else some (RegionSpec.mk idSets titles))
 /-- Decidable form of both residual conjuncts for one executed component run. -/
 private def rmfn_checkRun (P : Params) (inp : Input) (labels : List MeasuredLabel)
     (g : Graph) (spec : Option RegionSpec) (comp : List Nat) (idx : Nat) : Bool :=
   match componentRunR P [] spec inp (componentCandidateR spec g comp idx) labels {} with
   | .error _ => true
   | .ok (cg', run) =>
     ((List.range comp.length).filterMap fun mi =>
       match comp[mi]? with
       | none => none
       | some key => match inp.boxes[key]? with
         | none => none
         | some cb => if cb.parent == "" then none
           else match (inp.boxes.zipIdx.find? fun q => q.1.id == cb.parent).map Prod.snd with
             | none => none
             | some pi => some (mi, pi)).all fun q =>
       match (comp.zipIdx.find? fun r => r.1 == q.2).map Prod.snd with
       | none => true
       | some pj =>
         match cg'.nodes[q.1]? with
         | none => false
         | some member =>
           let parentFrame := frameRect P cg' run pj
           if member.border == 0 then
             match run.proper.nodes[q.1]? with
             | none => false
             | some actual =>
               actual.node.clusterPath == member.clusterPath &&
               decide (parentFrame.x ≤ (Labels.rectAt run.proper run.xs run.ys q.1).x) &&
               decide ((Labels.rectAt run.proper run.xs run.ys q.1).x +
                 (Labels.rectAt run.proper run.xs run.ys q.1).w ≤
                 parentFrame.x + parentFrame.w)
           else if member.border == -2 then
             decide (parentFrame.Contained (frameRect P cg' run q.1))
           else true

 /-- Residual evidence over all components and candidates `0‥4`. -/
 private def rmfn_evidence (sets : List ModelRegionSet) (inp : Input) : Bool :=
   match rmfn_prefix inp sets with
   | .error _ => false
   | .ok (P, g, measured, spec) =>
     (components g).all fun comp =>
       ([0, 1, 2, 3, 4].all fun idx =>
         rmfn_checkRun P inp measured g spec comp idx)

 #eval rmfn_evidence rmfn_sets2 rmfn_inp2
 #eval rmfn_evidence rmfn_setsN rmfn_inpN
 #eval rmfn_evidence rmfn_setsT rmfn_inpT
 #eval (framedParents rmfn_inp2, framedParents rmfn_inpN, framedParents rmfn_inpT)
 /-! ## Ordering / rank replay over the shared graph construction.

 `SceneExecutionR` builds `graph0`/`graph` with the same `measuredGraph` /
 `exactGraph` calls as `SceneExecutionX`, so these transfer lemmas replay the
 `ExactMemberInFrame.lean` local copies verbatim. -/
 private theorem rmfn_linesLen {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
     execution.lines.length = inp.boxes.length := by
   have h := execution.lines_eq
   simp only [boxLines] at h
   exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx

 private def rmfn_proj (n : Node) : Nat × Int × List Nat :=
   (n.decl, n.border, n.clusterPath)

 private theorem rmfn_projMap {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
     List.map rmfn_proj execution.graph.nodes =
       List.map rmfn_proj execution.graph0.nodes := by
   have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
     exactGraph_length execution.graph_eq
   apply List.ext_getElem?
   intro v
   rw [List.getElem?_map, List.getElem?_map]
   cases h0 : execution.graph0.nodes[v]? with
   | none =>
     have hnone : execution.graph.nodes[v]? = none := by
       rw [List.getElem?_eq_none_iff] at h0 ⊢
       omega
     rw [hnone]
   | some nd0 =>
     obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq h0
     rw [hnd']
     simp only [Option.map_some, rmfn_proj, hnb, hnap, hnd]

 /-- Every region-graph node comes from the measured-graph node at the same
 index with the same key fields. -/
 private theorem rmfn_revKey {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
     {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
     ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
       nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
   have hmap := rmfn_projMap execution
   have h1 : (List.map rmfn_proj execution.graph.nodes)[v]? = some (rmfn_proj nd) := by
     simp only [List.getElem?_map, h, Option.map_some]
   rw [hmap] at h1
   rw [List.getElem?_map] at h1
   obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
   simp only [rmfn_proj, Prod.mk.injEq] at hproj
   exact ⟨nd0, hnd0, hproj.1, hproj.2.1, hproj.2.2⟩
 /-- A measured-graph node below the box count is a plain node or a group top. -/
 private theorem rmfn_borderSplit {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
     {key : Nat} (hkeyLen : key < inp.boxes.length)
     {member : Node} (hmemberGraph : execution.graph0.nodes[key]? = some member) :
     member.border = 0 ∨ member.border = -2 := by
   obtain ⟨nodes, edges, titles, hprepared, hnodeLen, hmetadata⟩ :=
     measuredGraph_prepared_source execution.graph0_eq
   have hkeyNodes : key < nodes.length := by
     rw [hnodeLen, rmfn_linesLen]
     exact hkeyLen
   rw [hprepared] at hmemberGraph
   have hdemoted : (inp.boxes.map (fun source : ModelBox =>
       if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
         { source with role := .node } else source))[key]? =
       some ((fun source : ModelBox =>
       if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
         { source with role := .node } else source) inp.boxes[key]) := by
     simp only [List.getElem?_map, List.getElem?_eq_getElem hkeyLen, Option.map_some]
   by_cases hng : ((fun source : ModelBox =>
       if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
         { source with role := .node } else source) inp.boxes[key]).role = .group
   · rw [Compound.prepare_group_title_record _ _ _ ⟨nodes, edges, execution.params.slot⟩
       hkeyNodes hdemoted hng] at hmemberGraph
     refine Or.inr ?_
     have hb := congrArg Node.border (Option.some.inj hmemberGraph)
     simpa using hb.symm
   · rw [Compound.prepare_plain_node_record _ _ _ ⟨nodes, edges, execution.params.slot⟩
       hkeyNodes hdemoted hng] at hmemberGraph
     refine Or.inl ?_
     have hsrc := hmetadata key nodes[key] (List.getElem?_eq_getElem hkeyNodes)
     have hb : member.border = nodes[key].border :=
       (congrArg Node.border (Option.some.inj hmemberGraph)).symm
     rw [hb]
     exact hsrc.2

 /-- A plain measured-graph node resolves to its input box and compound path. -/
 private theorem rmfn_plainPath {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
     {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
     (hplain : node.border = 0) :
     ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
       node.clusterPath = Compound.path inp.boxes box := by
   have hlineLength : execution.lines.length = inp.boxes.length := rmfn_linesLen execution
   obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
     measuredGraph_prepared_source execution.graph0_eq
   have hpreparedNode := hnode
   rw [hprepared] at hpreparedNode
   have hi : index < nodes.length := by
     by_cases hi : index < nodes.length
     · exact hi
     · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
         hpreparedNode
       omega
   have hibox : index < inp.boxes.length := by omega
   let box := inp.boxes[index]'hibox
   have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
   obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
   obtain ⟨hdecl, hpath⟩ :=
     prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
   exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩
 /-- Region candidates share the component-graph nodes (no cycle breaking). -/
 private theorem rmfn_candNodesEq (spec : Option RegionSpec) (g : Graph)
     (comp : List Nat) (candidate : Nat) :
     (componentCandidateR spec g comp candidate).nodes =
       (componentGraph g comp).nodes := by
   cases spec with
   | none => exact componentCandidate_nodes g comp candidate
   | some _ => rfl

 /-- Candidate member lookups read back the execution-graph node. -/
 private theorem rmfn_memberGraph {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
     {comp : List Nat} {spec' : Option RegionSpec} {candidate memberIndex key : Nat}
     {member : Node} (hkey : comp[memberIndex]? = some key)
     (hkeyLen : key < inp.boxes.length)
     (hmember : (componentCandidateR spec' execution.graph comp candidate).nodes[memberIndex]? =
       some member) :
     execution.graph.nodes[key]? = some member := by
   have h := hmember
   rw [rmfn_candNodesEq] at h
   dsimp only [componentGraph] at h
   simp only [List.getElem?_map, Option.map_some, hkey,
     List.getD_eq_getElem?_getD] at h
   have hgl : key < execution.graph.nodes.length := by
     have h1 := exactGraph_length execution.graph_eq
     have h2 := measuredGraph_nodes_length_ge execution.graph0_eq
       (rmfn_linesLen execution)
     omega
   cases hkeyOpt : execution.graph.nodes[key]? with
   | none =>
     have hnone : execution.graph.nodes[key]? = none := hkeyOpt
     rw [List.getElem?_eq_none_iff] at hnone
     omega
   | some node =>
     rw [hkeyOpt] at h
     simpa using h

 /-- Candidate parent lookups read back the paired group marker. -/
 private theorem rmfn_parentNode {spec' : Option RegionSpec} {g : Graph} {comp : List Nat}
     {candidate parentIndex : Nat} {parentKey : Nat} {top : Node}
     (hparentIndex : comp[parentIndex]? = some parentKey)
     (htopLookup : g.nodes[parentKey]? = some top) :
     (componentCandidateR spec' g comp candidate).nodes[parentIndex]? = some top := by
   rw [rmfn_candNodesEq]
   simp only [componentGraph, List.getElem?_map, Option.map_some, hparentIndex,
     List.getD_eq_getElem?_getD, htopLookup, Option.getD_some]

 /-- Plain member frames are their proper rects. -/
 private theorem rmfn_memberFrameEq (P : Params) (cg : Graph) (run : Run)
     {memberIndex : Nat} {member : Node} {actual : ProperNode}
     (hmemberGet : cg.nodes.getD memberIndex default = member)
     (hplain : member.border = 0)
     (hproper : run.proper.nodes[memberIndex]? = some actual) :
     frameRect P cg run memberIndex =
       Labels.rectAt run.proper run.xs run.ys memberIndex := by
   unfold frameRect
   rw [hmemberGet]
   simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
   unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
     RouteImpl.nodeW RouteImpl.nodeH
   simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
 /-- Locate the referenced parent as a group marker in the region candidate. -/
 private theorem rmfn_locateParent {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
     (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
     {comp : List Nat} {candidate : Nat} {spec' : Option RegionSpec}
     {key parentKey parentIndex : Nat}
     {childBox : ModelBox} (hchildBox : inp.boxes[key]? = some childBox)
     {parentBox : ModelBox} (hparentBox : inp.boxes[parentKey]? = some parentBox)
     (hparentRef : childBox.parent = parentBox.id) (hparentNe : childBox.parent ≠ "")
     (hparentIndex : comp[parentIndex]? = some parentKey) :
     ∃ top : Node,
       (componentCandidateR spec' execution.graph comp candidate).nodes[parentIndex]? =
         some top ∧
       top.border = -2 ∧ top.decl = parentKey ∧
       execution.graph.nodes[parentKey]? = some top := by
   obtain ⟨pb, hpbMem, hpid, hpgroup, hpnotfixed⟩ := framedParents_parent hframed
     (List.mem_of_getElem? hchildBox) hparentNe
   have hnod := Model.boxIds_nodup hwf
   obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpbMem
   have hmapLen : parentKey < (inp.boxes.map (·.id)).length := by
     rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hparentBox).1
   have hmapLen2 : pi < (inp.boxes.map (·.id)).length := by
     rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
   have hid : (inp.boxes.map (·.id))[pi]? = (inp.boxes.map (·.id))[parentKey]? := by
     rw [List.getElem?_map, hpi, List.getElem?_map, hparentBox]
     simp only [Option.map_some, hpid, hparentRef]
   have hpe : pi = parentKey := (hnod.getElem?_inj hmapLen2).mp hid
   have hpe' : parentKey = pi := hpe.symm
   subst hpe'
   have hsame : pb = parentBox :=
     Option.some.inj (hpi.symm.trans hparentBox)
   subst hsame
   have hpbLookup : inp.boxes[parentKey]? = some pb := hparentBox
   have hfPb : ((fun source : ModelBox =>
       if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
         { source with role := .node } else source) pb) = pb := by
     simp [hpnotfixed]
   have hdemP : (inp.boxes.map (fun source : ModelBox =>
       if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
         { source with role := .node } else source))[parentKey]? = some pb := by
     rw [List.getElem?_map, hpbLookup]
     simp only [Option.map_some, hfPb]
   have hpkLines : parentKey < execution.lines.length := by
     rw [rmfn_linesLen]
     exact (List.getElem?_eq_some_iff.mp hpbLookup).1
   obtain ⟨top0, -, htopLookup0, -, htopBorder0, -, htopDecl0, -, -, -, -, -⟩ :=
     measuredGraph_paired_markers execution.graph0_eq hpkLines hdemP hpgroup
   obtain ⟨top, htopLookup, htopBorderD, _, htopDeclD⟩ :=
     exactGraph_node_key execution.graph_eq htopLookup0
   have htopBorder : top.border = -2 := htopBorderD.trans htopBorder0
   have htopDecl : top.decl = parentKey := htopDeclD.trans htopDecl0
   have hparentNode : (componentCandidateR spec' execution.graph comp candidate).nodes[parentIndex]? =
       some top :=
     rmfn_parentNode hparentIndex htopLookup
   exact ⟨top, hparentNode, htopBorder, htopDecl, htopLookup⟩
 /-- Region member frames nest in their parent frame, from the residual. -/
 theorem R_memberFramesNestR_holds {exactIds : List String}
     {idSets : List (String × List String)}
     (hresid : R_RegionNestResidual exactIds idSets) :
     R_MemberFramesNestR exactIds idSets := by
   intro inp o res execution hwf hframed comp candidate spec' cg' run orderOptions
     hcomp hrun
   intro memberIndex key parentKey parentIndex member hkey hkeyLen hmember
   intro childBox hchildBox parentBox hparentBox hparentRef hparentNe hparentIndex
   have hmemberGraph : execution.graph.nodes[key]? = some member :=
     rmfn_memberGraph execution hkey hkeyLen hmember
   obtain ⟨top, hparentNode, htopBorder, htopDecl, htopLookup⟩ :=
     rmfn_locateParent execution hwf hframed hchildBox hparentBox
       hparentRef hparentNe hparentIndex
   obtain ⟨member0, hmember0Graph, hmember0Decl, hmember0Border, hmember0Path⟩ :=
     rmfn_revKey execution hmemberGraph
   rcases rmfn_borderSplit execution hkeyLen hmember0Graph with hborder0 | hborderM2
   · obtain ⟨b0, hb0lookup, -, hpath0⟩ :=
       rmfn_plainPath execution hmember0Graph hborder0
     have hb0eq : b0 = childBox := Option.some.inj (hb0lookup.symm.trans hchildBox)
     have hstep : Compound.path inp.boxes childBox =
         Compound.path inp.boxes parentBox ++ [parentKey] :=
       Compound.path_of_parent (inputModel inp o) hwf hparentBox hchildBox
         hparentRef hparentNe
     have hmemberBorder : member.border = 0 := hmember0Border.symm.trans hborder0
     have hmemberPath : member.clusterPath = Compound.path inp.boxes childBox := by
       rw [← hmember0Path, hpath0, hb0eq]
     have hin : parentKey ∈ member.clusterPath := by
       rw [hmemberPath, hstep]
       exact List.mem_append_right _ (List.mem_singleton_self _)
     obtain ⟨actual, hproper, hactualPath, hlo, hhi⟩ := hresid.1 execution hwf hframed
       comp candidate spec' cg' run orderOptions hcomp hrun parentIndex memberIndex
       top member hparentNode htopBorder hmember hmemberBorder
       (by rw [htopDecl]; exact List.contains_iff_mem.mpr hin)
     have hmemberGet : (componentCandidateR spec' execution.graph comp candidate).nodes.getD
         memberIndex default = member := by
       simp only [List.getD_eq_getElem?_getD, hmember, Option.getD_some]
     have hmemberFrame := rmfn_memberFrameEq execution.params _ run
       hmemberGet hmemberBorder hproper
     have hparentGet : (componentCandidateR spec' execution.graph comp candidate).nodes.getD
         parentIndex default = top := by
       simp only [List.getD_eq_getElem?_getD, hparentNode, Option.getD_some]
     have hq : (actual, memberIndex) ∈ run.proper.nodes.zipIdx :=
       List.mk_mem_zipIdx_iff_getElem?.mpr hproper
     have hscope : actual.node.clusterPath.contains
         ((componentCandidateR spec' execution.graph comp candidate).nodes.getD
           parentIndex default).decl = true := by
       rw [hparentGet, htopDecl, hactualPath]
       exact List.contains_iff_mem.mpr hin
     have hvert := frameRect_member_vertical (P := execution.params)
       (cg := componentCandidateR spec' execution.graph comp candidate) (run := run)
       (i := parentIndex) (q := (actual, memberIndex))
       (by rw [hparentGet]; exact htopBorder) hq hscope
     rw [hmemberFrame]
     unfold Rect.Contained
     exact ⟨hlo, hhi, hvert.1, hvert.2⟩
   · obtain ⟨hdeclM0, -, -, -, -⟩ :=
       measuredGraph_group_origin execution.graph0_eq hmember0Graph hborderM2
     have hmemberBorder : member.border = -2 := hmember0Border.symm.trans hborderM2
     have hdeclM : member.decl = key := hmember0Decl.symm.trans hdeclM0
     have hparentBoxDecl : inp.boxes[top.decl]? = some parentBox := by
       rw [htopDecl]; exact hparentBox
     have hchildBoxDecl : inp.boxes[member.decl]? = some childBox := by
       rw [hdeclM]; exact hchildBox
     exact hresid.2 execution hwf hframed comp candidate spec' cg' run orderOptions
       hcomp hrun parentIndex memberIndex top member hparentNode htopBorder
       hmember hmemberBorder parentBox childBox hparentBoxDecl hchildBoxDecl
       hparentRef hparentNe
