 import Elegant.Layered.ExactFlatC5Rank
 import Elegant.Layered.StrictMemberFrameProof
 import Elegant.Layered.ComponentRunGenGeometry
 import Elegant.Layered.ExactRunFrameNestingProof
 import Elegant.Layered.LoopRectRealQProof
 import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

 /-! # Exact loop-rect top same-part (W form), closed modulo outsider disjointness

 The full split disjunction (strict-inside for members, disjointness with
 positivity for outsiders) is false in general: group `g` with member `a`,
 plus zero-size outsider `b` (`fixedSizes [("b", 0, 0)]`, `exactIds ["b"]`)
 in the same component. Pair `(g, b)` is disjoint but has `fw = 0, 0`.
 The consumer needs only `XL_TopSamePartW`: the group-top frame and a
 plain frame in the same component are never equal. Inside pairs close by
 strict member-left; outside pairs close by outsider disjointness
 (`XLrr_TopOutsideDisjointW`) plus group positivity (proved here).

Probe evidence (`proofs/wip/Probe/ExactTopSamePartTProbe.lean`):
`wit/exact-b`: `v=0 w=1 inside=true cont=true strict=true disj=false neq=true
fw=2051,3072 fv=8194,12288`; `v=0 w=2 inside=false cont=false strict=false
disj=true neq=true fw=0,0 fv=8194,12288`.
`zero-group/exact-a`: `v=0 w=1 inside=true cont=true strict=true disj=true
neq=true fw=0,0 fv=7680,13056`.
Eight inputs of `ExactLoopRectFactsTProbe` give `neq=true` on every top pair.
-/

/-- Per-execution outsider disjointness: a plain run frame outside the group is
disjoint from the group-top frame. Strictly narrower than `XL_TopSamePartW`
(outside half only, no equality conclusion). True on the probes above. -/
def XLrr_TopOutsideDisjointW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run →
    ∀ {v w : Nat} {node member : Node},
      (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
      node.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
      member.border = 0 →
      ¬(member.clusterPath.contains node.decl = true) →
      Disjoint (frameRect execution.params (componentCandidate execution.graph comp candidate) run w)
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run v)

 /-- Per-execution W form of `XL_TopSamePart`: a plain run frame never equals a
 group-top run frame over the actual executed component run. -/
 def XL_TopSamePartW (exactIds : List String) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
     {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
     componentRunX execution.params (exactDecls exactIds inp)
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run →
     ∀ {v w : Nat} {node member : Node},
       (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
       node.border = -2 →
       (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
       member.border = 0 →
       frameRect execution.params (componentCandidate execution.graph comp candidate) run w =
         frameRect execution.params (componentCandidate execution.graph comp candidate) run v →
       False

 /-- Member containment (non-strict core of the member case), proved fully via
 `exactRunFrameNesting`: every plain member inside a group lies in its frame. -/
 theorem XLrr_topMemberContainedW_holds (exactIds : List String) :
     ∀ {inp : Input} {o : Options} {res : FamilyResult}
       (execution : SceneExecutionX exactIds inp o res)
       (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
       {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
       {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
       componentRunX execution.params (exactDecls exactIds inp)
         (componentCandidate execution.graph comp candidate) execution.measured
         orderOptions = .ok run →
       ∀ {v w : Nat} {node member : Node},
         (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
         node.border = -2 →
         (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
         member.border = 0 →
         member.clusterPath.contains node.decl = true →
         (frameRect execution.params (componentCandidate execution.graph comp candidate)
           run v).Contained
           (frameRect execution.params (componentCandidate execution.graph comp candidate)
             run w) := by
   intro inp o res execution hwf hfp comp _hcomp candidate run orderOptions hrun
   intro v w node member hnode hgroup hmember hplain hinside
   exact (exactRunFrameNesting (exactIds := exactIds) (inp := inp) (o := o) (res := res) execution hwf hfp).1 comp candidate run
     orderOptions _hcomp hrun v w node member hnode hgroup hmember hplain hinside


private def etsp_proj (n : Node) : Nat × Int × List Nat := (n.decl, n.border, n.clusterPath)

private theorem etsp_projMap {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    List.map etsp_proj execution.graph.nodes =
      List.map etsp_proj execution.graph0.nodes := by
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
    simp only [Option.map_some, etsp_proj, hnb, hnap, hnd]

private theorem etsp_revKey {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
    ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
      nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
  have hmap := etsp_projMap execution
  have h1 : (List.map etsp_proj execution.graph.nodes)[v]? = some (etsp_proj nd) := by
    simp only [List.getElem?_map, h, Option.map_some]
  rw [hmap] at h1
  rw [List.getElem?_map] at h1
  obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
  simp only [etsp_proj, Prod.mk.injEq] at hproj
  exact ⟨nd0, hnd0, hproj.1, hproj.2.1, hproj.2.2⟩

private theorem etsp_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx

private theorem etsp_plainPath {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  have hlineLength : execution.lines.length = inp.boxes.length := etsp_lines_len execution
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

private theorem etsp_groupPath {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box ++ [index] := by
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnode hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, hdecl, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap, hdecl] at hpath
  exact hpath

/-- Exact member paths extend the group path (prefixed copy). -/
private theorem etsp_member_path_prefix {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    node.clusterPath <+: member.clusterPath := by
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := etsp_revKey execution hgroupSource
  have hnonempty : member.clusterPath ≠ [] := by
    intro hempty
    simp [hempty] at hinside
  obtain ⟨_, _, hmemberSource⟩ :=
    componentCandidate_nonempty_path_source hmember hnonempty
  obtain ⟨member0, hmember0, _hmemberDeclM, hbM, hpM⟩ := etsp_revKey execution hmemberSource
  obtain ⟨groupBox, hgroupBox, hgroupDecl, hgroupPath⟩ :=
    etsp_groupPath execution hgroup0 (hbG.trans hgroup)
  obtain ⟨memberBox, hmemberBox, hmemberDecl, hmemberPath⟩ :=
    etsp_plainPath execution hmember0 (hbM.trans hplain)
  have hin : group0.decl ∈ Compound.path inp.boxes memberBox := by
    have h := hinside
    rw [← hpM, hmemberPath, List.contains_iff_mem] at h
    rwa [← hdG] at h
  have hg : (inputModel inp o).boxes[group0.decl]? = some groupBox := by
    rw [hgroupDecl]
    exact hgroupBox
  have hm : (inputModel inp o).boxes[member0.decl]? = some memberBox := by
    rw [hmemberDecl]
    exact hmemberBox
  have hprefix := Compound.path_ancestor_prefix (inputModel inp o) hwf hg hm hin
  rw [← hpG, hgroupPath, ← hgroupDecl, ← hpM, hmemberPath]
  exact hprefix

private theorem etsp_ranked_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      ∀ edge ∈ (Compound.rankingGraph cg).edges,
        edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  unfold componentRunX at h
  obtain ⟨rr, hrr, h⟩ := bind_ok h
  obtain ⟨normalized, hn, h⟩ := bind_ok h
  obtain ⟨labeled, hl, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have heq := Except.ok.inj h
  subst run
  refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
  apply rank_feasible (Compound.rankingGraph cg) rr.ranks
  simp only [RankImpl.rank, hrr]

private theorem etsp_plain_anchor_dims (P : Params) {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨sized, hs, he, hb', hw, hh⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.edge = nd.edge ∧ sized.node.border = 0 ∧
        nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
    · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
      exact Int.le_max_left _ _
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? = some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split <;> exact ⟨_, rfl, he, hb', hw, hh⟩

private theorem etsp_plain_node_dims {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

private theorem etsp_sized_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  unfold sizeProperPortsX
  simp

private theorem etsp_coordinateGraph0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := etsp_sized_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

private theorem etsp_coordinateGraph_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases etsp_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

private theorem etsp_original_plain_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = node.clusterPath ∧ actual.edge = none ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := etsp_ranked_source hrun
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, hedge, hborder, hwidth, hheight⟩ :=
    etsp_plain_anchor_dims P hsource hplain
  have hmetadata : actual.dummy = false ∧ actual.node.clusterPath = node.clusterPath := by
    rcases etsp_coordinateGraph_lookup P exact labeled hactual with
      ⟨original, horiginal, hd, _, hp, _⟩ | ⟨_, hside⟩ |
        ⟨_, _, _, _, _, hb3, _⟩
    · have heq : original = ⟨node, false, none, false⟩ :=
        Option.some.inj (horiginal.symm.trans hsource)
      subst original
      exact ⟨hd, hp rfl⟩
    · rcases hside with hside | hside <;> omega
    · omega
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := etsp_plain_node_dims hrun hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, _, _, _⟩ := componentRunX_spec hrun
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hmetadata.1, hborder, hmetadata.2,
    hedge, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

private theorem etsp_titled_alignment (P : Params) (exact : List Nat) {source : Proper}
    (h : source.nodes.length = source.rank.length) :
    (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length := by
  rw [titleReservations_nodes]
  simp only [List.length_append, List.length_map, etsp_sized_length]
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank]
  simp only [List.length_append, List.length_map]
  omega

/-- Exact-sized nodes preserve origin (prefixed copy). -/
private theorem etsp_sized_origin (P : Params) (exact : List Nat) (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

private theorem etsp_titled_origin {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
    (hnode : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some node) :
    (∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath) ∨
    (node.dummy = false ∧ node.node.border = 3) := by
  rw [titleReservations_nodes] at hnode
  by_cases hi : index < (sizeProperPortsX P exact source).nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map] at hnode
    obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨original, horiginal, hd, hb, hp⟩ :=
      etsp_sized_origin P exact source hsized
    have ht := titleF_keys sized
    rw [heq] at ht
    exact Or.inl ⟨original, horiginal, ht.1.trans hd,
      ht.2.1.trans hb, ht.2.2.1.trans hp⟩
  · rw [List.getElem?_append_right (by
      simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getElem?_map] at hnode
    obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hd, hb, _⟩ :=
      etsp_sized_origin P exact source hsized
    have hreal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · rw [hplain] at hb
        omega
    right
    rw [← heq]
    exact ⟨hd.trans hreal, rfl⟩

private theorem etsp_cgShape {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    CgShape execution.graph := by
  have hshape := measuredGraph_shape execution.graph0_eq
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    obtain ⟨na0, ha0, _, hb1, hp1⟩ := etsp_revKey execution ha
    obtain ⟨nb0, hb0, _, hb2, hp2⟩ := etsp_revKey execution hb
    exact hshape.1 a b na0 nb0 ha0 hb0 (by rw [hb1]; exact h1) (by rw [hb2]; exact h2)
      (by rw [hp1, hp2]; exact hp)
  · intro n hn
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, h0, _, hb, _⟩ := etsp_revKey execution hv
    have h3 := hshape.2 n0 (List.mem_of_getElem? h0)
    rw [hb] at h3
    exact h3

private theorem etsp_marker_shape {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  by_cases hplain : node.border = 0
  · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
  · obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hnode hplain
    obtain ⟨member0, hmember0, _, hborder, hpath⟩ := etsp_revKey execution hsource
    obtain ⟨hdisj, hne⟩ := measuredGraph_marker_shape execution.graph0_eq hmember0
    refine ⟨?_, ?_⟩
    · rcases hdisj with h0 | h2 | h2
      · exact Or.inl (hborder.symm.trans h0)
      · exact Or.inr (Or.inl (hborder.symm.trans h2))
      · exact Or.inr (Or.inr (hborder.symm.trans h2))
    · intro hgroup
      have h0 : member0.border = -2 := hborder.trans hgroup
      rw [← hpath]
      exact hne h0

private theorem etsp_titled_border_ready {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, etsp_titled_alignment P _ haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases etsp_titled_origin hkeys hindex with
      ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases etsp_titled_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases etsp_titled_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases etsp_titled_origin hkeys hb with
        ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases etsp_titled_origin hkeys hindex with
      ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy

private theorem etsp_prepared_titled_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := etsp_ranked_source hrun
  have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (etsp_cgShape execution) candidate
  have hready := etsp_titled_border_ready (P := execution.params)
    (exact := exactDecls exactIds inp) hk hshape
    (fun _ _ hnode => etsp_marker_shape execution hnode) haligned
  refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_⟩
  · intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  · intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank

private theorem etsp_titled_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some (titleF node) := by
  have hnonplain : node.node.border ≠ 0 := by
    rcases hborder with hborder | hborder <;> omega
  have hsized : (sizeProperPortsX P exact source).nodes[index]? = some node := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some,
      Nat.zero_add]
    simp [hnonplain]
  rw [titleReservations_nodes, List.getElem?_append_left (by
    simp only [List.length_map, etsp_sized_length]
    exact (List.getElem?_eq_some_iff.mp hnode).1)]
  simp only [List.getElem?_map, hsized, Option.map_some]

private theorem etsp_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2)
    (hdummy : node.dummy = false) :
    (coordinateGraphX P exact source).nodes[index]? = some (clearF (titleF node)) := by
  have htitled := etsp_titled_marker_record (P := P) (exact := exact) hnode hborder
  obtain ⟨extra, hextension, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  have hbordered : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some (titleF node) := by
    rw [hextension, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitled).1]
    exact htitled
  have hcleared : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some (clearF (titleF node)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hbordered]
    rfl
  have hreal : (clearF (titleF node)).dummy = false :=
    (clearF_keys _).1.trans ((titleF_keys node).1.trans hdummy)
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hcleared, Option.map_some,
    Nat.zero_add, hreal, Bool.false_eq_true, ↓reduceIte]

private theorem etsp_side_original {P : Params} {exact : List Nat} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {side : ProperNode}
    (hside : (coordinateGraphX P exact source).nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source))
        P.clusterBorderW).nodes[index]? = some side := by
  have hwf : OrderImpl.BordersWellFormed (coordinateGraphX P exact source) := by
    unfold coordinateGraphX
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed
        (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
        have hz := hwf.2.2 index side hside hd
        rcases hborder with hborder | hborder <;> omega
  obtain ⟨cleared, hcleared, hd, _, _, heq⟩ :=
    materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)) hside
  have hclearedReal : cleared.dummy = false := hd.symm.trans hreal
  have hsame : side = cleared := heq hclearedReal
  have hclearLookup : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some side := by
    rw [hsame]
    exact hcleared
  rw [clearProxyExtents_nodes, List.getElem?_map] at hclearLookup
  obtain ⟨original, horiginal, hclearEq⟩ := Option.map_eq_some_iff.mp hclearLookup
  have hb : side.node.border = original.node.border := by
    rw [← hclearEq]
    exact (clearF_keys original).2.1
  have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
    rwa [hb] at hborder
  have hclearId : clearF original = original := by
    unfold clearF
    rcases hoside with hoside | hoside <;> simp [hoside]
  exact horiginal.trans (congrArg some (hclearId.symm.trans hclearEq))

private theorem etsp_proxy_side_source {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner sideIndex : Nat) (side : ProperNode),
      node.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  obtain ⟨owner, span, howner, hspan⟩ :=
    proxyWidths_proxy_span_source hproxy hnode hborder
  obtain ⟨sideIndex, side, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    proxySpan_side_source hspan
  exact ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩

private theorem etsp_titled_marker_source_record {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hkeys : NodeKeys cg source)
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {index : Nat} {marker : ProperNode}
    (hmarker : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some marker)
    (hborder : marker.node.border = -2 ∨ marker.node.border = 2) :
    ∃ original : Node, cg.nodes[index]? = some original ∧
      marker.node.border = original.border ∧
      marker = titleF ⟨original, false, none, false⟩ := by
  rcases etsp_titled_origin hkeys hmarker with
    ⟨before, hbefore, _, hb, _⟩ | ⟨_, hb⟩
  · rcases hkeys index before hbefore with
      ⟨original, horiginal, _, hsourceBorder, _⟩ | ⟨_, hplain, _⟩
    · have hborderOriginal : original.border = -2 ∨ original.border = 2 := by
        rcases hborder with hborder | hborder <;> omega
      have hforward := etsp_titled_marker_record (P := P) (exact := exact)
        (hrecords index original horiginal) hborderOriginal
      exact ⟨original, horiginal, hb.trans hsourceBorder,
        Option.some.inj (hmarker.symm.trans hforward)⟩
    · rcases hborder with hborder | hborder <;> omega
  · rcases hborder with hborder | hborder <;> omega

/-- Exact title-reservation rank prefix (prefixed copy). -/
private theorem etsp_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

/-- Exact titled rank record (prefixed copy). -/
private theorem etsp_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := etsp_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Exact coordinate rank anchor prefix (prefixed copy). -/
private theorem etsp_coordinate_anchor_prefix (P : Params) (exact : List Nat) (p : Proper) :
    ∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra := by
  obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  obtain ⟨tail, htitle⟩ := etsp_titled_rank_prefix P exact p
  refine ⟨tail ++ extraRanks, ?_⟩
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
  rw [hr, htitle, List.append_assoc]

/-- Exact coordinate rank record (prefixed copy). -/
private theorem etsp_coordinate_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := etsp_coordinate_anchor_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Exact sided nodes transfer through the coordinate construction (prefixed copy). -/
private theorem etsp_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

/-- Exact coordinate side-rank pairs (prefixed copy). -/
private theorem etsp_coordinate_rank_pair (P : Params) (exact : List Nat)
    (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
      rank)
    (hhi : rank ≤
      (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, etsp_side_record hl rfl (Or.inl rfl),
    etsp_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

/-- Exact titled nodes preserve the executed rank (prefixed copy). -/
private theorem etsp_titled_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := etsp_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index

/-- Exact coordinate nodes preserve the executed rank (prefixed copy). -/
private theorem etsp_coordinate_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (coordinateGraphX P exact source).rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hcoordinateLookup := etsp_coordinate_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

/-- Exact border side nodes transfer to the proper run (prefixed copy). -/
private theorem etsp_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact coordinate titles are unique per cluster path (prefixed copy). -/
private theorem etsp_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases etsp_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

/-- Exact group side borders for a member rank (prefixed copy). -/
private theorem etsp_group_member_borders {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank memberIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank memberIndex := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hgroup
  obtain ⟨originalBottom, horiginalBottom, _, _, _, hconstraintBottom⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq hk hrecords hnode
      hgroup hbottom
  have hinterval := ranked_compound_member_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hgroup hconstraintBottom
    (List.mk_mem_zipIdx_iff_getElem?.mpr hmember) hplain hinside
  have htopRank := etsp_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hnode).1
  have hmemberRank := etsp_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hmember).1
  have hbottomRank := etsp_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp horiginalBottom).1
  have hnonnegative := rankWithBudget_rk_nonneg hrr memberIndex
  have htopBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hbottomForTop :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨node, false, none, false⟩).node.clusterPath) =
        some bottom := by
    simpa [titleF, hgroup] using hbottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    etsp_coordinate_rank_pair execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) htopBorder hbottomForTop
      (rank := (rk rr.ranks memberIndex).toNat)
      (by
        dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢
        omega)
      (by
        dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢
        omega)
  have hmemberCoordinate := etsp_coordinate_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hmember).1
  have hnatcast : ((rk rr.ranks memberIndex).toNat : Int) = rk rr.ranks memberIndex := by
    omega
  have hleftValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank left = rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank right = rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [← hc]
  exact ⟨left, right, hleft, hright, hleftValue.trans hmemberCoordinate.symm,
    hrightValue.trans hmemberCoordinate.symm⟩

/-- Exact runs are border-well-formed (prefixed copy). -/
private theorem etsp_bordersWellFormed {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _⟩ :=
    etsp_prepared_titled_source execution hcomp hrun
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready

/-- Exact member bracket (prefixed copy). -/
private theorem etsp_member_bracket {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers ∧
      run.coordinateProper.nodes[memberIndex]? = some actual ∧
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.xs.getD memberIndex 0 = run.coordinateXs.getD memberIndex 0 ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left memberIndex right := by
  have hprefix := etsp_member_path_prefix execution hwf hnode hgroup hmember hplain hinside
  obtain ⟨actual, hcoordinate, hproper, hreal, hactualPlain, hactualPath,
    _, _, _, hx⟩ := etsp_original_plain_record hrun hmember hplain
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    etsp_group_member_borders execution hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwformed := etsp_bordersWellFormed execution hcomp hrun
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath <+: actual.node.clusterPath := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath <+: actual.node.clusterPath
    rw [(titleF_keys _).2.2.1, hactualPath]
    exact hprefix
  have hleftNe : left ≠ memberIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (-1 : Int) = actual.node.border at hb
    omega
  have hrightNe : right ≠ memberIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (1 : Int) = actual.node.border at hb
    omega
  refine ⟨actual, ord, left, right, horder, hlayers, hcoordinate, hproper, hreal,
    hactualPlain, hactualPath, hx, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left memberIndex right _ actual _ hleft hcoordinate hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

/-- Exact member strict-left: the left side marker sits strictly left of a plain
member inside the same group (strict half of the member border interval). -/
private theorem etsp_member_strict_left {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ left : Nat,
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x <
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x := by
  obtain ⟨actual, ord, left, right, _, hlayers, hcoordinate, hproper, _, hactualPlain,
    hactualPath, hx, hleft, hright, hbracket⟩ :=
    etsp_member_bracket execution hwf hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨_, labeled, _, hc, hk, _, _, _⟩ :=
    etsp_prepared_titled_source execution hcomp hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (etsp_cgShape execution) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact etsp_pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb)
      hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left memberIndex _ _ hlt hli hmi hleft hcoordinate
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
  obtain ⟨hleftFinal, hleftX⟩ := etsp_border_record hrun hleft (Or.inl rfl)
  have hactualWidth := (sizesNonneg_lookup hsizes memberIndex actual hcoordinate).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hactualLoops : 0 ≤ (actual.node.loopExtent : Int) := Int.natCast_nonneg _
  have hgroupLoops : 0 ≤ (node.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  change 0 ≤ execution.params.clusterBorderW at hleftWidth
  refine ⟨left, hleftFinal, ?_⟩
  simp only [coordSep, CoordsImpl.nodeW, hleft, hcoordinate, OrderImpl.borderLeft] at hleftSep
  simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
    hleftFinal, hproper, hleftX, hx, OrderImpl.borderLeft,
    titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
  omega

/-- Exact member strict-left implies the group frame starts left of a plain
member frame: the first private hypothesis of the same-part skeleton. -/
private theorem etsp_hLeft
    (exactIds : List String)
    : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        orderOptions = .ok run →
      ∀ {v w : Nat} {node member : Node},
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
        node.border = -2 →
        (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
        member.border = 0 →
        member.clusterPath.contains node.decl = true →
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).x <
          (frameRect execution.params (componentCandidate execution.graph comp candidate) run w).x := by
  intro inp o res execution hwf _hfp comp hcomp candidate run orderOptions hrun
  intro v w node member hnode hgroup hmember hplain hinside
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨left, hleftFinal, hlt⟩ :=
    etsp_member_strict_left execution hwf hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨actual, _, hproper, _, _, _, _, _, _, _⟩ :=
    etsp_original_plain_record hrun hmember hplain
  have hgroupGet : cg.nodes.getD v default = node := by
    simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframeGroup : (cg.nodes.getD v default).border = -2 := by
    rw [hgroupGet]
    exact hgroup
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := etsp_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpath0⟩ := etsp_groupPath execution hgroup0 (hbG.trans hgroup)
  have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    rw [← hpG, hpath0, ← hdeclG, hdG]
  have hleftPath : (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, v)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD v default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hgroupGet]
    exact hgroupPath
  have hleftContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal) (Or.inl rfl) hleftPath
  have hmemberGet : cg.nodes.getD w default = member := by
    simp only [cg, List.getD_eq_getElem?_getD, hmember, Option.getD_some]
  have hmemberFrame : frameRect execution.params cg run w =
      Labels.rectAt run.proper run.xs run.ys w := by
    unfold frameRect
    rw [hmemberGet]
    simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
    unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
      RouteImpl.nodeW RouteImpl.nodeH
    simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
  rw [hmemberFrame]
  exact Int.lt_of_le_of_lt hleftContained.1 hlt

/-- A candidate group node's own cluster path contains its declaration
(prefixed copy of the path half of the caption top/bottom path lemmas). -/
private theorem etsp_group_self_mem {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hgroup : node.border = -2) :
    node.clusterPath.contains node.decl = true := by
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := etsp_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpath0⟩ := etsp_groupPath execution hgroup0 (hbG.trans hgroup)
  have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    rw [← hpG, hpath0, ← hdeclG, hdG]
  simp [hgroupPath]

/-- Exact group side markers at the group-top rank (member-free width source). -/
private theorem etsp_side_at_top {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hgroup : node.border = -2) :
    ∃ left right : Nat,
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, v) execution.params.clusterBorderW) ∧
      run.proper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, v) execution.params.clusterBorderW) := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hgroup
  obtain ⟨original, horiginal, _, _, _, hsourceFind⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq hk hrecords hnode
      hgroup hbottom
  obtain ⟨rr2, _, hrr2, _, _, _, hranks2, hlt⟩ :=
    X_group_top_lt_bottom execution.graph0_eq execution.graph_eq hcomp hrun
  have heq : rr2 = rr := Except.ok.inj (hrr2.symm.trans hrr)
  have hltRR := hlt v node (original, bottom.2) hnode hgroup hsourceFind
  rw [heq] at hltRR
  have htopT := etsp_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hnode).1
  have hbotT := etsp_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp horiginal).1
  have htopBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hbottomForTop :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨node, false, none, false⟩).node.clusterPath) =
        some bottom := by
    simpa [titleF, hgroup] using hbottom
  obtain ⟨left, right, hleft, hright, _, _⟩ :=
    etsp_coordinate_rank_pair execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) htopBorder hbottomForTop
      (rank := (rk (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)).rank
        v).toNat)
      (Nat.le_refl _)
      (by
        dsimp only at htopT hbotT hltRR ⊢
        omega)
  rw [hc] at hleft hright
  obtain ⟨hleftFinal, _⟩ := etsp_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, _⟩ := etsp_border_record hrun hright (Or.inr rfl)
  exact ⟨left, right, hleftFinal, hrightFinal⟩

/-- Exact group frames have positive width: a side marker rect at the group-top
rank is contained in the group frame and carries the full border width. -/
private theorem etsp_frame_width_pos {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hgroup : node.border = -2) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w := by
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨left, right, hleftFinal, hrightFinal⟩ :=
    etsp_side_at_top execution hcomp hrun hnode hgroup
  have hgroupGet : cg.nodes.getD v default = node := by
    simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframeGroup : (cg.nodes.getD v default).border = -2 := by
    rw [hgroupGet]
    exact hgroup
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := etsp_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpath0⟩ := etsp_groupPath execution hgroup0 (hbG.trans hgroup)
  have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    rw [← hpG, hpath0, ← hdeclG, hdG]
  have hrightPath : (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, v)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD v default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hgroupGet]
    exact hgroupPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal) (Or.inr rfl) hrightPath
  have hrectW : (Labels.rectAt run.proper run.xs run.ys right).w =
      execution.params.clusterBorderW := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeW, hrightFinal,
      OrderImpl.borderRight]
  have hrectW_pair : (Labels.rectAt run.proper run.xs run.ys
      (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, v)
        execution.params.clusterBorderW, right).snd).w =
      execution.params.clusterBorderW := hrectW
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have h1 := hrightContained.1
  have h2 := hrightContained.2.1
  show 0 < (frameRect execution.params cg run v).w
  omega

/-- Exact pre-reserve coordinates: unfold one `componentRunX` to expose the
rank-axis output (prefixed copy). -/
private theorem etsp_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (y_pre top_pre ys_pre : List Int),
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
      proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
      reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
        .ok (run.ys, run.top) ∧
      run.coordinateYs = y_pre := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨routed, hprojection, h⟩ := bind_ok h
  obtain ⟨lanes, hr, h⟩ := bind_ok h
  obtain ⟨yt, hy, h⟩ := bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  cases yt with
  | mk y top =>
    exact ⟨y, top, _, hy, rfl, hres, rfl⟩

private theorem etsp_foldl_preserves (step : List Int → (Node × Nat) → List Int)
    (topLen : Nat)
    (hstep : ∀ acc q, acc.length = topLen → (∀ i, 0 ≤ acc.getD i 0) →
      (step acc q).length = topLen ∧ ∀ i, 0 ≤ (step acc q).getD i 0)
    (xs : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = topLen) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (xs.foldl step acc).length = topLen ∧
      ∀ i, 0 ≤ (xs.foldl step acc).getD i 0 := by
  induction xs generalizing acc with
  | nil => exact ⟨hlen, hpos⟩
  | cons q xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hlen', hpos'⟩ := hstep acc q hlen hpos
    exact ih _ hlen' hpos'

private theorem etsp_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
    (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (acc.set m (max (acc.getD m 0) needed)).length = acc.length ∧
      ∀ i, 0 ≤ (acc.set m (max (acc.getD m 0) needed)).getD i 0 := by
  refine ⟨List.length_set, ?_⟩
  intro i
  have hset : (acc.set m (max (acc.getD m 0) needed))[i]? =
      if m = i then if m < acc.length then some (max (acc.getD m 0) needed) else none
      else acc[i]? :=
    List.getElem?_set
  rw [List.getD_eq_getElem?_getD, hset]
  by_cases heq : m = i
  · subst heq
    by_cases hlt : m < acc.length
    · have h0 : 0 ≤ acc[m] := by
        have h := hpos m
        simpa [hlt] using h
      simp [hlt]
      exact Int.le_trans h0 (Int.le_max_left _ _)
    · simp [hlt]
  · have hne : m ≠ i := heq
    simp [hne]
    exact hpos i

private theorem etsp_extra_step_concrete (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    (acc : List Int) (q : Node × Nat)
    (hlen : acc.length = top.length) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
            Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 -
            heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
              Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
              top.getD ((p.rank.getD q.2 0).toNat) 0 -
              heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
  by_cases h1 : (!exact.contains q.1.decl) = true
  · rw [ite_eq_left h1]
    exact ⟨hlen, hpos⟩
  · rw [ite_eq_right h1]
    by_cases h2 : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
    · rw [ite_eq_left h2]
      exact ⟨hlen, hpos⟩
    · rw [ite_eq_right h2]
      obtain ⟨hlen', hpos'⟩ := etsp_extra_step_preserves acc _ _ hpos
      exact ⟨hlen'.trans hlen, hpos'⟩

private theorem etsp_extra_fold (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
    let extra := cg.nodes.zipIdx.foldl (fun (acc : List Int) (q : Node × Nat) =>
      if !exact.contains q.1.decl then acc
      else
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        if sizes.isEmpty then acc
        else
          let rank := (p.rank.getD q.2 0).toNat
          let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
          let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
            heights.getD rank 0
          acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))
    extra.length = top.length ∧ ∀ i, 0 ≤ extra.getD i 0 := by
  have hbase : (List.replicate top.length (0 : Int)).length = top.length := by simp
  have hbasePos : ∀ i, 0 ≤ (List.replicate top.length (0 : Int)).getD i 0 := by
    intro i
    by_cases h : i < top.length
    · have hg : (List.replicate top.length (0 : Int))[i]? = some 0 := by
        rw [List.getElem?_eq_getElem (by simpa using h)]
        simp
      rw [List.getD_eq_getElem?_getD, hg]
      simp
    · have hg : (List.replicate top.length (0 : Int))[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt h)
      rw [List.getD_eq_getElem?_getD, hg]
      simp
  have hstep : ∀ (acc : List Int) (q : Node × Nat), acc.length = top.length →
    (∀ i, 0 ≤ acc.getD i 0) →
      (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
            Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
            top.getD ((p.rank.getD q.2 0).toNat) 0 -
            heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
              Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
              top.getD ((p.rank.getD q.2 0).toNat) 0 -
              heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
    intro acc q hlen hpos
    exact etsp_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
  have h := etsp_foldl_preserves (fun (acc : List Int) (q : Node × Nat) =>
    if !exact.contains q.1.decl then acc
    else
      let sizes := loopSizes cg.edges labels q.2 cg.slot
      if sizes.isEmpty then acc
      else
        let rank := (p.rank.getD q.2 0).toNat
        let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
        let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
          heights.getD rank 0
        acc.set rank (max (acc.getD rank 0) needed)) top.length hstep
    cg.nodes.zipIdx (List.replicate top.length (0 : Int)) hbase hbasePos
  exact h

private theorem etsp_prefix_length (es : List Int) (s : Int) (out : List Int) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
      out.length + es.length := by
  induction es generalizing s out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

private theorem etsp_prefix_pairwise (es : List Int) (hpos : ∀ e ∈ es, 0 ≤ e)
    (s : Int) (out : List Int)
    (hm : out.Pairwise (· ≤ ·)) (hle : ∀ x ∈ out, x ≤ s) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).Pairwise
      (· ≤ ·) := by
  induction es generalizing s out with
  | nil => simpa
  | cons e es ih =>
    have he : 0 ≤ e := hpos e List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih
    · intro e' he'
      exact hpos e' (List.mem_cons_of_mem e he')
    · apply List.pairwise_append.mpr
      refine ⟨hm, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      rw [hy]
      exact hle x hx
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := hle x hx
        omega
      · omega

private theorem etsp_pairwise_getD_le {l : List Int} (hp : l.Pairwise (· ≤ ·))
    {i j : Nat} (hij : i < j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := by omega
  have hgi : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  have hgj : l[j]? = some l[j] := List.getElem?_eq_getElem hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hgi, hgj]
  simp only [Option.getD_some]
  exact hp.rel_getElem_of_lt hi hj hij

/-- Strict shift transfer for tops only: a strict pre-reserve gap survives
nondecreasing shifts (prefixed copy). -/
private theorem etsp_shift_strict_tops {p : Proper} {layers : List (List Nat)}
    {top : List Int} {extra shifts : List Int} {top' : List Int}
    (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top.getD r' 0)
    (hextraLen : extra.length = top.length)
    (hpos : ∀ e ∈ extra, 0 ≤ e)
    (hshifts : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (htopLen : top.length = layers.length)
    (htop : ∀ (r : Nat), r < top.length → top'.getD r 0 =
      top.getD r 0 + shifts.getD r 0) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top'.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top'.getD r' 0 := by
  have hshiftsLen : shifts.length = top.length := by
    rw [hshifts, etsp_prefix_length]
    simp [hextraLen]
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hshifts]
    exact etsp_prefix_pairwise extra hpos 0 [] (by simp) (by simp)
  have hmono : ∀ i j, i < j → j < shifts.length →
      shifts.getD i 0 ≤ shifts.getD j 0 :=
    fun i j hij hj => etsp_pairwise_getD_le hpair hij hj
  intro r r' l l' hlt hly hly'
  have hrTop : r < top.length := by
    rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
  have hrTop' : r' < top.length := by
    rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly').1
  have hrShift' : r' < shifts.length := by rw [hshiftsLen]; exact hrTop'
  have e1 := htop r hrTop
  have hle := hmono r r' hlt hrShift'
  have e1' := htop r' hrTop'
  have hd := hdisj r r' l l' hlt hly hly'
  rw [e1, e1']
  omega

/-- Post-reserve top equation (prefixed copy). -/
private theorem etsp_top_eq {inp : Input} {exactIds : List String}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {top_pre ys_pre : List Int}
    (hreserve : reserveExactRanks cg (exactDecls exactIds inp) labels run.coordinateProper
      run.layers ys_pre top_pre = .ok (run.ys, run.top)) :
    ∀ (r : Nat), r < top_pre.length → run.top.getD r 0 =
      top_pre.getD r 0 +
        ((cg.nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes cg.edges labels q.2 cg.slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 := by
  intro r hr
  have hrZ : r < (top_pre.zipIdx).length := by
    rw [List.length_zipIdx]
    exact hr
  have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
    have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
    simp [List.getElem?_zipIdx, h1]
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htopM, h1⟩ := bind_ok hreserve
  obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
  have hpair := Except.ok.inj h2
  have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
  rw [htopNew_eq] at htopM
  obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
  obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
  have hbeq : b = top_pre[r] +
      ((cg.nodes.zipIdx.foldl
        (fun (acc : List Int) (q : Node × Nat) =>
          if !(exactDecls exactIds inp).contains q.1.decl then acc
          else
            let sizes := loopSizes cg.edges labels q.2 cg.slot
            if sizes.isEmpty then acc
            else
              let rank := (run.coordinateProper.rank.getD q.2 0).toNat
              let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
              let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
              acc.set rank (max (acc.getD rank 0) needed))
        (List.replicate top_pre.length (0 : Int))).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 :=
    Measure.checkedI32_ok hb
  have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
  have e3 : top_pre.getD r 0 = top_pre[r] := by
    rw [List.getD_eq_getElem?_getD, h1]
    rfl
  have e4 : run.top.getD r 0 = b := by
    rw [List.getD_eq_getElem?_getD, hbr]
    rfl
  rw [e4, e3]
  exact hbeq

/-- Post-reserve strict band tops (prefixed copy). -/
private theorem etsp_post_strict_gap {P : Params} {exactIds : List String} {inp : Input}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        run.top.getD r' 0 := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := etsp_run_pre hrun
  have hdisjPre : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      top_pre.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        top_pre.getD r' 0 :=
    fun r r' l l' hlt hly hly' => rankAxis_band_top_strict hry r r' l l' hlt hly hly'
  have hextra := etsp_extra_fold cg (exactDecls exactIds inp) labels run.coordinateProper
    ys_pre top_pre
    (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
  have hposM : ∀ e ∈ cg.nodes.zipIdx.foldl
      (fun (acc : List Int) (q : Node × Nat) =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes cg.edges labels q.2 cg.slot
          if sizes.isEmpty then acc
          else
            let rank := (run.coordinateProper.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
            let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
              (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed))
      (List.replicate top_pre.length (0 : Int)), 0 ≤ e := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    have h := hextra.2 i
    rw [List.getD_eq_getElem?_getD, hi] at h
    simp at h
    exact h
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  exact etsp_shift_strict_tops hdisjPre hextra.1 hposM rfl htopLen
    (etsp_top_eq hreserve)

/-- Proxy-interval record transfer for `±2` markers (prefixed copy). -/
private theorem etsp_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
      run.proper.nodes[index]? =
        some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf run.proper run.xs index = span.lo ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = q0.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

/-- Bottom marker coordinate record (prefixed copy). -/
private theorem etsp_bottom_coordinate {P : Params} {exact : List Nat} {cg : Graph}
    {labeled : Proper} {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hrec : ∀ (index : Nat) (node : Node),
      cg.nodes[index]? = some node → labeled.nodes[index]? = some ⟨node, false, none, false⟩)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  have hrec := hrec v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact) hrec (Or.inr hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))

/-- Bottom marker proper record with zero height (prefixed copy). -/
private theorem etsp_bottom_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      p.node.border = coord.node.border ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _, _⟩ :=
    etsp_proxy_interval hrun hcoord (Or.inr hb)
  refine ⟨_, hproper, rfl, rfl, ?_⟩
  simp only [RouteImpl.nodeH, hproper]
  exact hcoordH
 /-- Top marker coordinate record (prefixed copy of the bottom half). -/
 private theorem etsp_top_coordinate {P : Params} {exact : List Nat} {cg : Graph}
     {labeled : Proper} {run : Run}
     (hc : coordinateGraphX P exact labeled = run.coordinateProper)
     (hrec : ∀ (index : Nat) (node : Node),
       cg.nodes[index]? = some node → labeled.nodes[index]? = some ⟨node, false, none, false⟩)
     {v : Nat} {nd : Node}
     (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = -2) :
     ∃ coord : ProperNode,
       run.coordinateProper.nodes[v]? = some coord ∧
       coord.node.border = -2 ∧ coord.dummy = false ∧
       coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
   have hrec := hrec v nd hnode
   have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact) hrec (Or.inl hgroup) rfl
   rw [hc] at hmarker
   refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
   · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
     rw [hb, (titleF_keys _).2.1]
     exact hgroup
   · exact (clearF_keys _).1.trans (titleF_keys _).1
   · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
   · exact (clearF_keys _).2.2.2.trans
       ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inl hgroup))

 /-- Top marker proper record with zero height (prefixed copy of the bottom half). -/
 private theorem etsp_top_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {v : Nat} {coord : ProperNode}
     (hcoord : run.coordinateProper.nodes[v]? = some coord)
     (hb : coord.node.border = -2) (hcoordH : coord.node.h = 0) :
     ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
       p.node.clusterPath = coord.node.clusterPath ∧
       p.node.border = coord.node.border ∧
       RouteImpl.nodeH run.proper v = 0 := by
   obtain ⟨owner, span, _, _, hproper, _, _, _⟩ :=
     etsp_proxy_interval hrun hcoord (Or.inl hb)
   refine ⟨_, hproper, rfl, rfl, ?_⟩
   simp only [RouteImpl.nodeH, hproper]
   exact hcoordH

 /-- Exact group frames have positive height: top and bottom markers at
 strictly separated ranks force the member-hull vertical span positive. -/
 private theorem etsp_frame_height_pos {exactIds : List String} {inp : Input}
     {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRunX execution.params (exactDecls exactIds inp)
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run) {v : Nat} {node : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
     (hgroup : node.border = -2) :
     0 < (frameRect execution.params
       (componentCandidate execution.graph comp candidate) run v).h := by
   let cg := componentCandidate execution.graph comp candidate
   obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
     X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hnode hgroup
   obtain ⟨originalBottom, horiginalBottom, hborderBottom, hpathBottom, hrecordBottom,
       hsourceFind⟩ :=
     X_bottom_constraint_source execution.graph0_eq execution.graph_eq hk hrecords hnode
       hgroup hbottom
   obtain ⟨rr2, _, hrr2, _, _, _, _, hlt⟩ :=
     X_group_top_lt_bottom execution.graph0_eq execution.graph_eq hcomp hrun
   have heq : rr2 = rr := Except.ok.inj (hrr2.symm.trans hrr)
   have hltRR := hlt v node (originalBottom, bottom.2) hnode hgroup hsourceFind
   rw [heq] at hltRR
   have hvLen : v < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnode).1
   have hbLen : bottom.2 < cg.nodes.length :=
     (List.getElem?_eq_some_iff.mp horiginalBottom).1
   have htopC : rk run.coordinateProper.rank v = rk rr.ranks v := by
     have h := etsp_coordinate_original_rk (P := execution.params)
       (exact := exactDecls exactIds inp) hrr hranks hvLen
     rwa [hc] at h
   have hbotC : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
     have h := etsp_coordinate_original_rk (P := execution.params)
       (exact := exactDecls exactIds inp) hrr hranks hbLen
     rwa [hc] at h
   obtain ⟨tcoord, htcoord, htb, htdummy, htpath, hth⟩ :=
     etsp_top_coordinate (P := execution.params) (exact := exactDecls exactIds inp)
       hc hrecords hnode hgroup
   obtain ⟨bcoord, hbcoord, hbb, hbdummy, hbpath, hbh⟩ :=
     etsp_bottom_coordinate (P := execution.params) (exact := exactDecls exactIds inp)
       hc hrecords horiginalBottom hborderBottom
   obtain ⟨tprop, htprop, htpropPath, htpropBorder, htpropH⟩ :=
     etsp_top_proper hrun htcoord htb hth
   obtain ⟨bprop, hbprop, hbpropPath, hbpropBorder, hbpropH⟩ :=
     etsp_bottom_proper hrun hbcoord hbb hbh
   have htpropH' : tprop.node.h = 0 := by
     have h : RouteImpl.nodeH run.proper v = tprop.node.h := by
       simp only [RouteImpl.nodeH, htprop]
     rw [h] at htpropH
     exact htpropH
   have hbpropH' : bprop.node.h = 0 := by
     have h : RouteImpl.nodeH run.proper bottom.2 = bprop.node.h := by
       simp only [RouteImpl.nodeH, hbprop]
     rw [h] at hbpropH
     exact hbpropH
   have hrecTop : ∃ cw : ProperNode, run.coordinateProper.nodes[v]? = some cw ∧
       cw.node.border = tprop.node.border ∧ cw.node.h = tprop.node.h :=
     ⟨tcoord, htcoord, by rw [htpropBorder], by rw [hth, htpropH']⟩
   have hrecBot : ∃ cw : ProperNode, run.coordinateProper.nodes[bottom.2]? = some cw ∧
       cw.node.border = bprop.node.border ∧ cw.node.h = bprop.node.h :=
     ⟨bcoord, hbcoord, by rw [hbpropBorder], by rw [hbh, hbpropH']⟩
   obtain ⟨lTop, hlyTop, hbandTopLo, hbandTopHi⟩ :=
     componentRunX_node_band hrun htprop hrecTop
   obtain ⟨lBot, hlyBot, hbandBotLo, _⟩ :=
     componentRunX_node_band hrun hbprop hrecBot
   have hnnT := rankWithBudget_rk_nonneg hrr v
   have hnnB := rankWithBudget_rk_nonneg hrr bottom.2
   have hltRR' : rk rr.ranks v + 1 ≤ rk rr.ranks bottom.2 := hltRR
   have hltNat : (rk run.coordinateProper.rank v).toNat <
       (rk run.coordinateProper.rank bottom.2).toNat := by omega
   have hgap := etsp_post_strict_gap hrun _ _ lTop lBot hltNat hlyTop hlyBot
   have hgroupGet : cg.nodes.getD v default = node := by
     simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
   have hframeGroup : (cg.nodes.getD v default).border = -2 := by
     rw [hgroupGet]
     exact hgroup
   have hself : node.clusterPath.contains node.decl = true :=
     etsp_group_self_mem execution hnode hgroup
   have hmemTop : tprop.node.clusterPath.contains (cg.nodes.getD v default).decl = true := by
     rw [hgroupGet, htpropPath, htpath]
     exact hself
   have hmemBot : bprop.node.clusterPath.contains (cg.nodes.getD v default).decl = true := by
     rw [hgroupGet, hbpropPath, hbpath, hpathBottom]
     exact hself
   have htopVert := frameRect_member_vertical (P := execution.params) (cg := cg)
     (run := run) (i := v) (q := (tprop, v)) hframeGroup
     (List.mk_mem_zipIdx_iff_getElem?.mpr htprop) hmemTop
   have hbotVert := frameRect_member_vertical (P := execution.params) (cg := cg)
     (run := run) (i := v) (q := (bprop, bottom.2)) hframeGroup
     (List.mk_mem_zipIdx_iff_getElem?.mpr hbprop) hmemBot
   have hyTop : (Labels.rectAt run.proper run.xs run.ys v).y = run.ys.getD v 0 := by
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
   have hhTop : (Labels.rectAt run.proper run.xs run.ys v).h =
       RouteImpl.nodeH run.proper v := by
     simp only [Labels.rectAt, Labels.labelRect]
   have hyBot : (Labels.rectAt run.proper run.xs run.ys bottom.2).y =
       run.ys.getD bottom.2 0 := by
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
   have hhBot : (Labels.rectAt run.proper run.xs run.ys bottom.2).h =
       RouteImpl.nodeH run.proper bottom.2 := by
     simp only [Labels.rectAt, Labels.labelRect]
   have hyTop_pair : (Labels.rectAt run.proper run.xs run.ys (tprop, v).snd).y =
       run.ys.getD v 0 := hyTop
   have hhTop_pair : (Labels.rectAt run.proper run.xs run.ys (tprop, v).snd).h =
       RouteImpl.nodeH run.proper v := hhTop
   have hyBot_pair : (Labels.rectAt run.proper run.xs run.ys (bprop, bottom.2).snd).y =
       run.ys.getD bottom.2 0 := hyBot
   have hhBot_pair : (Labels.rectAt run.proper run.xs run.ys (bprop, bottom.2).snd).h =
       RouteImpl.nodeH run.proper bottom.2 := hhBot
   show 0 < (frameRect execution.params cg run v).h
   omega

 /-- Group positivity for the skeleton: width via side markers, height via
 top/bottom marker separation. -/
 private theorem etsp_hPos (exactIds : List String) :
     ∀ {inp : Input} {o : Options} {res : FamilyResult}
       (execution : SceneExecutionX exactIds inp o res)
       (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
       {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
       {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
       componentRunX execution.params (exactDecls exactIds inp)
         (componentCandidate execution.graph comp candidate) execution.measured
         orderOptions = .ok run →
       ∀ {v : Nat} {node : Node},
         (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
         node.border = -2 →
         0 < (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).w ∧
           0 < (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).h := by
   intro inp o res execution _hwf _hfp comp hcomp candidate run orderOptions hrun
   intro v node hnode hgroup
   exact ⟨etsp_frame_width_pos execution hcomp hrun hnode hgroup,
     etsp_frame_height_pos execution hcomp hrun hnode hgroup⟩


/-- Skeleton: same-part from member strict-left plus outsider disjointness and
group positivity (the latter two to be folded into the single residual). -/
private theorem etsp_samePart_skel
    (exactIds : List String)
    (hLeft : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        orderOptions = .ok run →
      ∀ {v w : Nat} {node member : Node},
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
        node.border = -2 →
        (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
        member.border = 0 →
        member.clusterPath.contains node.decl = true →
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).x <
          (frameRect execution.params (componentCandidate execution.graph comp candidate) run w).x)
    (hDisj : XLrr_TopOutsideDisjointW exactIds)
    (hPos : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        orderOptions = .ok run →
      ∀ {v : Nat} {node : Node},
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
        node.border = -2 →
        0 < (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).w ∧
          0 < (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).h) :
    XL_TopSamePartW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro v w node member hnode hgroup hmember hplain hframe
  by_cases hinside : member.clusterPath.contains node.decl = true
  · have hlt := hLeft execution hwf hfp (comp := comp) hcomp
      (candidate := candidate) (run := run) (orderOptions := orderOptions)
      hrun (v := v) (w := w) hnode hgroup hmember hplain hinside
    rw [hframe] at hlt
    exact absurd hlt (Int.lt_irrefl _)
  · have hdis := hDisj execution hwf hfp (comp := comp) hcomp
      (candidate := candidate) (run := run) (orderOptions := orderOptions)
      hrun (v := v) (w := w) hnode hgroup hmember hplain hinside
    have hpos := hPos execution hwf hfp (comp := comp) hcomp
      (candidate := candidate) (run := run) (orderOptions := orderOptions)
      hrun (v := v) hnode hgroup
    have hposW : 0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).w ∧
        0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run w).h := by
      rw [hframe]
      exact hpos
    exact loopRect_frameNe_of_disjoint hdis hframe hposW.1 hposW.2

 /-- Closed same-part: the group-top frame and a plain frame in the same
 component are never equal, modulo outsider disjointness. -/
 theorem XL_topSamePartW_closed (exactIds : List String)
     (hDisj : XLrr_TopOutsideDisjointW exactIds) : XL_TopSamePartW exactIds :=
   etsp_samePart_skel exactIds (etsp_hLeft exactIds) hDisj (etsp_hPos exactIds)

end PipelineImpl
end Layered
end Elegant
