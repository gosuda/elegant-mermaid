import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.ExactFlatC5Bottom
import Elegant.Layered.ExactReservedRouteCoordsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem exactSideMarkerPath {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {index owner : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some owner) :
    ∃ box : ModelBox, inp.boxes[owner]? = some box ∧
      OrderImpl.nodePath run.coordinateProper index = Compound.path inp.boxes box ++ [owner] := by
  obtain ⟨_, labeled, _, hcoord, hkeys, hready, hrecords, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hs : (coordinateGraphX execution.params (exactDecls exactIds inp) labeled).nodes[index]? =
      some side := by
    rw [hcoord]
    exact hside
  have hlook := X_side_original hready hs hborder
  obtain ⟨anchor, hanchor, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hlook) hborder
  obtain ⟨hzip, hmark⟩ := List.mem_filter.mp hanchor
  have hb : anchor.1.node.border = -2 := by simpa using hmark
  obtain ⟨node, hnode, hnodeBorder, hnodeRecord⟩ :=
    X_titled_marker_source_record hkeys hrecords (List.mem_zipIdx_iff_getElem?.mp hzip) (Or.inl hb)
  obtain ⟨box, hbox, hboxPath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq
    hnode (hnodeBorder.symm.trans hb)
  have hcpath := hpath.trans ((congrArg (fun nd : ProperNode => nd.node.clusterPath) hnodeRecord).trans
    ((titleF_keys ⟨node, false, none, false⟩).2.2.1.trans hboxPath))
  have heq : node.decl = owner := by
    rw [hcpath] at howner
    simpa [List.getLast?_append] using howner
  have hwell : OrderImpl.BordersWellFormed run.coordinateProper := by
    rw [← hcoord]
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hd : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
      have hz := hwell.2.2 index side hside hd
      rcases hborder with h | h <;> omega
  rw [heq] at hbox hcpath
  exact ⟨box, hbox, (OrderImpl.nodePath_of_nondummy hside hd).trans hcpath⟩

/-- The inclusive interval between two executed same-owner side markers stays
inside the owner's ordering scope. In particular, this applies to dummies. -/
theorem sceneExecutionX_sideBracket_prefix {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j k left v right owner : Nat} {lnode rnode : ProperNode}
    (hi : layer[i]? = some left) (hj : layer[j]? = some v) (hk : layer[k]? = some right)
    (hl : run.coordinateProper.nodes[left]? = some lnode)
    (hr : run.coordinateProper.nodes[right]? = some rnode)
    (hlb : lnode.node.border = -1 ∨ lnode.node.border = 1)
    (hrb : rnode.node.border = -1 ∨ rnode.node.border = 1)
    (hlo : lnode.node.clusterPath.getLast? = some owner)
    (hro : rnode.node.clusterPath.getLast? = some owner)
    (hij : i ≤ j) (hjk : j ≤ k) :
    ∃ box : ModelBox, inp.boxes[owner]? = some box ∧
      Compound.path inp.boxes box ++ [owner] <+: OrderImpl.nodePath run.coordinateProper v := by
  obtain ⟨box, hbox, hleft⟩ := exactSideMarkerPath execution hcomp hrun hl hlb hlo
  obtain ⟨other, hother, hright⟩ := exactSideMarkerPath execution hcomp hrun hr hrb hro
  have hs : other = box := Option.some.inj (hother.symm.trans hbox)
  subst other
  refine ⟨box, hbox, ?_⟩
  by_cases hil : i = j
  · rw [← hil] at hj
    rw [← Option.some.inj (hi.symm.trans hj), hleft]
    exact List.prefix_rfl
  by_cases hir : j = k
  · rw [hir] at hj
    rw [Option.some.inj (hj.symm.trans hk), hright]
    exact List.prefix_rfl
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have ho : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  have hd : layer.Nodup := OrderImpl.layering_mem_nodup
    (OrderImpl.orderWithBudget_spec _ _ _ horder).1 (hlayers.symm ▸ hlayer)
  let path := Compound.path inp.boxes box ++ [owner]
  let segment := layer.filter (fun index => path.isPrefixOf (OrderImpl.nodePath run.coordinateProper index))
  have hsegment : segment.IsInfix layer :=
    OrderImpl.order_clusters_contiguous _ _ _ ho layer hlayer path
  have hleftMem : left ∈ segment := List.mem_filter.mpr
    ⟨List.mem_of_getElem? hi, by rw [hleft]; exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl⟩
  have hrightMem : right ∈ segment := List.mem_filter.mpr
    ⟨List.mem_of_getElem? hk, by rw [hright]; exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl⟩
  have hv := mem_of_between_infix hd hsegment hleftMem hrightMem hi hj hk (by omega) (by omega)
  exact List.isPrefixOf_iff_prefix.mp (List.mem_filter.mp hv).2

private theorem sizeFloor (nodes : List ProperNode) (seed : Int) :
    let bound := nodes.foldl (fun w nd => min w nd.node.w) seed
    bound ≤ seed ∧ ∀ nd ∈ nodes, bound ≤ nd.node.w := by
  induction nodes generalizing seed with
  | nil => simp
  | cons nd rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨hle, hall⟩ := ih (min seed nd.node.w)
    refine ⟨Int.le_trans hle (Int.min_le_left _ _), ?_⟩
    intro other hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Int.le_trans hle (Int.min_le_right _ _)
    · exact hall other hm

private theorem exactSizedCoordinate {P : Params} {exact : List Nat} {source : Proper} :
    ∃ params : Params, sizeProperPorts params (sizeProperPortsX P exact source) =
      sizeProperPortsX P exact source ∧
      coordinateGraph params (sizeProperPortsX P exact source) = coordinateGraphX P exact source := by
  let sized := sizeProperPortsX P exact source
  let params : Params := { P with portGap := sized.nodes.foldl (fun w nd => min w nd.node.w) 0 }
  obtain ⟨hport, hwidth⟩ := sizeFloor sized.nodes 0
  have hnodes : (sizeProperPorts params sized).nodes = sized.nodes := by
    apply List.ext_getElem?
    intro i
    cases hi : sized.nodes[i]? with
    | none => simp [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hi]
    | some nd =>
      have hmax (degree : Nat) :
          max nd.node.w (((degree + 1 : Nat) : Int) * params.portGap) = nd.node.w := by
        apply Int.max_eq_left
        have hm := Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg degree) hport
        have hw := hwidth nd (List.mem_of_getElem? hi)
        change (((degree + 1 : Nat) : Int) * (sized.nodes.foldl
          (fun w nd => min w nd.node.w) 0)) ≤ nd.node.w
        rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
        omega
      simp only [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hi,
        Option.map_some, Nat.zero_add]
      split
      · rfl
      · simp only [hmax]
  have hsized : sizeProperPorts params sized = sized :=
    congrArg (fun nodes => { sized with nodes := nodes }) hnodes
  refine ⟨params, hsized, ?_⟩
  change materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts params sized)) P.clusterBorderW)) =
    materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations sized) P.clusterBorderW))
  rw [hsized]

private theorem sizedKeys {cg : Graph} {source : Proper} (P : Params) (exact : List Nat)
    (hkeys : NodeKeys cg source) : NodeKeys cg (sizeProperPortsX P exact source) := by
  intro v nd hnd
  obtain ⟨orig, ho, hd, hb, hp⟩ := X_sizeProperPorts_node_origin P exact source hnd
  rcases hkeys v orig ho with ⟨node, hnode, hd', hb', hp'⟩ | ⟨hd', hb', hp'⟩
  · exact Or.inl ⟨node, hnode, hd.trans hd', hb.trans hb', hp.trans hp'⟩
  · exact Or.inr ⟨hd.trans hd', hb.trans hb', hp.trans hp'⟩

private theorem coordinatePath_of_source {P : Params} {p : Proper} {index : Nat}
    {nd : ProperNode} (hsize : sizeProperPorts P p = p)
    (hnode : p.nodes[index]? = some nd) (hreal : nd.dummy = false) :
    ((coordinateGraph P p).nodes.getD index default).node.clusterPath = nd.node.clusterPath := by
  let titled := titleReservations p
  have hlook : titled.nodes[index]? = some (titleF nd) := by
    rw [titleReservations_nodes, List.getElem?_append_left (by
      rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hnode).1)]
    simp only [List.getElem?_map, hnode, Option.map_some]
  obtain ⟨extra, hextra, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hbordered : (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[index]? =
      some (titleF nd) := by
    rw [hextra, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlook).1]
    exact hlook
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[index]? =
      some (clearF (titleF nd)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hbordered]
    rfl
  have hd := (clearF_keys (titleF nd)).1.trans ((titleF_keys nd).1.trans hreal)
  have hm : (coordinateGraph P p).nodes[index]? = some (clearF (titleF nd)) := by
    unfold coordinateGraph
    rw [hsize]
    change (materializeDummyPaths
      (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW))).nodes[index]? =
      some (clearF (titleF nd))
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hclear,
      Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, hm, Option.getD_some,
    (clearF_keys (titleF nd)).2.2.1, (titleF_keys nd).2.2.1]

private theorem rankAt_coordinate_source {P : Params} {source : Proper}
    {index : Nat} (hi : index < source.rank.length) :
    rk (coordinateGraph P source).rank index = rk source.rank index := by
  have hs : source.rank[index]? = some source.rank[index] := List.getElem?_eq_getElem hi
  have hc := coordinateGraph_rank_record (P := P) hs
  simp only [rk, List.getD_eq_getElem?_getD, hs, hc, Option.getD_some]

private theorem linesCoverBoxes {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  exact (mapM_getElem? _ _ _ h).1.trans (List.length_zipIdx ..)

set_option maxHeartbeats 1000000 in
private theorem originalMemberRankBound {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t g : Nat} {bottom top : Node}
    (ht : (componentCandidate execution.graph comp candidate).nodes[t]? = some bottom)
    (hbot : bottom.border = 2)
    (hg : (componentCandidate execution.graph comp candidate).nodes[g]? = some top)
    (htop : top.border = -2) (hdecl : bottom.decl = top.decl)
    {v : Nat} {node : Node}
    (hv : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (howner : node.clusterPath.contains top.decl = true) :
    rk run.coordinateProper.rank v ≤ rk run.coordinateProper.rank t ∧
      (node.border ≠ 2 → rk run.coordinateProper.rank v < rk run.coordinateProper.rank t) := by
  let cg := componentCandidate execution.graph comp candidate
  have h0 := execution.graph0_eq
  have he := execution.graph_eq
  have hl := linesCoverBoxes execution
  obtain ⟨rr, src, hrr, hc, _, _, _, hranks, _⟩ := X_cg_run_bundle h0 he hcomp hrun
  change rankWithBudget (Compound.rankingGraph cg) = .ok rr at hrr
  obtain ⟨params, _, hcoord⟩ := exactSizedCoordinate
    (P := execution.params) (exact := exactDecls exactIds inp) (source := src)
  have hcoordRun := hcoord.trans hc
  have hrk (i : Nat) (hi : i < cg.nodes.length) :
      rk run.coordinateProper.rank i = rk rr.ranks i := by
    obtain ⟨_, _, hinv, _⟩ := RankImpl.rank_spec
      (g := Compound.rankingGraph cg) (r := rr.ranks) (by rw [RankImpl.rank, hrr])
    have hir : i < rr.ranks.length := by rw [hinv.1]; exact hi
    have hr : rr.ranks[i]? = some rr.ranks[i] := List.getElem?_eq_getElem hir
    have hs := hranks i _ hr
    have hs' : (sizeProperPortsX execution.params (exactDecls exactIds inp) src).rank[i]? =
        some rr.ranks[i] := hs
    have hkeep := coordinateGraph_rank_record (P := params) hs'
    rw [hcoordRun] at hkeep
    simp only [rk, List.getD_eq_getElem?_getD, hr, hkeep, Option.getD_some]
  have htRank := hrk t (List.getElem?_eq_some_iff.mp ht).1
  have hvRank := hrk v (List.getElem?_eq_some_iff.mp hv).1
  have htFind : (cg.nodes.zipIdx.find? fun q =>
      q.1.border == 2 && q.1.decl == top.decl) = some (bottom, t) := by
    simpa only [hdecl] using X_bottom_find_eq h0 he hcomp ht hbot
  have outerBottomBound {j : Nat} {nd : Node}
      (hj : cg.nodes[j]? = some nd) (hb : nd.border = 2)
      (hown : nd.clusterPath.contains top.decl = true) :
      rk run.coordinateProper.rank j ≤ rk run.coordinateProper.rank t := by
    by_cases heq : nd.decl = top.decl
    · have hjFind := X_bottom_find_eq h0 he hcomp hj hb
      rw [heq] at hjFind
      have heqIdx : j = t := congrArg Prod.snd (Option.some.inj (hjFind.symm.trans htFind))
      simpa only [heqIdx] using Int.le_refl (rk run.coordinateProper.rank t)
    · exact Xb_NestedExact_holds exactIds h0 he hl hwf hframed hcomp hrun
        ht hg hbot htop hdecl hj hb heq hown
  rcases (X_componentCandidate_marker_shape h0 he hv).1 with hp | htopV | hbotV
  · have hm : rk rr.ranks v + 1 ≤ rk rr.ranks t :=
      (ranked_compound_member_interval hrr (top := (top, g)) (member := (node, v))
        (List.mem_zipIdx_iff_getElem?.mpr hg) htop htFind
        (List.mem_zipIdx_iff_getElem?.mpr hv) hp howner).2
    rw [hvRank, htRank]
    have hlt : rk rr.ranks v < rk rr.ranks t := by omega
    exact ⟨Int.le_of_lt hlt, fun _ => hlt⟩
  · obtain ⟨inner, hinner⟩ := X_componentRun_cg_bottom_find h0 he hl hcomp hv htopV
    have hget : cg.nodes[inner.2]? = some inner.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hinner)
    have hinnerKeys : inner.1.border = 2 ∧ inner.1.decl = node.decl := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hinner
    obtain ⟨topBox, htopBox, htopPath⟩ := X_cg_group_box h0 he hv htopV
    obtain ⟨botBox, hbotBox, hbotPath⟩ := X_cg_bottom_box h0 he hget hinnerKeys.1
    rw [hinnerKeys.2] at hbotBox hbotPath
    have hboxEq := Option.some.inj (hbotBox.symm.trans htopBox)
    have hpath : inner.1.clusterPath = node.clusterPath := by
      rw [hbotPath, htopPath, hboxEq]
    have hle := outerBottomBound hget hinnerKeys.1 (hpath.symm ▸ howner)
    obtain ⟨rr', _, hrr', _, _, _, _, hinterval⟩ := X_group_top_lt_bottom h0 he hcomp hrun
    have hrrEq : rr' = rr := Except.ok.inj (hrr'.symm.trans hrr)
    have hlt := hinterval v node inner hv htopV hinner
    rw [hrrEq] at hlt
    have hiRank := hrk inner.2 (List.getElem?_eq_some_iff.mp hget).1
    rw [hiRank, htRank] at hle
    rw [hvRank, htRank]
    exact ⟨by omega, fun _ => by omega⟩
  · exact ⟨outerBottomBound hv hbotV howner, fun hn => (hn hbotV).elim⟩

private theorem chainRank_strict_before_last {p : Proper} {chain : List Nat}
    (hstep : ∀ (j : Nat) (hj : j < chain.length) (hj' : j + 1 < chain.length),
      rk p.rank (chain[j + 1]'hj') = rk p.rank (chain[j]'hj) + 1)
    {v last : Nat} (hv : v ∈ chain) (hlast : chain.getLast? = some last)
    (hne : v ≠ last) : rk p.rank v < rk p.rank last := by
  obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
  have hz : chain[chain.length - 1]? = some last := by
    rwa [← List.getLast?_eq_getElem?]
  obtain ⟨jbound, hlastGet⟩ := List.getElem?_eq_some_iff.mp hz
  have hlt : i < chain.length - 1 := by
    by_cases h : i < chain.length - 1
    · exact h
    · have he : i = chain.length - 1 := by omega
      subst i
      exact (hne (hvi.symm.trans hlastGet)).elim
  have hmono (j : Nat) (hj : j < chain.length) (hij : i < j) :
      rk p.rank (chain[i]'hi) < rk p.rank (chain[j]'hj) := by
    induction j with
    | zero => omega
    | succ j ih =>
      have hj' : j < chain.length := by omega
      have hs := hstep j hj' hj
      by_cases he : i = j
      · subst i
        omega
      · have hm := ih hj' (by omega)
        omega
  simpa only [hvi, hlastGet] using hmono _ jbound hlt

set_option maxHeartbeats 1200000 in
private theorem dummyRank_lt_scoped_head {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v owner : Nat} {nd : ProperNode} (hv : run.coordinateProper.nodes[v]? = some nd)
    (hd : nd.dummy = true) (howner : owner ∈ OrderImpl.nodePath run.coordinateProper v) :
    ∃ head node, cg.nodes[head]? = some node ∧ node.clusterPath.contains owner = true ∧
      rk run.coordinateProper.rank v < rk run.coordinateProper.rank head := by
  obtain ⟨rr, norm, src, _, hnorm, hlabels, hcoord, _⟩ := X_componentRun_ranked_source hrun
  let sized := sizeProperPortsX P exact src
  obtain ⟨params, hsize, hc⟩ := exactSizedCoordinate (P := P) (exact := exact) (source := src)
  have hcRun : coordinateGraph params sized = run.coordinateProper := hc.trans hcoord
  have hkeys : NodeKeys cg src := addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabels
  have hk := sizedKeys P exact hkeys
  have hnLen := (normalize_node_rank_alignment hnorm).1
  have hm := Labels.addLabelNodes_metadata hlabels
  have hv' : (coordinateGraph params sized).nodes[v]? = some nd := by
    rw [hcRun]
    exact hv
  obtain ⟨sv, hsv, hdv⟩ : ∃ n, sized.nodes[v]? = some n ∧ n.dummy = true := by
    rcases coordinateGraph_lookup params sized hv' with
      ⟨n, hn, he, _, _, _⟩ | ⟨hf, _⟩ | ⟨_, _, _, _, _, hb, _⟩
    · exact ⟨n, hn, he.symm.trans hd⟩
    · simp only [hf, Bool.false_eq_true] at hd
    · have hz := pc_plain (P := params) hk hv' hd
      omega
  have hgetV : run.coordinateProper.nodes.getD v default = nd := by
    simp only [List.getD_eq_getElem?_getD, hv, Option.getD_some]
  unfold OrderImpl.nodePath at howner
  simp only [hgetV, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at howner
  generalize hfind : run.coordinateProper.chains.find? (fun members => members.contains v) =
    selected at howner
  cases selected with
  | none => exact (List.not_mem_nil howner).elim
  | some chain =>
    have hin : v ∈ chain := List.contains_iff_mem.mp
      (List.find?_some (p := fun members : List Nat => members.contains v) hfind)
    have hchains : run.coordinateProper.chains = norm.chains := by
      rw [← hcoord, coordinateGraphX_chains, hm.2.2.1]
    have hmem := List.mem_of_find?_eq_some hfind
    rw [hchains] at hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    have hi' : i < cg.edges.length := by
      rw [← normalize_chains_length hnorm]
      exact (List.getElem?_eq_some_iff.mp hi).1
    let edge := cg.edges[i]'hi'
    have hedge : cg.edges[i]? = some edge := List.getElem?_eq_getElem hi'
    have hchain := ((normalize_ok hnorm).2.2 i hi' edge hedge).2
    change (if edge.tail = edge.head then norm.chains[i]? = some []
      else ∃ ch, norm.chains[i]? = some ch ∧ 2 ≤ ch.length ∧
        ch.head? = some edge.tail ∧ ch.getLast? = some edge.head ∧
        ∀ (j : Nat) (hj : j < ch.length) (hj' : j + 1 < ch.length),
          ∃ pe ∈ norm.edges, pe.original = i ∧ pe.decl = edge.decl ∧
            pe.tail = ch[j] ∧ pe.head = ch[j + 1]) at hchain
    by_cases he : edge.tail = edge.head
    · simp only [he, ↓reduceIte] at hchain
      have hempty := Option.some.inj (hi.symm.trans hchain)
      simp [hempty] at hin
    simp only [he, ↓reduceIte] at hchain
    obtain ⟨ch, hch, _, _, hlast, hsteps⟩ := hchain
    have hchEq := Option.some.inj (hch.symm.trans hi)
    subst ch
    have hcg := (normalize_node_rank_alignment hnorm).2
    have hhead := (RankImpl.wellformed_spec hcg edge (List.mem_of_getElem? hedge)).2.1
    let head := cg.nodes[edge.head]'hhead
    have hheadGet : cg.nodes[edge.head]? = some head := List.getElem?_eq_getElem hhead
    have hnormHead := normalize_node_record hnorm hheadGet
    have hsrcHead := addLabelNodes_untouched_node hlabels hnormHead rfl
    have hsLen : sized.nodes.length = src.nodes.length := by simp [sized, sizeProperPortsX]
    have hheadSized : edge.head < sized.nodes.length := by
      rw [hsLen]
      exact (List.getElem?_eq_some_iff.mp hsrcHead).1
    let sd := sized.nodes[edge.head]'hheadSized
    have hsd : sized.nodes[edge.head]? = some sd := List.getElem?_eq_getElem hheadSized
    have ⟨srcHead, hsHead, hsDummy, _, hsPath⟩ := X_sizeProperPorts_node_origin P exact src hsd
    have hsEq := Option.some.inj (hsHead.symm.trans hsrcHead)
    rw [hsEq] at hsDummy hsPath
    have hne : v ≠ edge.head := by
      intro h
      rw [h] at hsv
      have heq := Option.some.inj (hsv.symm.trans hsd)
      rw [heq, hsDummy] at hdv
      simp at hdv
    have hlastD : chain.getLastD v = edge.head := by
      rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
    have hCommon : owner ∈ OrderImpl.commonPath
        (run.coordinateProper.nodes.getD (chain.headD v) default).node.clusterPath
        (run.coordinateProper.nodes.getD edge.head default).node.clusterPath := by
      simpa only [hlastD] using howner
    have hheadPath := (commonPath_member_both _ _ hCommon).2
    have hcoordHeadPath := coordinatePath_of_source hsize hsd hsDummy
    rw [hcRun, hsPath] at hcoordHeadPath
    have hownerHead : head.clusterPath.contains owner = true := by
      rw [hcoordHeadPath] at hheadPath
      exact List.contains_iff_mem.mpr hheadPath
    have hlt := chainRank_strict_before_last (p := norm) (chain := chain) (v := v)
      (last := edge.head) (fun j hj hj' => by
        obtain ⟨pe, hpe, _, _, htail, hhead⟩ := hsteps j hj hj'
        have hs := normalize_proper _ _ _ hnorm pe hpe
        simp only [Proper.span, htail, hhead] at hs
        omega) hin hlast hne
    have hrank (j : Nat) (hj : j < sized.nodes.length) :
        rk run.coordinateProper.rank j = rk norm.rank j := by
      have hr : j < sized.rank.length := by
        rw [hsLen, ← addLabelNodes_node_length hlabels, hnLen] at hj
        simpa only [show sized.rank = src.rank from rfl, hm.2.1] using hj
      have h := rankAt_coordinate_source (P := params) hr
      rw [hcRun, show sized.rank = src.rank from rfl, hm.2.1] at h
      exact h
    rw [← hrank v (List.getElem?_eq_some_iff.mp hsv).1, ← hrank edge.head hheadSized] at hlt
    exact ⟨edge.head, head, hheadGet, hownerHead, hlt⟩

set_option maxHeartbeats 1600000 in
/-- The bottom-marker interval has zero node height in every successful exact
component run drawn from a well-formed framed execution. -/
theorem sceneExecutionX_bottomBracketVacant {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run) :
    ExactBottomBracketVacant run := by
  intro layer t left v right i j k owner proxy lnode rnode
    hlayer ht hbot hproxy howner hi hj hk hl hr hlb hrb hlo hro hij hjk
  let cg := componentCandidate execution.graph comp candidate
  have h0 := execution.graph0_eq
  have he := execution.graph_eq
  obtain ⟨_, src, _, hcoord, hkeys, _, _, _, haligned⟩ := X_cg_run_bundle h0 he hcomp hrun
  let sized := sizeProperPortsX execution.params (exactDecls exactIds inp) src
  obtain ⟨params, _, hc⟩ := exactSizedCoordinate (P := execution.params)
    (exact := exactDecls exactIds inp) (source := src)
  have hcRun : coordinateGraph params sized = run.coordinateProper := hc.trans hcoord
  have hkey := sizedKeys execution.params (exactDecls exactIds inp) hkeys
  have hsAlign : sized.nodes.length = sized.rank.length := by
    simpa [sized, sizeProperPortsX] using haligned
  have hshape : CgShape cg := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) he) candidate
  obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, hroute, _, _⟩ := componentRunX_spec hrun
  obtain ⟨_, _, hlen, _, hlookup, _⟩ := proxyWidths_rel hprox
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨actual, hactual, _, hab, _⟩ := hlookup t proxy hproxy
  have hactual' : run.proper.nodes[t]? = some actual := by rwa [hnodes]
  have hb : proxy.node.border = 2 := hab.symm.trans ((isBottom_iff hactual').mp hbot).2
  have hp : (coordinateGraph params sized).nodes[t]? = some proxy := by
    rw [hcRun]
    exact hproxy
  obtain ⟨bottom, hbGet, hbBorder, hbPath⟩ : ∃ bottom, cg.nodes[t]? = some bottom ∧
      bottom.border = 2 ∧ proxy.node.clusterPath = bottom.clusterPath := by
    rcases coordinateGraph_lookup params sized hp with
      ⟨node, hnode, _, hborder, hpath, _⟩ | ⟨_, hside⟩ | ⟨_, _, _, _, _, htitle, _⟩
    · rcases hkey t node hnode with ⟨bottom, hbottom, hd, hb', hbp⟩ | ⟨_, hz, _⟩
      · exact ⟨bottom, hbottom, hb'.symm.trans (hborder.symm.trans hb), (hpath hd).trans hbp⟩
      · omega
    · rcases hside with h | h <;> omega
    · omega
  obtain ⟨bBox, _, hbBoxPath⟩ := X_cg_bottom_box h0 he hbGet hbBorder
  have hbOwner : bottom.decl = owner := by
    rw [hbPath, hbBoxPath] at howner
    simpa [List.getLast?_append] using howner
  obtain ⟨anchor, hfind⟩ :=
    X_componentRun_cg_top_of_bottom h0 he (linesCoverBoxes execution) hcomp hbGet hbBorder
  have haGet : cg.nodes[anchor.2]? = some anchor.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
  have haKeys : anchor.1.border = -2 ∧ anchor.1.clusterPath = bottom.clusterPath := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hfind
  obtain ⟨aBox, _, haBoxPath⟩ := X_cg_group_box h0 he haGet haKeys.1
  have haDecl : bottom.decl = anchor.1.decl := by
    have hh := congrArg List.getLast? haKeys.2.symm
    rw [hbBoxPath, haBoxPath] at hh
    simpa [List.getLast?_append] using hh
  have haOwner : anchor.1.decl = owner := haDecl.symm.trans hbOwner
  have hrankMember {index : Nat} {node : Node} (hget : cg.nodes[index]? = some node)
      (hin : node.clusterPath.contains owner = true) :
      rk run.coordinateProper.rank index ≤ rk run.coordinateProper.rank t ∧
      (node.border ≠ 2 → rk run.coordinateProper.rank index < rk run.coordinateProper.rank t) :=
    originalMemberRankBound execution hwf hframed hcomp hrun hbGet hbBorder haGet haKeys.1 haDecl
      hget (by rwa [haOwner])
  obtain ⟨_, _, hmem, _, _⟩ := RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨row, hrow⟩ := List.mem_iff_getElem?.mp hlayer
  obtain ⟨_, htRank⟩ := hmem row layer hrow t ht
  obtain ⟨hvbound, hvRank⟩ := hmem row layer hrow v (List.mem_of_getElem? hj)
  have hsame : rk run.coordinateProper.rank v = rk run.coordinateProper.rank t := by
    rw [X_proper_rank_eq_local hrun t] at htRank
    rw [X_proper_rank_eq_local hrun v] at hvRank
    exact hvRank.trans htRank.symm
  have hvBound : v < run.coordinateProper.nodes.length := by rwa [hnodes, hlen] at hvbound
  let nd := run.coordinateProper.nodes[v]'hvBound
  have hv : run.coordinateProper.nodes[v]? = some nd := List.getElem?_eq_getElem hvBound
  have hv' : (coordinateGraph params sized).nodes[v]? = some nd := by
    rw [hcRun]
    exact hv
  have hheight : RouteImpl.nodeH run.proper v = nd.node.h := by
    calc
      RouteImpl.nodeH run.proper v = RouteImpl.nodeH q0 v := by simp only [RouteImpl.nodeH, hnodes]
      _ = RouteImpl.nodeH run.coordinateProper v := nodeH_proxy hprox v
      _ = nd.node.h := by simp only [RouteImpl.nodeH, hv]
  rw [hheight]
  by_cases hside : nd.node.border = -1 ∨ nd.node.border = 1
  · exact coordinateGraph_side_height hkey
      (fun _ _ hget => (X_componentCandidate_marker_shape h0 he hget).1) hv' hside
  by_cases hframe : nd.node.border = -2 ∨ nd.node.border = 2
  · exact pc_frame_flat hv' hframe
  obtain ⟨box, _, hprefix⟩ := sceneExecutionX_sideBracket_prefix execution hcomp hrun hlayer
    hi hj hk hl hr hlb hrb hlo hro hij hjk
  have hscope : owner ∈ OrderImpl.nodePath run.coordinateProper v := by
    obtain ⟨rest, heq⟩ := hprefix
    rw [← heq]
    simp
  cases hd : nd.dummy with
  | true =>
    obtain ⟨head, node, hget, hcontains, hlt⟩ := dummyRank_lt_scoped_head hrun hv hd hscope
    have hle := (hrankMember hget hcontains).1
    omega
  | false =>
    have hin : nd.node.clusterPath.contains owner = true := by
      rw [OrderImpl.nodePath_of_nondummy hv hd] at hscope
      exact List.contains_iff_mem.mpr hscope
    by_cases htitle : nd.node.border = 3
    · obtain ⟨a, source, hsource, hbSource, hdSource, _, hpath, htitleRank⟩ :=
        coordinateGraph_title_rank_source hkey hshape hsAlign hv' htitle
      rcases hkey a source hsource with ⟨node, hn, _, hborder, hsourcePath⟩ | ⟨hd', _, _⟩
      · have hnBorder : node.border ≠ 2 := by omega
        have hcontains : node.clusterPath.contains owner = true := by
          rwa [hpath, hsourcePath] at hin
        have hlt := (hrankMember hn hcontains).2 hnBorder
        have haRankBound : a < sized.rank.length := by
          rw [← hsAlign]
          exact (List.getElem?_eq_some_iff.mp hsource).1
        have hsameRank := htitleRank.trans (rankAt_coordinate_source (P := params) haRankBound).symm
        rw [hcRun] at hsameRank
        omega
      · rw [hdSource] at hd'
        cases hd'
    · rcases coordinateGraph_lookup params sized hv' with
        ⟨source, hs, hd', hb', hpath, _⟩ | ⟨_, hside'⟩ | ⟨_, _, _, _, _, htitle', _⟩
      · rcases hkey v source hs with ⟨node, hget, hreal, hborder, hp'⟩ | ⟨hdummy, _, _⟩
        · have hcontains : node.clusterPath.contains owner = true := by
            rwa [hpath hreal, hp'] at hin
          have hnBorder : node.border ≠ 2 := by
            intro hn
            exact hframe (Or.inr (hb'.trans (hborder.trans hn)))
          have hlt := (hrankMember hget hcontains).2 hnBorder
          omega
        · rw [hdummy, hd] at hd'
          cases hd'
      · exact (hside hside').elim
      · exact (htitle htitle').elim

/-- Candidate counterexample for the unrestricted run statement. The proxy
has the same path as the anchor but a different declaration. The rank
constraints pair by declaration, while the side-marker fold pairs by path.
The predicate checks the live run, including both inclusive-order bounds. -/
def exactBottomBracketMalformedWitness : Except LayoutError Bool := do
  let params ← checkedParams .cell "flowchart"
  let graph : Graph :=
    { nodes := [
        { decl := 0, border := -2, clusterPath := [0], w := 3, h := 2 },
        { decl := 1, border := 2, clusterPath := [0], w := 0, h := 0 }]
      edges := []
      slot := params.slot }
  let run ← componentRunX params [] graph [] {}
  pure <| run.layers.any fun row =>
    let proxy := run.coordinateProper.nodes.getD 1 default
    let left := run.coordinateProper.nodes.getD 3 default
    let right := run.coordinateProper.nodes.getD 4 default
    let owner := proxy.node.clusterPath.getLast?
    row.contains 1 && row.contains 2 && row.contains 3 && row.contains 4 &&
      RouteImpl.frameKind run.proper 1 == 2 &&
      decide (0 < RouteImpl.nodeH run.proper 2) &&
      owner == some 0 && left.node.clusterPath.getLast? == owner &&
      right.node.clusterPath.getLast? == owner &&
      left.node.border == -1 && right.node.border == 1 &&
      decide (row.idxOf 3 ≤ row.idxOf 2) && decide (row.idxOf 2 ≤ row.idxOf 4)

end Elegant.Layered.PipelineImpl
