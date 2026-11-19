import Elegant.Layered.StrictDummyFrameProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.DummyChainRankProof
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Order
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ExecutedBorderOrderFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Elegant Layered

/-- Every side marker emitted by `addClusterBorders` carries the border width.
Copy of the private lemma in `ForeignBorderAlignRankProof`. -/
private theorem addClusterBorders_side_width_copy (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper => ∀ n ∈ cur.nodes,
        n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
    · intro n hn hs
      rcases hs with hs | hs
      · exact ((hready.1 n hn).1 hs).elim
      · exact ((hready.1 n hn).2 hs).elim
    · intro state hstate entry hentry
      unfold OrderImpl.borderStep
      split
      · exact hstate
      · apply OrderImpl.foldl_inv
          (fun cur : Proper => ∀ n ∈ cur.nodes,
            n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
        · exact hstate
        · intro st hst off _
          intro n hn hs
          have hn' : n ∈ st.nodes ++
              [OrderImpl.borderLeft entry width,
                OrderImpl.borderRight entry width] := hn
          rcases List.mem_append.mp hn' with hold | hnew
          · exact hst n hold hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
            rcases hnew with rfl | rfl <;> rfl
  exact hP node (List.mem_of_getElem? hnode) hside

/-- Component group box. Copy of the private lemma in `BottomNestedRankProof`. -/
private theorem bnr_cg_group_box_copy {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨_, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  rw [← hdecl] at hbox
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath


 /-- Executed proper dummy has the same record in the coordinate graph. Copy of
 the private lemma in `StrictDummyFrameProof`. -/
 private theorem proper_to_coordinate_dummy_copy2 {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     {i : Nat} {pn : ProperNode}
     (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
     ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
       cn.node.border = pn.node.border ∧ cn.node.clusterPath = pn.node.clusterPath := by
   obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hprox, hdrop, _, _, _, _, _⟩ :=
     componentRun_spec hrun
   have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
   have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
   have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
     (proxyWidths_rel hprox).2.2.1
   have hiC : i < run.coordinateProper.nodes.length := by
     have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
     omega
   obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
     ⟨_, List.getElem?_eq_getElem hiC⟩
   obtain ⟨nd', hnd', hddum, _, _⟩ :=
     (proxyWidths_rel hprox).2.2.2.2.1 i cn hcn
   have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
   have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
   have hK : NodeKeys cg labeled :=
     addLabelNodes_keys _ _ _ (normalize_keys hn) hl
   have hcnL : (coordinateGraph P labeled).nodes[i]? = some cn := by
     rw [hc]; exact hcn
   have hbord0 : cn.node.border = 0 := pc_plain hK hcnL hcnDum
   have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
     rw [hbord0]; decide
   obtain ⟨hsame, _⟩ := (proxyWidths_rel hprox).2.2.2.2.2 i cn hcn hnp
   have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
   exact ⟨cn, hcn, hcnDum, by rw [hcnEq], by rw [hcnEq]⟩

 /-- Canonical cluster path of an executed side marker. Copy of the private
lemma in `SideMarkerPathsProof`. -/
private theorem sideMarkerCanon_copy {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[decl]? = some box ∧
      na.node.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [decl] := by
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ := componentRun_ranked_source hrun
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun index node hnode => componentCandidate_marker_shape hgraph hnode
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)) :=
    titled_border_ready hkeys hshape hmarkers haligned
  have hcoordinate : (coordinateGraph P labeled).nodes[a]? = some na := by
    rw [hcoord]; exact hna
  have horiginal := coordinateGraph_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal)
      hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases titled_node_origin hkeys hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hkeys top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨_, _, hsrcG⟩ := componentCandidate_nonplain_source hbn (by omega)
      obtain ⟨_, boxG, hboxG, _, hpathG⟩ :=
        measuredGraph_group_origin hgraph hsrcG hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      have hdeclEq : bn.decl = decl :=
        Option.some.inj (hnaLast.symm.trans hlast)
      rw [hdeclEq] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hpathG, hdeclEq]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega

/-- Executed dummy marker bracket: every linked dummy sits between its group's
side markers at its own rank, with positive marker widths. Markers come from
`bracketMarkersAtRank'` at the dummy's own rank; widths from the side-marker
border width; layer positions from the border-before order. -/
theorem dummyMarkerBracket_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    (_hxalign : ForeignBorderChainXAligned) :
    DummyMarkerBracket (componentCandidate execution.graph comp candidate) run := by
  intro gpos gn hg hgroup d nd hnd hdum hpath
  have hgraph := execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    have hlen := (mapM_getElem? _ _ _ h).1
    simpa only [List.length_zipIdx] using hlen
  have hcontain : nd.node.clusterPath.contains gn.decl = true :=
    List.contains_iff_mem.mpr hpath
  have hdLen : d < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnd).1
  -- Markers at the dummy's own rank.
  have hrk := (bracketMarkersAtRank' (P := execution.params) (inp := inp) (o := o)
    (lines := execution.lines) (graph := execution.graph) hgraph hlines hwf hframed
    (comp := comp) hcomp (candidate := candidate) (run := run)
    (labels := execution.measured) (orderOptions := orderOptions) hrun
    (decl := gn.decl) ((rk run.proper.rank d).toNat) (low := d) (high := d)
    (lowNd := nd) (highNd := nd) hnd hcontain (by omega) hnd hcontain (by omega))
  obtain ⟨mL, mR, nL, nR, hML, hbL, hlastL, hrankML, hMR, hbR, hlastR, hrankMR⟩ := hrk
  -- Rank equalities asInts.
  have hrkEq : run.proper.rank = run.coordinateProper.rank :=
    proper_rank_eq_coordinate hrun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouteOk, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteOk).1).2.2.2.1
  obtain ⟨_, _, _, hnnD⟩ := hcov d hdLen
  have hnnC : 0 ≤ rk run.coordinateProper.rank d := by
    rw [← hrkEq]; exact hnnD
  have hcast : ((rk run.coordinateProper.rank d).toNat : Int) =
      rk run.coordinateProper.rank d :=
    Int.toNat_of_nonneg hnnC
  have hrankL : rk run.coordinateProper.rank mL = rk run.coordinateProper.rank d := by
    rw [hrkEq] at hrankML
    rw [hrankML, hcast]
  have hrankR : rk run.coordinateProper.rank mR = rk run.coordinateProper.rank d := by
    rw [hrkEq] at hrankMR
    rw [hrankMR, hcast]
  -- Widths from the border width.
  obtain ⟨labeled, hcoordL, hready⟩ :=
    componentRun_titled_border_ready (P := execution.params) (inp := inp) (o := o)
      (lines := execution.lines) (graph := execution.graph) execution.graph_eq hcomp hrun
  have hcoordML : (coordinateGraph execution.params labeled).nodes[mL]? = some nL := by
    rw [hcoordL]; exact hML
  have hcoordMR : (coordinateGraph execution.params labeled).nodes[mR]? = some nR := by
    rw [hcoordL]; exact hMR
  have horigL := coordinateGraph_side_original hready hcoordML (Or.inl hbL)
  have horigR := coordinateGraph_side_original hready hcoordMR (Or.inr hbR)
  have hwL : nL.node.w = execution.params.clusterBorderW :=
    addClusterBorders_side_width_copy _ _ hready horigL (Or.inl hbL)
  have hwR : nR.node.w = execution.params.clusterBorderW :=
    addClusterBorders_side_width_copy _ _ hready horigR (Or.inr hbR)
  have hgeL : 1 ≤ nL.node.w := by
    rw [hwL]; exact checkedParams_clusterBorderW_ge_one execution.checked
  have hgeR : 1 ≤ nR.node.w := by
    rw [hwR]; exact checkedParams_clusterBorderW_ge_one execution.checked
  -- Markers share the canonical path.
  have hsame : nL.node.clusterPath = nR.node.clusterPath :=
    sideMarkerSamePath (P := execution.params) (inp := inp) (o := o)
      (lines := execution.lines) (graph := execution.graph) execution.graph_eq
      (comp := comp) hcomp (candidate := candidate) (run := run)
      (labels := execution.measured) (orderOptions := orderOptions) hrun
      (decl := gn.decl) (m := mL) (m' := mR) (marker := nL) (marker' := nR)
      hML hbL hlastL hMR hbR hlastR
  -- Marker path equals the group path via the shared fixedSizes box.
  obtain ⟨boxM, hboxM, hpathM⟩ :=
    sideMarkerCanon_copy (P := execution.params) (inp := inp) (o := o)
      (lines := execution.lines) (graph := execution.graph) execution.graph_eq
      hcomp hrun hML (Or.inl hbL) hlastL
  obtain ⟨boxG, hboxG, hpathG⟩ :=
    bnr_cg_group_box_copy (P := execution.params) (inp := inp) (o := o)
      (lines := execution.lines) (graph := execution.graph) execution.graph_eq hg hgroup
  have hmapGet := (fixedSizes_path_index inp hboxG).2.1
  have hmapPath := (fixedSizes_path_index inp hboxG).2.2
  have hboxM_eq : boxM = (fun box : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) boxG := by
    have hmapped : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[gn.decl]? = some boxM := hboxM
    rw [hmapGet] at hmapped
    exact Option.some.inj hmapped.symm
  have hmarkPath : nL.node.clusterPath = gn.clusterPath := by
    rw [hpathM, hboxM_eq, hmapPath, ← hpathG]
  have hmarkPathR : nR.node.clusterPath = gn.clusterPath := hsame.symm.trans hmarkPath
  -- Order setup for the bracket.
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ := componentRun_spec hrun
  have hwfB := componentRun_coordinate_bordersWellFormed (P := execution.params)
    (inp := inp) (o := o) (lines := execution.lines) (graph := execution.graph)
    execution.graph_eq hcomp hrun
  have hbb : OrderImpl.LayersBB run.coordinateProper ord.layers := by
    unfold OrderImpl.orderWithBudget at horder
    split at horder
    · split at horder
      · simp only [Except.ok.injEq] at horder
        subst horder
        exact OrderImpl.runKey_bb hwfB orderOptions.key OrderImpl.sweepMax
          OrderImpl.sweepStall OrderImpl.sweepMax 0
          (OrderImpl.seedBest run.coordinateProper orderOptions.start)
          (OrderImpl.crossCount run.coordinateProper
            (OrderImpl.seedBest run.coordinateProper orderOptions.start)) 0
          (OrderImpl.seedBest_spec run.coordinateProper orderOptions.start).1
          (OrderImpl.seedBest_bb hwfB orderOptions.start)
      · simp at horder
    · simp at horder
  have hspec := (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord
    horder).1
  -- Marker non-dummy and node paths.
  have hdmL : nL.dummy = false := by
    cases hd : nL.dummy with
    | false => rfl
    | true =>
      have h0 := hwfB.2.2 mL nL hML hd
      omega
  have hdmR : nR.dummy = false := by
    cases hd : nR.dummy with
    | false => rfl
    | true =>
      have h0 := hwfB.2.2 mR nR hMR hd
      omega
  have hnpL : OrderImpl.nodePath run.coordinateProper mL = nL.node.clusterPath :=
    OrderImpl.nodePath_of_nondummy hML hdmL
  have hnpR : OrderImpl.nodePath run.coordinateProper mR = nR.node.clusterPath :=
    OrderImpl.nodePath_of_nondummy hMR hdmR
  -- Lay equalities and the common layer.
  have hlayML : OrderImpl.lay run.coordinateProper mL =
      OrderImpl.lay run.coordinateProper d := by
    simp only [OrderImpl.lay, hrankL]
  have hlayMR : OrderImpl.lay run.coordinateProper mR =
      OrderImpl.lay run.coordinateProper d := by
    simp only [OrderImpl.lay, hrankR]
  rw [hlayers] at hbb
  -- Coordinate record of the dummy: same cluster path as the proper record.
  obtain ⟨cn, hcn, hcnDum, _, hcnPath⟩ :=
    proper_to_coordinate_dummy_copy2 hrun hnd hdum
  have hcnB0 : cn.node.border = 0 := hwfB.2.2 d cn hcn hcnDum
  -- Border-0 node paths unfold to cluster paths, even for dummies.
  have hnpD : OrderImpl.nodePath run.coordinateProper d = cn.node.clusterPath :=
    plainNodePathEq hrun hcn hcnB0
  -- Prefix of the dummy node path via the executed scoped-path transport:
  -- the group path prefixes every executed proper path containing its
  -- declaration, and the dummy's coordinate path equals its proper path.
  have hprefix : nL.node.clusterPath <+: OrderImpl.nodePath run.coordinateProper d := by
    have hmem : nd ∈ run.proper.nodes := List.mem_of_getElem? hnd
    have hpre : gn.clusterPath <+: nd.node.clusterPath :=
      execution.component_run_proper_scoped hwf hrun hg hgroup nd hmem hpath
    rw [hmarkPath, hnpD, hcnPath]
    exact hpre
  -- The common layer of the dummy and both markers.
  have hlenD : OrderImpl.lay run.coordinateProper d < run.layers.length := by
    rw [← hlayers]
    exact (ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord
      horder hcn).1
  let layer : List Nat := run.layers[OrderImpl.lay run.coordinateProper d]'hlenD
  have hlayerMem : layer ∈ run.layers := List.getElem_mem hlenD
  have hopt : run.layers[OrderImpl.lay run.coordinateProper d]? = some layer :=
    List.getElem?_eq_some_iff.mpr ⟨hlenD, rfl⟩
  obtain ⟨_, hmemD0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hcn
  obtain ⟨_, hmemL0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hML
  obtain ⟨_, hmemR0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hMR
  rw [hlayML] at hmemL0
  rw [hlayMR] at hmemR0
  have hmemD : d ∈ layer := by
    have h1 := hmemD0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hmemL : mL ∈ layer := by
    have h1 := hmemL0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hmemR : mR ∈ layer := by
    have h1 := hmemR0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  obtain ⟨li, hli⟩ := List.mem_iff_getElem?.mp hmemL
  obtain ⟨mi, hmi⟩ := List.mem_iff_getElem?.mp hmemD
  obtain ⟨ri, hri⟩ := List.mem_iff_getElem?.mp hmemR
  -- Distinctness from border values.
  have hneML : mL ≠ d := by
    intro heq
    subst heq
    have hcnEq : nL = cn := Option.some.inj (hML.symm.trans hcn)
    rw [hcnEq, hcnB0] at hbL
    omega
  have hneMR : mR ≠ d := by
    intro heq
    subst heq
    have hcnEq : nR = cn := Option.some.inj (hMR.symm.trans hcn)
    rw [hcnEq, hcnB0] at hbR
    omega
  -- Prefix facts for the BBp applications.
  have hpreL : OrderImpl.nodePath run.coordinateProper mL <+:
      OrderImpl.nodePath run.coordinateProper d := by
    rw [hnpL]
    exact hprefix
  have hpreR : OrderImpl.nodePath run.coordinateProper mR <+:
      OrderImpl.nodePath run.coordinateProper d := by
    rw [hnpR, ← hsame]
    exact hprefix
  have hbdL : (run.coordinateProper.nodes.getD mL default).node.border = -1 := by
    rw [OrderImpl.getD_border hML]
    exact hbL
  have hbdR : (run.coordinateProper.nodes.getD mR default).node.border = 1 := by
    rw [OrderImpl.getD_border hMR]
    exact hbR
  have hbbLayer := hbb layer hlayerMem
  have hsubL : [mL, d].Sublist layer := (hbbLayer mL d hmemL hmemD hneML hpreL).1 hbdL
  have hsubR : [d, mR].Sublist layer := (hbbLayer mR d hmemR hmemD hneMR hpreR).2 hbdR
  have hnd : layer.Nodup :=
    OrderImpl.layering_mem_nodup hspec (by rw [hlayers]; exact hlayerMem)
  have hlt : li < mi :=
    OrderImpl.index_lt_of_pair_sublist hnd hsubL hneML hli hmi
  have hgt : mi < ri :=
    OrderImpl.index_lt_of_pair_sublist hnd hsubR hneMR.symm hmi hri
  exact ⟨mL, mR, nL, nR, layer, hlayerMem, hML, hMR, hbL, hbR, hlastL, hlastR,
    hgeL, hgeR, hrankL, hrankR, li, mi, ri, hli, hmi, hri, hlt, hgt⟩

end Elegant.Layered.PipelineImpl
