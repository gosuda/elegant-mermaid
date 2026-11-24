import Elegant.Layered.ExactBottomLoopTransportProof
import Elegant.Layered.ExactCaptionAncestorLinkVerticalProof
import Elegant.Layered.ExactCaptionAncestorsLocalProof
import Elegant.Layered.ExactGroupLoopFixedLeafGapProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.ExactPlainAncestorImpossibleProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A self-loop reservation starts at its owner's right edge, including for a
zero-sized owner. -/
theorem exactNonforwardHull_owner_disjoint {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (t : Nat) :
    Disjoint (frameRect P cg run t) (loopFootprintExt cg run labels t) := by
  have hx : (loopFootprintExt cg run labels t).x =
      (frameRect P cg run t).x + (frameRect P cg run t).w := rfl
  exact rect_disjoint_of_x (Or.inl (by omega))

/-- A zero extent on either axis makes the compared frame disjoint. -/
theorem exactNonforwardHull_empty_disjoint {frame footprint : Rect}
    (hempty : frame.w ≤ 0 ∨ frame.h ≤ 0) : Disjoint frame footprint := by
  rcases hempty with hw | hh
  · unfold Disjoint Rect.meetsInterior
    omega
  · unfold Disjoint Rect.meetsInterior
    omega

private theorem originalCandidateDecl {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate pos : Nat}
    {node : Node} (hnode : (componentCandidate execution.graph comp candidate).nodes[pos]? = some node)
    (hborder : node.border = 0 ∨ node.border = -2) : comp[pos]? = some node.decl := by
  rw [componentCandidate_nodes] at hnode
  change (comp.map (fun k => execution.graph.nodes.getD k default))[pos]? = some node at hnode
  rw [List.getElem?_map] at hnode
  obtain ⟨key, hkey, hget⟩ := Option.map_eq_some_iff.mp hnode
  obtain ⟨_, hkeys⟩ := mem_components_eq hcomp
  have hkeyMem := List.mem_of_getElem? hkey
  rw [hkeys] at hkeyMem
  have hk := List.mem_range.mp (List.mem_filter.mp hkeyMem).1
  have hk₀ : key < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact hk
  have hbase := List.getElem?_eq_getElem hk₀
  obtain ⟨actual, hactual, hb, _, hdecl⟩ := exactGraph_node_key execution.graph_eq hbase
  have heq : actual = node := by
    simpa only [List.getD_eq_getElem?_getD, hactual, Option.getD_some] using hget
  subst actual
  have hindex : execution.graph0.nodes[key].decl = key := by
    rcases hborder with hplain | hgroup
    · obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
        measuredGraph_prepared_source execution.graph0_eq
      have hlines := execution.lines_eq
      unfold boxLines at hlines
      have hlineLength : execution.lines.length = inp.boxes.length := by
        simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
      have hpreparedLookup := congrArg (fun g : Graph => g.nodes[key]?) hprepared
      have hpreparedNode := hpreparedLookup.symm.trans hbase
      have hzero : (execution.graph0.nodes[key]'hk₀).border = 0 := hb.symm.trans hplain
      have hi : key < nodes.length := by
        by_cases hi : key < nodes.length
        · exact hi
        · have hbottom := (Compound.prepare_bottom_of_index _ _ _ _ key
            (by dsimp only; omega) hpreparedNode).1
          omega
      have hibox : key < inp.boxes.length := by omega
      obtain ⟨_, hchangedBox, _⟩ := fixedSizes_path_index inp (List.getElem?_eq_getElem hibox)
      exact (prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hzero hchangedBox).1
    · exact (measuredGraph_group_origin execution.graph0_eq hbase (hb.symm.trans hgroup)).1
  rw [hdecl.trans hindex]
  exact hkey

private theorem originalCandidateDecl_ne {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate i j : Nat}
    {a b : Node} (ha : (componentCandidate execution.graph comp candidate).nodes[i]? = some a)
    (hb : (componentCandidate execution.graph comp candidate).nodes[j]? = some b)
    (haBorder : a.border = 0 ∨ a.border = -2) (hbBorder : b.border = 0 ∨ b.border = -2)
    (hne : i ≠ j) : a.decl ≠ b.decl := by
  have hia := originalCandidateDecl execution hcomp ha haBorder
  have hjb := originalCandidateDecl execution hcomp hb hbBorder
  have hi := (List.getElem?_eq_some_iff.mp hia).1
  intro hdecl
  rw [hdecl, ← hjb] at hia
  exact hne (((components_nodup execution.graph comp hcomp).getElem?_inj hi).mp hia)

private theorem candidateSlot_pos {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) :
    0 < (componentCandidate execution.graph comp candidate).slot := by
  have hparams := (checkedParams_valid execution.checked).2.2.1
  obtain ⟨_, _, _, hprepared, _, _⟩ := measuredGraph_prepared_source execution.graph0_eq
  have hslot₀ : execution.graph0.slot = execution.params.slot := congrArg Graph.slot hprepared
  have hexact := execution.graph_eq
  unfold exactGraph at hexact
  obtain ⟨_, _, hgraph⟩ := bind_ok hexact
  have hslot := congrArg Graph.slot (Except.ok.inj hgraph).symm
  change execution.graph.slot = execution.graph0.slot at hslot
  have hcandidate : (componentCandidate execution.graph comp candidate).slot =
      execution.graph.slot := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  rw [hcandidate, hslot, hslot₀]
  omega

/-- The extended footprint of a looping group uses exactly its frame height.
The measured title record already reserves the entire loop-label stack. -/
theorem exactNonforwardHull_group_height {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t : Nat} {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : owner.border = -2)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) :
    (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t).h =
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).h := by
  let cg := componentCandidate execution.graph comp candidate
  let sizes := loopSizes cg.edges execution.measured t cg.slot
  obtain ⟨edge, hmem, htail, hhead⟩ := hloop
  have hsizeMem : stackSize cg.slot (routeLabels execution.measured edge.decl) ∈ sizes := by
    unfold sizes loopSizes loopEdges
    exact List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨hmem, by simp [htail, hhead]⟩, rfl⟩
  have hslot : 0 < cg.slot := candidateSlot_pos execution comp candidate
  have hwidth : ∀ s ∈ sizes, 0 ≤ s.width := by
    intro s hs
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hs
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hpos : 0 < (if run.exact.contains t then Loops.exactExtent cg.slot sizes
      else Loops.extent cg.slot sizes) := by
    split
    · apply exactExtent_pos cg.slot sizes hslot
      intro hnil
      rw [hnil] at hsizeMem
      exact List.not_mem_nil hsizeMem
    · have h := Loops.outer_label_extent cg.slot sizes (Int.le_of_lt hslot) hwidth _ hsizeMem
      have hmul := Int.mul_pos hslot (show (0 : Int) < (sizes.length : Int) + 1 by omega)
      have hw := hwidth _ hsizeMem
      omega
  obtain ⟨_, _, _, _, _, _, _, hmarker, _, hr, _, hlast, _⟩ :=
    xleg_loopMarkerCoreX_holds exactIds inp o res execution comp candidate run orderOptions cg
      hcomp rfl hrun t owner howner ⟨edge, hmem, htail, hhead⟩ hgroup
  have hcopy := xleg_rightMarker_copies_extent execution.graph0_eq execution.graph_eq
    hcomp hrun howner hgroup hmarker hr hlast
  have hext := xleg_rightMarker_extent_ge execution hcomp hrun howner hgroup hmarker hr hlast
  rw [hcopy] at hext
  change (if run.exact.contains t then Loops.exactExtent cg.slot sizes
    else Loops.extent cg.slot sizes) ≤ (owner.loopExtent : Int) at hext
  have hownerExtent : 0 < owner.loopExtent := by omega
  have hreserve := required_height_le_group_top execution hcomp howner hgroup hownerExtent
  change 2 * (sizes.length : Int) * Loops.band cg.slot sizes ≤ owner.h at hreserve
  obtain ⟨title, htitle⟩ := group_title_record hrun howner hgroup
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq howner hgroup
  have htitlePath : (copyF (⟨owner, false, none, false⟩, t)).node.clusterPath.contains
      owner.decl = true := by
    change owner.clusterPath.contains owner.decl = true
    simp [hpath]
  have hmember : Labels.rectAt run.proper run.xs run.ys title ∈ groupMemberRects cg run owner.decl :=
    fbs_groupMemberRects_mem htitle htitlePath
  have hheight : owner.h ≤ (frameRect execution.params cg run t).h := by
    have h := boundsOf_height_ge_member hmember
    rw [rectAt_eq] at h
    change RouteImpl.nodeH run.proper title ≤ _ at h
    simp only [RouteImpl.nodeH, htitle, copyF] at h
    rw [frameRect_group_span howner hgroup]
    exact h
  have hband : 0 ≤ Loops.band cg.slot sizes := by
    have hfold : ∀ (ls : List LoopLabel) (init : Int),
        init ≤ ls.foldl (fun acc l => max acc l.height) init := by
      intro ls
      induction ls with
      | nil => intro init; exact Int.le_refl init
      | cons l rest ih =>
        intro init
        exact Int.le_trans (Int.le_max_left init l.height) (ih _)
    exact Int.le_trans (by omega) (hfold sizes (2 * cg.slot))
  have hnonneg := Int.mul_nonneg (Int.natCast_nonneg sizes.length) hband
  rw [Int.mul_assoc] at hreserve
  change max (frameRect execution.params cg run t).h
    ((sizes.length : Int) * Loops.band cg.slot sizes) = (frameRect execution.params cg run t).h
  exact Int.max_eq_left (by omega)

/-- A nonexact plain owner also has no vertical expansion of its footprint. -/
theorem exactNonforwardHull_plain_nonexact_height
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t : Nat} {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hplain : owner.border = 0) (hnonexact : run.exact.contains t = false)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) :
    (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t).h =
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).h := by
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨edge, hmem, ht, hh⟩ := hloop
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  have hs : edge.tail = edge.head := ht.trans hh.symm
  subst t
  have hb : (cg.nodes.getD edge.tail default).border ≠ -2 := by
    simp [cg, List.getD_eq_getElem?_getD, howner, hplain]
  have h := XLEM_plainReserve_holds exactIds inp o res execution comp candidate run
    orderOptions cg k edge hcomp rfl hrun hk hs hb hnonexact
  exact Int.max_eq_left h

/-- Transfer the strict direct-parent steps through the checked candidate-level
ancestor walk. This is the unextended frame containment used before widening
an ancestor's interior obligation to the loop reservation. -/
theorem exactNonforwardHull_group_ancestor_frame_strict
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hownerBorder : owner.border = -2) (hgroupBorder : group.border = -2)
    (hne : t ≠ pos) (hanc : group.decl ∈ owner.clusterPath) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run t) := by
  exact XC_ancestorGroupFrameXW_of_linkW exactIds (XCA_groupLinkXW_closed exactIds)
    execution hwf hfp hcomp hrun t pos owner group howner hownerBorder hgroup hgroupBorder
    (originalCandidateDecl_ne execution hcomp howner hgroup (Or.inr hownerBorder)
      (Or.inr hgroupBorder) hne) (List.contains_iff_mem.mpr hanc)

/-- For a looping group strictly inside an ancestor group, only the footprint's
extended right edge remains to be bounded. -/
theorem exactNonforwardHull_group_ancestor_iff_right
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hownerBorder : owner.border = -2) (hgroupBorder : group.border = -2)
    (hne : t ≠ pos) (hanc : group.decl ∈ owner.clusterPath)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) :
    let cg := componentCandidate execution.graph comp candidate
    let ancestor := frameRect execution.params cg run pos
    let footprint := loopFootprintExt cg run execution.measured t
    ancestor.StrictInside footprint ↔ footprint.x + footprint.w < ancestor.x + ancestor.w := by
  let cg := componentCandidate execution.graph comp candidate
  let ancestor := frameRect execution.params cg run pos
  let frame := frameRect execution.params cg run t
  let footprint := loopFootprintExt cg run execution.measured t
  have hstrict : ancestor.StrictInside frame :=
    exactNonforwardHull_group_ancestor_frame_strict execution hwf hfp hcomp hrun
      howner hgroup hownerBorder hgroupBorder hne hanc
  have ht := componentRunX_original_nodes_covered hrun t (List.getElem?_eq_some_iff.mp howner).1
  have hw : 0 ≤ frame.w :=
    (frameRect_dims_nonneg execution.params cg run t (componentRunX_dims_nonneg hrun) ht).1
  have hx : footprint.x = frame.x + frame.w := rfl
  have hy : footprint.y = frame.y := rfl
  have hh : footprint.h = frame.h :=
    exactNonforwardHull_group_height execution hcomp hrun howner hownerBorder hloop
  change ancestor.StrictInside footprint ↔ footprint.x + footprint.w < ancestor.x + ancestor.w
  refine ⟨fun h => h.2.1, fun hright => ⟨?_, hright, hstrict.2.2.1, ?_⟩⟩
  · rw [hx]
    exact Int.lt_of_lt_of_le hstrict.1 (by omega)
  · rw [hy, hh]
    exact hstrict.2.2.2

/-- In a framed execution, a group below the loop owner ends to the left of
its reservation. A plain owner cannot occur on a group ancestor path, and a
bottom marker cannot own a loop. -/
theorem exactNonforwardHull_nested_disjointW
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t)
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hgroupBorder : group.border = -2) (hne : t ≠ pos)
    (hnest : owner.decl ∈ group.clusterPath) :
    Disjoint (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos)
      (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t) := by
  rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq howner).1 with
    hplain | htop | hbottom
  · have hlines := execution.lines_eq
    unfold boxLines at hlines
    have hlength : execution.lines.length = inp.boxes.length := by
      simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
    exact (exactPlainAncestorImpossible_holds exactIds execution.graph0_eq execution.graph_eq
      hlength hwf hfp hcomp hgroup hgroupBorder howner hplain
      (originalCandidateDecl_ne execution hcomp hgroup howner (Or.inr hgroupBorder)
        (Or.inl hplain) hne.symm) (List.contains_iff_mem.mpr hnest)).elim
  · have h := exactNonforwardHull_group_ancestor_frame_strict execution hwf hfp hcomp hrun
      hgroup howner hgroupBorder htop hne.symm hnest
    have hx : (loopFootprintExt (componentCandidate execution.graph comp candidate) run
      execution.measured t).x =
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).x +
          (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).w := rfl
    exact rect_disjoint_of_x (Or.inl (Int.le_of_lt (hx.symm ▸ h.2.1)))
  · exact (exactBottomNoLoopX execution comp candidate run orderOptions hcomp _ rfl
      hrun t owner howner hbottom hloop).elim

end Elegant.Layered.PipelineImpl
