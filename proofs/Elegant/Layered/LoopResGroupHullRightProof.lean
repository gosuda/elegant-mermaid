import Elegant.Layered.LoopHullCoverProof
import Elegant.Layered.LoopResMarkerCopyProof
import Elegant.Layered.LoopResTopReservationProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ForeignBorderSpansProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Witness for the group-owner hull cover: ordered right markers in a shared layer.
Strictly narrower than `LoopResGroupHullRight` (marker indices and layer order,
no footprint inequality). True on the group-loop probes (`LoopHullCoverTProbe`
`grpLoopWide`/`grpLoopMin` with wide and minimal labels, nested groups, and a
sibling right of the group): inner right markers precede outer right markers in
every shared layer. -/
def LoopResGroupHullRightWitness (cg : Graph) (run : Run) : Prop :=
  forall (t : Nat) (nt : Node), cg.nodes[t]? = some nt ->
    (Exists fun e => e ∈ cg.edges /\ e.tail = t /\ e.head = t) ->
    nt.border = -2 ->
    forall (pos : Nat) (np : Node), cg.nodes[pos]? = some np -> np.border = -2 ->
      pos ≠ t -> np.decl ∈ nt.clusterPath ->
      Exists fun (mRt : Nat) => Exists fun (mRp : Nat) => Exists fun (nRt : ProperNode) =>
        Exists fun (nRp : ProperNode) => Exists fun (layer : List Nat) =>
          Exists fun (j : Nat) => Exists fun (iv : Nat) =>
            run.coordinateProper.nodes[mRt]? = some nRt /\
            nRt.node.border = 1 /\ nRt.node.clusterPath.getLast? = some nt.decl /\
            run.coordinateProper.nodes[mRp]? = some nRp /\
            nRp.node.border = 1 /\ nRp.node.clusterPath.getLast? = some np.decl /\
            layer ∈ run.layers /\ layer[j]? = some mRt /\ layer[iv]? = some mRp /\ j < iv


/-- Local copy of `lrt_no_group_at_b`: a recorded non-marker index is never a
group-top position of the candidate graph. -/
private theorem lgr_no_group_at_b {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {b : Nat} {actualB : ProperNode}
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2)) :
    ((componentCandidate e.graph comp candidate).nodes.getD b default).border ≠ -2 := by
  intro hcon
  have hdef : (default : Node).border = 0 := rfl
  by_cases hsome : ∃ nodeB : Node,
      (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB
  · obtain ⟨nodeB, hnodeB⟩ := hsome
    have hget : (componentCandidate e.graph comp candidate).nodes.getD b default =
        nodeB := by
      simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
    have hbB : nodeB.border = -2 := by rw [← hget]; exact hcon
    obtain ⟨rr, labeled, hrr, hc, hkeys, hready, hrecords, _⟩ :=
      componentRun_prepared_titled_source e.graph_eq hcomp hrun
    have hlab : labeled.nodes[b]? =
        some (⟨nodeB, false, none, false⟩ : ProperNode) :=
      hrecords b nodeB hnodeB
    have hcoord : (coordinateGraph e.params labeled).nodes[b]? =
        some (clearF (titleF (⟨nodeB, false, none, false⟩ : ProperNode))) :=
      coordinateGraph_marker_record hlab (Or.inl hbB) rfl
    rw [hc] at hcoord
    have hinj : clearF (titleF (⟨nodeB, false, none, false⟩ : ProperNode)) =
        actualB :=
      Option.some.inj (hcoord.symm.trans hcoordB)
    have hbdr : (clearF (titleF
        (⟨nodeB, false, none, false⟩ : ProperNode))).node.border = -2 :=
      (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hbB)
    rw [hinj] at hbdr
    exact hbne (Or.inl hbdr)
  · have hnone : (componentCandidate e.graph comp candidate).nodes[b]? = none := by
      cases h : (componentCandidate e.graph comp candidate).nodes[b]? with
      | none => rfl
      | some nodeB => exact absurd ⟨nodeB, h⟩ hsome
    have hget : (componentCandidate e.graph comp candidate).nodes.getD b default =
        default := by
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [hget, hdef] at hcon
    omega
/-- Local copy of `lrt_frameB_x`: the frame left edge at a non-group position
is the placed rect left edge. -/
private theorem lgr_frameB_x {P : Params} {cg : Graph} {run : Run}
    {b : Nat} {actualB : ProperNode}
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hgetNe : (cg.nodes.getD b default).border ≠ -2) :
    (frameRect P cg run b).x = (Labels.rectAt run.proper run.xs run.ys b).x := by
  have hframe : frameRect P cg run b = nodeRect cg run b := by
    unfold frameRect
    simp only []
    exact ite_eq_left (by simpa using hgetNe)
  have hrect : nodeRect cg run b = Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hproperB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hproperB]
  rw [hframe, hrect]

/-- Local copy of the private side-marker width lemma: every side marker
emitted by `addClusterBorders` carries the border width. -/
private theorem lgr_side_width (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper =>
        ∀ n ∈ cur.nodes,
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
          (fun cur : Proper =>
            ∀ n ∈ cur.nodes,
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


/-- Bottom loop owners are vacuous: a `border = 2` candidate node owns no
loop sizes (`LoopFootprintBottomEmpty_holds`), contradicting the self-loop
witness. -/
private theorem lgr_bottom_vacuous {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate e.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 2)
    (het : ∃ e_ ∈ (componentCandidate e.graph comp candidate).edges,
      e_.tail = t ∧ e_.head = t) : False := by
  have hvlen : t < (componentCandidate e.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnt).1
  have hget : (componentCandidate e.graph comp candidate).nodes.getD t default = nt := by
    simp only [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
  have hborder : ((componentCandidate e.graph comp candidate).nodes.getD t default).border
      = 2 := by rw [hget, htB]
  have hempty := LoopFootprintBottomEmpty_holds e comp candidate run orderOptions t
    hcomp hrun hvlen hborder
  obtain ⟨ed, hmem, htail, hhead⟩ := het
  have hmemF : ed ∈ loopEdges (componentCandidate e.graph comp candidate).edges t := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    simp only [htail, hhead, beq_self_eq_true, Bool.and_self]
  have hne : loopEdges (componentCandidate e.graph comp candidate).edges t ≠ [] :=
    List.ne_nil_of_mem hmemF
  have hneS : loopSizes (componentCandidate e.graph comp candidate).edges e.measured t
      (componentCandidate e.graph comp candidate).slot ≠ [] := by
    intro hnil
    have hmap : (loopEdges (componentCandidate e.graph comp candidate).edges t).map
        (fun e_ => stackSize (componentCandidate e.graph comp candidate).slot
          (routeLabels e.measured e_.decl)) = [] := hnil
    rw [List.map_eq_nil_iff] at hmap
    exact hne hmap
  exact hneS hempty

/-- Top reservation bound from the witness markers: the group-top footprint
ends left of the ancestor right marker's frame left edge. Marker copy supplies
the extent, alignment comes from `hx`, and the shared-layer order is the
witness. -/
private theorem lgr_top_bound {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate e.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    {mRt mRp : Nat} {nRt nRp : ProperNode}
    (hcoordT : run.coordinateProper.nodes[mRt]? = some nRt)
    (hbT : nRt.node.border = 1)
    (hlastT : nRt.node.clusterPath.getLast? = some nt.decl)
    (hcoordP : run.coordinateProper.nodes[mRp]? = some nRp)
    (hbP : nRp.node.border = 1)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {j iv : Nat} (hj : layer[j]? = some mRt) (hiv : layer[iv]? = some mRp)
    (hlt : j < iv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).w ≤
      (frameRect default (componentCandidate e.graph comp candidate) run mRp).x := by
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hext := loopResMarkerCopy_holds e comp candidate orderOptions run hcomp hrun
    hnt htG hcoordT hbT hlastT
  have hbne : ¬ (nRp.node.border = -2 ∨ nRp.node.border = 2) := by
    rw [hbP]; decide
  obtain ⟨hproperP, hxsP⟩ :=
    componentRun_border_record hrun hcoordP (Or.inr hbP)
  exact loopResTopReservation_holds e hwf hfp hcomp hrun hnt htG hcoordT hbT
    hlastT hext halign hcoordP hbne hproperP hxsP hlayer hj hiv hlt
/-- Frame achiever strictness: the ancestor right marker's frame left edge is
strictly left of the ancestor hull's right edge (membership + positive marker
width). -/
private theorem lgr_hull_strict {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate e.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    {mRp : Nat} {nRp : ProperNode}
    (hcoordP : run.coordinateProper.nodes[mRp]? = some nRp)
    (hbP : nRp.node.border = 1)
    (hlastP : nRp.node.clusterPath.getLast? = some np.decl) :
    (frameRect default (componentCandidate e.graph comp candidate) run mRp).x <
      (frameRect e.params (componentCandidate e.graph comp candidate) run pos).x +
        (frameRect e.params (componentCandidate e.graph comp candidate) run pos).w := by
  obtain ⟨hproperP, _⟩ :=
    componentRun_border_record hrun hcoordP (Or.inr hbP)
  have hbne : ¬ (nRp.node.border = -2 ∨ nRp.node.border = 2) := by
    rw [hbP]; decide
  have hGb : ((componentCandidate e.graph comp candidate).nodes.getD mRp default).border
      ≠ -2 := lgr_no_group_at_b e hcomp hrun hcoordP hbne
  have hframeB : (frameRect default (componentCandidate e.graph comp candidate) run
      mRp).x = (Labels.rectAt run.proper run.xs run.ys mRp).x :=
    lgr_frameB_x hproperP hGb
  have hmemB : Labels.rectAt run.proper run.xs run.ys mRp ∈
      groupBorderRects (componentCandidate e.graph comp candidate) run np.decl :=
    groupBorderRects_mem_of_record hproperP (Or.inr hbP) hlastP
  have hright_le := (boundsOf_rect_mem hmemB).2
  have hframe := frameRect_group_span (P := e.params) (run := run) hnp hgrp
  have hframeR : (frameRect e.params
      (componentCandidate e.graph comp candidate) run pos).x +
      (frameRect e.params
      (componentCandidate e.graph comp candidate) run pos).w =
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate)
        run np.decl) []).right := by
    rw [hframe]
    dsimp only
    omega
  obtain ⟨labeled, hcoordEq, hreadyB⟩ :=
    componentRun_titled_border_ready e.graph_eq hcomp hrun
  have hcoordML : (coordinateGraph e.params labeled).nodes[mRp]? = some nRp := by
    rw [hcoordEq]; exact hcoordP
  have horigP := coordinateGraph_side_original hreadyB hcoordML (Or.inr hbP)
  have hwEq : nRp.node.w = e.params.clusterBorderW :=
    lgr_side_width _ _ hreadyB horigP (Or.inr hbP)
  have hbw : 1 ≤ e.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one e.checked
  have hwpos : 0 < (Labels.rectAt run.proper run.xs run.ys mRp).w := by
    have hwRect : (Labels.rectAt run.proper run.xs run.ys mRp).w =
        nRp.node.w := by
      simp only [rectAt_eq, RouteImpl.nodeW, hproperP]
    omega
  omega
/-- Group-top hull cover from explicit ordered markers: top reservation bounds
the footprint by the ancestor marker's frame left, the achiever pushes that
strictly inside the ancestor hull. -/
private theorem lgr_group_of_markers {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate e.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate e.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    {mRt mRp : Nat} {nRt nRp : ProperNode}
    (hcoordT : run.coordinateProper.nodes[mRt]? = some nRt)
    (hbT : nRt.node.border = 1)
    (hlastT : nRt.node.clusterPath.getLast? = some nt.decl)
    (hcoordP : run.coordinateProper.nodes[mRp]? = some nRp)
    (hbP : nRp.node.border = 1)
    (hlastP : nRp.node.clusterPath.getLast? = some np.decl)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {j iv : Nat} (hj : layer[j]? = some mRt) (hiv : layer[iv]? = some mRp)
    (hlt : j < iv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).w <
      (frameRect e.params (componentCandidate e.graph comp candidate) run pos).x +
        (frameRect e.params (componentCandidate e.graph comp candidate) run pos).w := by
  have hle := lgr_top_bound e hwf hfp hx hcomp hrun hnt htG hcoordT hbT hlastT
    hcoordP hbP hlayer hj hiv hlt
  have hlt2 := lgr_hull_strict e hcomp hrun hnp hgrp hcoordP hbP hlastP
  omega
/-- The residual `LoopResGroupHullRight` holds for executed runs modulo the
single ordered-marker witness (plus the accepted alignment seam `hx`).
Plain owners are impossible (`≠ 0` vs `= 0`), bottom owners are vacuous
(`lgr_bottom_vacuous`), group tops use the witness via `lgr_group_of_markers`. -/
theorem loopResGroupHullRight_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hord : LoopResGroupHullRightWitness
      (componentCandidate execution.graph comp candidate) run) :
    LoopResGroupHullRight execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro t nt hnt het hne0 pos np hnp hgrp hne hmem
  have hshape := (componentCandidate_marker_shape execution.graph_eq hnt).1
  rcases hshape with ht0 | htG | htBot
  · exact absurd ht0 hne0
  · obtain ⟨mRt, mRp, nRt, nRp, layer, j, iv, hcoordT, hbT, hlastT, hcoordP,
        hbP, hlastP, hlayer, hj, hiv, hlt⟩ :=
      hord t nt hnt het htG pos np hnp hgrp hne hmem
    exact lgr_group_of_markers execution hwf hfp hx hcomp hrun hnt htG hnp hgrp
      hcoordT hbT hlastT hcoordP hbP hlastP hlayer hj hiv hlt
  · exact False.elim (lgr_bottom_vacuous execution hcomp hrun hnt htBot het)
/-- Executed ancestor-hull right cover modulo the witness: the conclusion of
`loopHullRightCover_holds` with the named residual discharged by
`loopResGroupHullRight_holds`. The only open content is the single
ordered-marker witness (plus the accepted alignment seam `hx`). -/
theorem loopHullRightCover_closed {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hord : LoopResGroupHullRightWitness
      (componentCandidate execution.graph comp candidate) run) :
    LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hGrp := loopResGroupHullRight_holds hwf hframed hx execution hcomp hrun hord
  exact loopHullRightCover_holds hwf hframed execution hcomp hrun hGrp







end PipelineImpl
end Layered
end Elegant
