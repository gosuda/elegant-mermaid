import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.Route
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.Loops
import Elegant.Layered.Rank
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.LoopFootprintGeneralOrder

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-- Exact-run membership bridge: an index recorded in `run.exact` (a filtered
`zipIdx`) is a valid graph node carrying an exact decl. -/
private theorem XLEML_exact_bound {cg : Graph} {exact : List Nat} {t : Nat}
    (h : (cg.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none).contains t = true) :
    t < cg.nodes.length ∧ exact.contains (cg.nodes.getD t default).decl = true := by
  have hm : t ∈ cg.nodes.zipIdx.filterMap fun q =>
      if exact.contains q.1.decl then some q.2 else none :=
    List.contains_iff_mem.mp h
  obtain ⟨q, hq, hfq⟩ := List.mem_filterMap.mp hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  rw [List.getElem?_zipIdx] at hi
  cases hni : cg.nodes[i]? with
  | none => simp [hni] at hi
  | some ni =>
    simp only [hni, Option.map_some, Nat.zero_add] at hi
    have hqq : (ni, i) = q := Option.some.inj hi
    rw [← hqq] at hfq
    dsimp only at hfq
    by_cases hc : exact.contains ni.decl = true
    · simp only [hc, ↓reduceIte] at hfq
      have hti : i = t := Option.some.inj hfq
      subst hti
      refine ⟨(List.getElem?_eq_some_iff.mp hni).1, ?_⟩
      rw [List.getD_eq_getElem?_getD, hni, Option.getD_some]
      exact hc
    · have hconj : exact.contains ni.decl = true ∧ i = t := by simpa using hfq
      exact absurd hconj.1 hc

/-- Exact proper nodes transfer unchanged for non-proxy borders. -/
private theorem XLEML_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- `coordinateGraphX` preserves the loop extent of a plain anchor. -/
private theorem XLEML_coord_loopExtent {P : Params} {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.node.loopExtent = nd.node.loopExtent := by
  obtain ⟨sized, hs, hb', hle⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.node.border = 0 ∧ sized.node.loopExtent = nd.node.loopExtent := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, hb, rfl⟩
    · refine ⟨_, rfl, hb, rfl⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
        some sized := by
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
  split
  · refine ⟨_, rfl, ?_⟩
    show sized.node.loopExtent = nd.node.loopExtent
    exact hle
  · exact ⟨_, rfl, hle⟩

/-- Exact original plain nodes keep their measured record through the
coordinate phases. -/
private theorem XLEML_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := (XLEML_nonproxy_record h hcoordinate (by rw [hborder]; decide)).1
  have hxs := (XLEML_nonproxy_record h hcoordinate (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  exact hxs


/-- The extended footprint starts at the owner frame's right edge and has
nonnegative width in both sizing branches. -/
private theorem XLEML_fp_self_edges {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {t : Nat}
    (hFr : frameRect default cg run t = RouteImpl.boxRect run.proper run.xs run.ys t)
    (hslot : 0 ≤ cg.slot)
    (hw : ∀ l ∈ loopSizes cg.edges labels t cg.slot, 0 ≤ l.width) :
    (loopFootprintExt cg run labels t).x =
      (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w ∧
    0 ≤ (loopFootprintExt cg run labels t).w := by
  have hmono : ∀ (acc : Int), 0 ≤ acc → ∀ (ss : List LoopLabel),
      0 ≤ ss.foldl (fun w l => max w l.width) acc := by
    intro acc ha ss
    induction ss generalizing acc with
    | nil => exact ha
    | cons s rest ih =>
      simp only [List.foldl]
      exact ih _ (Int.le_trans ha (Int.le_max_left _ _))
  have hwide : (0 : Int) ≤ (loopSizes cg.edges labels t cg.slot).foldl
      (fun w l => max w l.width) 0 :=
    hmono 0 (Int.le_refl _) _
  have hfold : ∀ (acc : Int), 0 ≤ acc → ∀ (l : List Int),
      (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.foldl (· + ·) acc := by
    intro acc ha l hl
    induction l generalizing acc with
    | nil => exact ha
    | cons a rest ih =>
      simp only [List.foldl]
      exact ih _ (by have hha := hl a (List.mem_cons.mpr (Or.inl rfl)); omega)
        (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
  have hterm : ∀ q ∈ (loopSizes cg.edges labels t cg.slot).zipIdx.map
      (fun q => cg.slot * ((q.2 : Int) + 2) + q.1.width), (0 : Int) ≤ q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨_, hjlen, ha⟩ := List.mem_zipIdx hp
    have h1 : p.2 < (loopSizes cg.edges labels t cg.slot).length := by omega
    have hmem : p.1 ∈ loopSizes cg.edges labels t cg.slot := by
      have h2 : (loopSizes cg.edges labels t cg.slot)[p.2]? =
          some ((loopSizes cg.edges labels t cg.slot)[p.2]) :=
        List.getElem?_eq_getElem h1
      simp only [Nat.sub_zero] at ha
      rw [← ha] at h2
      exact List.mem_of_getElem? h2
    have hslot2 : (0 : Int) ≤ cg.slot * ((p.2 : Int) + 2) :=
      Int.mul_nonneg hslot (by omega)
    have hwp : (0 : Int) ≤ p.1.width := hw p.1 hmem
    omega
  unfold loopFootprintExt
  simp only [hFr]
  constructor
  · trivial
  · by_cases hex : run.exact.contains t = true
    · simp only [hex, ↓reduceIte]
      unfold Loops.exactExtent
      dsimp only
      split
      · exact hwide
      · have hnn : (0 : Int) ≤
            ((loopSizes cg.edges labels t cg.slot).length : Int) :=
          Int.natCast_nonneg _
        have h3 : (0 : Int) ≤ cg.slot *
            (2 * (((loopSizes cg.edges labels t cg.slot).length : Int)) + 1) :=
          Int.mul_nonneg hslot (by omega)
        omega
    · have hcon : run.exact.contains t = false := Bool.eq_false_iff.mpr hex
      simp only [hcon, Bool.false_eq_true, ↓reduceIte]
      unfold Loops.extent
      exact hfold 0 (Int.le_refl _) _ hterm
/-! Same-rank half of the exact loop-envelope miss, over exact runs.
Proved for border-0 owners in three directions (right, left, self); group-top
owners stay as the single named residual `XLEM_GroupOwnerMiss`. -/
/-- Same-rank half of `X_LoopEnvelopeMiss`: the extended footprint of a
self-loop edge misses every in-scope real box that shares the owner's
layer. Same binders as `X_LoopEnvelopeMiss` plus the same-layer premise. -/
def XLEM_SameRankMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Right side for plain owners: a box after a border-0 loop owner in the
same layer misses the extended footprint. Replay of `loopRes_sameLayer_holds`
over `componentRunX`. -/
def XLEM_PlainRightMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg.nodes.getD e.tail default).border = 0 →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v → pu < pv →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Left side: a box before a plain loop owner in the same layer misses the
extended footprint. Follows from `XB_orderedIntervals_holds` and the
footprint starting at the owner frame. -/
def XLEM_LeftMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg.nodes.getD e.tail default).border = 0 →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v → pv < pu →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Owner itself: the footprint of a plain loop owner misses the owner box.
The footprint starts where the owner frame ends. -/
def XLEM_OwnerSelfMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg.nodes.getD e.tail default).border = 0 →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu : Nat}, layer[pu]? = some e.tail → layer[pu]? = some v →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Named residual: a group-top loop owner. The footprint is bounded through
the group's right marker (`loopResTopReservation_holds` pattern); the replay
of that case over `componentRunX` is deferred. Covers every same-rank
position (left, right, and self): strictly narrower than the target, a single
fact, and true on every probe case (group-owner loops in
`ExactLoopEnvelopeLayerTProbe` are all disjoint). -/
def XLEM_GroupOwnerMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg.nodes.getD e.tail default).border ≠ 0 →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Owner itself, proved: the footprint of a plain loop owner misses the
owner box. -/
theorem XLEM_self_holds (exactIds : List String) : XLEM_OwnerSelfMiss exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 layer hlayer pu hpu hpv
  have htv : e.tail = v := Option.some.inj (hpu.symm.trans hpv)
  subst htv
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp hbd (List.mem_of_getElem? hk)
  have hltCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
    hbnd.1
  obtain ⟨nt, hnt⟩ : ∃ nt,
      (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some nt :=
    ⟨_, List.getElem?_eq_getElem hltCG⟩
  have hnb : nt.border = 0 := by
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default = nt := by
      rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    rw [← hget]
    exact hB0
  have hne2 : ((componentCandidate execution.graph comp candidate).nodes.getD e.tail
      default).border ≠ -2 := by
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default = nt := by
      rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    rw [hget]
    omega
  have hFrBox := plain_frame_eq_boxRect default _ run e.tail hv hne2
  obtain ⟨actual, hcoord, hpropT, _, _, _, _⟩ :=
    XLEML_original_plain_record hrun hnt hnb
  have hw : ∀ l ∈ loopSizes (componentCandidate execution.graph comp candidate).edges
      execution.measured e.tail
      (componentCandidate execution.graph comp candidate).slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hslot : 0 ≤ (componentCandidate execution.graph comp candidate).slot :=
    componentRunX_slot_nonneg hrun
  obtain ⟨e1, hW⟩ := XLEML_fp_self_edges hFrBox hslot hw
  have hBwEq : (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w = actual.node.w := by
    simp only [RouteImpl.boxRect, RouteImpl.nodeW, hpropT]
  have hdims := componentRunX_dims_nonneg hrun
  have hBW : (0 : Int) ≤ (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w := by
    rw [hBwEq]
    exact (hdims e.tail actual hpropT).1
  intro hmeet
  obtain ⟨hx, _hy⟩ := hmeet
  rw [e1] at hx
  omega
/-- Same-rank half: the self case is proved (`XLEM_self_holds`); the plain
right/left replays stay as narrow explicit hypotheses, and group-top owners
stay as the single named residual `XLEM_GroupOwnerMiss`. -/
theorem XLEM_sameRankMiss_holds (exactIds : List String)
    (hRight : XLEM_PlainRightMiss exactIds)
    (hLeft : XLEM_LeftMiss exactIds)
    (hGrp : XLEM_GroupOwnerMiss exactIds) :
    XLEM_SameRankMiss exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 layer hlayer pu pv hpu hpv
  by_cases hB0 : (cg.nodes.getD e.tail default).border = 0
  · by_cases hlt : pu < pv
    · exact hRight inp o res execution comp candidate run orderOptions cg k e v
        hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hlayer
        hpu hpv hlt
    · by_cases hgt : pv < pu
      · exact hLeft inp o res execution comp candidate run orderOptions cg k e v
          hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hlayer
          hpu hpv hgt
      · have heq : pu = pv := by omega
        subst heq
        exact XLEM_self_holds exactIds inp o res execution comp candidate run
          orderOptions cg k e v hcomp hcg hrun hk hloop hv hreal hscope0 hscope1
          hB0 hlayer hpu hpv
  · exact hGrp inp o res execution comp candidate run orderOptions cg k e v
      hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hlayer
      hpu hpv
