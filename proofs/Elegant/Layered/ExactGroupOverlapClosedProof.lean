import Elegant.Layered.BracketInsideStructuralFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactGroupOverlapPlainGapProof
import Elegant.Layered.ExactGroupOverlapTitleGapProof
import Elegant.Layered.ForeignNonGroupSpansProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem classify_group_overlap_target {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {v : Nat} {target : ProperNode} (htarget : run.proper.nodes[v]? = some target)
    (hreal : RouteImpl.IsReal run.proper v) :
    (∃ n : Node, (componentCandidate execution.graph comp candidate).nodes[v]? = some n ∧
      n.border = 0) ∨ target.node.border = 3 ∨ target.node.h = 0 := by
  obtain ⟨_, labeled, _, hcoord, hkeys, _, hrecords, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨_, _, _, q, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨_, _, hlen, _, htransport, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hv : v < run.coordinateProper.nodes.length := by
    have hv := (List.getElem?_eq_some_iff.mp htarget).1
    rwa [hnodes, hlen] at hv
  obtain ⟨coordinate, hcoordinate⟩ : ∃ nd, run.coordinateProper.nodes[v]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  obtain ⟨out, hout, hdOut, hbOut, hhOut⟩ := htransport v coordinate hcoordinate
  rw [← hnodes, htarget] at hout
  have heqOut : out = target := Option.some.inj hout.symm
  subst out
  rw [← hcoord] at hcoordinate
  unfold coordinateGraphX at hcoordinate
  obtain ⟨cleared, hcleared, hdCoord, hbCoord, hhCoord, _⟩ := materialize_lookup _ hcoordinate
  rw [clearProxyExtents_nodes, List.getElem?_map] at hcleared
  obtain ⟨before, hbefore, hclear⟩ := Option.map_eq_some_iff.mp hcleared
  have hclearKeys := clearF_keys before
  rw [hclear] at hclearKeys
  have hdBefore := hdOut.trans (hdCoord.trans hclearKeys.1)
  have hbBefore := hbOut.trans (hbCoord.trans hclearKeys.2.1)
  have hhBefore := hhOut.trans (hhCoord.trans hclearKeys.2.2.2)
  let titled := titleReservations (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)
  change (OrderImpl.addClusterBorders titled execution.params.clusterBorderW).nodes[v]? =
    some before at hbefore
  obtain ⟨extra, hnodesExtra, hside⟩ :=
    addClusterBorders_extra_height titled execution.params.clusterBorderW
  rw [hnodesExtra] at hbefore
  by_cases hvTitled : v < titled.nodes.length
  · rw [List.getElem?_append_left hvTitled] at hbefore
    have htitled : (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[v]? = some before := hbefore
    rcases X_titled_node_origin hkeys htitled with
      ⟨source, hsource, hdSource, _, _⟩ | ⟨_, hbTitle⟩
    · rcases hkeys v source hsource with ⟨n, hn, _, _, _⟩ | ⟨hdDummy, _, _⟩
      · rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq hn).1 with
          hplain | hproxyBorder
        · exact Or.inl ⟨n, hn, hplain⟩
        · let marker : ProperNode := ⟨n, false, none, false⟩
          have hmarker : labeled.nodes[v]? = some marker := hrecords v n hn
          have hmarked := X_titled_marker_record (P := execution.params)
            (exact := exactDecls exactIds inp) hmarker hproxyBorder
          have heqMarker : before = titleF marker := Option.some.inj (htitled.symm.trans hmarked)
          have hhMarker : before.node.h = 0 := by
            rw [heqMarker]
            exact (titleF_keys marker).2.2.2 hproxyBorder
          exact Or.inr (Or.inr (hhBefore.trans hhMarker))
      · have hcontradiction := hdDummy.symm.trans
          ((hdBefore.trans hdSource).symm.trans (hreal target htarget))
        cases hcontradiction
    · exact Or.inr (Or.inl (hbBefore.trans hbTitle))
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hvTitled)] at hbefore
    exact Or.inr (Or.inr (hhBefore.trans (hside before (List.mem_of_getElem? hbefore)).2.2))

/-- The group-loop overlap miss for one successful well-formed framed execution,
with the same in-scope, other-rank real targets as `XLEM_GroupOverlapMiss`. -/
theorem XLEM_groupOverlapMiss_holdsW (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    ∀ (comp : List Nat) (candidate : Nat) (run : Run)
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
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →
    (cg.nodes.getD e.tail default).border = -2 →
    max (loopFootprintExt cg run execution.measured e.tail).y
        (RouteImpl.boxRect run.proper run.xs run.ys v).y <
      min ((loopFootprintExt cg run execution.measured e.tail).y +
        (loopFootprintExt cg run execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
          (RouteImpl.boxRect run.proper run.xs run.ys v).h) →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  intro comp candidate run orderOptions cg k e v hcomp hcg hrun hedge hself hv hreal
    _hscope0 _hscope1 _hrank hbdr hyov
  subst cg
  obtain ⟨target, htarget⟩ : ∃ target, run.proper.nodes[v]? = some target :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  rcases classify_group_overlap_target execution hcomp hrun htarget hreal with
    ⟨n, hn, hplain⟩ | htitle | hzero
  · exact rect_disjoint_of_x (xlem_groupOverlapForeignGap_plain exactIds execution hwf hframed
      hcomp rfl hrun hedge hself hbdr hn hplain hyov)
  · have hbound := candidate_edge_endpoints_bounded_general execution.graph comp candidate
      hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)
    obtain ⟨owner, howner⟩ : ∃ owner,
        (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some owner :=
      ⟨_, List.getElem?_eq_getElem hbound.1⟩
    have hgroup : owner.border = -2 := by
      simpa only [List.getD_eq_getElem?_getD, howner, Option.getD_some] using hbdr
    exact rect_disjoint_of_x (componentRunX_groupLoop_title_horizontal_gap execution hwf hframed
      hcomp hrun hedge hself howner hgroup htarget htitle hyov)
  · have hh : (RouteImpl.boxRect run.proper run.xs run.ys v).h = 0 := by
      change RouteImpl.nodeH run.proper v = 0
      simpa only [RouteImpl.nodeH, htarget] using hzero
    have himpossible : False := by omega
    exact himpossible.elim

end Elegant.Layered.PipelineImpl
