import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactCaptionCapBandProof
import Elegant.Layered.ExactCaptionSelfBottomProof
import Elegant.Layered.ExactCaptionSelfNarrowProof
import Elegant.Layered.ExactPlainAncestorImpossibleProof
import Elegant.Layered.ExactPlainNodePathProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The executed title band with the same local admission premises as its
part-level consumer. -/
def X_RunTitleBandClearXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate execution.graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    ∀ (raw : Nat × Rect),
    raw ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run →
    raw.1 = v →
    ∀ {w : Nat} {nodeW : Node} {k : Nat} {fBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW →
    nodeW.border = 0 →
    comp[w]? = some k →
    inp.boxes[k]? = some fBox →
    fBox.exclusive = true →
    Disjoint (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w)
      { raw.2 with
        w := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).w
        h := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).h }

private theorem measuredSource {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {key : Nat} {node : Node} (hnode : execution.graph.nodes[key]? = some node) :
    ∃ original, execution.graph0.nodes[key]? = some original ∧
      node.border = original.border ∧ node.decl = original.decl := by
  have hkey := (List.getElem?_eq_some_iff.mp hnode).1
  rw [exactGraph_length execution.graph_eq] at hkey
  have horig : execution.graph0.nodes[key]? = some execution.graph0.nodes[key] :=
    List.getElem?_eq_getElem hkey
  obtain ⟨out, hout, hb, _, hd⟩ := exactGraph_node_key execution.graph_eq horig
  have he := Option.some.inj (hout.symm.trans hnode)
  exact ⟨_, horig, he ▸ hb, he ▸ hd⟩

private theorem groupDeclLookup {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} {candidate v : Nat} {group : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some group)
    (hgroup : group.border = -2) : execution.graph.nodes[group.decl]? = some group := by
  obtain ⟨index, _, hsrc⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨base, hbase, hborder, hdecl⟩ := measuredSource execution hsrc
  have hindex := (measuredGraph_group_origin execution.graph0_eq hbase
    (hborder.symm.trans hgroup)).1
  rw [hdecl, hindex]
  exact hsrc

private theorem plainDeclLookup {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactTitleRunContext exactIds inp o)
    {comp : List Nat} {candidate w key : Nat} {node : Node} {box : ModelBox}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[w]? = some node)
    (hplain : node.border = 0) (hcompKey : comp[w]? = some key)
    (hbox : inp.boxes[key]? = some box) : execution.graph.nodes[node.decl]? = some node := by
  have hkey := (List.getElem?_eq_some_iff.mp hbox).1
  obtain ⟨nodes, edges, titles, hprepared, hlen, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hbaseLen : key < nodes.length := by
    rw [hlen, execution.lines_len]
    exact hkey
  have hgraphKey : key < execution.graph.nodes.length := by
    refine Nat.lt_of_lt_of_le hbaseLen ?_
    rw [exactGraph_length execution.graph_eq, hprepared]
    exact Compound.prepare_nodes_length_ge _ execution.params.clusterPad titles
      ⟨nodes, edges, execution.params.slot⟩
  have hsrc : execution.graph.nodes[key]? = some node := by
    have h := hnode
    rw [componentCandidate_nodes] at h
    simp only [componentGraph, List.getElem?_map, hcompKey, Option.map_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgraphKey, Option.getD_some,
      Option.some.injEq] at h
    rw [List.getElem?_eq_getElem hgraphKey, h]
  obtain ⟨base, hbase, hb, hd⟩ := measuredSource execution hsrc
  rw [hprepared] at hbase
  obtain ⟨_, hchanged, _⟩ := fixedSizes_path_index inp hbox
  have hdecl := (prepare_plain_path_origin _ _ _ _ hmetadata hbase
    (hb.symm.trans hplain) hchanged).1
  rwa [hd, hdecl]

/-- A member is below the title copy's reservation band. For a foreign plain
frame, the measured caption fits inside the group frame and the exact side
markers and rank bands separate that frame from the plain frame. Both
arguments use closed intervals as separators, including for zero-size boxes. -/
theorem componentRunX_title_clear_of_plain
    {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactTitleRunContext exactIds inp o)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) {stored : Rect}
    (hraw : (v, stored) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    {w k : Nat} {nodeW : Node} {fBox : ModelBox}
    (hwNode : (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW)
    (hwPlain : nodeW.border = 0)
    (hcompW : comp[w]? = some k) (hbox : inp.boxes[k]? = some fBox) :
    Disjoint (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w)
      (transportCaption execution.params o execution.lines comp v stored) := by
  have hne : nd.decl ≠ nodeW.decl := by
    intro he
    have hg := groupDeclLookup execution hnode hgroup
    rw [he] at hg
    have hp := plainDeclLookup execution hwNode hwPlain hcompW hbox
    have hb := congrArg Node.border (Option.some.inj (hg.symm.trans hp))
    omega
  cases hpath : nodeW.clusterPath.contains nd.decl with
  | true =>
    exact componentRunX_title_clear_of_plain_member execution hcomp hrun hnode hgroup
      hwNode hwPlain hpath
      (componentRunX_title_bottom_le_rank_band execution hcomp hrun hraw hnode hgroup)
  | false =>
    have hreverse : nd.clusterPath.contains nodeW.decl = false := by
      apply Bool.eq_false_iff.mpr
      exact exactPlainAncestorImpossible_holds exactIds execution.graph0_eq execution.graph_eq
        execution.lines_len hwf hfp hcomp hnode hgroup hwNode hwPlain hne
    have hframes := XN_foreignNonGroupSpansClear_holds exactIds
      (XN_bracketMarkersAtRank_holds exactIds)
      (XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds))
      (XN_sideMarkerSpanAligned_of_chain exactIds (X_foreignBorderChainXAligned_framed exactIds))
      execution.graph0_eq execution.graph_eq execution.lines_len hwf hfp hcomp hrun
      hnode hwNode hgroup (by omega) hne hpath hreverse
    obtain ⟨hleft, hright⟩ :=
      componentRunX_title_inside_frame_x execution hcomp hrun hraw hnode hgroup
    have hrawY := componentTitles_y_eq_frame hraw
    have hpad := checkedParams_clusterPad_pos execution.checked
    have hheight := componentRunX_title_height_lt_frame execution hcomp hrun hnode hgroup
    have hty : (transportCaption execution.params o execution.lines comp v stored).y =
        stored.y := rfl
    have hth : (transportCaption execution.params o execution.lines comp v stored).h =
        (transportCapSize execution.params o execution.lines comp v).2 := rfl
    have hcontain : (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run v).Contained (transportCaption execution.params o execution.lines comp v stored) :=
      ⟨by omega, by omega, by omega, by omega⟩
    exact (Disjoint.comm _ _).mp (disjoint_of_sub_disjoint hcontain hframes)

theorem x_runTitleBandClearXW_holds (exactIds : List String) :
    X_RunTitleBandClearXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro v nd hnode hgroup raw hraw hrawIndex w nodeW k fBox hwNode hwPlain hcompW hbox _hex
  obtain ⟨i, stored⟩ := raw
  change i = v at hrawIndex
  subst i
  exact componentRunX_title_clear_of_plain execution.exactTitleContext hwf hfp
    hcomp hrun hnode hgroup hraw hwNode hwPlain hcompW hbox

end Elegant.Layered.PipelineImpl
