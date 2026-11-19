import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.SizingFacts
import Elegant.Layered.Labels
import Elegant.Layered.Normalize
import Elegant.Layered.Rank
import Elegant.Layered.Order

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact plain-node path fact over `componentRunX`

Proves `XN_plainNodePathResidual_holds : XN_PlainNodePathResidual exactIds`
(the residual isolated in `ExactSideMarkerFactsProof.lean`): on a border-`0`
coordinate node of an executed exact run, `OrderImpl.nodePath` unfolds to the
node's cluster path. For non-dummy nodes this is `OrderImpl.nodePath_of_nondummy`;
for dummy nodes it is the `materializeDummyPaths` equation plus chain-endpoint
stability (endpoints are normalize-chain ends, hence non-dummy originals whose
records survive every stage to the prepared graph). Replay of
`SideMarkerPathsProof.plainNodePathEq` over `componentRunX`, following the
`XSc8a_pathEq` replay in `ExactC8aSpansProof.lean` (whose helpers are private
there, so file-prefixed copies live here).

Combined with the sibling `X6_runPathGroupsW_holds`
(`ExactRunPathGroupsProof.lean`: every cluster-path entry of an executed exact
run node is a group-role box), the `nodeKeys_path_group` transport, and the
`Compound.path` origin, this gives the member reading: `g` is on a plain
node's cluster path iff the node belongs to group `g`. The dummy case routes
through `OrderImpl.commonPath` and its membership fact
`commonPath_member_both`. The side-marker same-path fact used alongside this
residual is proved in `ExactSideMarkerFactsProof.lean` (`xsmf_samePath_of`).

Probe evidence: `proofs/wip/Probe/PlainNodePathTPathEq.lean` replays the
equation checker over `componentRunX` on seven inputs (sibling groups, nested
groups, self-loop, empty group, deep chain with a rank-spanning long edge,
zero-size fixed box with `exactIds ["G1"]` and `framedParents = false`,
ill-formed dangling-route input): 63 border-`0` checks with 12 dummy
border-`0` nodes, zero violations; the ill-formed input is rejected at prep
with `.domain` (vacuous, not a counterexample). No falsifying witness under
the stated premises was found, so the replay proceeds.

Nothing stays open: the residual is proved outright, with no new residual. -/

/-- A labeled original index keeps a non-dummy record through exact title
reservation, border insertion, and proxy clearing (copy of the private
`preparedNondummyOfLabeled` in `SideMarkerPathsProof`, via `XSc8a_preparedNondummy`
in `ExactC8aSpansProof`; file-unique prefix since those copies are private). -/
private theorem xpnpp_preparedNondummy {P : Params} {exact : List Nat}
    {labeled : Proper} {e : Nat} {ndL : ProperNode}
    (hlabeled : labeled.nodes[e]? = some ndL) (hdL : ndL.dummy = false) :
    ∃ pm : ProperNode,
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes[e]? = some pm ∧ pm.dummy = false := by

  have hsize : ∃ sized, (sizeProperPortsX P exact labeled).nodes[e]? = some sized ∧
      sized.dummy = false := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hlabeled,
      Option.map_some]
    split
    · exact ⟨_, rfl, hdL⟩
    · exact ⟨_, rfl, hdL⟩
  obtain ⟨sized, hsized, hdS⟩ := hsize
  have hlenS : e < (sizeProperPortsX P exact labeled).nodes.length :=
    (List.getElem?_eq_some_iff.mp hsized).1
  have htitle : (titleReservations (sizeProperPortsX P exact labeled)).nodes[e]? =
      some (titleF sized) := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hlenS)]
    simp [List.getElem?_map, hsized]
  have hdT : (titleF sized).dummy = false := by
    rw [(titleF_keys sized).1]; exact hdS
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hlenT : e < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map]
    omega
  have hborders : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[e]? = some (titleF sized) := by
    rw [hnodes, List.getElem?_append_left hlenT]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW)).nodes[e]? = some (clearF (titleF sized)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders, Option.map_some]
  exact ⟨_, hclear, by rw [(clearF_keys _).1]; exact hdT⟩

/-- Materialization preserves the cluster path at a non-dummy index (copy of
the private `matEndpointClusterPath` in `SideMarkerPathsProof`, via
`XSc8a_matEndpoint` in `ExactC8aSpansProof`; the statement is hook-independent). -/
private theorem xpnpp_matEndpoint {PREP : Proper} {e : Nat}
    {pm : ProperNode}
    (hprep : PREP.nodes[e]? = some pm) (hd : pm.dummy = false) :
    ((materializeDummyPaths PREP).nodes.getD e default).node.clusterPath =
      (PREP.nodes.getD e default).node.clusterPath := by
  have hmat : (materializeDummyPaths PREP).nodes[e]? = some pm := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
      hprep, Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]
  have h1 : (materializeDummyPaths PREP).nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hmat]
  have h2 : PREP.nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hprep]
  rw [h1, h2]

/-- Chain-endpoint path stability for the dummy case (second half of the
`XSc8a_pathEq` replay): a non-self-loop normalize chain's head/last endpoints
are non-dummy originals whose records survive to the prepared graph, so
materialization preserves their cluster paths. -/
private theorem xpnpp_endpointPaths {P : Params} {exact : List Nat} {cg : Graph}
    {ranks : List Int} {normalized labeled : Proper}
    {labels : List MeasuredLabel}
    (hnorm : NormalizeImpl.normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    {chain : List Nat} {v : Nat} (hmemC : v ∈ chain)
    {idx : Nat} (hidx : normalized.chains[idx]? = some chain)
    (hidxB : idx < cg.edges.length)
    {edge : Edge} (hedge : cg.edges[idx]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ((materializeDummyPaths (clearProxyExtents
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact
        labeled)) P.clusterBorderW))).nodes.getD
      (chain.headD v) default).node.clusterPath =
      ((clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD
        (chain.headD v) default).node.clusterPath ∧
    ((materializeDummyPaths (clearProxyExtents
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact
        labeled)) P.clusterBorderW))).nodes.getD
      (chain.getLastD v) default).node.clusterPath =
      ((clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD
        (chain.getLastD v) default).node.clusterPath := by
  obtain ⟨hanchor, hrest⟩ := (normalize_ok hnorm).2.2 idx hidxB edge hedge
  have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnorm).2
  have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
  have hbounds := RankImpl.wellformed_spec hwf edge hedgeMem
  obtain ⟨htailB, hheadB, _⟩ := hbounds
  have hself : ¬edge.tail = edge.head := hne
  simp only [hself, ↓reduceIte] at hrest
  obtain ⟨chl, hch, _, hhead, hlast, _⟩ := hrest
  have hcc : chl = chain := Option.some.inj (hch.symm.trans hidx)
  have hhead' : chain.head? = some edge.tail := by
    rw [← hcc]; exact hhead
  have hlast' : chain.getLast? = some edge.head := by
    rw [← hcc]; exact hlast
  have ehead : chain.headD v = edge.tail := by
    cases hc : chain with
    | nil => simp [hc] at hmemC
    | cons h t =>
      have h2 := hhead'; rw [hc] at h2
      simp only [List.head?_cons, Option.some.injEq] at h2
      exact h2
  have elast : chain.getLastD v = edge.head := by
    rw [List.getLastD_eq_getLast?, hlast', Option.getD_some]
  obtain ⟨nT, hnT⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
    ⟨_, List.getElem?_eq_getElem htailB⟩
  have hnormT : normalized.nodes[edge.tail]? =
      some ⟨nT, false, none, false⟩ :=
    normalize_node_record hnorm hnT
  have hlabT : labeled.nodes[edge.tail]? =
      some ⟨nT, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels hnormT rfl
  obtain ⟨pmT, hprepT, hdT2⟩ := xpnpp_preparedNondummy hlabT rfl
  obtain ⟨nH, hnH⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
    ⟨_, List.getElem?_eq_getElem hheadB⟩
  have hnormH : normalized.nodes[edge.head]? =
      some ⟨nH, false, none, false⟩ :=
    normalize_node_record hnorm hnH
  have hlabH : labeled.nodes[edge.head]? =
      some ⟨nH, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels hnormH rfl
  obtain ⟨pmH, hprepH, hdH2⟩ := xpnpp_preparedNondummy hlabH rfl
  refine ⟨?_, ?_⟩
  · rw [ehead]
    exact xpnpp_matEndpoint hprepT hdT2
  · rw [elast]
    exact xpnpp_matEndpoint hprepH hdH2

/-- On a border-`0` coordinate node of an executed exact run, `nodePath`
unfolds to the cluster path: replay of `SideMarkerPathsProof.plainNodePathEq`
over `componentRunX`. The pipeline premises (`measuredGraph`, `exactGraph`)
are not needed for the equation itself, so the proved statement is stronger
(fewer premises) than the residual asks. -/
theorem XN_plainNodePathResidual_holds (exactIds : List String) :
    XN_PlainNodePathResidual exactIds := by
  intro P inp _o _lines _measured _graph0 graph _h0 _h comp _hcomp candidate run
    _labels _orderOptions hrun v nd hlook hborder
  by_cases hd : nd.dummy = false
  · exact OrderImpl.nodePath_of_nondummy hlook hd
  · have hdT : nd.dummy = true := by
      cases h : nd.dummy with
      | false => exact absurd h hd
      | true => rfl
    obtain ⟨_, normalized, labeled, _, hnorm, hlabels, hcoord, _⟩ :=
      X_componentRun_ranked_source hrun
    have hcoordM : materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          (exactDecls exactIds inp) labeled)) P.clusterBorderW)) =
        run.coordinateProper := by
      exact hcoord
    have hlookM : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          (exactDecls exactIds inp) labeled)) P.clusterBorderW))).nodes[v]? =
        some nd := by
      rw [hcoordM]; exact hlook
    obtain ⟨mp, hmp, hdm, _, _, _⟩ :=
      materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW)) hlookM
    have hmpT : mp.dummy = true := hdm.symm.trans hdT
    have hpath : nd.node.clusterPath = OrderImpl.nodePath (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          (exactDecls exactIds inp) labeled)) P.clusterBorderW)) v := by
      have h := hlookM
      simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
        hmp, Option.map_some, hmpT, ↓reduceIte, Option.some.injEq] at h
      rw [← h]
      simp only [Nat.zero_add]
    rw [← hcoordM, hpath]
    have hchains : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          (exactDecls exactIds inp) labeled)) P.clusterBorderW))).chains =
        (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P (exactDecls exactIds inp)
            labeled)) P.clusterBorderW)).chains := rfl
    have hgetM : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          (exactDecls exactIds inp) labeled)) P.clusterBorderW))).nodes.getD v
        default = nd := by
      simp [List.getD_eq_getElem?_getD, hlookM]
    have hgetP : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp)
          labeled)) P.clusterBorderW)).nodes.getD v default = mp := by
      simp [List.getD_eq_getElem?_getD, hmp]
    unfold OrderImpl.nodePath
    dsimp only
    rw [hgetM, hdT, hgetP, hmpT, hchains]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases hfind : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp)
          labeled)) P.clusterBorderW)).chains.find?
        (fun chain => chain.contains v) with
    | none => rfl
    | some chain =>
      dsimp only
      have hmemC : v ∈ chain := by
        have hfv := List.find?_some hfind
        simpa only [List.contains_iff_mem] using hfv
      have hcmem : chain ∈ (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P (exactDecls exactIds inp)
            labeled)) P.clusterBorderW)).chains :=
        List.mem_of_find?_eq_some hfind
      have ePREP : (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P (exactDecls exactIds inp)
            labeled)) P.clusterBorderW)).chains = labeled.chains :=
        (OrderImpl.addClusterBorders_metadata _ _).2.1
      have hcNorm : chain ∈ normalized.chains := by
        have h1 := hcmem
        rw [ePREP, (Labels.addLabelNodes_metadata hlabels).2.2.1] at h1
        exact h1
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hcNorm
      have hidxB : idx < (componentCandidate graph comp candidate).edges.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hidx).1
        rwa [normalize_chains_length hnorm] at hlt
      obtain ⟨edge, hedge⟩ : ∃ e,
          (componentCandidate graph comp candidate).edges[idx]? = some e :=
        ⟨_, List.getElem?_eq_getElem hidxB⟩
      have hfact := (normalize_ok hnorm).2.2 idx hidxB edge hedge
      obtain ⟨hanchor, hrest⟩ := hfact
      by_cases hself : edge.tail = edge.head
      · simp only [hself, ↓reduceIte] at hrest
        have hempty : chain = [] := Option.some.inj (hidx.symm.trans hrest)
        rw [hempty] at hmemC
        simp at hmemC
      · have hne : edge.tail ≠ edge.head := hself
        obtain ⟨hclH, hclL⟩ :=
          xpnpp_endpointPaths hnorm hlabels hmemC hidx hidxB hedge hne
        rw [hclH, hclL]
end PipelineImpl
end Layered
end Elegant
