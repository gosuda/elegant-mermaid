import Elegant.Layered.ExactForeignBorderSpansProof

set_option autoImplicit false

/-!
# Exact foreign rank-pair anchors

Proves `XB_foreignRankPairAnchors_holds : XB_ForeignRankPairAnchors exactIds`
by replaying the plain `foreignRankPairAnchors` anchor construction over the
exact run: the titled top comes from `X_titled_marker_record`, the path-matched
bottom from `X_prepared_group_bottom` (no `hlines` needed), and the declaration
tails from `X_cg_group_box`. The shared run bundle is `X_cg_run_bundle`.

No open residual remains; this closes the single residual behind
`XB_foreignClusterRankSpans_holds`.

Probe: `proofs/wip/Probe/ExactC8aSpansTProbe.lean` checker G evaluates anchor
existence plus the run equation on executed runs: 81 checks, 0 violations over
siblings, nested, self-loop, empty-group, zero-size, and nested-only inputs
(the ill-formed input is rejected at prep).
-/

namespace Elegant.Layered.PipelineImpl

theorem XB_foreignRankPairAnchors_holds (exactIds : List String) :
    XB_ForeignRankPairAnchors exactIds := by
  intro P inp o lines measured graph0 graph hg0 hgX comp hcomp candidate run
    labels orderOptions hrun u w uNode wNode hu hw hbU hbW _hne
  obtain ⟨rr, labeled, hrr, hcoord, hkeys, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle hg0 hgX hcomp hrun
  have hlenEq :=
    X_titleReservations_node_rank_alignment (exact := exactDecls exactIds inp) P
      haligned
  obtain ⟨_, _, hpathU⟩ := X_cg_group_box hg0 hgX hu hbU
  obtain ⟨_, _, hpathW⟩ := X_cg_group_box hg0 hgX hw hbW
  have hlabU : labeled.nodes[u]? =
      some (⟨uNode, false, none, false⟩ : ProperNode) :=
    hrecords u uNode hu
  have hlabW : labeled.nodes[w]? =
      some (⟨wNode, false, none, false⟩ : ProperNode) :=
    hrecords w wNode hw
  have htopU : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[u]? =
      some (titleF (⟨uNode, false, none, false⟩ : ProperNode)) :=
    X_titled_marker_record (exact := exactDecls exactIds inp) hlabU (Or.inl hbU)
  have htopW : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[w]? =
      some (titleF (⟨wNode, false, none, false⟩ : ProperNode)) :=
    X_titled_marker_record (exact := exactDecls exactIds inp) hlabW (Or.inl hbW)
  have htopUmem : (titleF (⟨uNode, false, none, false⟩ : ProperNode), u) ∈
      (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopU
  have htopWmem : (titleF (⟨wNode, false, none, false⟩ : ProperNode), w) ∈
      (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopW
  have hbUtop : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.border
      = -2 := by
    rw [(titleF_keys _).2.1]; exact hbU
  have hbWtop : (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.border
      = -2 := by
    rw [(titleF_keys _).2.1]; exact hbW
  have hlastTopU : (titleF
      (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast?
      = some uNode.decl := by
    rw [show (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath
      = uNode.clusterPath from (titleF_keys _).2.2.1,
      hpathU, List.getLast?_append]
    simp
  have hlastTopW : (titleF
      (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast?
      = some wNode.decl := by
    rw [show (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath
      = wNode.clusterPath from (titleF_keys _).2.2.1,
      hpathW, List.getLast?_append]
    simp
  obtain ⟨botU, _, hfindU⟩ :=
    X_prepared_group_bottom hg0 hgX hcomp hrun hcoord hkeys hready hrecords hu
      hbU
  obtain ⟨botW, _, hfindW⟩ :=
    X_prepared_group_bottom hg0 hgX hcomp hrun hcoord hkeys hready hrecords hw
      hbW
  have htopPathU : (titleF
      (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath =
      uNode.clusterPath :=
    (titleF_keys _).2.2.1
  have htopPathW : (titleF
      (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath =
      wNode.clusterPath :=
    (titleF_keys _).2.2.1
  have hbotU : ((titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
      (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
        entry.1.node.clusterPath ==
          (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath) =
        some botU) := by
    rw [htopPathU]; exact hfindU
  have hbotW : ((titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
      (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
        entry.1.node.clusterPath ==
          (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath) =
        some botW) := by
    rw [htopPathW]; exact hfindW
  exact ⟨labeled, rr, hcoord, haligned, hkeys, hrr, hranks, hrecords, hlenEq,
    (titleF (⟨uNode, false, none, false⟩ : ProperNode), u), botU,
    htopUmem, hbUtop, hlastTopU, hbotU,
    (titleF (⟨wNode, false, none, false⟩ : ProperNode), w), botW,
    htopWmem, hbWtop, hlastTopW, hbotW⟩

end Elegant.Layered.PipelineImpl
