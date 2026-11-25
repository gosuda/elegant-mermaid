import Elegant.Layered.ForeignSideChainShapeProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Executed titled-edge endpoint bound.

Target (body of `BorderInnerTitledBoundResidual` in
`BorderInnerFoldProof`, written out in full so its owner can close that def
by `exact`): for the executed titled source
`titleReservations (sizeProperPorts P labeled)`, every edge endpoint is below
the source node count. The titled edges are those installed when title-copy
nodes are added (`titleReservations`); both `sizeProperPorts` and
`titleReservations` only rewrite/append nodes and leave edges definitionally
unchanged, so the bound reduces to endpoint validity of the executed
`normalize` output, transported through `addLabelNodes` (edges unchanged,
node count unchanged).

Execution evidence: the two executed stage equations `hn` (normalize) and
`hl` (label nodes) that the owner obtains from
`componentRun_ranked_source hrun`. No other execution hypothesis is needed;
in particular the side (`hside`), layer (`hpos`), and pass (`k`) evidence
that `foreignSideChainShape` takes are irrelevant to this construction-phase
fact, so they are not taken (an unused hypothesis would be a warning).

Probe: `proofs/wip/Probe/ShapeTitledBoundProbe.lean` checks the conclusion
on executed layouts with titled groups (1-2 `-2` anchors), nested groups,
edge labels, cell profile, and LR direction: `bad=0` on every run with
6-10 side markers present.
-/

/-- Endpoint validity of `normalize` output: every edge endpoint is below
the node count. This replays `NormalizeImpl.normalize_proper` but concludes
the `PInv` endpoint bounds (which that theorem discards in favour of the
span conclusion) together with the `PInv` node/rank length alignment. -/
theorem normalize_edges_bound {cg : Graph} {rr : RankImpl.RankResult} {p : Proper}
    (h : NormalizeImpl.normalize cg rr.ranks = .ok p) :
    ∀ e ∈ p.edges, e.tail < p.nodes.length ∧ e.head < p.nodes.length := by
  have hPInv : NormalizeImpl.PInv p := by
    unfold NormalizeImpl.normalize at h
    split at h
    · simp at h
    · next slot hslot =>
      split at h
      · next hc =>
        have hmem : ∀ q ∈ cg.edges.zipIdx, q.1.tail < cg.nodes.length ∧ q.1.head < cg.nodes.length ∧ 1 ≤ q.1.minLen := by
          intro q hq
          exact RankImpl.wellformed_spec hc.1 q.1 (RankImpl.mem_of_mem_zipIdx hq)
        have hP : NormalizeImpl.PInv { nodes := cg.nodes.map fun n => ⟨n, false, none, false⟩, edges := [], rank := rr.ranks, chains := [] } := by
          refine ⟨by simp [hc.2.1], ?_⟩
          intro e he
          simp at he
        exact NormalizeImpl.normalizeLoop_inv slot cg.nodes.length _ _ p hmem (by simp [hc.2.1]) hP h
      · simp at h
  intro e he
  obtain ⟨ht, hh, _⟩ := hPInv.2 e he
  rw [← hPInv.1] at ht hh
  exact ⟨ht, hh⟩

/-- Executed titled-edge endpoint bound: the titled edges (those of the
executed `titleReservations`/`sizeProperPorts` stage) never reach an
appended side marker, because their endpoints lie below the node count that
existed before the border fold. This is the body of
`BorderInnerTitledBoundResidual` for the executed source. -/
theorem borderInnerTitledBound_executed
    {P : Params} {cg : Graph} {labels : List MeasuredLabel}
    {rr : RankImpl.RankResult} {normalized labeled : Proper}
    (hn : NormalizeImpl.normalize cg rr.ranks = .ok normalized)
    (hl : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
    ∀ e ∈ (titleReservations (sizeProperPorts P labeled)).edges,
      e.tail < (titleReservations (sizeProperPorts P labeled)).nodes.length ∧
      e.head < (titleReservations (sizeProperPorts P labeled)).nodes.length := by
  intro e he
  have hE : (titleReservations (sizeProperPorts P labeled)).edges = labeled.edges := rfl
  have hEL : e ∈ labeled.edges := hE ▸ he
  have hEN : e ∈ normalized.edges := by
    have hEq := (Labels.addLabelNodes_metadata hl).1
    rw [hEq] at hEL
    exact hEL
  obtain ⟨ht, hh⟩ := normalize_edges_bound hn e hEN
  have hLL : normalized.nodes.length = labeled.nodes.length :=
    addLabelNodes_node_length hl
  have hSP : (sizeProperPorts P labeled).nodes.length = labeled.nodes.length :=
    sizeProperPorts_length P labeled
  have hT : labeled.nodes.length ≤ (titleReservations (sizeProperPorts P labeled)).nodes.length := by
    have hlen : (titleReservations (sizeProperPorts P labeled)).nodes.length =
        labeled.nodes.length + ((titleNodes (sizeProperPorts P labeled)).map copyF).length := by
      rw [titleReservations_nodes, List.length_append, List.length_map, hSP]
    omega
  omega

end Elegant.Layered.PipelineImpl
