import Elegant.Layered.ExactBorderChainXAlignedProof
import Elegant.Layered.ExactBorderDivergeProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ForeignBorderEdgesNoncrossingProof
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-!
# Exact diverge-stability bridge: verdict and obstruction.

Question: does the plain ordering fact `ForeignBorderDivergeStable` imply its
exact twin `X_ForeignBorderDivergeStable exactIds`, and hence (with the closed
shape fact) `X_ForeignBorderChainXAligned exactIds` and
`XB_ForeignBorderChainXAligned exactIds`?

Verdict: the ordering stage of `componentRunX` is the same `orderWithBudget`
call as the plain `componentRun` (compare `ExactPipeline.componentRunX` with
`Pipeline.componentRun`): rank, normalize, label, size, order, cross. The two
order inputs differ only in node widths: `sizeProperPortsX` skips exact decls
while `sizeProperPorts` sizes every plain port, and both keep
(dummy, border, clusterPath) per index (`sizeProperPortsX_key`; title,
border-marker, proxy-extent, and dummy-path wrappers are shared). The order
stage itself never reads widths: `Valid`, `seedBest`, `sweepLayers`,
`crossCount`, `siblingOrders`, `nodePath`, `clusterIds`, `parentOf` consult only
lengths, ranks, edges, chains, decl, dummy, border, and clusterPath.

Even so, `x_foreignBorderDivergeStable_of_plain` from the plain hypothesis alone
is not proved here. Precise obstruction, three parts:

1. Graph-class mismatch. `ForeignBorderDivergeStable` quantifies over graphs
   with `measuredGraph ... = .ok graph` and runs with
   `componentRun ... = .ok run`. The exact goal quantifies over
   `exactGraph ... = .ok graph` outputs (fixed sizes need not be realizable as
   measured sizes) and `componentRunX` runs (reserved ranks shift ys/top and
   routes downstream). The plain hypothesis does not apply on its face.
2. Success transfer. Applying the plain fact to the measured-graph run on the
   same component needs that plain run to succeed with identical layers and
   order-input keys. Width-dependent downstream checks (`FramePorts.checked`,
   proxy spans, reserve shifts) can fail or move independently, so success of
   the exact run does not entail success of the plain run. This is isolated as
   the single residual `XDB_ExactPlainRunTransfer` below.
3. Order congruence. Even with a succeeding plain run, concluding equal layers
   needs a congruence lemma (key-agreeing propers order equally) that does not
   exist yet. Applying the plain fact also needs `comp ∈ components graph0`,
   which follows from components equality (edges and length proved here;
   constraint congruence still to show).

Probe evidence: `wip/Probe/ExactDivergeBridgeTOrderProbe.lean` runs the plain
and exact pipelines side by side on six inputs (flat huge, flat zero-size,
empty group, self-loop, nested huge, ill-formed exact id without fixed sizes).
On every succeeding component and candidate (0, 1, 2): both pipelines succeed
together, `components` coincide, `layersEq = true`, and order-input keys agree
(`keysEq = true`); the ill-formed input fails in `exactGraph` with
`.domain` as designed. So the transfer residual holds on every executed probe
and the width-independence half is confirmed; the proof gaps above remain.

Proved in this module:

* `xdb_exactGraph_edges`, `xdb_exactGraph_length`, `xdb_exactGraph_key`:
  `exactGraph` keeps edges, node count, and per-index
  (decl, border, clusterPath) — the components-transfer groundwork.
* `xdb_chainAligned_of_stableX`: `X_ForeignBorderChainXAligned` from
  `X_ForeignBorderDivergeStable` alone, discharging the shape premise with the
  closed `X_foreignSideChainShapeClosed_holds`. This narrows the `c8aChain`
  field from two premises to one.

Open: `X_ForeignBorderDivergeStable` itself, modulo exactly the residual
`XDB_ExactPlainRunTransfer`. `XB_ForeignBorderChainXAligned` is not stated as a
bridge: its path goes through ordered intervals and foreign-span facts that are
still open independently of stability.
-/

/-- `exactGraph` keeps the edge list. -/
theorem xdb_exactGraph_edges {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g graph : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok graph) :
    graph.edges = g.edges := by
  unfold exactGraph at h
  obtain ⟨nodes, _, hrest⟩ := bind_ok h
  have hgeq : graph = { g with nodes := nodes } := Except.ok.inj hrest.symm
  subst hgeq
  rfl

/-- `exactGraph` keeps the node count. -/
theorem xdb_exactGraph_length {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g graph : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok graph) :
    graph.nodes.length = g.nodes.length := by
  unfold exactGraph at h
  obtain ⟨nodes, hmap, hrest⟩ := bind_ok h
  have hgeq : graph = { g with nodes := nodes } := Except.ok.inj hrest.symm
  obtain ⟨hlen, _⟩ := mapM_getElem? _ _ _ hmap
  subst hgeq
  exact hlen

/-- `orientNode` keeps decl/border/clusterPath. -/
private theorem xdb_orientNode_key (d : Direction) (n : Node) :
    (orientNode d n).decl = n.decl ∧ (orientNode d n).border = n.border ∧
      (orientNode d n).clusterPath = n.clusterPath := by
  cases d <;> exact ⟨rfl, rfl, rfl⟩

/-- Exact-graph nodes keep decl/border/clusterPath of the source node. -/
theorem xdb_exactGraph_key {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g graph : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok graph)
    {i : Nat} {n : Node} (hn : graph.nodes[i]? = some n) :
    ∃ n0 : Node, g.nodes[i]? = some n0 ∧ n.decl = n0.decl ∧ n.border = n0.border ∧
      n.clusterPath = n0.clusterPath := by
  unfold exactGraph at h
  obtain ⟨nodes, hmap, hrest⟩ := bind_ok h
  have hgeq : graph = { g with nodes := nodes } := Except.ok.inj hrest.symm
  have hnodes : nodes[i]? = some n := by subst hgeq; exact hn
  obtain ⟨hlen, hrec⟩ := mapM_getElem? _ _ _ hmap
  have hi : i < g.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hnodes).1
    omega
  obtain ⟨n0, h0⟩ : ∃ n0, g.nodes[i]? = some n0 :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨b, hfb, hbnodes⟩ := hrec i n0 h0
  have hb : b = n := Option.some.inj (hbnodes.symm.trans hnodes)
  dsimp only at hfb
  cases hbx : inp.boxes[n0.decl]? with
  | none =>
    simp only [hbx] at hfb
    have hbn : b = n0 := (Except.ok.inj hfb.symm)
    exact ⟨n0, h0, by rw [← hb, hbn], by rw [← hb, hbn], by rw [← hb, hbn]⟩
  | some box =>
    simp only [hbx] at hfb
    by_cases hc : ((!exactIds.contains box.id &&
      !(box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true)
    · rw [ite_eq_left hc] at hfb
      have hbn : b = n0 := (Except.ok.inj hfb.symm)
      exact ⟨n0, h0, by rw [← hb, hbn], by rw [← hb, hbn], by rw [← hb, hbn]⟩
    · rw [ite_eq_right hc] at hfb
      cases hfind : inp.fixedSizes.find? (·.1 == box.id) with
      | none =>
        simp only [hfind] at hfb
        cases hfb
      | some fixed =>
        simp only [hfind] at hfb
        by_cases he1 : Loops.exactExtent P.slot
          (loopSizes g.edges measured n0.decl P.slot) < 0
        · rw [ite_eq_left he1] at hfb
          cases hfb
        · rw [ite_eq_right he1] at hfb
          generalize hsz : orientNode o.direction
            { n0 with w := fixed.2.w, h := fixed.2.h } = size at hfb
          by_cases he2 : I32_MAX < Loops.exactExtent P.slot
            (loopSizes g.edges measured n0.decl P.slot) ∨
            I32_MAX < size.w + 2 * Loops.exactExtent P.slot
              (loopSizes g.edges measured n0.decl P.slot)
          · rw [ite_eq_left he2] at hfb
            cases hfb
          · rw [ite_eq_right he2] at hfb
            have hbn : b = { size with loopExtent :=
              (Loops.exactExtent P.slot
                (loopSizes g.edges measured n0.decl P.slot)).toNat } :=
              Except.ok.inj hfb.symm
            obtain ⟨hd, hbdr, hp⟩ := xdb_orientNode_key o.direction
              { n0 with w := fixed.2.w, h := fixed.2.h }
            rw [hsz] at hd hbdr hp
            exact ⟨n0, h0, by rw [← hb, hbn]; exact hd,
              by rw [← hb, hbn]; exact hbdr, by rw [← hb, hbn]; exact hp⟩

/-- Chain alignment from X-stability alone: the side-chain shape half is closed,
so the `c8aChain` field needs exactly one remaining premise. -/
theorem xdb_chainAligned_of_stableX (exactIds : List String)
    (hstabX : X_ForeignBorderDivergeStable exactIds) :
    X_ForeignBorderChainXAligned exactIds :=
  X_foreignBorderChainXAligned_of_stable exactIds hstabX
    (X_foreignSideChainShapeClosed_holds exactIds)

/-- Transfer residual: every executed exact run is matched by a succeeding
plain run on the measured-graph candidate with identical layers and
order-input keys. Strictly narrower than `X_ForeignBorderDivergeStable` (it
says nothing about divergent order; together with the plain stability fact it
yields the exact twin). True on every executed probe in
`wip/Probe/ExactDivergeBridgeTOrderProbe.lean` (both-ok with equal layers and
keys on flat huge, flat zero-size, empty group, self-loop, and nested huge
inputs; ill-formed inputs fail before any run). -/
def XDB_ExactPlainRunTransfer (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {runX : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok runX →
    ∃ runP : Run,
      componentRun P (componentCandidate graph0 comp candidate) labels orderOptions = .ok runP ∧
      runP.layers = runX.layers ∧
      ∀ v : Nat,
        (runP.coordinateProper.nodes[v]?).map
            (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) =
          (runX.coordinateProper.nodes[v]?).map
            (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath))

end PipelineImpl
end Layered
end Elegant
