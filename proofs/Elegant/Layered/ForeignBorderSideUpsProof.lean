import Elegant.Layered.ForeignBorderAlignRankProof
import Elegant.Layered.BorderChainPickFacts
import Elegant.Layered.BorderChainPickExecuted

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Foreign border side chains form single alignment blocks.

`ForeignBorderSideUps` (`ForeignClusterFactsProof`) is the alignment-phase
residual behind `ForeignBorderSpansSeparated`: along one side border chain of
one declaration (the `border = -1` or `border = 1` markers of one declaration
on consecutive ranks), each marker's upper-neighbour pick in the alignment
pass is its chain predecessor, so the chain forms one alignment block
(`borderChainBlock_of_ups` consumes exactly this).

The chain edges are the border chain edges added by
`OrderImpl.addClusterBorders` (`borderLinks` pairing consecutive same-side
pairs of one anchor), duplicated by `CoordsImpl.borderAlignment` between
adjacent layers. A side marker's only incident context edges are these
parallel chain edges, so it has exactly one upper neighbour (its chain
predecessor) and the median pick is forced through it.
-/

/-- The executed side chain: every marker of `side`/`decl` carried by the
executed `coordinateProper`, in layer order. -/
def sideChainNodes (P : Params) (run : Run) (side : Int) (decl : Nat) : List Nat :=
  run.layers.flatten.filter fun v =>
    match run.coordinateProper.nodes[v]? with
    | some na =>
      na.node.border == side &&
        (na.node.w == P.clusterBorderW && na.node.clusterPath.getLast? == some decl)
    | none => false

/-- The pass processing order of the side chain (ascending `(rank, pos)` of
the executed cluster context), the order in which `alignAll` processes it. -/
def sideOrdered (P : Params) (run : Run) (pos : Array Nat) (k : Nat)
    (side : Int) (decl : Nat) : List Nat :=
  (sideChainNodes P run side decl).mergeSort
    (keyLe
      (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k))

/-- Membership in the executed side chain is exactly the marker
characterization of `ForeignBorderSideUps`. Coverage (every matching node
lies on the executed layers) comes from the executed `checkLayers`. -/
theorem mem_sideChainNodes {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers =
      .ok pos)
    {a : Nat} :
    a ∈ sideChainNodes P run side decl ↔
      ∃ na, run.coordinateProper.nodes[a]? = some na ∧
        na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
        na.node.clusterPath.getLast? = some decl := by
  unfold sideChainNodes
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hpred⟩
    cases hna : run.coordinateProper.nodes[a]? with
    | none => simp [hna] at hpred
    | some na =>
      simp only [hna, Bool.and_eq_true, beq_iff_eq] at hpred
      obtain ⟨hb, hw, hlast⟩ := hpred
      exact ⟨na, rfl, hb, hw, hlast⟩
  · rintro ⟨na, hna, hb, hw, hlast⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
      obtain ⟨pos', hpos'⟩ := hlp
      obtain ⟨_, _, hcov⟩ := CoordsImpl.layerPositions_spec hpos'
      have hlen : (CoordsImpl.borderAlignment run.coordinateProper run.layers).nodes =
          run.coordinateProper.nodes := rfl
      have hlt : a < (CoordsImpl.borderAlignment run.coordinateProper run.layers).nodes.length := by
        rw [hlen]
        exact (List.getElem?_eq_some_iff.mp hna).1
      exact hcov a hlt
    · have e1 : (na.node.border == side) = true := by simp [hb]
      have e2 : (na.node.w == P.clusterBorderW) = true := by simp [hw]
      have e3 : (na.node.clusterPath.getLast? == some decl) = true := by simp [hlast]
      simp [hna, e1, e2, e3]


/-! ## Executed contexts and proved chain facts -/

/-- The border-aligned proper graph of the executed run
(`CoordsImpl.borderAlignment` only appends edges; nodes are unchanged). -/
def sideBase (run : Run) : Proper :=
  CoordsImpl.borderAlignment run.coordinateProper run.layers

/-- The executed pass context for pass `k`. -/
def sideCtx (P : Params) (run : Run) (pos : Array Nat) (k : Nat) : CoordsImpl.Ctx :=
  CoordsImpl.clusterCtx P.nodeGap P.clusterPad (sideBase run) run.layers
    (CoordsImpl.typeOneConflicts (sideBase run) pos) k

/-- The pass order is the processing order by definition. -/
theorem sideOrdered_ctx (P : Params) (run : Run) (pos : Array Nat) (k : Nat)
    (side : Int) (decl : Nat) :
    OrderedByCtx (sideCtx P run pos k) (sideChainNodes P run side decl)
      (sideOrdered P run pos k side decl) := by
  rfl

/-- The side chain inherits nodup from the executed layer cover. -/
theorem sideChainNodes_nodup {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    (sideChainNodes P run side decl).Nodup := by
  have hflat : run.layers.flatten.Nodup := by
    obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
    obtain ⟨pos', hpos'⟩ := hlp
    obtain ⟨hnd, _, _⟩ := CoordsImpl.layerPositions_spec hpos'
    exact hnd
  exact List.Sublist.nodup List.filter_sublist hflat

/-- Every side-chain node lies on the executed layers. -/
theorem sideChainNodes_flat {P : Params} {run : Run} {side : Int} {decl : Nat}
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl) :
    v ∈ run.layers.flatten :=
  (List.mem_filter.mp hv).1

/-- Every side-chain node carries a border side sign: the characterization
forces `border = side` and the hypothesis fixes `side = ±1`. -/
theorem sideChain_border_val {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat}
    (hside : side = -1 ∨ side = 1)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl) :
    ((sideBase run).nodes.getD v default).node.border = -1 ∨
      ((sideBase run).nodes.getD v default).node.border = 1 := by
  have hpos' : CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers =
      .ok pos := hpos
  obtain ⟨na, hna, hb, _, _⟩ := (mem_sideChainNodes hpos').mp hv
  have hget : (sideBase run).nodes[v]? = some na := by
    show (CoordsImpl.borderAlignment run.coordinateProper run.layers).nodes[v]? = some na
    exact hna
  have hgetD : (sideBase run).nodes.getD v default = na :=
    borderEnv_getD_of_get? hget
  rw [hgetD, hb]
  exact hside

/-! ## Residuals: border-construction shape and alignment-fold bound

The `BorderChainUps` conclusion needs two facts about the executed run that
are not yet proved. Both are pinned to the same three execution equations
as `ForeignBorderSideUps` (they take the executed `run` and its layer-check
`pos`), each is about one phase, and each is strictly simpler than the
`up`-pointer goal they feed.

Probe evidence (evaluation of the real `componentRun` pipeline, since removed):
five inputs (nested groups with cross-boundary edges, three-level nesting,
sibling groups with crossing member edges, diamond through a group, sibling
LR) times every group declaration, side, and pass `k < 4` give 80 nonempty
side chains. On all of them: the head has `up = none` and every later marker
has `up = some` predecessor; `chainPred` agrees; every non-head marker has
exactly two parallel upper edges (its chain predecessor through the
`borderLinks` synthetic and the `borderAlignment` pair); the running
`foldLast` bound holds at every non-head marker; cluster paths are uniform
within each chain. The purely geometric sufficient condition (every upper
neighbour of every layer-prefix node sits left of the predecessor) fails on
30 of the 80 chains while the conclusion still holds, so the fold residual
below is the pick property (which accounts for marking and `last`-gating),
not the geometric condition.
-/
/-- Border-construction residual (one phase: the `OrderImpl.addClusterBorders`
side pairs duplicated by `CoordsImpl.borderAlignment` on the executed run).
The side set of one declaration has the occurring-chain rank shape (at most
one node per rank, no rank gap between neighbours in rank order, shared cluster
path) and its context edges are the border-chain edges: every edge touching
a chain node reaches another chain node, and rank-adjacent chain nodes are
joined by an edge. The old all-pairs `rank_adj` (any two distinct nodes on
adjacent ranks) is false on real chains of length three or more and is
replaced by `rank_consec` mirroring `OccurringBorderChain`. -/
structure ForeignSideChainShape (P : Params) (run : Run) (side : Int) (decl : Nat)
    (pos : Array Nat) (k : Nat) : Prop where
  rank_inj : ∀ u ∈ sideChainNodes P run side decl,
    ∀ w ∈ sideChainNodes P run side decl,
    (sideCtx P run pos k).rank[u]! = (sideCtx P run pos k).rank[w]! → u = w
  rank_consec : ∀ u ∈ sideChainNodes P run side decl,
    ∀ v ∈ sideChainNodes P run side decl,
    (sideCtx P run pos k).rank[u]! < (sideCtx P run pos k).rank[v]! →
    (∀ w ∈ sideChainNodes P run side decl,
      ¬ ((sideCtx P run pos k).rank[u]! < (sideCtx P run pos k).rank[w]! ∧
        (sideCtx P run pos k).rank[w]! < (sideCtx P run pos k).rank[v]!)) →
    (sideCtx P run pos k).rank[u]! + 1 = (sideCtx P run pos k).rank[v]!
  path_consec : ∀ i : Nat, i + 1 < (sideChainNodes P run side decl).length →
    ((sideBase run).nodes.getD (sideChainNodes P run side decl)[i]! default).node.clusterPath =
      ((sideBase run).nodes.getD
        (sideChainNodes P run side decl)[i + 1]! default).node.clusterPath
  incident_border : ∀ v ∈ sideChainNodes P run side decl, ∀ e : Nat,
    e < (sideCtx P run pos k).edges.size →
    ((sideCtx P run pos k).edges[e]!.tail = v ∨
      (sideCtx P run pos k).edges[e]!.head = v) →
    CoordsImpl.borderChain (sideBase run) (sideCtx P run pos k).edges[e]! = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd (sideCtx P run pos k).edges[e]! v = u ∧ u ≠ v
  consec_edge : ∀ v ∈ sideChainNodes P run side decl,
    ∀ w ∈ sideChainNodes P run side decl,
    (sideCtx P run pos k).rank[v]! + 1 = (sideCtx P run pos k).rank[w]! →
    ∃ e : Nat, e < (sideCtx P run pos k).edges.size ∧
      (((sideCtx P run pos k).edges[e]!.head = v ∧
        (sideCtx P run pos k).edges[e]!.tail = w) ∨
        ((sideCtx P run pos k).edges[e]!.tail = v ∧
          (sideCtx P run pos k).edges[e]!.head = w))

/-- Alignment-fold residual (one phase: the `CoordsImpl.alignLayer` fold on
the executed pass context). At each non-head chain node, every alignment
pick made while processing the layer prefix before the node targets a
position strictly left of the chain predecessor's position. This is exactly
the `prefix_pick_left` field of `ExecutedChainFacts`; it implies the running
`last` at the node's fold point is below the predecessor position
(`lastLtPred_of_executedChainFacts`), which forces the median pick onto the
predecessor. Its `foldLast` consequence held on all 80 probe chains. -/
def ForeignSideFoldBound (P : Params) (run : Run) (side : Int) (decl : Nat)
    (pos : Array Nat) (k : Nat) : Prop :=
  ∀ v ∈ sideChainNodes P run side decl, ∀ pred : Nat,
    chainPred (sideCtx P run pos k) (sideChainNodes P run side decl) v = some pred →
    ∀ x ∈ ((sideCtx P run pos k).layers.getD ((sideCtx P run pos k).rank[v]!) []).take
      ((sideCtx P run pos k).pos[v]!),
    ∀ last : Int, ∀ w : Nat,
      CoordsImpl.alignPick (sideCtx P run pos k) x last = some w →
        (((sideCtx P run pos k).pos[w]! : Int) <
          ((sideCtx P run pos k).pos[pred]! : Int))

/-! ## Assembly: the side chain is one alignment block -/

/-- The side chain lies on the pass layers: `passLayers` only permutes. -/
theorem sideChainNodes_flat_ctx {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat} {k : Nat}
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl) :
    v ∈ (sideCtx P run pos k).layers.flatten := by
  have hmem : v ∈ run.layers.flatten := sideChainNodes_flat hv
  have hctx : (sideCtx P run pos k).layers = CoordsImpl.passLayers run.layers k := rfl
  rw [hctx]
  exact (CoordsImpl.passLayers_perm run.layers k).mem_iff.mpr hmem

/-- `ForeignBorderSideUps` from the two residuals: the shape residual builds
`OccurringBorderChain` and four of the five `ExecutedChainFacts` fields
(the fifth is the fold residual); the proved pipeline
`borderChainPickFacts_of_executedChainFacts` / `borderChainPick_of_facts` /
`borderChainUps_of_pick` turns them into `BorderChainUps`. -/
theorem foreignBorderSideUps_of
    (hshape : ∀ {P : Params} {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
      {k : Nat},
      side = -1 ∨ side = 1 → k < 4 →
      CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos →
      ForeignSideChainShape P run side decl pos k)
    (hfold : ∀ {P : Params} {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
      {k : Nat},
      side = -1 ∨ side = 1 → k < 4 →
      CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos →
      ForeignSideFoldBound P run side decl pos k) :
    ForeignBorderSideUps := by
  intro P inp o lines graph hgraph _hlines _hwf _hframed comp hcomp candidate run labels orderOptions hrun
    decl side hside k hk pos hpos
  have hpos' : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos := hpos
  refine ⟨sideChainNodes P run side decl, sideOrdered P run pos k side decl,
    ?_, ?_⟩
  · intro a
    exact mem_sideChainNodes hpos
  · intro hL
    have hsh : ForeignSideChainShape P run side decl pos k :=
      hshape hside hk hpos'
    have hfo : ForeignSideFoldBound P run side decl pos k :=
      hfold hside hk hpos'
    have hocc : OccurringBorderChain (sideCtx P run pos k)
        (sideChainNodes P run side decl) :=
      ⟨sideChainNodes_nodup (P := P) (run := run) (side := side) (decl := decl) hpos',
        fun v hv => sideChainNodes_flat_ctx hv, hsh.rank_inj, hsh.rank_consec⟩
    have hF : ExecutedChainFacts (sideBase run) (sideCtx P run pos k)
        (sideChainNodes P run side decl) :=
      ⟨fun v hv => sideChain_border_val hside hpos' hv, hsh.path_consec,
        hsh.incident_border, hsh.consec_edge, hfo⟩
    have hedges : (sideCtx P run pos k).edges.size = (sideBase run).edges.length ∧
        ∀ i, i < (sideBase run).edges.length →
          (sideCtx P run pos k).edges[i]! = (sideBase run).edges[i]! :=
      executedClusterCtx_edges
    have hmarked : (sideCtx P run pos k).marked =
        CoordsImpl.typeOneConflicts (sideBase run) pos := rfl
    have hE : CoordsImpl.EdgeOK (sideCtx P run pos k) :=
      (Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos').2
    have hpickFacts : BorderChainPickFacts (sideCtx P run pos k)
        (sideChainNodes P run side decl) hocc :=
      borderChainPickFacts_of_executedChainFacts hF hedges hmarked hE
    have hpick : BorderChainPick (sideCtx P run pos k)
        (sideChainNodes P run side decl) hocc :=
      borderChainPick_of_facts hpickFacts
    have hord := sideOrdered_ctx P run pos k side decl
    exact borderChainUps_of_pick hL hocc hord hpick

/-- In a successful framed run, every two same-side markers of one declaration
share one closed `x`-interval, given the chain shape and fold bound. -/
theorem foreignBorderChainXAligned_of
    (hshape : ∀ {P : Params} {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
      {k : Nat},
      side = -1 ∨ side = 1 → k < 4 →
      CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos →
      ForeignSideChainShape P run side decl pos k)
    (hfold : ∀ {P : Params} {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
      {k : Nat},
      side = -1 ∨ side = 1 → k < 4 →
      CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos →
      ForeignSideFoldBound P run side decl pos k) :
    ForeignBorderChainXAligned :=
  foreignBorderChainXAligned (foreignBorderSideUps_of hshape hfold)

end Elegant.Layered.PipelineImpl
