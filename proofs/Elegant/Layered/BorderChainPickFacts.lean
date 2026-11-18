import Elegant.Layered.BorderChainUps

set_option autoImplicit false

namespace Elegant.Layered
open Elegant.Layered.CoordsImpl

/-!
# `BorderChainPick` for the chains the executed pipeline produces (layered-107)

`BorderChainUps.borderChainUps_of_pick` reduces layered-107 to the named
hypothesis `BorderChainPick`: at each chain node's actual fold point the head
picks nothing and every later node picks its chain predecessor through a
border-alignment edge.

This module discharges `BorderChainPick` from precisely named premises about
the pass context `c`:

* `ChainEdgesClosed` — every edge of `c.edges` that touches a chain node joins
  it to another chain node at an adjacent rank. For the executed pipeline
  (`clusterCtx` over `borderAlignment p layers`) this is the border-alignment
  edge structure: `borderAlignment` pairs and the `borderLinks` synthetics of
  `OrderImpl.addClusterBorders` are the only edges incident to border nodes.
* `BorderChainPickFacts` — the pick-level bundle: edge closure, existence of
  an upper edge for every non-head chain node, unmarkedness of those upper
  edges, and the running-`last` bound `last_lt_pred`.
* `upper_to_pred_of_closed` and `upperEdges_nil_of_chainPred_none` — under
  edge closure every upper edge of a non-head chain node ends at its chain
  predecessor, and a chain node without a predecessor has no upper edges.
* `alignPick_eq_pred_of_facts` — the executed median pick returns the chain
  predecessor at a non-head chain node's fold point.
* `borderChainPick_of_facts` — the assembly: `alignPick` returns `none` at the
  chain head (no upper edges) and `some pred` at every later chain node (every
  upper edge ends at `pred`, all are unmarked, and `last < pos[pred]`).
  Discharging `BorderChainPickFacts` for the executed context
  `clusterCtx ng cp p layers marked k` — edge closure through
  `border_alignment_chain_edge`, unmarkedness through
  `borderChain`/`typeOneConflicts_borderChain_unmarked`, and the
  `last < pos` bookkeeping — is the remaining premise-level obligation.
-/

/-- Every edge of the pass context that touches a chain node joins it to
another chain node at an adjacent rank. For the executed pipeline the edges
incident to border nodes are exactly the border-alignment edges. -/
def ChainEdgesClosed (c : Ctx) (chain : List Nat) : Prop :=
  ∀ v ∈ chain, ∀ e, e < c.edges.size →
    (c.edges[e]!.tail = v ∨ c.edges[e]!.head = v) →
    ∃ u ∈ chain, otherEnd c.edges[e]! v = u ∧
      (c.rank[u]! + 1 = c.rank[v]! ∨ c.rank[v]! + 1 = c.rank[u]!)

/-- Under edge closure, every upper edge of a non-head chain node ends at its
chain predecessor: the predecessor is the unique chain node one rank below. -/
theorem upper_to_pred_of_closed {c : Ctx} {chain : List Nat}
    (hocc : OccurringBorderChain c chain) (hclosed : ChainEdgesClosed c chain)
    {v pred e : Nat} (hv : v ∈ chain) (hpred : chainPred c chain v = some pred)
    (he : e ∈ upperEdges c.edges c.rank c.pos v) :
    otherEnd c.edges[e]! v = pred := by
  obtain ⟨hesz, hcase⟩ := mem_upperEdges he
  obtain ⟨u, hu, hu0, hadj⟩ := hclosed v hv e hesz (by
    rcases hcase with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr h1
    · exact Or.inl h1)
  have hru : c.rank[u]! < c.rank[v]! := by
    unfold otherEnd at hu0
    split at hu0
    · rename_i htv
      have hteq : c.edges[e]!.tail = v := beq_iff_eq.mp htv
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hteq] at h2
        exact absurd h2 (Nat.lt_irrefl _)
      · have hu2 : u = c.edges[e]!.head := hu0.symm
        rw [hu2]
        exact h2
    · rename_i htv
      have htnv : c.edges[e]!.tail ≠ v := by
        intro h2
        exact htv (beq_iff_eq.mpr h2)
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hu2 : u = c.edges[e]!.tail := hu0.symm
        rw [hu2]
        exact h2
      · exact absurd h1 htnv
  have hadj' : c.rank[u]! + 1 = c.rank[v]! := by
    rcases hadj with h | h <;> omega
  unfold chainPred at hpred
  have hpmem : pred ∈ chain := List.mem_of_find?_eq_some hpred
  have hpspec : decide (c.rank[pred]! + 1 = c.rank[v]!) = true := by
    simpa using List.find?_some hpred
  have hprk : c.rank[pred]! + 1 = c.rank[v]! := of_decide_eq_true hpspec
  have hu_eq : u = pred := hocc.rank_inj u hu pred hpmem (by omega)
  exact hu0.trans hu_eq

/-- Under edge closure, a chain node with no chain predecessor has no upper
edges at all: any upper edge would end at a chain node one rank below. -/
theorem upperEdges_nil_of_chainPred_none {c : Ctx} {chain : List Nat}
    (_hocc : OccurringBorderChain c chain) (hclosed : ChainEdgesClosed c chain)
    {v : Nat} (hv : v ∈ chain) (hpred : chainPred c chain v = none) :
    upperEdges c.edges c.rank c.pos v = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  obtain ⟨hesz, hcase⟩ := mem_upperEdges he
  obtain ⟨u, hu, hu0, hadj⟩ := hclosed v hv e hesz (by
    rcases hcase with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr h1
    · exact Or.inl h1)
  have hru : c.rank[u]! < c.rank[v]! := by
    unfold otherEnd at hu0
    split at hu0
    · rename_i htv
      have hteq : c.edges[e]!.tail = v := beq_iff_eq.mp htv
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hteq] at h2
        exact absurd h2 (Nat.lt_irrefl _)
      · have hu2 : u = c.edges[e]!.head := hu0.symm
        rw [hu2]
        exact h2
    · rename_i htv
      have htnv : c.edges[e]!.tail ≠ v := by
        intro h2
        exact htv (beq_iff_eq.mpr h2)
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hu2 : u = c.edges[e]!.tail := hu0.symm
        rw [hu2]
        exact h2
      · exact absurd h1 htnv
  have hadj' : c.rank[u]! + 1 = c.rank[v]! := by
    rcases hadj with h | h <;> omega
  have hpmem : u ∈ chain := hu
  unfold chainPred at hpred
  rw [List.find?_eq_none] at hpred
  exact hpred u hpmem (by
    show decide (c.rank[u]! + 1 = c.rank[v]!) = true
    exact decide_eq_true hadj')

/-- The pick-level facts `BorderChainPick` needs, stated as named premises
about the pass context. `edge_closed` is the structural border-edge property;
`upper_nonempty`, `upper_unmarked` and `last_lt_pred` are the executed
alignment behaviour. -/
structure BorderChainPickFacts (c : Ctx) (chain : List Nat)
    (hocc : OccurringBorderChain c chain) : Prop where
  /-- Every edge touching a chain node joins two chain nodes at adjacent
  ranks. -/
  edge_closed : ChainEdgesClosed c chain
  /-- A non-head chain node has an upper edge (the border-alignment edge to
  its chain predecessor). -/
  upper_nonempty : ∀ v ∈ chain, ∀ pred, chainPred c chain v = some pred →
    ∃ e, e ∈ upperEdges c.edges c.rank c.pos v
  /-- Upper edges of chain nodes are unmarked by `typeOneConflicts`. -/
  upper_unmarked : ∀ v ∈ chain, ∀ e ∈ upperEdges c.edges c.rank c.pos v,
    c.marked[e]! = false
  /-- The running `last` at a non-head chain node's fold point is below the
  position of its chain predecessor. -/
  last_lt_pred : ∀ v ∈ chain, ∀ pred, chainPred c chain v = some pred →
    foldLast c (c.rank[v]!) (c.pos[v]!) < (c.pos[pred]! : Int)

/-- `alignPick` at a non-head chain node's fold point selects the chain
predecessor: every upper edge ends at `pred`, all are unmarked, `last` is
below `pos[pred]`, and the first median candidate succeeds. -/
theorem alignPick_eq_pred_of_facts {c : Ctx} {chain : List Nat}
    {hocc : OccurringBorderChain c chain} (hF : BorderChainPickFacts c chain hocc)
    {v pred : Nat} (hv : v ∈ chain) (hpred : chainPred c chain v = some pred) :
    alignPick c v (foldLast c (c.rank[v]!) (c.pos[v]!)) = some pred := by
  obtain ⟨_, he0⟩ := hF.upper_nonempty v hv pred hpred
  have hne : upperEdges c.edges c.rank c.pos v ≠ [] := by
    intro hnil
    rw [hnil] at he0
    exact List.not_mem_nil he0
  have hlen : 0 < (upperEdges c.edges c.rank c.pos v).length :=
    List.length_pos_iff.mpr hne
  have hk1 : ((upperEdges c.edges c.rank c.pos v).length - 1) / 2 <
      (upperEdges c.edges c.rank c.pos v).length := by omega
  have hget : (upperEdges c.edges c.rank c.pos v)[
      ((upperEdges c.edges c.rank c.pos v).length - 1) / 2]? =
      some (upperEdges c.edges c.rank c.pos v)[
        ((upperEdges c.edges c.rank c.pos v).length - 1) / 2] :=
    getElem?_pos (upperEdges c.edges c.rank c.pos v)
      (((upperEdges c.edges c.rank c.pos v).length - 1) / 2) hk1
  have hmem : (upperEdges c.edges c.rank c.pos v)[
      ((upperEdges c.edges c.rank c.pos v).length - 1) / 2] ∈
      upperEdges c.edges c.rank c.pos v :=
    List.getElem_mem hk1
  have hto := upper_to_pred_of_closed hocc hF.edge_closed hv hpred hmem
  have hun := hF.upper_unmarked v hv _ hmem
  have hlt := hF.last_lt_pred v hv pred hpred
  unfold alignPick
  dsimp only
  rw [List.findSome?_cons]
  simp only [hget, Option.bind_some]
  simp only [hto]
  have hdec : decide (foldLast c (c.rank[v]!) (c.pos[v]!) <
      (c.pos[pred]! : Int)) = true := decide_eq_true hlt
  simp only [hun, hdec]
  simp

/-- `BorderChainPick` from the pick-level facts: the head picks nothing (no
upper edges under edge closure) and every later chain node picks its chain
predecessor through a border-alignment edge. -/
theorem borderChainPick_of_facts {c : Ctx} {chain : List Nat}
    {hocc : OccurringBorderChain c chain} (hF : BorderChainPickFacts c chain hocc) :
    BorderChainPick c chain hocc := by
  refine ⟨?_, ?_⟩
  · intro v hv hpred
    have hE := upperEdges_nil_of_chainPred_none hocc hF.edge_closed hv hpred
    unfold alignPick
    dsimp only
    rw [hE]
    simp
  · intro v hv pred hpred
    obtain ⟨e, he⟩ := hF.upper_nonempty v hv pred hpred
    obtain ⟨hesz, hcase⟩ := mem_upperEdges he
    have hto := upper_to_pred_of_closed hocc hF.edge_closed hv hpred he
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- head = v, rank[tail] < rank[v]: tail ≠ v, otherEnd = tail = pred
      have hnt : c.edges[e]!.tail ≠ v := by
        intro h3
        rw [h3] at h2
        exact (Nat.lt_irrefl _) h2
      refine ⟨e, hesz, ⟨Or.inl ⟨h1, ?_⟩, alignPick_eq_pred_of_facts hF hv hpred⟩⟩
      unfold otherEnd at hto
      split at hto
      · rename_i htv
        exact absurd (beq_iff_eq.mp htv) hnt
      · exact hto
    · -- tail = v, rank[head] < rank[v]: otherEnd = head = pred
      refine ⟨e, hesz, ⟨Or.inr ⟨h1, ?_⟩, alignPick_eq_pred_of_facts hF hv hpred⟩⟩
      unfold otherEnd at hto
      split at hto
      · exact hto
      · rename_i htv
        exact absurd (beq_iff_eq.mpr h1) htv

end Elegant.Layered
