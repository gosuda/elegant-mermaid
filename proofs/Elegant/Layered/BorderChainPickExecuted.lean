import Elegant.Layered.BorderChainPickFacts
import Elegant.Layered.BorderChainUps
import Elegant.Layered.FrameEnvelope

set_option autoImplicit false

/-!
# `BorderChainPick` for the executed border-alignment context (layered-107)

`BorderChainUps.borderChainUps_of_pick` reduces layered-107 to `BorderChainPick`,
and `BorderChainPickFacts.borderChainPick_of_facts` reduces that to the named
premises `edge_closed` / `upper_nonempty` / `upper_unmarked` / `last_lt_pred`
about the executed `clusterCtx ng cp p layers marked k`.

`OccurringBorderChain` alone does not carry the border/cluster-path facts that
`border_alignment_chain_edge` needs, so this module packages them, together with
the guarantees of the border-alignment construction (`borderChain`, the image of
`OrderImpl.addClusterBorders`/`borderAlignment`), into one named structure
`ExecutedChainFacts`, and derives the pick premises from it:

* `edgeClosed_of_executedChainFacts` — the chain edges are closed: every context
  edge touching a chain node joins chain nodes at adjacent ranks (`edge_closed`).
* `upperNonempty_of_executedChainFacts` — the rank predecessor is reachable.
* `upperUnmarked_of_executedChainFacts` — chain edges are unmarked
  (`upper_unmarked`), from `typeOneConflicts_borderChain_unmarked`.
* `lastLtPred_of_executedChainFacts` — the fold bookkeeping (`last_lt_pred`).
* `borderChainPickFacts_of_executedChainFacts` — the assembly.

`borderChain_endpoints` reads the border value and the shared cluster path off
the definition of `borderChain`; `pathConsec_of_borderChainEdges` shows that the
consecutive-path field holds for chains whose consecutive nodes are joined by
`borderChain` edges, as the executed construction produces them.
-/

namespace Elegant.Layered
open Elegant.Layered.CoordsImpl

/-- The executed border-chain facts that `border_alignment_chain_edge` and the
pick derivation need beyond `OccurringBorderChain`: every chain node carries a
border side sign, consecutive chain nodes share the cluster path, and the
border-alignment construction guarantees that the context edges touching the
chain are exactly the chain edges. -/
structure ExecutedChainFacts (p : Proper) (c : Ctx) (chain : List Nat) : Prop where
  /-- Every chain node is a border side node of `p`. -/
  border_val : ∀ v ∈ chain,
    (p.nodes.getD v default).node.border = -1 ∨ (p.nodes.getD v default).node.border = 1
  /-- Consecutive chain nodes carry the same cluster path. -/
  path_consec : ∀ i : Nat, i + 1 < chain.length →
    (p.nodes.getD chain[i]! default).node.clusterPath =
      (p.nodes.getD chain[i + 1]! default).node.clusterPath
  /-- The construction: every context edge touching a chain node is a
  `borderChain` edge whose far end is another chain node. -/
  incident_border : ∀ v ∈ chain, ∀ e : Nat, e < c.edges.size →
    (c.edges[e]!.tail = v ∨ c.edges[e]!.head = v) →
    borderChain p c.edges[e]! = true ∧
    ∃ u ∈ chain, otherEnd c.edges[e]! v = u ∧ u ≠ v
  /-- Rank-adjacent chain nodes are joined by an edge of the pass context. -/
  consec_edge : ∀ v ∈ chain, ∀ w ∈ chain, c.rank[v]! + 1 = c.rank[w]! →
    ∃ e : Nat, e < c.edges.size ∧
      ((c.edges[e]!.head = v ∧ c.edges[e]!.tail = w) ∨
        (c.edges[e]!.tail = v ∧ c.edges[e]!.head = w))
  /-- Bookkeeping: any alignment pick of a node processed before a chain node
  in its layer targets a position strictly left of the chain predecessor's
  position. Only the layer prefix (`take (pos[v])`) feeds the fold's `last`
  at the chain node's pick point, so the field is stated for the prefix. -/
  prefix_pick_left : ∀ v ∈ chain, ∀ pred : Nat, chainPred c chain v = some pred →
    ∀ x ∈ (c.layers.getD (c.rank[v]!) []).take (c.pos[v]!), ∀ last : Int, ∀ w : Nat,
      alignPick c x last = some w → (c.pos[w]! : Int) < (c.pos[pred]! : Int)

/-- From the definition of `borderChain`: the endpoints of a border-chain edge
carry a border side sign, the same border value, and the same cluster path —
exactly what `border_alignment_chain_edge` consumes. -/
theorem borderChain_endpoints {p : Proper} {e : ProperEdge}
    (hb : borderChain p e = true) :
    ((p.nodes.getD e.tail default).node.border == -1 ||
        (p.nodes.getD e.tail default).node.border == 1) = true ∧
    (p.nodes.getD e.tail default).node.border =
      (p.nodes.getD e.head default).node.border ∧
    (p.nodes.getD e.tail default).node.clusterPath =
      (p.nodes.getD e.head default).node.clusterPath := by
  cases hp : p.nodes[e.tail]? with
  | none =>
    unfold borderChain at hb
    rw [hp] at hb
    simp at hb
  | some a =>
    cases hq : p.nodes[e.head]? with
    | none =>
      unfold borderChain at hb
      rw [hp, hq] at hb
      simp at hb
    | some b =>
      have g1 : p.nodes.getD e.tail default = a := borderEnv_getD_of_get? hp
      have g2 : p.nodes.getD e.head default = b := borderEnv_getD_of_get? hq
      unfold borderChain at hb
      rw [hp, hq] at hb
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
      refine ⟨?_, ?_, ?_⟩
      · rw [g1]
        simp only [Bool.or_eq_true, beq_iff_eq]
        exact hb.1.1
      · rw [g1, g2]
        exact hb.1.2
      · rw [g1, g2]
        exact hb.2

/-- Chains whose consecutive nodes are joined by `borderChain` edges of `p` —
the shape the executed border-alignment construction produces — satisfy the
shared-cluster-path field. -/
theorem pathConsec_of_borderChainEdges {p : Proper} {chain : List Nat}
    (hbc : ∀ i : Nat, i + 1 < chain.length →
      ∃ e ∈ p.edges, borderChain p e = true ∧
        ((e.tail = chain[i]! ∧ e.head = chain[i + 1]!) ∨
          (e.tail = chain[i + 1]! ∧ e.head = chain[i]!))) :
    ∀ i : Nat, i + 1 < chain.length →
      (p.nodes.getD chain[i]! default).node.clusterPath =
        (p.nodes.getD chain[i + 1]! default).node.clusterPath := by
  intro i hi
  obtain ⟨e, _he_mem, hb, hor⟩ := hbc i hi
  obtain ⟨_, _, hpath⟩ := borderChain_endpoints hb
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have t1 : p.nodes[chain[i]!]? = p.nodes[e.tail]? := by rw [h1]
    have t2 : p.nodes[chain[i + 1]!]? = p.nodes[e.head]? := by rw [h2]
    simp only [List.getD_eq_getElem?_getD]
    rw [t1, t2]
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact hpath
  · have t1 : p.nodes[chain[i]!]? = p.nodes[e.head]? := by rw [h2]
    have t2 : p.nodes[chain[i + 1]!]? = p.nodes[e.tail]? := by rw [h1]
    simp only [List.getD_eq_getElem?_getD]
    rw [t1, t2]
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact hpath.symm

/-- Reverse membership in `upperEdges`: an in-range edge whose far end lies at a
smaller rank is an upper edge of `v`. -/
theorem upperEdges_mem_of {edges : Array ProperEdge} {rank pos : Array Nat} {v e : Nat}
    (hsz : e < edges.size)
    (hcond : (edges[e]!.head = v ∧ rank[edges[e]!.tail]! < rank[v]!) ∨
      (edges[e]!.tail = v ∧ rank[edges[e]!.head]! < rank[v]!)) :
    e ∈ upperEdges edges rank pos v := by
  simp only [upperEdges]
  refine List.mem_map.mpr ⟨(pos[otherEnd edges[e]! v]!, e), ?_, rfl⟩
  refine List.mem_mergeSort.mpr ?_
  refine List.mem_map.mpr ⟨e, ?_, rfl⟩
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hsz, ?_⟩
  rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact Or.inl ⟨h1, h2⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact Or.inr ⟨h1, h2⟩

/-- The fold bookkeeping: if every pick along a fold targets a value below `B`,
the accumulated `last` stays below `B`. -/
private theorem foldl_alignNode_snd_lt {c : Ctx} {B : Int} :
    ∀ l : List Nat, ∀ a : Al × Int, a.2 < B →
      (∀ x ∈ l, ∀ last : Int, ∀ w : Nat, alignPick c x last = some w →
        (c.pos[w]! : Int) < B) →
      (l.foldl (alignNode c) a).2 < B := by
  intro l
  induction l with
  | nil =>
    intro a ha _
    simpa using ha
  | cons x xs ih =>
    intro a ha hp
    simp only [List.foldl_cons]
    have hstep : (alignNode c a x).2 < B := by
      unfold alignNode
      split
      · next w hw => exact hp x (by simp) a.2 w hw
      · next => exact ha
    exact ih (alignNode c a x) hstep
      (fun y hy last w hw => hp y (by simp [hy]) last w hw)

/-- Premise 1 (`edge_closed`): under `ExecutedChainFacts` every context edge
touching a chain node joins chain nodes at adjacent ranks — the far end is a
chain node by the construction and the rank adjacency comes from
`OccurringBorderChain.rank_adj`. -/
theorem edgeClosed_of_executedChainFacts {p : Proper} {c : Ctx} {chain : List Nat}
    {hocc : OccurringBorderChain c chain}
    (hF : ExecutedChainFacts p c chain) :
    ChainEdgesClosed c chain := by
  intro v hv e he htouch
  obtain ⟨_hbc, u, hu_mem, hu_other, hne⟩ := hF.incident_border v hv e he htouch
  exact ⟨u, hu_mem, hu_other, hocc.rank_adj u hu_mem v hv hne⟩

/-- The rank predecessor of a chain node is reachable through an upper edge. -/
theorem upperNonempty_of_executedChainFacts {p : Proper} {c : Ctx} {chain : List Nat}
    (hF : ExecutedChainFacts p c chain)
    {v pred : Nat} (hv : v ∈ chain) (hpred : chainPred c chain v = some pred) :
    ∃ e, e ∈ upperEdges c.edges c.rank c.pos v := by
  unfold chainPred at hpred
  have hpmem : pred ∈ chain := List.mem_of_find?_eq_some hpred
  have hpspec : decide (c.rank[pred]! + 1 = c.rank[v]!) = true := by
    simpa using List.find?_some hpred
  have hrk : c.rank[pred]! + 1 = c.rank[v]! := of_decide_eq_true hpspec
  obtain ⟨e, hesz, hor⟩ := hF.consec_edge pred hpmem v hv hrk
  have hlt : c.rank[pred]! < c.rank[v]! := by omega
  refine ⟨e, upperEdges_mem_of hesz ?_⟩
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨h2, ?_⟩
    rw [h1]
    exact hlt
  · refine Or.inl ⟨h2, ?_⟩
    rw [h1]
    exact hlt

/-- Premise 2 (`upper_unmarked`): context edges touching chain nodes are
`borderChain` edges, which `typeOneConflicts` never marks; edges beyond the base
edge array fall outside the marking table and default to `false`. -/
theorem upperUnmarked_of_executedChainFacts {p : Proper} {c : Ctx} {chain : List Nat}
    {pos : Array Nat}
    (hF : ExecutedChainFacts p c chain)
    (hedges : c.edges.size = p.edges.length ∧
      ∀ i, i < p.edges.length → c.edges[i]! = p.edges[i]!)
    (hmarked : c.marked = typeOneConflicts p pos)
    {v : Nat} (hv : v ∈ chain) {e : Nat} (he : e ∈ upperEdges c.edges c.rank c.pos v) :
    c.marked[e]! = false := by
  obtain ⟨hesz, hcase⟩ := mem_upperEdges he
  obtain ⟨hbc, _, _, _, _⟩ := hF.incident_border v hv e hesz (by
    rcases hcase with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr h1
    · exact Or.inl h1)
  rw [hmarked]
  by_cases hlt : e < p.edges.length
  · have hb' : borderChain p p.edges[e] = true := by
      have h1 : c.edges[e]! = p.edges[e]! := hedges.2 e hlt
      have h2 : p.edges[e]! = p.edges[e] := getElem!_pos p.edges e hlt
      rw [← h2, ← h1]
      exact hbc
    exact typeOneConflicts_borderChain_unmarked hlt hb'
  · unfold typeOneConflicts
    rw [getElem!_neg _ e (by simpa using hlt)]
    rfl

/-- Premise 3 (`last_lt_pred`): the fold's running `last` at a chain node's
point is the accumulated pick target of its layer prefix, and every such target
stays left of the chain predecessor's position. -/
theorem lastLtPred_of_executedChainFacts {p : Proper} {c : Ctx} {chain : List Nat}
    (hF : ExecutedChainFacts p c chain)
    {v pred : Nat} (hv : v ∈ chain) (hpred : chainPred c chain v = some pred) :
    foldLast c (c.rank[v]!) (c.pos[v]!) < (c.pos[pred]! : Int) := by
  have hB : (-1 : Int) < (c.pos[pred]! : Int) := by omega
  have hp : ∀ x ∈ (c.layers.getD (c.rank[v]!) []).take (c.pos[v]!), ∀ last : Int,
      ∀ w : Nat, alignPick c x last = some w → (c.pos[w]! : Int) < (c.pos[pred]! : Int) := by
    intro x hx last w hw
    exact hF.prefix_pick_left v hv pred hpred x hx last w hw
  have hmain := foldl_alignNode_snd_lt (c := c)
    ((c.layers.getD (c.rank[v]!) []).take (c.pos[v]!))
    (foldToLayer c (c.rank[v]!), -1) hB hp
  simpa only [foldLast] using hmain

/-- The assembly: the executed chain facts yield the four pick premises, hence
`BorderChainPick` through `BorderChainPickFacts.borderChainPick_of_facts`. -/
theorem borderChainPickFacts_of_executedChainFacts {p : Proper} {c : Ctx}
    {chain : List Nat} {pos : Array Nat} {hocc : OccurringBorderChain c chain}
    (hF : ExecutedChainFacts p c chain)
    (hedges : c.edges.size = p.edges.length ∧
      ∀ i, i < p.edges.length → c.edges[i]! = p.edges[i]!)
    (hmarked : c.marked = typeOneConflicts p pos) :
    BorderChainPickFacts c chain hocc :=
   ⟨edgeClosed_of_executedChainFacts (hocc := hocc) hF,
   fun _ hv _ hpred => upperNonempty_of_executedChainFacts hF hv hpred,
   fun _ hv _ he => upperUnmarked_of_executedChainFacts hF hedges hmarked hv he,
   fun _ hv _ hpred => lastLtPred_of_executedChainFacts hF hv hpred⟩

/-- The edge facts of the executed cluster context: its edge array is exactly the
base proper's edge array (`mkCtx` stores `p.edges.toArray` and `clusterCtx` only
overrides the pair gap), so the marking table indices and the context indices
coincide. -/
theorem executedClusterCtx_edges {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {marked : Array Bool} {k : Nat} :
    (clusterCtx ng cp p layers marked k).edges.size = p.edges.length ∧
      ∀ i, i < p.edges.length →
        (clusterCtx ng cp p layers marked k).edges[i]! = p.edges[i]! := by
  have h : (clusterCtx ng cp p layers marked k).edges = p.edges.toArray := rfl
  refine ⟨by rw [h]; exact List.size_toArray, ?_⟩
  intro i hi
  rw [h]
  exact List.getElem!_toArray

/-- End to end: executed chain facts give `BorderChainPick`, hence
`BorderChainUps` and `BorderChainBlock` through the landed consumer chain. -/
theorem borderChainPick_of_executedChainFacts {p : Proper} {c : Ctx} {chain : List Nat}
    {pos : Array Nat} {hocc : OccurringBorderChain c chain}
    (hF : ExecutedChainFacts p c chain)
    (hedges : c.edges.size = p.edges.length ∧
      ∀ i, i < p.edges.length → c.edges[i]! = p.edges[i]!)
    (hmarked : c.marked = typeOneConflicts p pos) :
    BorderChainPick c chain hocc :=
  borderChainPick_of_facts (borderChainPickFacts_of_executedChainFacts hF hedges hmarked)

/-- The assembly applies at the real executed context: for
`clusterCtx ng cp (borderAlignment p0 layers) layers
(typeOneConflicts (borderAlignment p0 layers) pos) k` the edge and marking
premises hold definitionally, so executed chain facts yield `BorderChainPick`
there — and `BorderChainUps` through `borderChainUps_of_pick`. -/
theorem executed_borderChainPick {ng cp : Int} {p0 : Proper}
    {layers : List (List Nat)} {pos : Array Nat} {k : Nat} {chain : List Nat}
    (hocc : OccurringBorderChain (clusterCtx ng cp (borderAlignment p0 layers) layers
      (typeOneConflicts (borderAlignment p0 layers) pos) k) chain)
    (hF : ExecutedChainFacts (borderAlignment p0 layers)
      (clusterCtx ng cp (borderAlignment p0 layers) layers
        (typeOneConflicts (borderAlignment p0 layers) pos) k) chain) :
    BorderChainPick (clusterCtx ng cp (borderAlignment p0 layers) layers
      (typeOneConflicts (borderAlignment p0 layers) pos) k) chain hocc :=
  borderChainPick_of_executedChainFacts hF
    (executedClusterCtx_edges (p := borderAlignment p0 layers)) rfl

end Elegant.Layered
