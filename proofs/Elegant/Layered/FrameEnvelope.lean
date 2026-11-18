import Elegant.Layered.Coords

/-!
# Border-chain straightness of the cross-axis phase

`border_chain_straight` of spec/layout/layered.md (layered-107): for every well-formed input
and every cluster `C`, the cross-axis phase gives equal left-border coordinates across all
ranks of the span of `C`, and equal right-border coordinates across all ranks of the span
of `C`.

This module lands the coordinate-phase half of that obligation over the actual
`crossCoordsClusterWith` / `clusterPass` / `balance` definitions of `Coords.lean`:

* `typeOneConflicts_borderChain_unmarked` — the marking rule of layered-38 part 1: a
  border-chain segment is never marked by `typeOneConflicts`.
* `border_alignment_chain_edge` — `borderAlignment` inserts the chain edge between the
  same-side border nodes of one cluster at adjacent layers.
* `run_pass_block_x_eq` — every node of one alignment block gets the same coordinate in a
  pass output (`Done` through `placeRoots_spec`).
* `cluster_pass_block_x_eq` — the same for the cluster-separated passes of
  `crossClusterPasses`.
* `balance_block_x_eq` — `balance` is pointwise, so four pass arrays that agree on the
  chain give a balanced output that agrees on the chain.
* `BorderChainBlock` — the alignment-pick obligation of layered-107 that remains at the
  pipeline level: the border chain of one cluster is a single alignment block of each of
  the four passes.
* `border_chain_straight` — the assembly: under `BorderChainBlock`, the output of
  `crossCoordsClusterWith` is constant on the chain.
-/

namespace Elegant
namespace Layered
open Elegant.Layered.CoordsImpl

theorem borderEnv_rangeMapList {n : Nat} (f : Nat → Int) {i : Nat} (hi : i < n) :
    ((List.range n).map f)[i]! = f i := by
  have hl : ((List.range n).map f).length = n := by simp
  have hs : i < ((List.range n).map f).length := by rw [hl]; exact hi
  rw [getElem!_pos (List.map f (List.range n)) i hs, List.getElem_map,
    List.getElem_range (by simpa using hi)]

theorem borderEnv_getD_of_get? {α : Type} [Inhabited α] {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : l.getD i default = x := by
  simp [List.getD, h]

/-- The marking rule of layered-38 part 1: a border-chain segment is never marked. -/
theorem typeOneConflicts_borderChain_unmarked {p : Proper} {pos : Array Nat} {i : Nat}
    (hi : i < p.edges.length) (hb : borderChain p p.edges[i] = true) :
    (typeOneConflicts p pos)[i]! = false := by
  unfold typeOneConflicts
  have hs : i < (p.edges.map
      (fun e => !borderChain p e &&
        (crossesAmong p pos (borderChain p) e || (!innerEdge p e && crossesInner p pos e)))).toArray.size := by
    simpa using hi
  rw [getElem!_pos ((p.edges.map
      (fun e => !borderChain p e &&
        (crossesAmong p pos (borderChain p) e || (!innerEdge p e && crossesInner p pos e)))).toArray) i hs,
    List.getElem_toArray (by simpa using hs), List.getElem_map]
  simp [hb]

/-- Under the sibling cluster order rule the border chain of a cluster at adjacent layers
is connected: `borderAlignment` inserts an edge from the earlier-layer border node to the
later-layer border node of one cluster with the same border sign. -/
theorem border_alignment_chain_edge {p : Proper} {layers : List (List Nat)}
    {l1 l2 : List Nat} {a b : Nat} {na nb : ProperNode}
    (hpair : (l1, l2) ∈ layers.zip layers.tail)
    (ha : a ∈ l1) (hb : b ∈ l2)
    (hna : p.nodes[a]? = some na) (hnb : p.nodes[b]? = some nb)
    (hsign : (na.node.border == -1 || na.node.border == 1) = true)
    (heq : na.node.border = nb.node.border)
    (hpath : na.node.clusterPath = nb.node.clusterPath) :
    ∃ e, e ∈ (borderAlignment p layers).edges ∧ e.tail = a ∧ e.head = b := by
  have gda : (p.nodes.getD a default).node = na.node := by
    rw [borderEnv_getD_of_get? hna]
  have gdb : (p.nodes.getD b default).node = nb.node := by
    rw [borderEnv_getD_of_get? hnb]
  simp only [borderAlignment]
  refine ⟨{ tail := a, head := b, decl := na.node.decl, original := 0 },
    List.mem_append.mpr (Or.inr ?_), rfl, rfl⟩
  refine List.mem_flatMap.mpr ⟨(l1, l2), hpair, ?_⟩
  refine List.mem_flatMap.mpr ⟨a, ha, ?_⟩
  refine List.mem_filterMap.mpr ⟨b, hb, ?_⟩
  have c2 : (na.node.border == nb.node.border) = true := by simp [heq]
  have c3 : (na.node.clusterPath == nb.node.clusterPath) = true := by simp [hpath]
  rw [gda, gdb]
  simp [hsign, c2, c3]

/-- Nodes of one alignment block get the same coordinate in a pass output: the block is
placed by a single `commit` of step C3, so `st.x` and `st.sink` agree on all of its
members, and `finalX` subtracts one shared pass minimum. -/
theorem run_pass_block_x_eq {c : Ctx} {odd : Bool} {x : Array Int}
    (hL : Lay c) (hE : EdgeOK c)
    (h : runPass c odd = .ok x)
    {r m : Nat} (hr : (alignAll c).root r = r)
    (hrin : r ∈ c.layers.flatten)
    (hm : m ∈ mem c (alignAll c) r)
    (hmn : m < c.n) (hrn : r < c.n) :
    x[m]! = x[r]! := by
  have hA := af_of_layout hL hE
  have hW := wf_of_af hA
  obtain ⟨st, hst, hx⟩ := runPass_ok h
  obtain ⟨hG, hall, _⟩ :=
    placeRoots_spec hW (c.n + 1) c.layers.flatten PS.init st (fun v hv => hv) ginv_init hst
  have hdone : Done c (alignAll c) st r := by
    rcases hG.set_ r hr (hall r hrin hr) with h0 | h0
    · exact absurd h0 (by simp)
    · exact h0
  obtain ⟨_, hxm, hskm⟩ := hdone m hm
  rw [hx, array_map_range_get _ hmn, array_map_range_get _ hrn]
  simp only [finalX, hxm, hskm]

theorem clusterCtx_facts {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {pos : Array Nat} {marked : Array Bool} {k : Nat}
    (hc : checkLayers p layers = .ok pos) :
    Lay (clusterCtx ng cp p layers marked k) ∧ EdgeOK (clusterCtx ng cp p layers marked k) := by
  obtain ⟨hL, hE⟩ := layout_facts (gap := ng) marked k hc
  refine ⟨⟨?_, ?_⟩, hE⟩
  · intro i l j v hl hv
    exact hL.idx i l j v hl hv
  · intro v hv
    exact hL.unset v hv

/-- Same-block equality for one cluster-separated pass. -/
theorem cluster_pass_block_x_eq {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {pos : Array Nat} {k : Nat} {x : Array Int}
    (hc : checkLayers p layers = .ok pos)
    (h : clusterPass ng cp p layers (typeOneConflicts p pos) k = .ok x)
    {r m : Nat}
    (hr : (alignAll (clusterCtx ng cp p layers (typeOneConflicts p pos) k)).root r = r)
    (hrin : r ∈ (clusterCtx ng cp p layers (typeOneConflicts p pos) k).layers.flatten)
    (hm : m ∈ mem (clusterCtx ng cp p layers (typeOneConflicts p pos) k)
      (alignAll (clusterCtx ng cp p layers (typeOneConflicts p pos) k)) r)
    (hmn : m < p.nodes.length) (hrn : r < p.nodes.length) :
    x[m]! = x[r]! := by
  obtain ⟨hL, hE⟩ := clusterCtx_facts (ng := ng) (cp := cp) hc
  exact run_pass_block_x_eq hL hE h hr hrin hm hmn hrn

theorem clusterPass_ok_of_crossClusterPasses {ng cp : Int} {p : Proper}
    {layers : List (List Nat)} {x0 x1 x2 x3 : Array Int}
    (h : crossClusterPasses ng cp p layers = .ok (x0, x1, x2, x3)) :
    ∃ pos : Array Nat,
      checkLayers p layers = .ok pos ∧ 1 ≤ ng ∧ 1 ≤ cp ∧
        clusterPass ng cp p layers (typeOneConflicts p pos) 0 = .ok x0 ∧
        clusterPass ng cp p layers (typeOneConflicts p pos) 1 = .ok x1 ∧
        clusterPass ng cp p layers (typeOneConflicts p pos) 2 = .ok x2 ∧
        clusterPass ng cp p layers (typeOneConflicts p pos) 3 = .ok x3 := by
  unfold crossClusterPasses at h
  split at h
  · simp at h
  · next pos hpos =>
    split at h
    · simp at h
    · next hg =>
      dsimp only at h
      split at h
      · simp at h
      · next y0 h0 =>
        split at h
        · simp at h
        · next y1 h1 =>
          split at h
          · simp at h
          · next y2 h2 =>
            split at h
            · simp at h
            · next y3 h3 =>
              simp only [not_or] at hg
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              refine ⟨pos, hpos, ?_, ?_, h0, h1, h2, h3⟩ <;> omega

/-- The pass data behind a successful `crossCoordsClusterWith`: the layer check of the
border-aligned graph, and either the empty-node fast path or the four cluster passes with
their balanced output. -/
theorem crossCoordsClusterWith_ok {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {xs : List Int} (h : crossCoordsClusterWith ng cp p layers = .ok xs) :
    ∃ pos : Array Nat, checkLayers (borderAlignment p layers) layers = .ok pos ∧
      ((p.nodes.length = 0 ∧ xs = []) ∨
        ∃ x0 x1 x2 x3 : Array Int,
          clusterPass ng cp (borderAlignment p layers) layers
            (typeOneConflicts (borderAlignment p layers) pos) 0 = .ok x0 ∧
          clusterPass ng cp (borderAlignment p layers) layers
            (typeOneConflicts (borderAlignment p layers) pos) 1 = .ok x1 ∧
          clusterPass ng cp (borderAlignment p layers) layers
            (typeOneConflicts (borderAlignment p layers) pos) 2 = .ok x2 ∧
          clusterPass ng cp (borderAlignment p layers) layers
            (typeOneConflicts (borderAlignment p layers) pos) 3 = .ok x3 ∧
          balance p.nodes.length x0 x1 x2 x3 = .ok xs) := by
  unfold crossCoordsClusterWith at h
  dsimp only at h
  split at h
  · next h0 =>
    split at h
    · simp at h
    · next pos hpos =>
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        exact ⟨pos, hpos, Or.inl ⟨h0, h.symm⟩⟩
  · split at h
    · simp at h
    · next x0 x1 x2 x3 hp =>
      obtain ⟨pos, hpos, _, _, hp0, hp1, hp2, hp3⟩ :=
        clusterPass_ok_of_crossClusterPasses (p := borderAlignment p layers) hp
      exact ⟨pos, hpos, Or.inr ⟨x0, x1, x2, x3, hp0, hp1, hp2, hp3, h⟩⟩

/-- `balance` of step C4 is pointwise: if the four pass arrays agree pairwise at indices
`i` and `j`, the balanced output agrees there too. -/
theorem balance_block_x_eq {n : Nat} {x0 x1 x2 x3 : Array Int} {xs : List Int}
    (h : balance n x0 x1 x2 x3 = .ok xs)
    {i j : Nat} (hi : i < n) (hj : j < n)
    (h0 : x0[i]! = x0[j]!) (h1 : x1[i]! = x1[j]!)
    (h2 : x2[i]! = x2[j]!) (h3 : x3[i]! = x3[j]!) :
    xs[i]! = xs[j]! := by
  unfold balance at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h
      obtain rfl := h
      unfold balanceValues
      dsimp only
      rw [borderEnv_rangeMapList _ hi, borderEnv_rangeMapList _ hj, h0, h1, h2, h3]

/-- The border chain `chain` of one cluster is a single alignment block of pass `k`:
some chain node is the block root, the root lies on a pass layer, and every chain node
lies on its member list. This is the alignment-pick fact of layered-107; it is the
remaining obligation at the pipeline level (the median pick of each chain node is its
chain predecessor, which needs the executed sibling-order facts). -/
def BorderChainBlock (ng cp : Int) (p : Proper) (layers : List (List Nat))
    (marked : Array Bool) (k : Nat) (chain : List Nat) : Prop :=
  ∃ r, r ∈ chain ∧
    (alignAll (clusterCtx ng cp p layers marked k)).root r = r ∧
    r ∈ (clusterCtx ng cp p layers marked k).layers.flatten ∧
    ∀ v ∈ chain, v ∈ mem (clusterCtx ng cp p layers marked k)
      (alignAll (clusterCtx ng cp p layers marked k)) r

/-- layered-107 at the coordinate-phase level: if the four cluster passes each align the
border chain of one cluster into a single block, the balanced output of
`crossCoordsClusterWith` is constant on the chain. -/
theorem border_chain_straight {ng cp : Int} {p : Proper}
    {layers : List (List Nat)} {xs : List Int} {chain : List Nat}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs)
    (hchain : ∀ v ∈ chain, v < p.nodes.length)
    (hblock : ∀ pos : Array Nat, checkLayers (borderAlignment p layers) layers = .ok pos →
      ∀ k < 4, BorderChainBlock ng cp (borderAlignment p layers) layers
        (typeOneConflicts (borderAlignment p layers) pos) k chain) :
    ∀ v ∈ chain, ∀ w ∈ chain, xs[v]! = xs[w]! := by
  obtain ⟨pos, hcl, hcase⟩ := crossCoordsClusterWith_ok h
  rcases hcase with ⟨h0, _⟩ | ⟨x0, x1, x2, x3, hp0, hp1, hp2, hp3, hbal⟩
  · intro v hv w _
    exact absurd (hchain v hv) (by rw [h0]; exact Nat.not_lt_zero v)
  · intro v hv w hw
    have hlen : (borderAlignment p layers).nodes.length = p.nodes.length := rfl
    have hpass : ∀ k : Nat, k < 4 → ∀ (x : Array Int),
        clusterPass ng cp (borderAlignment p layers) layers
          (typeOneConflicts (borderAlignment p layers) pos) k = .ok x →
        ∀ v ∈ chain, ∀ w ∈ chain, x[v]! = x[w]! := by
      intro k hk x hx v hv w hw
      obtain ⟨r, hrchain, hrr, hrrin, hmem⟩ := hblock pos hcl k hk
      have e1 := cluster_pass_block_x_eq hcl hx hrr hrrin (hmem v hv)
        (by rw [hlen]; exact hchain v hv) (by rw [hlen]; exact hchain r hrchain)
      have e2 := cluster_pass_block_x_eq hcl hx hrr hrrin (hmem w hw)
        (by rw [hlen]; exact hchain w hw) (by rw [hlen]; exact hchain r hrchain)
      rw [e1, e2]
    have q0 := hpass 0 (by omega) x0 hp0 v hv w hw
    have q1 := hpass 1 (by omega) x1 hp1 v hv w hw
    have q2 := hpass 2 (by omega) x2 hp2 v hv w hw
    have q3 := hpass 3 (by omega) x3 hp3 v hv w hw
    exact balance_block_x_eq hbal (hchain v hv) (hchain w hw) q0 q1 q2 q3

end Layered
end Elegant
