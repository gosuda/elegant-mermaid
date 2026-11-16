import ElegantGeometry.Basic
import Elegant.Gen.Layoutconst
import Elegant.Layered.Cycles
import Elegant.Layered.Rank

set_option autoImplicit false

/-! Dummy phase (spec/layout/layered.md, "Dummy and label nodes"): every edge of span `s`
becomes a chain of `s` unit-span edges through `s - 1` dummy nodes. `normalize_proper` proves
every edge of the result has span 1. -/

namespace Elegant
namespace Layered

open RankImpl (rk_of_lt wellformed_spec mem_of_mem_zipIdx)

structure ProperNode where
  node : Node
  dummy : Bool
  edge : Option Nat
  label : Bool := false
deriving DecidableEq, Repr, Inhabited

structure ProperEdge where
  tail : Nat
  head : Nat
  decl : Nat
  original : Nat
  synthetic : Bool := false
deriving DecidableEq, Repr, Inhabited

structure Proper where
  nodes : List ProperNode
  edges : List ProperEdge
  rank : List Int
  chains : List (List Nat)
deriving Repr, Inhabited

def Proper.span (p : Proper) (e : ProperEdge) : Int := rk p.rank e.head - rk p.rank e.tail

namespace NormalizeImpl

def chainNode (a b n0 s k : Nat) : Nat :=
  if k = 0 then a else if k = s then b else n0 + (k - 1)

def dummyNodes (e : Edge) (idx : Nat) (slot : Int) (s : Nat) : List ProperNode :=
  List.replicate (s - 1) ⟨{ decl := e.decl, w := slot, h := 0 }, true, some idx, false⟩

def dummyRanks (ra : Int) (s : Nat) : List Int :=
  (List.range (s - 1)).map fun (j : Nat) => ra + 1 + (j : Int)

def chainOf (a b n0 s : Nat) : List Nat :=
  (List.range (s + 1)).map (chainNode a b n0 s)

def chainEdges (e : Edge) (idx : Nat) (n0 s : Nat) : List ProperEdge :=
  (List.range s).map fun k =>
    { tail := chainNode e.tail e.head n0 s k,
      head := chainNode e.tail e.head n0 s (k + 1), decl := e.decl, original := idx }

def appendChain (slot : Int) (p : Proper) (e : Edge) (idx : Nat) (s : Nat) : Proper :=
  { nodes := p.nodes ++ dummyNodes e idx slot s
    edges := p.edges ++ chainEdges e idx p.nodes.length s
    rank := p.rank ++ dummyRanks (rk p.rank e.tail) s
    chains := p.chains ++ [chainOf e.tail e.head p.nodes.length s] }

def normalizeEdge (slot : Int) (p : Proper) (e : Edge) (idx : Nat) : Except LayoutError Proper :=
  if e.tail = e.head then .ok { p with chains := p.chains ++ [[]] }
  else if rk p.rank e.head - rk p.rank e.tail < e.minLen then .error .domain
  else if (p.nodes.length : Int) + (rk p.rank e.head - rk p.rank e.tail) - 1 > I32_MAX then
    .error .overflow
  else .ok (appendChain slot p e idx (rk p.rank e.head - rk p.rank e.tail).toNat)

def normalizeLoop (slot : Int) : List (Edge × Nat) → Proper → Except LayoutError Proper
  | [], p => .ok p
  | (e, i) :: rest, p =>
    match normalizeEdge slot p e i with
    | .error err => .error err
    | .ok p' => normalizeLoop slot rest p'

opaque defaultSlot : Option Int := some LayoutConst.slot.vector

def slotOf (g : Graph) : Option Int :=
  if g.slot = 0 then defaultSlot else some g.slot

def normalize (g : Graph) (rank : List Int) : Except LayoutError Proper :=
  match slotOf g with
  | none => .error .domain
  | some slot =>
    if g.wellformed = true ∧ rank.length = g.nodes.length ∧ 0 ≤ slot then
      normalizeLoop slot g.edges.zipIdx
        { nodes := g.nodes.map fun n => ⟨n, false, none, false⟩
          edges := []
          rank := rank
          chains := [] }
    else .error .domain

def PInv (p : Proper) : Prop :=
  p.nodes.length = p.rank.length ∧
    ∀ e ∈ p.edges, e.tail < p.rank.length ∧ e.head < p.rank.length ∧ p.span e = 1

theorem rk_append_left {r t : List Int} {v : Nat} (h : v < r.length) :
    rk (r ++ t) v = rk r v := by
  simp [rk, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rk_append_right {r t : List Int} {v : Nat} (h : r.length ≤ v) :
    rk (r ++ t) v = rk t (v - r.length) := by
  simp [rk, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem rk_dummyRanks (ra : Int) (s j : Nat) (h : j < s - 1) :
    rk (dummyRanks ra s) j = ra + 1 + (j : Int) := by
  have h' : j < (dummyRanks ra s).length := by simpa [dummyRanks] using h
  rw [rk_of_lt h']
  simp [dummyRanks]

theorem chain_rank {p : Proper} (hP : p.nodes.length = p.rank.length) {e : Edge} (idx : Nat)
    (slot : Int) (hA : e.tail < p.rank.length) (hB : e.head < p.rank.length) (s : Nat)
    (hs : 1 ≤ s) (hspan : rk p.rank e.head - rk p.rank e.tail = (s : Int)) :
    ∀ k, k ≤ s →
      chainNode e.tail e.head p.nodes.length s k < (appendChain slot p e idx s).rank.length ∧
      rk (appendChain slot p e idx s).rank (chainNode e.tail e.head p.nodes.length s k) =
        rk p.rank e.tail + (k : Int) := by
  intro k hk
  have hlen : (appendChain slot p e idx s).rank.length = p.rank.length + (s - 1) := by
    simp [appendChain, dummyRanks]
  by_cases h0 : k = 0
  · subst h0
    simp only [chainNode, ↓reduceIte]
    refine ⟨by rw [hlen]; omega, ?_⟩
    simp only [appendChain]
    rw [rk_append_left hA]
    simp
  · by_cases hks : k = s
    · subst hks
      simp only [chainNode, h0, ↓reduceIte]
      refine ⟨by rw [hlen]; omega, ?_⟩
      simp only [appendChain]
      rw [rk_append_left hB]
      omega
    · simp only [chainNode, h0, hks, ↓reduceIte]
      refine ⟨by rw [hlen, ← hP]; omega, ?_⟩
      simp only [appendChain]
      rw [rk_append_right (by rw [← hP]; omega), ← hP]
      have : p.nodes.length + (k - 1) - p.nodes.length = k - 1 := by omega
      rw [this, rk_dummyRanks _ _ _ (by omega)]
      omega

theorem normalizeEdge_inv {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat} (hP : PInv p)
    (hA : e.tail < p.rank.length) (hB : e.head < p.rank.length) (hm : 1 ≤ e.minLen)
    (h : normalizeEdge slot p e idx = .ok p') : PInv p' ∧ p.rank.length ≤ p'.rank.length := by
  unfold normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨hP, Nat.le_refl _⟩
  · split at h
    · simp at h
    · split at h
      · simp at h
      · next hne hlt hov =>
        simp only [Except.ok.injEq] at h
        subst h
        have hspan : 1 ≤ rk p.rank e.head - rk p.rank e.tail := by omega
        have hs1 : 1 ≤ (rk p.rank e.head - rk p.rank e.tail).toNat := by omega
        have hsc : rk p.rank e.head - rk p.rank e.tail =
            ((rk p.rank e.head - rk p.rank e.tail).toNat : Int) := by omega
        generalize hsdef : (rk p.rank e.head - rk p.rank e.tail).toNat = s at hs1 hsc
        have hcr := chain_rank hP.1 idx slot hA hB s hs1 hsc
        have hlen : (appendChain slot p e idx s).rank.length = p.rank.length + (s - 1) := by
          simp [appendChain, dummyRanks]
        refine ⟨⟨?_, ?_⟩, by rw [hlen]; omega⟩
        · simp [appendChain, dummyNodes, dummyRanks, hP.1]
        · intro e' he'
          simp only [appendChain] at he'
          rcases List.mem_append.mp he' with he' | he'
          · obtain ⟨h1, h2, h3⟩ := hP.2 e' he'
            have h1' : e'.tail < p.rank.length := h1
            have h2' : e'.head < p.rank.length := h2
            refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, ?_⟩
            unfold Proper.span at h3 ⊢
            simp only [appendChain]
            rw [rk_append_left h1', rk_append_left h2']
            exact h3
          · simp only [chainEdges, List.mem_map, List.mem_range] at he'
            obtain ⟨k, hk, rfl⟩ := he'
            have c1 := hcr k (by omega)
            have c2 := hcr (k + 1) (by omega)
            refine ⟨c1.1, c2.1, ?_⟩
            unfold Proper.span
            simp only
            rw [c1.2, c2.2]
            omega

theorem normalizeLoop_inv (slot : Int) (n : Nat) :
    ∀ (l : List (Edge × Nat)) (p p' : Proper),
      (∀ q ∈ l, q.1.tail < n ∧ q.1.head < n ∧ 1 ≤ q.1.minLen) →
      n ≤ p.rank.length → PInv p → normalizeLoop slot l p = .ok p' → PInv p' := by
  intro l
  induction l with
  | nil =>
    intro p p' _ _ hP h
    simp only [normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hP
  | cons q qs ih =>
    intro p p' hl hn hP h
    obtain ⟨e, i⟩ := q
    unfold normalizeLoop at h
    split at h
    · simp at h
    · next p1 h1 =>
      obtain ⟨hq1, hq2, hq3⟩ := hl (e, i) (by simp)
      obtain ⟨hP1, hlen⟩ := normalizeEdge_inv hP (by omega) (by omega) hq3 h1
      exact ih p1 p' (fun q hq => hl q (by simp [hq])) (by omega) hP1 h

theorem normalize_proper (g : Graph) (rank : List Int) (p : Proper)
    (h : normalize g rank = .ok p) : ∀ e ∈ p.edges, p.span e = 1 := by
  unfold normalize at h
  split at h
  · simp at h
  · next slot hslot =>
    split at h
    · next hc =>
      have hwf := hc.1
      have hmem : ∀ q ∈ g.edges.zipIdx,
          q.1.tail < g.nodes.length ∧ q.1.head < g.nodes.length ∧ 1 ≤ q.1.minLen := by
        intro q hq
        exact wellformed_spec hwf q.1 (mem_of_mem_zipIdx hq)
      have hP : PInv
          { nodes := g.nodes.map fun n => ⟨n, false, none, false⟩
            edges := []
            rank := rank
            chains := [] } := by
        refine ⟨by simp [hc.2.1], ?_⟩
        intro e he
        simp at he
      have := normalizeLoop_inv slot g.nodes.length _ _ p hmem (by simp [hc.2.1]) hP h
      intro e he
      exact (this.2 e he).2.2
    · simp at h

theorem normalizeEdge_chains_length {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (h : normalizeEdge slot p e idx = .ok p') :
    p'.chains.length = p.chains.length + 1 := by
  unfold normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp [appendChain]

theorem normalizeLoop_chains_length (slot : Int) :
    ∀ (l : List (Edge × Nat)) (p p' : Proper),
      normalizeLoop slot l p = .ok p' →
      p'.chains.length = p.chains.length + l.length := by
  intro l
  induction l with
  | nil =>
    intro p p' h
    simp only [normalizeLoop, Except.ok.injEq] at h
    subst h
    simp
  | cons q qs ih =>
    intro p p' h
    obtain ⟨e, i⟩ := q
    unfold normalizeLoop at h
    split at h
    · simp at h
    · next p1 h1 =>
      have h1len := normalizeEdge_chains_length h1
      have hrest := ih p1 p' h
      simp only [List.length_cons]
      omega

theorem normalize_chains_length {g : Graph} {rank : List Int} {p : Proper}
    (h : normalize g rank = .ok p) : p.chains.length = g.edges.length := by
  unfold normalize at h
  split at h
  · simp at h
  · next slot hslot =>
    split at h
    · next hc =>
      have hloop := normalizeLoop_chains_length slot g.edges.zipIdx
        { nodes := g.nodes.map fun n => ⟨n, false, none, false⟩
          edges := []
          rank := rank
          chains := [] } p h
      dsimp only at hloop
      rw [List.length_zipIdx] at hloop
      simpa only [List.length_nil, Nat.zero_add] using hloop
    · simp at h

/-! ## Declaration coverage and chain identity

`CovEdge` is the declaration-lookup bridge: a proper edge's declared `original` index is in
bounds of the input edge list and names an actual input edge with the same declaration.
`ChainFact` is the per-input-edge identity: the chain `normalize` wrote for input edge
`(e, i)` is empty exactly when `e` is a self-loop, otherwise it runs from `e.tail` to
`e.head` and every consecutive pair of its nodes is joined by an actual output proper edge
carrying index `i` and declaration `e.decl`. `NormalizeOk` packages both, and `normalize_ok`
derives the package from `normalize` success alone. -/

/-- A proper edge names a real input edge: its declared `original` index is in bounds of
`es` and the input edge stored there carries the same declaration. -/
def CovEdge (es : List Edge) (pe : ProperEdge) : Prop :=
  pe.original < es.length ∧ ∃ ge, es[pe.original]? = some ge ∧ pe.decl = ge.decl

/-- The normalize identity fact for one input edge `q = (e, i)`: `es[i]` really holds `e`,
and the chain the output holds for `q` (given as the option value `ch`) is the empty chain
when `e` is a self-loop, otherwise a chain of at least two nodes from `e.tail` to `e.head`
whose consecutive nodes are joined by output proper edges with original index `q.2` and
declaration `e.decl`. -/
def ChainFact (es : List Edge) (p : Proper) (q : Edge × Nat) (ch : Option (List Nat)) : Prop :=
  es[q.2]? = some q.1 ∧
  (if q.1.tail = q.1.head then ch = some []
   else ∃ chl, ch = some chl ∧ 2 ≤ chl.length ∧ chl.head? = some q.1.tail ∧
     chl.getLast? = some q.1.head ∧
     ∀ (j : Nat) (hj : j < chl.length) (hj1 : j + 1 < chl.length),
       ∃ pe ∈ p.edges, pe.original = q.2 ∧ pe.decl = q.1.decl ∧
         pe.tail = chl[j] ∧ pe.head = chl[j + 1])

theorem chainOf_length (a b n0 s : Nat) : (chainOf a b n0 s).length = s + 1 := by
  simp [chainOf]

theorem chainOf_getElem? (a b n0 s k : Nat) (hk : k ≤ s) :
    (chainOf a b n0 s)[k]? = some (chainNode a b n0 s k) := by
  have hlt : k < s + 1 := by omega
  simp only [chainOf, List.getElem?_map, List.getElem?_range hlt]
  simp

theorem chainOf_head? (a b n0 s : Nat) (h : 1 ≤ s) :
    (chainOf a b n0 s).head? = some a := by
  rw [List.head?_eq_getElem?, chainOf_getElem? a b n0 s 0 (by omega)]
  simp [chainNode]

theorem chainOf_getLast? (a b n0 s : Nat) (h : 1 ≤ s) :
    (chainOf a b n0 s).getLast? = some b := by
  have hlen : (chainOf a b n0 s).length = s + 1 := chainOf_length a b n0 s
  have hs0 : ¬(s = 0) := by omega
  rw [List.getLast?_eq_getElem?, hlen]
  have hidx : s + 1 - 1 = s := by omega
  rw [hidx, chainOf_getElem? a b n0 s s (by omega)]
  simp [chainNode, hs0]

theorem chainEdges_getElem? (e : Edge) (idx n0 s k : Nat) (h : k < s) :
    (chainEdges e idx n0 s)[k]? =
      some { tail := chainNode e.tail e.head n0 s k,
             head := chainNode e.tail e.head n0 s (k + 1), decl := e.decl, original := idx } := by
  simp only [chainEdges, List.getElem?_map, List.getElem?_range h]
  simp

theorem cov_chainEdges {es : List Edge} {e : Edge} {idx n0 s : Nat} (hge : es[idx]? = some e) :
    ∀ pe ∈ chainEdges e idx n0 s, CovEdge es pe := by
  intro pe he
  simp only [chainEdges, List.mem_map, List.mem_range] at he
  obtain ⟨k, hk, rfl⟩ := he
  obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp hge
  exact ⟨hb, ⟨e, hge, rfl⟩⟩

theorem normalizeEdge_cov {es : List Edge} {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hge : es[idx]? = some e) (hcov : ∀ pe ∈ p.edges, CovEdge es pe)
    (h : normalizeEdge slot p e idx = .ok p') : ∀ pe ∈ p'.edges, CovEdge es pe := by
  unfold normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    intro pe he
    exact hcov pe he
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        intro pe he
        simp only [appendChain] at he
        rcases List.mem_append.mp he with he | he
        · exact hcov pe he
        · exact cov_chainEdges hge pe he

theorem normalizeEdge_edges_sub {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (h : normalizeEdge slot p e idx = .ok p') : p.edges ⊆ p'.edges := by
  unfold normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact fun _ hp => hp
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact fun pe hp => List.mem_append.mpr (Or.inl hp)

theorem normalizeEdge_chains_append {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (h : normalizeEdge slot p e idx = .ok p') :
    ∃ x : List Nat, p'.chains = p.chains ++ [x] := by
  unfold normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl⟩
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact ⟨chainOf e.tail e.head p.nodes.length
          ((rk p.rank e.head - rk p.rank e.tail).toNat), rfl⟩

/-- `ChainFact` transfers along edge-list growth and chain-value equality. -/
theorem ChainFact.trans {es : List Edge} {p p' : Proper} {q : Edge × Nat}
    {ch ch' : Option (List Nat)} (h : ChainFact es p q ch) (he : p.edges ⊆ p'.edges)
    (hch : ch = ch') : ChainFact es p' q ch' := by
  obtain ⟨hanchor, hrest⟩ := h
  refine ⟨hanchor, ?_⟩
  by_cases hself : q.1.tail = q.1.head
  · rw [ite_eq_left hself] at hrest
    rw [ite_eq_left hself, ← hch]
    exact hrest
  · rw [ite_eq_right hself] at hrest
    rw [ite_eq_right hself]
    obtain ⟨chl, hcv, h2, h0, hlast, hconn⟩ := hrest
    refine ⟨chl, ?_, h2, h0, hlast, ?_⟩
    · rw [← hch]
      exact hcv
    · intro j hj hj1
      obtain ⟨pe, hpe, ho, hd, ht, hh⟩ := hconn j hj hj1
      exact ⟨pe, he hpe, ho, hd, ht, hh⟩

theorem chainFact_self {es : List Edge} {p : Proper} {e : Edge} {idx : Nat}
    (hge : es[idx]? = some e) (hself : e.tail = e.head) :
    ChainFact es p (e, idx) (some []) := by
  refine ⟨hge, ?_⟩
  simp only [ite_eq_left hself]

/-- The chain fact of a successful non-self `normalizeEdge`: the appended chain runs from
`e.tail` to `e.head` and its consecutive nodes are joined by the chain edges that
`appendChain` actually wrote, each carrying `idx` and `e.decl`. -/
theorem appendChain_chainFact {es : List Edge} {slot : Int} {p : Proper} {e : Edge}
    {idx s : Nat} (hge : es[idx]? = some e) (hne : e.tail ≠ e.head) (hs : 1 ≤ s) :
    ChainFact es (appendChain slot p e idx s) (e, idx)
      ((appendChain slot p e idx s).chains[p.chains.length]?) := by
  have hch : (appendChain slot p e idx s).chains[p.chains.length]? =
      some (chainOf e.tail e.head p.nodes.length s) := by
    simp only [appendChain]
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  unfold ChainFact
  refine ⟨hge, ?_⟩
  rw [ite_eq_right hne]
  refine ⟨chainOf e.tail e.head p.nodes.length s, hch, ?_, ?_, ?_, ?_⟩
  · rw [chainOf_length]
    omega
  · rw [chainOf_head? e.tail e.head p.nodes.length s hs]
  · rw [chainOf_getLast? e.tail e.head p.nodes.length s hs]
  · intro j hj hj1
    have hlen : (chainOf e.tail e.head p.nodes.length s).length = s + 1 :=
      chainOf_length _ _ _ _
    rw [hlen] at hj hj1
    refine ⟨{ tail := chainNode e.tail e.head p.nodes.length s j,
              head := chainNode e.tail e.head p.nodes.length s (j + 1),
              decl := e.decl, original := idx }, ?_, rfl, rfl, ?_, ?_⟩
    · simp only [appendChain]
      exact List.mem_append.mpr (Or.inr
        (List.mem_of_getElem? (chainEdges_getElem? e idx p.nodes.length s j (by omega))))
    · have hjle : j ≤ s := by omega
      obtain ⟨_, hget⟩ :=
        List.getElem?_eq_some_iff.mp (chainOf_getElem? e.tail e.head p.nodes.length s j hjle)
      rw [hget]
    · have hjle : j + 1 ≤ s := by omega
      obtain ⟨_, hget⟩ :=
        List.getElem?_eq_some_iff.mp
          (chainOf_getElem? e.tail e.head p.nodes.length s (j + 1) hjle)
      rw [hget]

theorem normalizeEdge_chainFact {es : List Edge} {slot : Int} {p p' : Proper} {e : Edge}
    {idx : Nat} (hge : es[idx]? = some e) (hcov : ∀ pe ∈ p.edges, CovEdge es pe)
    (hm : 1 ≤ e.minLen) (h : normalizeEdge slot p e idx = .ok p') :
    (∀ pe ∈ p'.edges, CovEdge es pe) ∧
    ChainFact es p' (e, idx) p'.chains[p.chains.length]? := by
  refine ⟨normalizeEdge_cov hge hcov h, ?_⟩
  unfold normalizeEdge at h
  split at h
  · next hself =>
    simp only [Except.ok.injEq] at h
    subst h
    refine ChainFact.trans (chainFact_self hge hself) (fun _ hp => hp) ?_
    show some [] = (p.chains ++ [[]])[p.chains.length]?
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  · split at h
    · simp at h
    · split at h
      · simp at h
      · next hne hlt _hov =>
        simp only [Except.ok.injEq] at h
        subst h
        have hspan : 1 ≤ rk p.rank e.head - rk p.rank e.tail := by omega
        have hs1 : 1 ≤ (rk p.rank e.head - rk p.rank e.tail).toNat := by omega
        refine ChainFact.trans (appendChain_chainFact hge hne hs1) (fun _ hp => hp) rfl

theorem normalizeLoop_edges_sub {slot : Int} :
    ∀ (l : List (Edge × Nat)) (p p' : Proper), normalizeLoop slot l p = .ok p' →
      p.edges ⊆ p'.edges := by
  intro l
  induction l with
  | nil =>
    intro p p' h
    simp only [normalizeLoop, Except.ok.injEq] at h
    subst h
    exact fun _ hp => hp
  | cons q qs ih =>
    intro p p' h
    unfold normalizeLoop at h
    split at h
    · simp at h
    · next p1 h1 =>
      intro pe hpemem
      exact ih p1 p' h (normalizeEdge_edges_sub h1 hpemem)

theorem normalizeLoop_chains_append {slot : Int} :
    ∀ (l : List (Edge × Nat)) (p p' : Proper), normalizeLoop slot l p = .ok p' →
      ∃ c : List (List Nat), p'.chains = p.chains ++ c := by
  intro l
  induction l with
  | nil =>
    intro p p' h
    simp only [normalizeLoop, Except.ok.injEq] at h
    subst h
    exact ⟨[], (List.append_nil p.chains).symm⟩
  | cons q qs ih =>
    intro p p' h
    obtain ⟨e, i⟩ := q
    unfold normalizeLoop at h
    split at h
    · simp at h
    · next p1 h1 =>
      obtain ⟨x, hx⟩ := normalizeEdge_chains_append h1
      obtain ⟨c, hc⟩ := ih p1 p' h
      exact ⟨[x] ++ c, by rw [hc, hx, List.append_assoc]⟩

/-- Chain facts and edge coverage survive the fold. The chain of the pair processed at
position `j` of `l` is the chain the output holds at position `p.chains.length + j`. -/
theorem normalizeLoop_chainFacts {es : List Edge} {slot : Int} :
    ∀ (l : List (Edge × Nat)) (p p' : Proper),
      (∀ x ∈ l, es[x.2]? = some x.1) →
      (∀ x ∈ l, 1 ≤ x.1.minLen) →
      normalizeLoop slot l p = .ok p' →
      (∀ pe ∈ p.edges, CovEdge es pe) →
      (∀ pe ∈ p'.edges, CovEdge es pe) ∧
      ∀ (j : Nat) (hj : j < l.length), ChainFact es p' l[j] p'.chains[p.chains.length + j]? := by
  intro l
  induction l with
  | nil =>
    intro p p' _ _ h hcov
    simp only [normalizeLoop, Except.ok.injEq] at h
    subst h
    exact ⟨hcov, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | cons q qs ih =>
    intro p p' hl hmin h hcov
    obtain ⟨e, i⟩ := q
    unfold normalizeLoop at h
    split at h
    · simp at h
    · next p1 h1 =>
      obtain ⟨hcov1, hchain⟩ := normalizeEdge_chainFact (hl (e, i) (by simp)) hcov
        (hmin (e, i) (by simp)) h1
      have h1len := normalizeEdge_chains_length h1
      obtain ⟨hcov', hrest⟩ := ih p1 p' (fun x hx => hl x (by simp [hx]))
        (fun x hx => hmin x (by simp [hx])) h hcov1
      obtain ⟨c, hcap⟩ := normalizeLoop_chains_append qs p1 p' h
      refine ⟨hcov', ?_⟩
      intro j hj
      cases j with
      | zero =>
        show ChainFact es p' (e, i) p'.chains[p.chains.length + 0]?
        rw [Nat.add_zero]
        have hpre : p.chains.length < p1.chains.length := by omega
        refine ChainFact.trans hchain (normalizeLoop_edges_sub qs p1 p' h) ?_
        rw [hcap, List.getElem?_append_left hpre]
      | succ k =>
        have hk : k < qs.length := by simpa using hj
        have hidx : p.chains.length + (k + 1) = p1.chains.length + k := by
          rw [h1len]; omega
        show ChainFact es p' (qs[k]) p'.chains[p.chains.length + (k + 1)]?
        rw [hidx]
        exact hrest k hk

/-- The normalize identity bridge for a successful run: every output proper edge declares an
in-bounds original index whose input edge carries the same declaration, the output holds one
chain per input edge, and every input edge index holds its own chain: empty for a self-loop,
otherwise a chain from the input tail to the input head whose consecutive nodes are joined by
output proper edges carrying that index and declaration. -/
def NormalizeOk (g : Graph) (_rank : List Int) (p : Proper) : Prop :=
  (∀ pe ∈ p.edges, CovEdge g.edges pe) ∧
  p.chains.length = g.edges.length ∧
  ∀ (i : Nat) (_hi : i < g.edges.length) (e : Edge), g.edges[i]? = some e →
    ChainFact g.edges p (e, i) p.chains[i]?

theorem normalize_ok {g : Graph} {rank : List Int} {p : Proper} (h : normalize g rank = .ok p) :
    NormalizeOk g rank p := by
  have hlength := normalize_chains_length h
  unfold normalize at h
  split at h
  · simp at h
  · next slot hslot =>
    split at h
    · next hc =>
      have hwf : g.wellformed = true := hc.1
      have hmem : ∀ x ∈ g.edges.zipIdx, g.edges[x.2]? = some x.1 :=
        fun x hx => List.mem_zipIdx_iff_getElem?.mp hx
      have hmin : ∀ x ∈ g.edges.zipIdx, 1 ≤ x.1.minLen := fun x hx =>
        (wellformed_spec hwf x.1 (mem_of_mem_zipIdx hx)).2.2
      obtain ⟨hcov1, hfacts⟩ :=
        normalizeLoop_chainFacts g.edges.zipIdx
          { nodes := g.nodes.map fun n => ⟨n, false, none, false⟩, edges := [], rank := rank,
            chains := [] } p hmem hmin h
          (by
            intro pe he
            simp at he)
      refine ⟨hcov1, hlength, ?_⟩
      intro i hi e hge
      have hlt : i < (g.edges.zipIdx).length := by
        rw [List.length_zipIdx]
        exact hi
      have h1 := List.getElem_zipIdx hlt
      have hpair : (g.edges.zipIdx)[i] = (e, i) := by
        rw [h1, (List.getElem?_eq_some_iff.mp hge).2]
        simp
      have hfact := hfacts i hlt
      rw [hpair] at hfact
      have hzero :
          ({ nodes := g.nodes.map fun n => ⟨n, false, none, false⟩, edges := [], rank := rank,
              chains := [] } : Proper).chains.length + i = i := by
        simp
      rw [hzero] at hfact
      exact hfact
    · simp at h

end NormalizeImpl

export NormalizeImpl (normalize)

theorem normalize_proper (g : Graph) (rank : List Int) (p : Proper)
    (h : normalize g rank = .ok p) : ∀ e ∈ p.edges, p.span e = 1 :=
  NormalizeImpl.normalize_proper g rank p h

theorem normalize_chains_length {g : Graph} {rank : List Int} {p : Proper}
    (h : normalize g rank = .ok p) : p.chains.length = g.edges.length :=
  NormalizeImpl.normalize_chains_length h

theorem normalize_ok {g : Graph} {rank : List Int} {p : Proper} (h : normalize g rank = .ok p) :
    NormalizeImpl.NormalizeOk g rank p :=
  NormalizeImpl.normalize_ok h

end Layered
end Elegant
