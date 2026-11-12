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
  List.replicate (s - 1) ⟨{ decl := e.decl, w := slot, h := 0 }, true, some idx⟩

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

opaque defaultSlot : Option Int :=
  match layoutconst.find? (fun c => c.name == "vector.slot") with
  | some c => some c.value
  | none => none

def slotOf (g : Graph) : Option Int :=
  if g.slot = 0 then defaultSlot else some g.slot

def normalize (g : Graph) (rank : List Int) : Except LayoutError Proper :=
  match slotOf g with
  | none => .error .domain
  | some slot =>
    if g.wellformed = true ∧ rank.length = g.nodes.length ∧ 0 ≤ slot then
      normalizeLoop slot g.edges.zipIdx
        { nodes := g.nodes.map fun n => ⟨n, false, none⟩
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
          { nodes := g.nodes.map fun n => ⟨n, false, none⟩
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

end NormalizeImpl

export NormalizeImpl (normalize)

theorem normalize_proper (g : Graph) (rank : List Int) (p : Proper)
    (h : normalize g rank = .ok p) : ∀ e ∈ p.edges, p.span e = 1 :=
  NormalizeImpl.normalize_proper g rank p h

end Layered
end Elegant
