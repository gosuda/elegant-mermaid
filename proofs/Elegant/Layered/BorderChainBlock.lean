import Elegant.Layered.FrameEnvelope

set_option autoImplicit false

/-!
# The border chain is a single alignment block (layered-107, alignment-pick half)

`FrameEnvelope.BorderChainBlock` is the pipeline-level obligation of layered-107 that
remains after the coordinate-phase half: the border chain of one cluster must be a
single alignment block of each of the four Brandes-Köpf passes.

This module discharges it for the border chains the executed pipeline produces
(`OrderImpl.addClusterBorders`/`OrderImpl.borderLinks`, duplicated by
`borderAlignment`). The executed-pipeline alignment behaviour is isolated in the
named hypothesis `BorderChainUps`; everything else is proved from the
`Coords.lean` alignment machinery (`alignAll`, `members`, `mem`, `AF`).
-/

namespace Elegant.Layered
open Elegant.Layered.CoordsImpl

/-! ## Executed-pipeline alignment fact

For the border chains the executed pipeline produces, the four-pass alignment
fold `alignAll` links each chain node to its chain neighbour in the pass's
processing direction: the node processed first (the chain end at the pass's top
rank) has `up = none`, and every other chain node has `up` equal to its
predecessor in the pass-oriented chain. This is the executed form of the
layered-107 pick mechanism: `borderAlignment` inserts the border edge between
adjacent same-side border nodes of one cluster,
`typeOneConflicts_borderChain_unmarked` leaves it unmarked, and the median pick
(`alignPick`) selects it because the sibling cluster order rule
(`order_siblings_consistent`) places the border edge at the chain node's median
upper-neighbour position with `last < pos` along the pass layer.
-/

/-- The executed pipeline's `up`-pointer behaviour on one border chain: `ordered`
is the chain in the pass's processing order (by `rank`, then `pos`, of the
cluster context). The first node has `up = none`; every later node `v` has
`up v = some pred` where `pred` is the immediately preceding element of
`ordered`. -/
def BorderChainUps (ng cp : Int) (p : Proper) (layers : List (List Nat))
    (marked : Array Bool) (k : Nat) (chain ordered : List Nat)
    (_hL : Lay (clusterCtx ng cp p layers marked k)) : Prop :=
  ordered.Nodup ∧ ordered.Perm chain ∧
    (∀ (top : Nat) (rest : List Nat), ordered = top :: rest →
      (alignAll (clusterCtx ng cp p layers marked k)).up top = none) ∧
    ∀ i, (h : i + 1 < ordered.length) →
      (alignAll (clusterCtx ng cp p layers marked k)).up ordered[i + 1] =
        some ordered[i]

/-! ## BorderChainBlock -/

/-- layered-107 alignment-pick half: under the executed pipeline's `up`-pointer
behaviour `BorderChainUps`, every border chain is a single alignment block of
each of the four passes. -/
theorem borderChainBlock_of_ups {ng cp : Int} {p : Proper}
    {layers : List (List Nat)} {k : Nat} {chain ordered : List Nat}
    (_hk : k < 4) (hchain : chain ≠ [])
    (hmem : ∀ v ∈ chain, v ∈ layers.flatten)
    {pos : Array Nat}
    (hc : checkLayers (borderAlignment p layers) layers = .ok pos)
    (hL : Lay (clusterCtx ng cp (borderAlignment p layers) layers
      (typeOneConflicts (borderAlignment p layers) pos) k))
    (hups : BorderChainUps ng cp (borderAlignment p layers) layers
      (typeOneConflicts (borderAlignment p layers) pos) k chain ordered hL) :
    BorderChainBlock ng cp (borderAlignment p layers) layers
      (typeOneConflicts (borderAlignment p layers) pos) k chain := by
  cases ordered with
  | nil => exact absurd hups.2.1.nil_eq.symm hchain
  | cons top rest =>
    obtain ⟨hL', hE⟩ := clusterCtx_facts hc
    have hA := af_of_layout hL' hE
    have hfl : ∀ v ∈ chain, v ∈
        (clusterCtx ng cp (borderAlignment p layers) layers
          (typeOneConflicts (borderAlignment p layers) pos) k).layers.flatten := by
      intro v hv
      have h1 := hmem v hv
      exact (passLayers_perm layers k).mem_iff.mpr h1
    have h0lt : 0 < (top :: rest).length := by simp
    have hroot : ∀ i, (h : i < (top :: rest).length) →
        (alignAll (clusterCtx ng cp (borderAlignment p layers) layers
          (typeOneConflicts (borderAlignment p layers) pos) k)).root
          (top :: rest)[i] = (top :: rest)[0] := by
      intro i
      induction i with
      | zero =>
        intro hi
        have hchain0 : (top :: rest)[0] ∈ chain :=
          (hups.2.1.mem_iff).mp (List.getElem_mem hi)
        have h0 : (top :: rest)[0] ∈
            (clusterCtx ng cp (borderAlignment p layers) layers
              (typeOneConflicts (borderAlignment p layers) pos) k).layers.flatten :=
          hfl _ hchain0
        rw [hA.root_eq _ h0]
        simp only [List.getElem_cons_zero, hups.2.2.1 top rest rfl]
      | succ i ih =>
        intro hi
        have hilt : i < (top :: rest).length := by omega
        have hmemi : (top :: rest)[i + 1] ∈ (top :: rest) :=
          List.getElem_mem hi
        have hv_in : (top :: rest)[i + 1] ∈ chain :=
          (hups.2.1.mem_iff).mp hmemi
        have hfl_i : (top :: rest)[i + 1] ∈
            (clusterCtx ng cp (borderAlignment p layers) layers
              (typeOneConflicts (borderAlignment p layers) pos) k).layers.flatten :=
          hfl _ hv_in
        have hup := hups.2.2.2 i hi
        rw [hA.root_eq _ hfl_i]
        simp only [hup]
        rw [ih hilt]
    refine ⟨(top :: rest)[0], ?_, ?_, ?_, ?_⟩
    · exact (hups.2.1.mem_iff).mp (List.getElem_mem h0lt)
    · exact hroot 0 h0lt
    · exact hfl _ ((hups.2.1.mem_iff).mp (List.getElem_mem h0lt))
    · intro v hv
      have hin : v ∈ (top :: rest) := (hups.2.1.mem_iff).mpr hv
      obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hin
      have hro := hroot i hilt
      have hmemi : (top :: rest)[i] ∈ (top :: rest) := List.getElem_mem hilt
      have hchaini : (top :: rest)[i] ∈ chain := (hups.2.1.mem_iff).mp hmemi
      have hm := node_mem hA _ (top :: rest)[i] (hfl _ hchaini) rfl
      rw [hro, hget] at hm
      exact hm

end Elegant.Layered
