import Elegant.Layered.DivergeSiblingTiesProof
import Elegant.Layered.DivergeTiedSweepProof
import Elegant.Layered.ForeignBorderDivergeStableProof
import Init.Data.List.Nat.Pairwise

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open OrderImpl

private theorem pair_sublist_iff_lt {row : List Nat} {a b i j : Nat}
    (hnd : row.Nodup) (hi : row[i]? = some a) (hj : row[j]? = some b) :
    [a, b].Sublist row ↔ i < j := by
  obtain ⟨hiLt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  refine ⟨?_, ?_⟩
  · intro hp
    simpa only [hnd.idxOf_getElem i hiLt, hnd.idxOf_getElem j hjLt] using
      idxOf_pair_lt hnd hp
  · have hp : row.Pairwise (fun x y => [x, y].Sublist row) :=
      List.pairwise_of_forall_sublist (fun h => h)
    exact List.pairwise_iff_getElem.mp hp i j hiLt hjLt

theorem divergeChainAgree_siblingNormalise
    {p : Proper} {Y : List (List Nat)}
    (hL : OrderImpl.Layering p Y) (hc : OrderImpl.LayersContiguous p Y)
    (ha : DivergeChainAgree p Y) :
    DivergeChainAgree p (OrderImpl.siblingNormalise p Y) := by
  rcases siblingNormalise_cases p Y with hsame | ⟨num, hmap⟩
  · simpa only [hsame] using ha
  rw [hmap]
  intro k1 k2 l1 l2 hk1 hk2 a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2 hA hB hAB
    i j i' j' hi1 hj1 hi2 hj2
  rw [List.getElem?_map] at hk1 hk2
  obtain ⟨row1, hY1, rfl⟩ := Option.map_eq_some_iff.mp hk1
  obtain ⟨row2, hY2, rfl⟩ := Option.map_eq_some_iff.mp hk2
  have hrow1 := List.mem_of_getElem? hY1
  have hrow2 := List.mem_of_getElem? hY2
  have hnd1 := layering_mem_nodup hL hrow1
  have hnd2 := layering_mem_nodup hL hrow2
  have perm1 := siblingLayer_perm p num row1
  have perm2 := siblingLayer_perm p num row2
  have hout1 := perm1.nodup_iff.mpr hnd1
  have hout2 := perm2.nodup_iff.mpr hnd2
  have hA' := hpathA.symm.trans hA
  have hB' := hpathB.symm.trans hB
  by_cases htie : num A = num B
  · have hmA := perm1.mem_iff.mp (List.mem_of_getElem? hi1)
    have hmB := perm1.mem_iff.mp (List.mem_of_getElem? hj1)
    have hmA' := perm2.mem_iff.mp (List.mem_of_getElem? hi2)
    have hmB' := perm2.mem_iff.mp (List.mem_of_getElem? hj2)
    have htie1 := siblingLayer_tied_pair_iff hnd1 (hc row1 hrow1) hmA hmB
      ((nodePath_of_node hna hda).trans hA) ((nodePath_of_node hnb hdb).trans hB) hAB htie
    have htie2 := siblingLayer_tied_pair_iff hnd2 (hc row2 hrow2) hmA' hmB'
      ((nodePath_of_node hna' hda').trans hA') ((nodePath_of_node hnb' hdb').trans hB') hAB htie
    obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp hmA
    obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hmB
    obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp hmA'
    obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hmB'
    calc
      i < j ↔ [a, b].Sublist (siblingLayer p num row1) := (pair_sublist_iff_lt hout1 hi1 hj1).symm
      _ ↔ [a, b].Sublist row1 := htie1.symm
      _ ↔ i0 < j0 := pair_sublist_iff_lt hnd1 hi0 hj0
      _ ↔ i0' < j0' := ha k1 k2 row1 row2 hY1 hY2 a b a' b' na nb na' nb'
        hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
        hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
      _ ↔ [a', b'].Sublist row2 := (pair_sublist_iff_lt hnd2 hi0' hj0').symm
      _ ↔ [a', b'].Sublist (siblingLayer p num row2) := htie2
      _ ↔ i' < j' := pair_sublist_iff_lt hout2 hi2 hj2
  · have e1 : siblingLayer p num (Y.getD k1 []) = siblingLayer p num row1 := by
      simp [List.getD_eq_getElem?_getD, hY1]
    have e2 : siblingLayer p num (Y.getD k2 []) = siblingLayer p num row2 := by
      simp [List.getD_eq_getElem?_getD, hY2]
    exact normalise_pair_stable (Y := Y) (num := num) (k1 := k1) (k2 := k2) e1 e2
      hna hnb hna' hnb' hda hdb hda' hdb' hA hB hA' hB' hAB htie hout1 hout2 hi1 hj1 hi2 hj2

end Elegant.Layered.PipelineImpl
