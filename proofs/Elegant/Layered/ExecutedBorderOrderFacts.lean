import Elegant.Layered.Order

set_option autoImplicit false

namespace Elegant.Layered

namespace ExecutedBorderOrder

 theorem node_layer
    (p : Proper) (opts : OrderOptions) (result : OrderResult)
    (h : OrderImpl.orderWithBudget p opts = .ok result)
    {v : Nat} {n : ProperNode} (hv : p.nodes[v]? = some n) :
    OrderImpl.lay p v < result.layers.length ∧
      v ∈ result.layers.getD (OrderImpl.lay p v) [] := by
  have hvalid : OrderImpl.Valid p := by
    unfold OrderImpl.orderWithBudget at h
    split at h
    · assumption
    · simp at h
  have hL := (OrderImpl.orderWithBudget_spec p opts result h).1
  have hvr : v < p.rank.length := by
    rw [← hvalid.1]
    exact (List.getElem?_eq_some_iff.mp hv).1
  have hr : OrderImpl.lay p v < result.layers.length := by
    rw [hL.1]
    exact OrderImpl.lay_lt_layerCount p hvr
  exact ⟨hr, (OrderImpl.layer_mem hL hr).mpr ⟨hvr, rfl⟩⟩

structure Bracket (p : Proper) (result : OrderResult) (left member right : Nat) : Prop where
  rank_lt : OrderImpl.lay p member < result.layers.length
  layer_mem : result.layers.getD (OrderImpl.lay p member) [] ∈ result.layers
  left_mem : left ∈ result.layers.getD (OrderImpl.lay p member) []
  member_mem : member ∈ result.layers.getD (OrderImpl.lay p member) []
  right_mem : right ∈ result.layers.getD (OrderImpl.lay p member) []
  positions : ∃ leftIndex memberIndex rightIndex : Nat,
    (result.layers.getD (OrderImpl.lay p member) [])[leftIndex]? = some left ∧
    (result.layers.getD (OrderImpl.lay p member) [])[memberIndex]? = some member ∧
    (result.layers.getD (OrderImpl.lay p member) [])[rightIndex]? = some right ∧
    leftIndex < memberIndex ∧ memberIndex < rightIndex

theorem bracket
    (p : Proper) (opts : OrderOptions) (result : OrderResult)
    (h : OrderImpl.orderWithBudget p opts = .ok result)
    (hwf : OrderImpl.BordersWellFormed p)
    (left member right : Nat) (nl nm nr : ProperNode)
    (hl : p.nodes[left]? = some nl) (hm : p.nodes[member]? = some nm)
    (hr : p.nodes[right]? = some nr)
    (hlay : OrderImpl.lay p left = OrderImpl.lay p member)
    (hray : OrderImpl.lay p right = OrderImpl.lay p member)
    (hbl : nl.node.border = -1) (hbr : nr.node.border = 1)
    (hdl : nl.dummy = false) (hdm : nm.dummy = false) (hdr : nr.dummy = false)
    (hpl : nl.node.clusterPath <+: nm.node.clusterPath)
    (hpr : nr.node.clusterPath <+: nm.node.clusterPath)
    (hlm : left ≠ member) (hrm : right ≠ member) :
    Bracket p result left member right := by
  have horder : OrderImpl.order p opts = .ok result.layers := by
    simp [OrderImpl.order, h]
  obtain ⟨hrank, hmember⟩ := node_layer p opts result h hm
  have hleft := (node_layer p opts result h hl).2
  have hright := (node_layer p opts result h hr).2
  rw [hlay] at hleft
  rw [hray] at hright
  let layer := result.layers.getD (OrderImpl.lay p member) []
  have hlayer : layer ∈ result.layers := by
    have heq : layer = result.layers[OrderImpl.lay p member] := by
      simp [layer, List.getD_eq_getElem?_getD, hrank]
    rw [heq]
    exact List.getElem_mem hrank
  obtain ⟨li, hli, heli⟩ := List.mem_iff_getElem.mp hleft
  obtain ⟨mi, hmi, hemi⟩ := List.mem_iff_getElem.mp hmember
  obtain ⟨ri, hri, heri⟩ := List.mem_iff_getElem.mp hright
  have hli' : layer[li]? = some left := by
    simp only [layer, List.getElem?_eq_getElem hli, heli]
  have hmi' : layer[mi]? = some member := by
    simp only [layer, List.getElem?_eq_getElem hmi, hemi]
  have hri' : layer[ri]? = some right := by
    simp only [layer, List.getElem?_eq_getElem hri, heri]
  have hbefore := (order_border_ends p opts result.layers horder hwf layer hlayer
    li mi left member nl nm hli' hmi' hl hm hlm hdl hdm hpl).1 hbl
  have hafter := (order_border_ends p opts result.layers horder hwf layer hlayer
    ri mi right member nr nm hri' hmi' hr hm hrm hdr hdm hpr).2 hbr
  exact ⟨hrank, hlayer, hleft, hmember, hright,
    ⟨li, mi, ri, hli', hmi', hri', hbefore, hafter⟩⟩

theorem title_bracket
    (p : Proper) (opts : OrderOptions) (result : OrderResult)
    (h : OrderImpl.orderWithBudget p opts = .ok result)
    (hwf : OrderImpl.BordersWellFormed p)
    (left title right : Nat) (nl nt nr : ProperNode)
    (hl : p.nodes[left]? = some nl) (ht : p.nodes[title]? = some nt)
    (hr : p.nodes[right]? = some nr)
    (hlay : OrderImpl.lay p left = OrderImpl.lay p title)
    (hray : OrderImpl.lay p right = OrderImpl.lay p title)
    (hbl : nl.node.border = -1) (hbt : nt.node.border = 3) (hbr : nr.node.border = 1)
    (hdl : nl.dummy = false) (hdt : nt.dummy = false) (hdr : nr.dummy = false)
    (hpl : nl.node.clusterPath <+: nt.node.clusterPath)
    (hpr : nr.node.clusterPath <+: nt.node.clusterPath) :
    Bracket p result left title right := by
  have hlt : left ≠ title := by
    intro heq
    subst left
    have hn : nl = nt := Option.some.inj (hl.symm.trans ht)
    subst nl
    omega
  have hrt : right ≠ title := by
    intro heq
    subst right
    have hn : nr = nt := Option.some.inj (hr.symm.trans ht)
    subst nr
    omega
  exact bracket p opts result h hwf left title right nl nt nr hl ht hr hlay hray
    hbl hbr hdl hdt hdr hpl hpr hlt hrt

end ExecutedBorderOrder

end Elegant.Layered
