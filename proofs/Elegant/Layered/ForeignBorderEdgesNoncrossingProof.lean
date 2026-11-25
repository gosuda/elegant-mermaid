import Elegant.Layered.ForeignSideMarkingCrossedProof
import Elegant.Layered.ForeignBorderSideUpsProof
import Elegant.Layered.Order
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameEnvelope

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Border-chain edges never strictly interleave in framed runs.

Two border chain edges over one layer pair never strictly interleave in a
successful component run of a measured, well-formed, framed input.

Proof idea: both edges join same-side, same-path marker pairs on consecutive
pass ranks, so the lower endpoints share one run layer and the upper endpoints
share the next. Transporting the pass positions to run-layer indices (via
`nodeTransport`, handling the pass permutation parity), the two cluster paths
are either prefix-comparable or divergent (`list_prefix_trichotomy`). In the
comparable case the outer marker's side forces the run order on both layers
(`OrderImpl.order_border_ends`), and exactly one layer contradicts the
interleave pattern whichever the parity. In the divergent case the relative
order is the same on both layers by `ForeignBorderDivergeStable`, which
contradicts the pattern.
-/

/-- Two cluster paths are divergent: they share a (possibly empty) prefix and
then differ. This is the negation of prefix comparability. -/
def Divergent (l1 l2 : List Nat) : Prop :=
  ∃ P A B r1 r2, l1 = P ++ A :: r1 ∧ l2 = P ++ B :: r2 ∧ A ≠ B

/-- Every two cluster paths are prefix-comparable or divergent. -/
theorem list_prefix_trichotomy (l1 l2 : List Nat) :
    l1 <+: l2 ∨ l2 <+: l1 ∨ Divergent l1 l2 := by
  induction l1 generalizing l2 with
  | nil => exact Or.inl ⟨l2, (List.nil_append l2).symm⟩
  | cons a s1 ih =>
    cases l2 with
    | nil => exact Or.inr (Or.inl ⟨a :: s1, (List.nil_append (a :: s1)).symm⟩)
    | cons b s2 =>
      by_cases hab : a = b
      · subst hab
        rcases ih s2 with h | h | h
        · obtain ⟨t, ht⟩ := h
          exact Or.inl ⟨t, by simp [ht, List.cons_append]⟩
        · obtain ⟨t, ht⟩ := h
          exact Or.inr (Or.inl ⟨t, by simp [ht, List.cons_append]⟩)
        · obtain ⟨P, A, B, r1, r2, h1, h2, hne⟩ := h
          exact Or.inr (Or.inr ⟨a :: P, A, B, r1, r2,
            by simp [h1, List.cons_append], by simp [h2, List.cons_append], hne⟩)
      · exact Or.inr (Or.inr ⟨[], a, b, s1, s2, rfl, rfl, hab⟩)

/-- A `borderChain` edge joins two same-side markers with one shared path.
The endpoint records are taken as hypotheses so that case analysis on lookups
never generalizes the caller's goal. -/
theorem borderChain_side_endpoints {p : Proper} {e : ProperEdge} {nt nh : ProperNode}
    (ht : p.nodes[e.tail]? = some nt) (hh : p.nodes[e.head]? = some nh)
    (hbc : CoordsImpl.borderChain p e = true) :
    ∃ s C, (s = -1 ∨ s = 1) ∧ nt.node.border = s ∧ nh.node.border = s ∧
      nt.node.clusterPath = C ∧ nh.node.clusterPath = C := by
  unfold CoordsImpl.borderChain at hbc
  rw [ht, hh] at hbc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbc
  obtain ⟨⟨h1 | h1, h2⟩, h3⟩ := hbc
  · exact ⟨_, _, Or.inl h1, rfl, h2.symm, rfl, h3.symm⟩
  · exact ⟨_, _, Or.inr h1, rfl, h2.symm, rfl, h3.symm⟩

/-- A `±1` border marker of a well-formed graph is not a dummy. -/
theorem dummy_false_of_border {p : Proper} (hwf : OrderImpl.BordersWellFormed p)
    {v : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n)
    (hb : n.node.border = -1 ∨ n.node.border = 1) : n.dummy = false := by
  generalize hd : n.dummy = d
  cases d with
  | false => rfl
  | true =>
    exfalso
    have h0 := hwf.2.2 v n hn hd
    rcases hb with h1 | h1 <;> omega

/-! ## Ordering-stage stability for framed inputs -/

/-- Divergent side markers retain their relative order across layers of a
successful framed run. The framing scope excludes the successful component run
in `wip/Probe/DivergeUnframedReturnedCounterexample.lean`, which reverses it. -/
def ForeignBorderDivergeStable : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
    ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      run.coordinateProper.nodes[a']? = some na' →
      run.coordinateProper.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      Divergent na.node.clusterPath nb.node.clusterPath →
      ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
        l2[i']? = some a' → l2[j']? = some b' →
        (i < j ↔ i' < j')

/-! ## The executed non-crossing theorem. -/

/-- Two border chain edges over one layer pair never strictly interleave in
a successful component run of a measured, well-formed, framed input. -/
theorem foreignBorderEdgesNoncrossing_executed {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hstab : ForeignBorderDivergeStable) :
    ForeignBorderEdgesNoncrossing P run pos k := by
  intro e f w x a b he hf he_or hf_or hbe hbf hr1 hr2 hr3 hp1 hp2
  obtain ⟨hL, hE⟩ :=
    Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos
  have hLay : CoordsImpl.Lay (sideCtx P run pos k) := hL
  have hEdge : CoordsImpl.EdgeOK (sideCtx P run pos k) := hE
  have hperm := CoordsImpl.passLayers_perm run.layers k
  have hctxL : (sideCtx P run pos k).layers = CoordsImpl.passLayers run.layers k := rfl
  have torun : ∀ v : Nat, v ∈ (sideCtx P run pos k).layers.flatten →
      v ∈ run.layers.flatten := by
    intro v hv
    rw [hctxL] at hv
    exact hperm.mem_iff.mp hv
  obtain ⟨hte_fl, hhe_fl, -⟩ := hEdge e he
  obtain ⟨htf_fl, hhf_fl, -⟩ := hEdge f hf
  have hew : (sideCtx P run pos k).edges[e]!.tail = w ∨
      (sideCtx P run pos k).edges[e]!.head = w := by
    rcases he_or with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hex : (sideCtx P run pos k).edges[e]!.tail = x ∨
      (sideCtx P run pos k).edges[e]!.head = x := by
    rcases he_or with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have hea : (sideCtx P run pos k).edges[f]!.tail = a ∨
      (sideCtx P run pos k).edges[f]!.head = a := by
    rcases hf_or with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have heb : (sideCtx P run pos k).edges[f]!.tail = b ∨
      (sideCtx P run pos k).edges[f]!.head = b := by
    rcases hf_or with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have hmw : w ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hew with h | h
    · rw [← h]; exact hte_fl
    · rw [← h]; exact hhe_fl
  have hmx : x ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hex with h | h
    · rw [← h]; exact hte_fl
    · rw [← h]; exact hhe_fl
  have hma : a ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hea with h | h
    · rw [← h]; exact htf_fl
    · rw [← h]; exact hhf_fl
  have hmb : b ∈ (sideCtx P run pos k).layers.flatten := by
    rcases heb with h | h
    · rw [← h]; exact htf_fl
    · rw [← h]; exact hhf_fl
  obtain ⟨hrank_w, lw, iw, jw, hiw, hjw, hposw, _hvalw, hrkw⟩ :=
    nodeTransport hpos hLay (torun w hmw)
  obtain ⟨hrank_a, la, ia, ja, hia, hja, hposa, _hvala, hrka⟩ :=
    nodeTransport hpos hLay (torun a hma)
  obtain ⟨hrank_x, lx, ix, jx, hix, hjx, hposx, _hvalx, hrkx⟩ :=
    nodeTransport hpos hLay (torun x hmx)
  obtain ⟨hrank_b, lb, ib, jb, hib, hjb, hposb, _hvalb, hrkb⟩ :=
    nodeTransport hpos hLay (torun b hmb)
  have hr1I : ((sideCtx P run pos k).rank[w]! : Int) + 1 =
      ((sideCtx P run pos k).rank[x]! : Int) := by exact_mod_cast hr1
  have hr2I : ((sideCtx P run pos k).rank[a]! : Int) + 1 =
      ((sideCtx P run pos k).rank[b]! : Int) := by exact_mod_cast hr2
  have hr3I : ((sideCtx P run pos k).rank[x]! : Int) =
      ((sideCtx P run pos k).rank[b]! : Int) := by exact_mod_cast hr3
  have hiw_eq : iw = ia := by
    have hlow : ((sideCtx P run pos k).rank[w]! : Int) =
        ((sideCtx P run pos k).rank[a]! : Int) := by omega
    rw [hrank_w, hrank_a] at hlow
    by_cases hk2 : 2 ≤ k
    · rw [ite_eq_left hk2, ite_eq_left hk2] at hlow
      omega
    · rw [ite_eq_right hk2, ite_eq_right hk2] at hlow
      omega
  have hix_eq : ix = ib := by
    have hhigh : ((sideCtx P run pos k).rank[x]! : Int) =
        ((sideCtx P run pos k).rank[b]! : Int) := by omega
    rw [hrank_x, hrank_b] at hhigh
    by_cases hk2 : 2 ≤ k
    · rw [ite_eq_left hk2, ite_eq_left hk2] at hhigh
      omega
    · rw [ite_eq_right hk2, ite_eq_right hk2] at hhigh
      omega
  subst hiw_eq
  subst hix_eq
  have hlla : lw = la := Option.some.inj (hiw.symm.trans hia)
  have hllb : lx = lb := Option.some.inj (hix.symm.trans hib)
  subst hlla
  subst hllb
  have hbw : jw < lw.length := (List.getElem?_eq_some_iff.mp hjw).1
  have hba : ja < lw.length := (List.getElem?_eq_some_iff.mp hja).1
  have hbx : jx < lx.length := (List.getElem?_eq_some_iff.mp hjx).1
  have hbb : jb < lx.length := (List.getElem?_eq_some_iff.mp hjb).1
  have tLo : (k % 2 = 1 → jw < ja) ∧ (k % 2 ≠ 1 → ja < jw) := by
    constructor
    · intro hkodd
      rw [ite_eq_left hkodd] at hposw hposa
      omega
    · intro hne
      rw [ite_eq_right hne] at hposw hposa
      omega
  have tHi : (k % 2 = 1 → jb < jx) ∧ (k % 2 ≠ 1 → jx < jb) := by
    constructor
    · intro hkodd
      rw [ite_eq_left hkodd] at hposx hposb
      omega
    · intro hne
      rw [ite_eq_right hne] at hposx hposb
      omega
  have hERec : ∃ se Ce nw nx, (sideBase run).nodes[w]? = some nw ∧
      (sideBase run).nodes[x]? = some nx ∧ (se = -1 ∨ se = 1) ∧
      nw.node.border = se ∧ nx.node.border = se ∧
      nw.node.clusterPath = Ce ∧ nx.node.clusterPath = Ce := by
    cases htE : (sideBase run).nodes[(sideCtx P run pos k).edges[e]!.tail]? with
    | none =>
      have hfalse : CoordsImpl.borderChain (sideBase run)
          (sideCtx P run pos k).edges[e]! = false := by
        unfold CoordsImpl.borderChain
        rw [htE]
      rw [hfalse] at hbe
      simp at hbe
    | some nt =>
      cases hhE : (sideBase run).nodes[(sideCtx P run pos k).edges[e]!.head]? with
      | none =>
        have hfalse : CoordsImpl.borderChain (sideBase run)
            (sideCtx P run pos k).edges[e]! = false := by
          unfold CoordsImpl.borderChain
          rw [htE, hhE]
        rw [hfalse] at hbe
        simp at hbe
      | some nh =>
        obtain ⟨s, C, hs, hst, hsh, hpt, hph⟩ := borderChain_side_endpoints htE hhE hbe
        rcases he_or with ⟨hte, hhe⟩ | ⟨hte, hhe⟩
        · rw [hte] at htE
          rw [hhe] at hhE
          exact ⟨s, C, nt, nh, htE, hhE, hs, hst, hsh, hpt, hph⟩
        · rw [hhe] at hhE
          rw [hte] at htE
          exact ⟨s, C, nh, nt, hhE, htE, hs, hsh, hst, hph, hpt⟩
  obtain ⟨se, Ce, nw, nx, hnw, hnx, hse_or, hsew, hsex, hpew, hpex⟩ := hERec
  have hFRec : ∃ sf Cf na nb, (sideBase run).nodes[a]? = some na ∧
      (sideBase run).nodes[b]? = some nb ∧ (sf = -1 ∨ sf = 1) ∧
      na.node.border = sf ∧ nb.node.border = sf ∧
      na.node.clusterPath = Cf ∧ nb.node.clusterPath = Cf := by
    cases htF : (sideBase run).nodes[(sideCtx P run pos k).edges[f]!.tail]? with
    | none =>
      have hfalse : CoordsImpl.borderChain (sideBase run)
          (sideCtx P run pos k).edges[f]! = false := by
        unfold CoordsImpl.borderChain
        rw [htF]
      rw [hfalse] at hbf
      simp at hbf
    | some nt =>
      cases hhF : (sideBase run).nodes[(sideCtx P run pos k).edges[f]!.head]? with
      | none =>
        have hfalse : CoordsImpl.borderChain (sideBase run)
            (sideCtx P run pos k).edges[f]! = false := by
          unfold CoordsImpl.borderChain
          rw [htF, hhF]
        rw [hfalse] at hbf
        simp at hbf
      | some nh =>
        obtain ⟨s, C, hs, hst, hsh, hpt, hph⟩ := borderChain_side_endpoints htF hhF hbf
        rcases hf_or with ⟨hta, hha⟩ | ⟨hta, hha⟩
        · rw [hta] at htF
          rw [hha] at hhF
          exact ⟨s, C, nt, nh, htF, hhF, hs, hst, hsh, hpt, hph⟩
        · rw [hha] at hhF
          rw [hta] at htF
          exact ⟨s, C, nh, nt, hhF, htF, hs, hsh, hst, hph, hpt⟩
  have hnw' : run.coordinateProper.nodes[w]? = some nw := hnw
  have hnx' : run.coordinateProper.nodes[x]? = some nx := hnx
  obtain ⟨sf, Cf, na, nb, hna, hnb, hsf_or, hsfa, hsfb, hpfa, hpfb⟩ := hFRec
  have hna' : run.coordinateProper.nodes[a]? = some na := hna
  have hnb' : run.coordinateProper.nodes[b]? = some nb := hnb
  have hbwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hdnw : nw.dummy = false :=
    dummy_false_of_border hbwf hnw' (by rw [hsew]; exact hse_or)
  have hdnx : nx.dummy = false :=
    dummy_false_of_border hbwf hnx' (by rw [hsex]; exact hse_or)
  have hdna : na.dummy = false :=
    dummy_false_of_border hbwf hna' (by rw [hsfa]; exact hsf_or)
  have hdnb : nb.dummy = false :=
    dummy_false_of_border hbwf hnb' (by rw [hsfb]; exact hsf_or)
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  have hwa : w ≠ a := by
    intro h
    rw [h] at hp1
    omega
  have hxb : x ≠ b := by
    intro h
    rw [h] at hp2
    omega
  have hmem_lo : lw ∈ run.layers := List.mem_of_getElem? hiw
  have hmem_hi : lx ∈ run.layers := List.mem_of_getElem? hix
  rcases list_prefix_trichotomy Ce Cf with hpre | hpre | hdiv
  · have hpre' : nw.node.clusterPath <+: na.node.clusterPath := by
      rw [hpew, hpfa]; exact hpre
    have hpreU' : nx.node.clusterPath <+: nb.node.clusterPath := by
      rw [hpex, hpfb]; exact hpre
    have oeLo := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hbwf lw hmem_lo jw ja w a nw na hjw hja hnw' hna' hwa hdnw hdna hpre'
    have oeHi := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hbwf lx hmem_hi jx jb x b nx nb hjx hjb hnx' hnb' hxb hdnx hdnb hpreU'
    rcases hse_or with hse | hse
    · by_cases hkodd : k % 2 = 1
      · have gHi : jx < jb := oeHi.1 (by rw [hsex, hse])
        have u := tHi.1 hkodd
        omega
      · have gLo : jw < ja := oeLo.1 (by rw [hsew, hse])
        have l := tLo.2 hkodd
        omega
    · by_cases hkodd : k % 2 = 1
      · have gLo : ja < jw := oeLo.2 (by rw [hsew, hse])
        have l := tLo.1 hkodd
        omega
      · have gHi : jb < jx := oeHi.2 (by rw [hsex, hse])
        have u := tHi.2 hkodd
        omega
  · have haw : a ≠ w := Ne.symm hwa
    have hbx' : b ≠ x := Ne.symm hxb
    have hpre' : na.node.clusterPath <+: nw.node.clusterPath := by
      rw [hpfa, hpew]; exact hpre
    have hpreU' : nb.node.clusterPath <+: nx.node.clusterPath := by
      rw [hpfb, hpex]; exact hpre
    have oeLo := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hbwf lw hmem_lo ja jw a w na nw hja hjw hna' hnw' haw hdna hdnw hpre'
    have oeHi := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hbwf lx hmem_hi jb jx b x nb nx hjb hjx hnb' hnx' hbx' hdnb hdnx hpreU'
    rcases hsf_or with hsf | hsf
    · by_cases hkodd : k % 2 = 1
      · have gLo : ja < jw := oeLo.1 (by rw [hsfa, hsf])
        have l := tLo.1 hkodd
        omega
      · have gHi : jb < jx := oeHi.1 (by rw [hsfb, hsf])
        have u := tHi.2 hkodd
        omega
    · by_cases hkodd : k % 2 = 1
      · have gHi : jx < jb := oeHi.2 (by rw [hsfb, hsf])
        have u := tHi.1 hkodd
        omega
      · have gLo : jw < ja := oeLo.2 (by rw [hsfa, hsf])
        have l := tLo.2 hkodd
        omega
  · have hdiv' : Divergent nw.node.clusterPath na.node.clusterPath := by
      rw [hpew, hpfa]; exact hdiv
    have hiff := hstab hgraph hlines hwf hframed hcomp hrun hmem_lo hmem_hi
      hnw' hna' (by rw [hsew]; exact hse_or) (by rw [hsfa]; exact hsf_or)
      hnx' hnb' (by rw [hsex]; exact hse_or) (by rw [hsfb]; exact hsf_or)
      (hpew.trans hpex.symm) (hpfa.trans hpfb.symm) hdiv' hjw hja hjx hjb
    by_cases hkodd : k % 2 = 1
    · have l := tLo.1 hkodd
      have u := tHi.1 hkodd
      omega
    · have l := tLo.2 hkodd
      have u := tHi.2 hkodd
      omega

end Elegant.Layered.PipelineImpl
