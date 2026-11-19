import Elegant.Layered.ForeignBorderSideUpsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Alignment-fold bound for foreign side chains.

Target: `foreignSideFoldBound` below — the `ForeignSideFoldBound` residual of
`ForeignBorderSideUpsProof`: at each non-head side-chain node, every alignment
pick made while processing the layer prefix before that node targets a position
strictly left of the chain predecessor's position.

Proof idea: a fold invariant over the layer prefix is overkill — the statement
quantifies over every `last`, so the running-`last` gating cannot be the
mechanism. The mechanism is conflict marking plus median structure: any pick
that would target a position at or right of the predecessor crosses the chain
edge and is therefore marked, hence never picked.

Probe (`proofs/wip/Probe/SideFoldBoundProbe.lean`, real `componentRun` on five
group inputs × components × candidates 0..4):
- 400 nonempty executed side chains; `foldFails = 0` on all 400 (conclusion holds).
- `prefixOk` (every upper neighbour left of the predecessor) fails on 130 of
  400 chains / 150 prefix nodes; every one of the 150 violating upper-neighbour
  edges is `marked = true`, `border = false`, `inner = false`.
- Census over every edge pair sharing a layer-pair with strict endpoint
  interleave against a border edge: 600 pairs, 600 marked, 0 unmarked (no
  unmarked pair of any kind — border, inner, or plain).

Residual left open (exactly one, about the marking pass): `ForeignSideMarkingCrossed`
— every edge interleaving a border chain edge over the same layer-pair is in the
conflict set. It is stated orientation-free (both endpoint orders allowed) so the
proof needs no proper-rank transport or pass-direction (`k`) case analysis; it
carries no inner-ness or border-ness premise because the probe census shows the
clean statement holds as stated (inner edges crossing a border edge are marked
by the pass's first disjunct, and no border edge interleaves a border edge in
the executed runs). The census product form implies the one-direction form used
here: `(w - a) > 0 ∧ (x - b) < 0` gives a negative product.
-/

/-- Marking-pass residual (one phase: the `typeOneConflicts` conflict set of the
executed pass). Any edge interleaving a border chain edge over the same layer
pair — endpoints in either order, one crossing direction — is marked. This is
the orientation-free form of the pass's cross-a-border-edge marking rule, which
the probe census validates (600/600 interleaves marked on executed runs). -/
def ForeignSideMarkingCrossed (P : Params) (run : Run) (pos : Array Nat)
    (k : Nat) : Prop :=
  ∀ (e f w x a b : Nat),
    e < (sideCtx P run pos k).edges.size →
    f < (sideCtx P run pos k).edges.size →
    ((sideCtx P run pos k).edges[e]!.tail = w ∧
        (sideCtx P run pos k).edges[e]!.head = x ∨
      (sideCtx P run pos k).edges[e]!.tail = x ∧
        (sideCtx P run pos k).edges[e]!.head = w) →
    ((sideCtx P run pos k).edges[f]!.tail = a ∧
        (sideCtx P run pos k).edges[f]!.head = b ∨
      (sideCtx P run pos k).edges[f]!.tail = b ∧
        (sideCtx P run pos k).edges[f]!.head = a) →
    CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[f]!) = true →
    (sideCtx P run pos k).rank[w]! + 1 = (sideCtx P run pos k).rank[x]! →
    (sideCtx P run pos k).rank[a]! + 1 = (sideCtx P run pos k).rank[b]! →
    (sideCtx P run pos k).rank[x]! = (sideCtx P run pos k).rank[b]! →
    ((sideCtx P run pos k).pos[a]! : Int) <
      ((sideCtx P run pos k).pos[w]! : Int) →
    ((sideCtx P run pos k).pos[x]! : Int) <
      ((sideCtx P run pos k).pos[b]! : Int) →
    (sideCtx P run pos k).marked[e]! = true

/-- From a successful pick, the median edge: unmarked, in `upperEdges`, ending
at `w`, one rank above. Mirrors `CoordsImpl.alignPick_spec`. -/
theorem alignPick_unmarked_edge {c : CoordsImpl.Ctx} (hE : CoordsImpl.EdgeOK c)
    {v : Nat} {last : Int} {w : Nat}
    (h : CoordsImpl.alignPick c v last = some w) :
    ∃ e : Nat, e < c.edges.size ∧
      e ∈ CoordsImpl.upperEdges c.edges c.rank c.pos v ∧
      c.marked[e]! = false ∧ CoordsImpl.otherEnd c.edges[e]! v = w ∧
      w ∈ c.layers.flatten ∧ c.rank[w]! + 1 = c.rank[v]! ∧
      last < (c.pos[w]! : Int) := by
  unfold CoordsImpl.alignPick at h
  obtain ⟨kk, _, hk⟩ := List.exists_of_findSome?_eq_some h
  cases hes : (CoordsImpl.upperEdges c.edges c.rank c.pos v)[kk]? with
  | none =>
    rw [hes] at hk
    cases hk
  | some e =>
    rw [hes] at hk
    simp only [Option.bind_some] at hk
    by_cases hc : (!c.marked[e]! &&
      decide (last < (c.pos[CoordsImpl.otherEnd c.edges[e]! v]! : Int))) = true
    · rw [ite_eq_left hc] at hk
      cases hk
      have hpair : c.marked[e]! = false ∧
          last < (c.pos[CoordsImpl.otherEnd c.edges[e]! v]! : Int) := by
        simpa using hc
      have hme := CoordsImpl.mem_upperEdges (List.mem_of_getElem? hes)
      obtain ⟨hesz, hcase⟩ := hme
      obtain ⟨ht, hh, hadj⟩ := hE e hesz
      refine ⟨e, hesz, List.mem_of_getElem? hes, hpair.1, rfl, ?_, ?_, ?_⟩
      · unfold CoordsImpl.otherEnd
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hnt : (c.edges[e]!.tail == v) = false := by
            have hne : c.edges[e]!.tail ≠ v := by
              intro e2
              rw [e2, ← h1] at h2
              omega
            simpa using hne
          rw [hnt]
          simp only [Bool.false_eq_true, ite_false]
          simpa using ht
        · have hnt : (c.edges[e]!.tail == v) = true := by simpa using h1
          rw [hnt]
          simp only [ite_true]
          simpa using hh
      · unfold CoordsImpl.otherEnd
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hnt : (c.edges[e]!.tail == v) = false := by
            have hne : c.edges[e]!.tail ≠ v := by
              intro e2
              rw [e2, ← h1] at h2
              omega
            simpa using hne
          rw [hnt]
          simp only [Bool.false_eq_true, ite_false]
          rw [h1] at hadj
          omega
        · have hnt : (c.edges[e]!.tail == v) = true := by simpa using h1
          rw [hnt]
          simp only [ite_true]
          rw [h1] at hadj
          omega
      · exact hpair.2
    · rw [ite_eq_right hc] at hk
      cases hk

/-- Nodes of a layer prefix sit on the same layer, left of the cutoff. -/
theorem prefix_mem_pos_lt {c : CoordsImpl.Ctx} (hL : CoordsImpl.Lay c)
    {v x : Nat} (hv : v ∈ c.layers.flatten)
    (hx : x ∈ (c.layers.getD (c.rank[v]!) []).take (c.pos[v]!)) :
    x ∈ c.layers.flatten ∧ c.rank[x]! = c.rank[v]! ∧
      c.pos[x]! < c.pos[v]! := by
  obtain ⟨L, hLget, hLv⟩ := hL.loc hv
  have hgetD : c.layers.getD (c.rank[v]!) [] = L := by
    rw [List.getD_eq_getElem?_getD, hLget]
    rfl
  rw [hgetD] at hx
  have hxL : x ∈ L := List.mem_of_mem_take hx
  have hFL : L ∈ c.layers := List.mem_of_getElem? hLget
  have hxF : x ∈ c.layers.flatten := List.mem_flatten.mpr ⟨L, hFL, hxL⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.length_take] at hlen
  have hjn : j < c.pos[v]! := Nat.lt_of_lt_of_le hlen (Nat.min_le_left _ _)
  have hLj : L[j]? = some x := by
    have h := List.getElem?_take_of_lt (l := L) hjn
    rw [h] at hj
    exact hj
  have hidx := hL.idx (c.rank[v]!) L j x hLget hLj
  exact ⟨hxF, hidx.1, by rw [hidx.2]; exact hjn⟩

/-- The alignment-fold bound for an executed run: every prefix pick lands left
of the chain predecessor. From the chain shape (edge closure, one node per
rank) and the marking residual. -/
theorem foreignSideFoldBound {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat} {k : Nat}
    (_hrun : ∃ (cg : Graph) (labels : List MeasuredLabel)
      (orderOptions : OrderOptions),
      componentRun P cg labels orderOptions = .ok run)
    (_hside : side = -1 ∨ side = 1) (_hk : k < 4)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hshape : ForeignSideChainShape P run side decl pos k)
    (hmark : ForeignSideMarkingCrossed P run pos k) :
    ForeignSideFoldBound P run side decl pos k := by
  unfold ForeignSideFoldBound
  intro v hv pred hpred x hx last w hpick
  have hfacts : CoordsImpl.Lay (sideCtx P run pos k) ∧
      CoordsImpl.EdgeOK (sideCtx P run pos k) :=
    Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos
  obtain ⟨hL, hE⟩ := hfacts
  obtain ⟨e, hesz, hemem, hmarked, hw, hwflat, hrank, _hlast⟩ :=
    alignPick_unmarked_edge (c := sideCtx P run pos k) hE hpick
  have hvF : v ∈ (sideCtx P run pos k).layers.flatten := by
    have hmem : v ∈ run.layers.flatten := sideChainNodes_flat hv
    have hctx : (sideCtx P run pos k).layers =
      CoordsImpl.passLayers run.layers k := rfl
    rw [hctx]
    exact (CoordsImpl.passLayers_perm run.layers k).mem_iff.mpr hmem
  obtain ⟨hxF, hrankx, hposx⟩ :=
    prefix_mem_pos_lt (c := sideCtx P run pos k) hL hvF hx
  unfold chainPred at hpred
  have hpmem : pred ∈ sideChainNodes P run side decl :=
    List.mem_of_find?_eq_some hpred
  have hpspec : decide ((sideCtx P run pos k).rank[pred]! + 1 =
      (sideCtx P run pos k).rank[v]!) = true := by
    simpa using List.find?_some hpred
  have hprk : (sideCtx P run pos k).rank[pred]! + 1 =
      (sideCtx P run pos k).rank[v]! :=
    of_decide_eq_true hpspec
  have hpredF : pred ∈ (sideCtx P run pos k).layers.flatten := by
    have hmem : pred ∈ run.layers.flatten := sideChainNodes_flat hpmem
    have hctx : (sideCtx P run pos k).layers =
      CoordsImpl.passLayers run.layers k := rfl
    rw [hctx]
    exact (CoordsImpl.passLayers_perm run.layers k).mem_iff.mpr hmem
  obtain ⟨f, hfsz, hfor⟩ := hshape.consec_edge pred hpmem v hv hprk
  have htouchF : (sideCtx P run pos k).edges[f]!.tail = pred ∨
      (sideCtx P run pos k).edges[f]!.head = pred := by
    rcases hfor with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inr h1
    · exact Or.inl h1
  have hincF := hshape.incident_border pred hpmem f hfsz htouchF
  obtain ⟨hbc, -, -, -⟩ := hincF
  have hfor' : ((sideCtx P run pos k).edges[f]!.tail = pred ∧
      (sideCtx P run pos k).edges[f]!.head = v ∨
    (sideCtx P run pos k).edges[f]!.tail = v ∧
      (sideCtx P run pos k).edges[f]!.head = pred) := by
    rcases hfor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h1, h2⟩
  have hmem2 := CoordsImpl.mem_upperEdges hemem
  obtain ⟨-, hcase⟩ := hmem2
  rcases Int.lt_trichotomy ((sideCtx P run pos k).pos[w]! : Int)
    ((sideCtx P run pos k).pos[pred]! : Int) with hgoal | heqI | hltI
  · exact hgoal
  · have heq : (sideCtx P run pos k).pos[pred]! =
        (sideCtx P run pos k).pos[w]! := by
      exact_mod_cast heqI.symm
    obtain ⟨Lw, hwLget, hwLv⟩ := hL.loc hwflat
    obtain ⟨Lp, hpLget, hpLv⟩ := hL.loc hpredF
    have hrankw : (sideCtx P run pos k).rank[w]! =
        (sideCtx P run pos k).rank[pred]! := by omega
    rw [hrankw] at hwLget
    have hLL : Lp = Lw := by
      rw [hpLget] at hwLget
      exact Option.some_inj.mp hwLget
    rw [hLL, heq] at hpLv
    rw [hpLv] at hwLv
    have hwp : w = pred := Option.some_inj.mp hwLv.symm
    have hxp : x ≠ pred := by
      intro hcon
      rw [hcon] at hrankx
      omega
    rcases hcase with ⟨hheadx, h2⟩ | ⟨htailx, -⟩
    · have htx : (sideCtx P run pos k).edges[e]!.tail ≠ x := by
        intro hcon
        rw [hcon] at h2
        exact absurd h2 (Nat.lt_irrefl _)
      have hnt : ((sideCtx P run pos k).edges[e]!.tail == x) = false := by
        simpa using htx
      have htail : (sideCtx P run pos k).edges[e]!.tail = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hnt] at hw
        simpa using hw
      have htouch : (sideCtx P run pos k).edges[e]!.tail = pred ∨
          (sideCtx P run pos k).edges[e]!.head = pred :=
        Or.inl (htail.trans hwp)
      have hinc := hshape.incident_border pred hpmem e hesz htouch
      obtain ⟨-, u, hu, huother, -⟩ := hinc
      have hbeq : ((sideCtx P run pos k).edges[e]!.tail == pred) = true := by
        have htp : (sideCtx P run pos k).edges[e]!.tail = pred :=
          htail.trans hwp
        simpa using htp
      have hueqx : CoordsImpl.otherEnd ((sideCtx P run pos k).edges[e]!)
          pred = x := by
        unfold CoordsImpl.otherEnd
        rw [hbeq]
        simp only [ite_true]
        exact hheadx
      have hueq : u = x := huother.symm.trans hueqx
      rw [hueq] at hu
      have hxv : x = v := hshape.rank_inj x hu v hv hrankx
      rw [hxv] at hposx
      exact False.elim (absurd hposx (Nat.lt_irrefl _))
    · have hbeq : ((sideCtx P run pos k).edges[e]!.tail == x) = true := by
        simpa using htailx
      have hhw : (sideCtx P run pos k).edges[e]!.head = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hbeq] at hw
        simpa using hw
      have htouch : (sideCtx P run pos k).edges[e]!.tail = pred ∨
          (sideCtx P run pos k).edges[e]!.head = pred :=
        Or.inr (hhw.trans hwp)
      have hinc := hshape.incident_border pred hpmem e hesz htouch
      obtain ⟨-, u, hu, huother, -⟩ := hinc
      have htne : (sideCtx P run pos k).edges[e]!.tail ≠ pred := by
        rw [htailx]
        exact hxp
      have hnt : ((sideCtx P run pos k).edges[e]!.tail == pred) = false := by
        simpa using htne
      have hueqx : CoordsImpl.otherEnd ((sideCtx P run pos k).edges[e]!)
          pred = x := by
        unfold CoordsImpl.otherEnd
        rw [hnt]
        simp only [Bool.false_eq_true, ite_false]
        exact htailx
      have hueq : u = x := huother.symm.trans hueqx
      rw [hueq] at hu
      have hxv : x = v := hshape.rank_inj x hu v hv hrankx
      rw [hxv] at hposx
      exact False.elim (absurd hposx (Nat.lt_irrefl _))
  · have hposxI : ((sideCtx P run pos k).pos[x]! : Int) <
        ((sideCtx P run pos k).pos[v]! : Int) := by
      exact_mod_cast hposx
    rcases hcase with ⟨hheadx, h2⟩ | ⟨htailx, -⟩
    · have htx : (sideCtx P run pos k).edges[e]!.tail ≠ x := by
        intro hcon
        rw [hcon] at h2
        exact absurd h2 (Nat.lt_irrefl _)
      have hnt : ((sideCtx P run pos k).edges[e]!.tail == x) = false := by
        simpa using htx
      have htail : (sideCtx P run pos k).edges[e]!.tail = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hnt] at hw
        simpa using hw
      have heD : ((sideCtx P run pos k).edges[e]!.tail = w ∧
          (sideCtx P run pos k).edges[e]!.head = x ∨
        (sideCtx P run pos k).edges[e]!.tail = x ∧
          (sideCtx P run pos k).edges[e]!.head = w) :=
        Or.inl ⟨htail, hheadx⟩
      have hmarked2 := hmark e f w x pred v hesz hfsz heD hfor' hbc hrank
        hprk hrankx hltI hposxI
      rw [hmarked2] at hmarked
      simp at hmarked
    · have hbeq : ((sideCtx P run pos k).edges[e]!.tail == x) = true := by
        simpa using htailx
      have hhw : (sideCtx P run pos k).edges[e]!.head = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hbeq] at hw
        simpa using hw
      have heD : ((sideCtx P run pos k).edges[e]!.tail = w ∧
          (sideCtx P run pos k).edges[e]!.head = x ∨
        (sideCtx P run pos k).edges[e]!.tail = x ∧
          (sideCtx P run pos k).edges[e]!.head = w) :=
        Or.inr ⟨htailx, hhw⟩
      have hmarked2 := hmark e f w x pred v hesz hfsz heD hfor' hbc hrank
        hprk hrankx hltI hposxI
      rw [hmarked2] at hmarked
      simp at hmarked

end Elegant.Layered.PipelineImpl