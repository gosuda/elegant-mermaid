import Elegant.Layered.LoopResNeighborGapProof
import Elegant.Layered.LoopResNeighborGapOffRankProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Coords

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop-footprint neighbor gap, disjoint form

The seam asks for an `x`-gap between a loop footprint and a foreign group
hull whenever the owner frame lies left of that hull. That statement is
false: with a top-level looping owner and an off-rank foreign hull on
another rank, the frame can sit left of the hull while the loop lane runs
past its left edge (`LoopResNeighborGapOffRankProof.lean`, witness `wit3r`:
frame-right `1026` against hull-left `3003`, footprint-right `13530`).

Consumer trace (files owned by another worker, not edited here): the plain
case splits in `loopResNeighborGap_plain_holds`
(`LoopResNeighborGapProof.lean`) over spanning/off-rank and assembles with
the two non-plain residuals in `loopResNeighborGap_holds`; the executed
`x`-gap feeds `loopHullRightNeighborCover_Disj_holds` below, whose
conclusion `LoopHullRightNeighborCover` (defined in
`LoopFootprintGroupHullProof.lean`)
is exactly what `FamilyAssemblyB.lean` consumes (both `flatC8b` sites) on
the way to `loopFootprintGroupHullClear_of_run` and the packed label/frame
clearance behind validator clause C8b (`layout_c8b`). The cover already
carries the `y`-overlap premise: it needs the `x`-gap only when footprint
and hull overlap in `y`. The top-level witness is `y`-disjoint, so it never
triggers the cover's `x`-gap obligation.

Weakest sufficient replacement (`LoopResNeighborGapDisj` below): the same
binders as the `x`-gap goal, concluding the `x`-gap OR a `y`-gap
(footprint above hull or hull above footprint). The witness satisfies the
`y`-gap disjunct; every grouped off-rank probe instance satisfies the `x`-gap
disjunct. From the disjunction plus the cover's `y`-overlap premise the
`x`-gap follows by cases, so the existing cover conclusion (the exact shape
`FamilyAssemblyB.lean` consumes) is recovered with no width reasoning. -/

/-- Weakest sufficient neighbor gap: the `x`-gap, or a `y`-gap in either
direction. Same binders as the `x`-gap goal (any owner, no spanning premise);
the witness `wit3r` satisfies the third disjunct, grouped and spanning
off-rank probes satisfy the first. -/
def LoopResNeighborGapDisj (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x ∨
      (loopFootprint cg run labels t).y + (loopFootprint cg run labels t).h ≤
        (frameRect P cg run pos).y ∨
      (frameRect P cg run pos).y + (frameRect P cg run pos).h ≤
        (loopFootprint cg run labels t).y

/-- Residual: the group-top owner case of the disjoint gap (loop on a group
top, `nt.border = -2`). Mirror of `LoopResNeighborGapGroupTop` with the
disjoint conclusion. -/
def LoopResNeighborGapGroupTopDisj (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = -2 →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x ∨
      (loopFootprint cg run labels t).y + (loopFootprint cg run labels t).h ≤
        (frameRect P cg run pos).y ∨
      (frameRect P cg run pos).y + (frameRect P cg run pos).h ≤
        (loopFootprint cg run labels t).y

/-- Residual: the bottom-marker owner case of the disjoint gap
(`nt.border = 2`). Mirror of `LoopResNeighborGapBottomOwner` with the
disjoint conclusion. -/
def LoopResNeighborGapBottomOwnerDisj (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = 2 →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x ∨
      (loopFootprint cg run labels t).y + (loopFootprint cg run labels t).h ≤
        (frameRect P cg run pos).y ∨
      (frameRect P cg run pos).y + (frameRect P cg run pos).h ≤
        (loopFootprint cg run labels t).y

/-- Private: when every member of the foreign group sits on a strictly smaller
rank than the plain owner, the hull bottom stays above the footprint top.
Bands contain the placed rects (`fbs_run_node_band`); smaller rank bands end
below the owner's band start (`rankAxis_bands_disjoint`); the hull bottom is
the members' max bottom (`boundsOf_bottom_le_of_all`, empty-tolerant). -/
private theorem lrnd_hullBelow_of_membersAbove {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {t : Nat} {nt : Node} (hnt : cg.nodes[t]? = some nt) (htB : nt.border = 0)
    {pos : Nat} {np : Node} (hnp : cg.nodes[pos]? = some np) (hgrpB : np.border = -2)
    (habove : ∀ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na →
      na.node.clusterPath.contains np.decl = true →
      (rk run.proper.rank a).toNat < (rk run.proper.rank t).toNat) :
    (frameRect P cg run pos).y + (frameRect P cg run pos).h ≤
      (loopFootprint cg run labels t).y := by
  obtain ⟨actualT, _, hproperT, _, _, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnt htB
  have hgetT : cg.nodes.getD t default = nt := by
    rw [List.getD_eq_getElem?_getD, hnt]; rfl
  have hframeT : frameRect P cg run t = nodeRect cg run t :=
    frameRect_of_border_zero hgetT htB
  have hnodeT : nodeRect cg run t =
      ⟨RouteImpl.leftOf run.proper run.xs t, run.ys.getD t 0,
        actualT.node.w, actualT.node.h⟩ := nodeRect_of_record hproperT
  have hfpy : (loopFootprint cg run labels t).y = (frameRect P cg run t).y := rfl
  have hFy : (frameRect P cg run t).y = run.ys.getD t 0 := by
    rw [hframeT, hnodeT]
  have htLen : t < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hproperT).1
  have hbandT := (fbs_run_node_band hrun t htLen).1
  have htopNN := fbs_run_top_nonneg hrun (rk run.proper.rank t).toNat
  have h0y : 0 ≤ (loopFootprint cg run labels t).y := by omega
  have hbot : (boundsOf (groupMemberRects cg run np.decl) []).bottom ≤
      (loopFootprint cg run labels t).y := by
    apply boundsOf_bottom_le_of_all h0y
    intro r hr
    obtain ⟨a, na, hrec, hcon, hrEq⟩ := fbs_groupMemberRects_spec hr
    have hrEqyh : r.y + r.h = run.ys.getD a 0 + RouteImpl.nodeH run.proper a := by
      rw [hrEq]
      rfl
    have haLen : a < run.proper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hrec).1
    have hbandA := fbs_run_node_band hrun a haLen
    obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, _, _⟩ :=
      componentRun_spec hrun
    have hrankEq : run.proper.rank = run.coordinateProper.rank := by
      rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
    have hcov :=
      (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
    obtain ⟨la, hlya, _, _⟩ := hcov a haLen
    obtain ⟨lt, hlyt, _, _⟩ := hcov t htLen
    have hlt := habove a na hrec hcon
    have hla_eq : run.layers.getD (rk run.coordinateProper.rank a).toNat [] = la := by
      have e : (rk run.coordinateProper.rank a).toNat = (rk run.proper.rank a).toNat := by
        rw [← hrankEq]
      rw [e, List.getD_eq_getElem?_getD, hlya, Option.getD_some]
    have hbands := CoordsImpl.rankAxis_bands_disjoint hry _ _ la lt hlt hlya hlyt
    rw [hla_eq] at hbandA
    omega
  have hhy : (frameRect P cg run pos).y =
      (boundsOf (groupMemberRects cg run np.decl) []).minY := by
    rw [frameRect_group_span hnp hgrpB]
  have hhh : (frameRect P cg run pos).h =
      (boundsOf (groupMemberRects cg run np.decl) []).bottom -
        (boundsOf (groupMemberRects cg run np.decl) []).minY := by
    rw [frameRect_group_span hnp hgrpB]
  omega
/-- Private: when every member of the foreign group sits on a strictly larger
rank than the plain owner, the footprint top stays above the hull top. Dual
of `lrnd_hullBelow_of_membersAbove`: the hull top is the members' max top
(`boundsOf_minY_ge_of_all`, needs the nonempty witness), each member top
lies at or below its band start, later bands start below the owner's band
end. -/
private theorem lrnd_hullAbove_of_membersBelow {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {t : Nat} {nt : Node} (hnt : cg.nodes[t]? = some nt) (htB : nt.border = 0)
    {pos : Nat} {np : Node} (hnp : cg.nodes[pos]? = some np) (hgrpB : np.border = -2)
    (hbelow : ∀ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na →
      na.node.clusterPath.contains np.decl = true →
      (rk run.proper.rank t).toNat < (rk run.proper.rank a).toNat)
    (hne : groupMemberRects cg run np.decl ≠ []) :
    (loopFootprint cg run labels t).y + (loopFootprint cg run labels t).h ≤
      (frameRect P cg run pos).y := by
  obtain ⟨actualT, _, hproperT, _, _, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnt htB
  have hgetT : cg.nodes.getD t default = nt := by
    rw [List.getD_eq_getElem?_getD, hnt]; rfl
  have hframeT : frameRect P cg run t = nodeRect cg run t :=
    frameRect_of_border_zero hgetT htB
  have hnodeT : nodeRect cg run t =
      ⟨RouteImpl.leftOf run.proper run.xs t, run.ys.getD t 0,
        actualT.node.w, actualT.node.h⟩ := nodeRect_of_record hproperT
  have hfpy : (loopFootprint cg run labels t).y = (frameRect P cg run t).y := rfl
  have hfph : (loopFootprint cg run labels t).h = (frameRect P cg run t).h := rfl
  have hFy : (frameRect P cg run t).y = run.ys.getD t 0 := by
    rw [hframeT, hnodeT]
  have hFh : (frameRect P cg run t).h = actualT.node.h := by
    rw [hframeT, hnodeT]
  have hnodeHt : RouteImpl.nodeH run.proper t = actualT.node.h := by
    simp only [RouteImpl.nodeH, hproperT]
  have htLen : t < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hproperT).1
  have hbandT := fbs_run_node_band hrun t htLen
  have hminY : (loopFootprint cg run labels t).y + (loopFootprint cg run labels t).h ≤
      (boundsOf (groupMemberRects cg run np.decl) []).minY := by
    apply boundsOf_minY_ge_of_all hne
    intro r hr
    obtain ⟨a, na, hrec, hcon, hrEq⟩ := fbs_groupMemberRects_spec hr
    have hlt := hbelow a na hrec hcon
    have haLen : a < run.proper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hrec).1
    have hbandA := (fbs_run_node_band hrun a haLen).1
    obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, _, _⟩ :=
      componentRun_spec hrun
    have hrankEq : run.proper.rank = run.coordinateProper.rank := by
      rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
    have hcov :=
      (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
    obtain ⟨la, hlya, _, _⟩ := hcov a haLen
    obtain ⟨lt, hlyt, _, _⟩ := hcov t htLen
    have hlt_eq : run.layers.getD (rk run.coordinateProper.rank t).toNat [] = lt := by
      have e : (rk run.coordinateProper.rank t).toNat = (rk run.proper.rank t).toNat := by
        rw [← hrankEq]
      rw [e, List.getD_eq_getElem?_getD, hlyt, Option.getD_some]
    have hbands := CoordsImpl.rankAxis_bands_disjoint hry _ _ lt la hlt hlyt hlya
    have hrEqy : r.y = run.ys.getD a 0 := by
      rw [hrEq]
      rfl
    rw [hlt_eq] at hbandT
    omega
  have hhy : (frameRect P cg run pos).y =
      (boundsOf (groupMemberRects cg run np.decl) []).minY := by
    rw [frameRect_group_span hnp hgrpB]
  omega
/-- Off-rank plain owners satisfy the disjoint gap through the `y`-gap: no
member shares the owner's rank (else low = high = that member would span),
so all members lie strictly above or strictly below; bands separate ranks,
so the hull lies wholly above or below the footprint. Needs no grouped
premise, hence discharges the top-level off-rank case that refutes the
`x`-gap form. -/
theorem loopResNeighborGapDisj_offRankYGap_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (hoff : ¬ LoopResNeighborSpanning run t np.decl)
    (_hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y := by
  have hrkNe : ∀ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na →
      na.node.clusterPath.contains np.decl = true →
      (rk run.proper.rank a).toNat ≠ (rk run.proper.rank t).toNat := by
    intro a na ha hc heq
    exact hoff ⟨a, a, na, na, ha, hc, Nat.le_of_eq heq, ha, hc, Nat.le_of_eq heq.symm⟩
  by_cases hex : ∃ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na ∧
      na.node.clusterPath.contains np.decl = true ∧
      (rk run.proper.rank t).toNat < (rk run.proper.rank a).toNat
  · obtain ⟨aw, naw, haw, hcw, hltw⟩ := hex
    have hbelow : ∀ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na →
        na.node.clusterPath.contains np.decl = true →
        (rk run.proper.rank t).toNat < (rk run.proper.rank a).toNat := by
      intro a na ha hc
      rcases Nat.lt_trichotomy (rk run.proper.rank t).toNat (rk run.proper.rank a).toNat with
        h | h | h
      · exact h
      · exact (hrkNe a na ha hc h.symm).elim
      · exact absurd (⟨a, aw, na, naw, ha, hc, Nat.le_of_lt h, haw, hcw,
          Nat.le_of_lt hltw⟩ :
          LoopResNeighborSpanning run t np.decl) hoff
    have hne : groupMemberRects
        (componentCandidate execution.graph comp candidate) run np.decl ≠ [] :=
      List.ne_nil_of_mem (fbs_groupMemberRects_mem haw hcw)
    exact Or.inr (Or.inl (lrnd_hullAbove_of_membersBelow hrun hnt htB hnp hgrpB
      hbelow hne))
  · have habove : ∀ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na →
        na.node.clusterPath.contains np.decl = true →
        (rk run.proper.rank a).toNat < (rk run.proper.rank t).toNat := by
      intro a na ha hc
      have hne := hrkNe a na ha hc
      have hle : ¬ (rk run.proper.rank t).toNat < (rk run.proper.rank a).toNat := by
        intro hlt
        exact hex ⟨a, na, ha, hc, hlt⟩
      omega
    exact Or.inr (Or.inr (lrnd_hullBelow_of_membersAbove hrun hnt htB hnp hgrpB
      habove))
/-- Grouped off-rank plain owners satisfy the disjoint gap through the
`x`-gap: the parent-chain residual plus the shared extent core
(`loopResNeighborGapOffRank_holds`). -/
theorem loopResNeighborGapDisj_groupedOffRank_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hchain : LoopResOffRankParentChain)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (hgrouped : nt.clusterPath ≠ [])
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (hoff : ¬ LoopResNeighborSpanning run t np.decl)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y := by
  exact Or.inl (loopResNeighborGapOffRank_holds hwf hframed execution hcomp hrun
    hchain hnt htB hgrouped _het hnp hgrpB _hne _hne2 _hni1 _hni2 hoff hFL)
/-- Spanning plain owners satisfy the disjoint gap through the `x`-gap
(`loopResNeighborGap_plainSpan_holds`). -/
theorem loopResNeighborGapDisj_span_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (hspan : LoopResNeighborSpanning run t np.decl)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y := by
  exact Or.inl (loopResNeighborGap_plainSpan_holds hwf hframed hx execution hcomp
    hrun hnt htB _het hnp hgrpB _hne _hne2 _hni1 _hni2 hspan hFL)
/-- Plain owners satisfy the disjoint gap: spanning through the `x`-gap,
grouped off-rank through the `x`-gap (parent-chain residual), top-level
off-rank through the `y`-gap. -/
theorem loopResNeighborGapDisj_plain_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hchain : LoopResOffRankParentChain)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y := by
  by_cases hspan : LoopResNeighborSpanning run t np.decl
  · exact loopResNeighborGapDisj_span_holds hwf hframed hx execution hcomp hrun
      hnt htB _het hnp hgrpB _hne _hne2 _hni1 _hni2 hspan hFL
  · by_cases hgrouped : nt.clusterPath = []
    · exact loopResNeighborGapDisj_offRankYGap_holds execution hcomp hrun hnt
        htB _het hnp hgrpB _hne _hne2 _hni1 _hni2 hspan hFL
    · exact loopResNeighborGapDisj_groupedOffRank_holds hwf hframed execution hcomp
        hrun hchain hnt htB hgrouped _het hnp hgrpB _hne _hne2 _hni1 _hni2 hspan
        hFL
/-- Full disjoint gap from the plain theorem and the two non-plain residuals.
Candidate loop owners have border `0`, `-2` or `2`
(`componentCandidate_marker_shape`). -/
theorem loopResNeighborGapDisj_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hchain : LoopResOffRankParentChain)
    (hgrp : LoopResNeighborGapGroupTopDisj execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hbot : LoopResNeighborGapBottomOwnerDisj execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl)
    (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y := by
  have hshape := (componentCandidate_marker_shape execution.graph_eq hnt).1
  rcases hshape with ht0 | htG | htBot
  · exact loopResNeighborGapDisj_plain_holds hwf hframed hx execution hcomp hrun
      hchain hnt ht0 het hnp hgrpB hne hne2 hni1 hni2 hFL
  · exact hgrp t nt hnt htG het pos np hnp hgrpB hne hne2 hni1 hni2 hFL
  · exact hbot t nt hnt htBot het pos np hnp hgrpB hne hne2 hni1 hni2 hFL
/-- Executed foreign-hull right-neighbor cover from the disjoint gap. Under
the cover's `y`-overlap premise the `y`-gap disjuncts are contradictory, so
the `x`-gap disjunct must hold; no width reasoning is needed. This is the exact
statement shape `FamilyAssemblyB.lean` consumes (both `flatC8b` sites apply
the `_holds` lemma to the seam field). -/
theorem loopHullRightNeighborCover_Disj_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hB : LoopResNeighborGapDisj execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    LoopHullRightNeighborCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have _hwf := hwf
  have _hframed := hframed
  have _hcomp := hcomp
  have _hrun := hrun
  intro t nt hnt het pos np hnp hgrp hne hne2 hni1 hni2 hFL hyOvl
  have hOR := hB t nt hnt het pos np hnp hgrp hne hne2 hni1 hni2 hFL
  rcases hOR with hx | hy1 | hy2
  · exact hx
  · exact absurd hy1 (fun ha => hyOvl (Or.inl ha))
  · exact absurd hy2 (fun hb => hyOvl (Or.inr hb))

end PipelineImpl
end Layered
end Elegant
