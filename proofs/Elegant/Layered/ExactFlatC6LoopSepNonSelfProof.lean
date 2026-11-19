import Elegant.Layered.ExactFlatC6LoopSepProof
import Elegant.Layered.ExactLoopEnvelopeMissProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactLoopEnvelopeFootBelowProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeGroupMissProof
import Elegant.Layered.ExactLoopEnvelopeRankProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.FlatC6Loops

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Scope bridge residual for `X6_LoopSep_NonSelf`: over an executed exact run
with local admission, a zero-border component index `b` distinct from a loop
owner `v` carrying edge `e` is in bounds, real, and outside the owner's
cluster paths. Strictly narrower than the target (scope facts only, no
separation claim); a lemma on the way to the envelope-miss application. True
on all `wip/Probe/X6LoopSepTProbe.lean` non-self checks (`flatTwoExact/ab`,
`nestedExact/m`, `loopZero/a`, `loopWide/a`, `flatTwo/none`, `ill/none` all
report `nonself=true`). -/
def X6_LoopSep_NonSelf_Scope (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run) (v b k : Nat) (e : Edge),
    comp ∈ components execution.graph →
    ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    v ≠ b →
    (componentCandidate execution.graph comp candidate).edges[k]? = some e →
    e.tail = v → e.head = v →
    b < run.proper.nodes.length ∧
    RouteImpl.IsReal run.proper b ∧
    RouteImpl.nodeDecl run.proper b ∉
      (((componentCandidate execution.graph comp candidate).nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
    RouteImpl.nodeDecl run.proper b ∉
      (((componentCandidate execution.graph comp candidate).nodes[e.head]?).map (·.clusterPath)).getD []

/-- Footprint width is zero when the loop-size list is empty, in both the
exact and the plain width branches. -/
private theorem x6lsns_foot_zero_of_nil {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat}
    (hempty : loopEdges cg.edges v = []) :
    (loopFootprint cg run labels v).w = 0 := by
  have hsizes : loopSizes cg.edges labels v cg.slot = [] := by
    unfold loopSizes
    rw [hempty]
    rfl
  unfold loopFootprint
  dsimp only
  rw [hsizes]
  by_cases hex : run.exact.contains v = true
  · simp only [hex, ↓reduceIte]
    unfold Loops.exactExtent
    simp
  · have hcon : run.exact.contains v = false := Bool.eq_false_of_ne_true hex
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    unfold Loops.extent
    simp

/-- A zero-width footprint is disjoint from every frame. -/
private theorem x6lsns_disjoint_of_zero_w {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hw : (loopFootprint cg run labels v).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A frame past the proper nodes has width zero (default proper node), hence
is disjoint from every loop footprint. -/
private theorem x6lsns_disjoint_of_proper_oob {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hbord : (cg.nodes.getD b default).border = 0)
    (hoob : run.proper.nodes.length ≤ b) :
    LoopFootprintSeparation cg run labels v b := by
  have hnone : run.proper.nodes[b]? = none := List.getElem?_eq_none (by omega)
  have hcond : ((cg.nodes.getD b default).border != -2) = true := by
    rw [hbord]
    decide
  have hfr : frameRect default cg run b = nodeRect cg run b := by
    unfold frameRect
    simp only [hcond, ↓reduceIte]
  have hw : (frameRect default cg run b).w = 0 := by
    rw [hfr]
    show (nodeRect cg run b).w = 0
    unfold nodeRect
    rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rfl
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega


/-- A nonempty loop-edge list yields a self-loop witness edge. -/
private theorem x6lsns_loop_edge_of_nonempty {edges : List Edge} {v : Nat}
    {hd : Edge} {tl : List Edge} (hcons : loopEdges edges v = hd :: tl) :
    ∃ (k : Nat) (e : Edge), edges[k]? = some e ∧ e.tail = v ∧ e.head = v := by
  have hmem : hd ∈ loopEdges edges v := by
    rw [hcons]
    exact List.mem_cons_self
  unfold loopEdges at hmem
  obtain ⟨hmemE, hpred⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmemE
  exact ⟨k, hd, hk, hpred.1, hpred.2⟩

/-- Exact flat C6 loop-footprint separation, non-self case: the loop footprint
of `v` misses the frame of a zero-border `b` with `v ≠ b`, over an executed
exact run with local admission. From the six named XLEM leaf defs plus the
single scope residual above. Leaf proof status:
`XLEM_PlainReserve` (def, no proof),
`XLEM_GroupOwnerOtherRank` (def, no proof),
`XLEM_PlainRightMiss` (def, no proof),
`XLEM_LeftNonPlain` (def, no proof; yields `XLEM_LeftMiss` by the proved
`XLEM_leftMiss_holds`),
`XLEG_GroupMarkerOrderX` (def, no proof; yields `XLEM_GroupOwnerMiss` by the
proved `XLEM_groupOwnerMiss_holds`),
`X_loopEnvOtherOwner` (def, no proof).
Derived by proved lemmas: `XLEM_otherRankMiss_closed`,
`X_loopEnvelopeMiss_closed`, `X_envelopeMiss_implies_footprintMiss`.
The no-loop case is direct (empty sizes give a zero-width footprint); the
out-of-bounds frame case is direct (default proper node has width zero). -/
theorem X6_loopSep_nonSelf_holds (exactIds : List String)
    (hRes : XLEM_PlainReserve exactIds)
    (hGrpOther : XLEM_GroupOwnerOtherRank exactIds)
    (hRight : XLEM_PlainRightMiss exactIds)
    (hLeftNP : XLEM_LeftNonPlain exactIds)
    (hOrd : XLEG_GroupMarkerOrderX exactIds)
    (hOwner : X_loopEnvOtherOwner exactIds)
    (hScope : X6_LoopSep_NonSelf_Scope exactIds) :
    X6_LoopSep_NonSelf exactIds := by
  intro inp o res execution hwf hfp comp candidate run v b hcomp hbord hrun hne
  have hOtherRank : XLEM_OtherRankMiss exactIds :=
    XLEM_otherRankMiss_closed exactIds hRes hGrpOther
  have hLeft : XLEM_LeftMiss exactIds := XLEM_leftMiss_holds exactIds hLeftNP
  have hGroup : XLEM_GroupOwnerMiss exactIds :=
    XLEM_groupOwnerMiss_holds exactIds hOrd
  have hMiss : X_LoopEnvelopeMiss exactIds :=
    X_loopEnvelopeMiss_closed exactIds hOtherRank hRight hLeft hGroup hOwner
  have hFootMiss := X_envelopeMiss_implies_footprintMiss exactIds hMiss
  by_cases hempty : loopEdges (componentCandidate execution.graph comp candidate).edges v = []
  · exact x6lsns_disjoint_of_zero_w (x6lsns_foot_zero_of_nil hempty)
  · cases hc : loopEdges (componentCandidate execution.graph comp candidate).edges v with
    | nil => exact absurd hc hempty
    | cons hd tl =>
      obtain ⟨k, e, hk, htail, hhead⟩ := x6lsns_loop_edge_of_nonempty hc
      obtain ⟨hlt, hreal, hscope₀, hscope₁⟩ :=
        hScope inp o res execution hwf hfp comp candidate run v b k e
          hcomp hbord hrun hne hk htail hhead
      have hmiss := hFootMiss inp o res execution comp candidate run
        (candidateOrder candidate)
        (componentCandidate execution.graph comp candidate) k e b
        hcomp rfl hrun hk (htail.trans hhead.symm) hlt hreal hscope₀ hscope₁
      rw [htail] at hmiss
      have hframe : frameRect default (componentCandidate execution.graph comp candidate) run b =
          RouteImpl.boxRect run.proper run.xs run.ys b :=
        plain_frame_eq_boxRect default (componentCandidate execution.graph comp candidate) run b hlt
          (by omega)
      unfold LoopFootprintSeparation
      rw [hframe]
      exact hmiss
end PipelineImpl
end Layered
end Elegant
