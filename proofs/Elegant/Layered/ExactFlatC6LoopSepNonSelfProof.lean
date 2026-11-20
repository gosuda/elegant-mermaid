import Elegant.Layered.ExactFlatC6LoopSepProof
import Elegant.Layered.ExactLoopEnvelopeMissProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactLoopEnvelopeFootBelowProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeGroupMissProof
import Elegant.Layered.ExactLoopEnvelopeRankProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.ExactFlatFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Bounded-exclusive scope for `X6_LoopSep_NonSelf`: the four scope facts
(in-bounds, real, declaration outside the owner's cluster paths) for an
in-part index `b` (`comp[b]? = some key`) whose box is exclusive. Strictly
narrower than the target (scope facts only, no separation claim). Proved
below as `x6_loopSep_nonSelf_scopeB_holds`; the old unbounded form was
FALSE (out-of-bounds `b` satisfies the border premise via `getD` default).
True on all `wip/Probe/X6LoopScopeTProbe.lean` checks (`bounded`, `scopeB`
all `true` on flatExact, nestedExact, loopZero, emptyGrp, ill). -/
def X6_LoopSep_NonSelf_ScopeB (exactIds : List String) : Prop :=
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
    ∀ (key : Nat) (source : ModelBox),
      comp[b]? = some key →
      inp.boxes[key]? = some source → source.exclusive = true →
      b < run.proper.nodes.length ∧
      RouteImpl.IsReal run.proper b ∧
      RouteImpl.nodeDecl run.proper b ∉
        (((componentCandidate execution.graph comp candidate).nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
      RouteImpl.nodeDecl run.proper b ∉
        (((componentCandidate execution.graph comp candidate).nodes[e.head]?).map (·.clusterPath)).getD []

/-- Residual separation for the cases `ScopeB` does not cover: in-proper
indices whose part entry (if any) is not an exclusive box — non-exclusive
boxes and component-beyond marker indices — conclude the footprint
separation directly. Separation-shaped (not the four scope facts): the
scope facts are FALSE for component-beyond markers (their declaration is
the group, which sits on the owner's cluster path), while the separation
itself holds on every `X6LoopScopeTProbe` full-range check (`sepfull`, no
`FAIL` on flatExact/nestedExact/loopZero/emptyGrp/ill, including marker and
out-of-proper indices). Strictly narrower than the target (extra proper
bound and non-exclusivity premises). -/
def X6_LoopSep_NonSelf_ScopeRest (exactIds : List String) : Prop :=
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
    b < run.proper.nodes.length →
    (∀ (key : Nat) (source : ModelBox), comp[b]? = some key →
      inp.boxes[key]? = some source → source.exclusive = false) →
    LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
      execution.measured v b

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

/-- Component candidate node count equals the part length (local copy of the
private `candidate_nodes_length_general`). -/
private theorem x6lss_cand_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- The bounded-exclusive scope holds: an in-part exclusive `b` is covered
by the proper run, real, and its declaration lies outside every candidate
cluster path. From the public run/node/path closers. -/
theorem x6_loopSep_nonSelf_scopeB_holds (exactIds : List String) :
    X6_LoopSep_NonSelf_ScopeB exactIds := by
  intro inp o res execution hwf hfp comp candidate run _v b k e
    hcomp _hbord hrun _hne hk _htail _hhead key source hcomp_b hsource hexcl
  have hbd := sceneExecutionX_edges_bounded execution
  have hmem : e ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hk
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd hmem
  have hlen : (componentCandidate execution.graph comp candidate).nodes.length =
      comp.length := x6lss_cand_length _ _ _
  have hblt : b < comp.length := (List.getElem?_eq_some_iff.mp hcomp_b).1
  have hb : b < (componentCandidate execution.graph comp candidate).nodes.length := by
    omega
  have hnode_b : (componentCandidate execution.graph comp candidate).nodes[b]? =
      some ((componentCandidate execution.graph comp candidate).nodes[b]) :=
    List.getElem?_eq_getElem hb
  have htail : (componentCandidate execution.graph comp candidate).nodes[e.tail]? =
      some ((componentCandidate execution.graph comp candidate).nodes[e.tail]) :=
    List.getElem?_eq_getElem hbnd.1
  have hhead : (componentCandidate execution.graph comp candidate).nodes[e.head]? =
      some ((componentCandidate execution.graph comp candidate).nodes[e.head]) :=
    List.getElem?_eq_getElem hbnd.2
  have hdecl : RouteImpl.nodeDecl run.proper b = key :=
    x_exclusiveRunNodeDecl_holds exactIds inp o res execution comp candidate run
      hcomp hrun b key source hcomp_b hsource
  have hout := x_exclusiveKeyOutsideCgPaths_holds exactIds inp o res hwf hfp comp
    candidate b key source execution hcomp hcomp_b hsource hexcl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact componentRunX_original_nodes_covered hrun b hb
  · exact X_componentRun_source_isReal hrun hnode_b
  · rw [htail, Option.map_some, Option.getD_some, hdecl]
    exact hout e.tail _ htail
  · rw [hhead, Option.map_some, Option.getD_some, hdecl]
    exact hout e.head _ hhead

/-- Exact flat C6 loop-footprint separation, non-self case: the loop footprint
of `v` misses the frame of a zero-border `b` with `v ≠ b`, over an executed
exact run with local admission. From the six named XLEM leaf defs plus the
two scope premises (`ScopeB` proved above, `ScopeRest` open). The no-loop
case is direct (empty sizes give a zero-width footprint); the out-of-proper
frame case is direct (default proper node has width zero); in-proper `b`
splits on whether its part entry is an exclusive box. -/
theorem X6_loopSep_nonSelf_holds (exactIds : List String)
    (hRes : XLEM_PlainReserve exactIds)
    (hGrpOther : XLEM_GroupOwnerOtherRank exactIds)
    (hRight : XLEM_PlainRightMiss exactIds)
    (hLeftNP : XLEM_LeftNonPlain exactIds)
    (hOrd : XLEG_GroupMarkerOrderX exactIds)
    (hOwner : X_loopEnvOtherOwner exactIds)
    (hScopeB : X6_LoopSep_NonSelf_ScopeB exactIds)
    (hScopeRest : X6_LoopSep_NonSelf_ScopeRest exactIds) :
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
      by_cases hproper : run.proper.nodes.length ≤ b
      · exact x6lsns_disjoint_of_proper_oob hbord hproper
      · have hlt : b < run.proper.nodes.length := by omega
        by_cases hexcl : ∃ key source, comp[b]? = some key ∧
            inp.boxes[key]? = some source ∧ source.exclusive = true
        · obtain ⟨key, source, hkey, hsource, hexclT⟩ := hexcl
          obtain ⟨hlt', hreal, hscope₀, hscope₁⟩ :=
            hScopeB inp o res execution hwf hfp comp candidate run v b k e
              hcomp hbord hrun hne hk htail hhead key source hkey hsource hexclT
          have hmiss := hFootMiss inp o res execution hwf hfp comp candidate run
            (candidateOrder candidate)
            (componentCandidate execution.graph comp candidate) k e b
            hcomp rfl hrun hk (htail.trans hhead.symm) hlt' hreal hscope₀ hscope₁
          rw [htail] at hmiss
          have hframe : frameRect default (componentCandidate execution.graph comp candidate) run b =
              RouteImpl.boxRect run.proper run.xs run.ys b :=
            plain_frame_eq_boxRect default (componentCandidate execution.graph comp candidate) run b hlt'
              (by omega)
          unfold LoopFootprintSeparation
          rw [hframe]
          exact hmiss
        · have hnotexcl : ∀ (key : Nat) (source : ModelBox), comp[b]? = some key →
              inp.boxes[key]? = some source → source.exclusive = false := by
            intro key source hkey hsource
            cases heq : source.exclusive with
            | true => exact absurd ⟨key, source, hkey, hsource, heq⟩ hexcl
            | false => rfl
          exact hScopeRest inp o res execution hwf hfp comp candidate run v b k e
            hcomp hbord hrun hne hk htail hhead hlt hnotexcl
end PipelineImpl
end Layered
end Elegant
