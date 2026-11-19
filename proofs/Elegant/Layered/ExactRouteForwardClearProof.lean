import Elegant.Layered.ExactRouteRunClearProof
import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.LabelsC7RunLocal

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact forward route-label clearance (`XF_routeForwardClearX_holds`)

Target: `hRrFwdX` of `XF_routeRunClearX_holds`
(`ExactRouteRunClearProof.lean:70`), the forward-edge case of
`XF_RouteRunClearX` over `componentRunX`: every placed label of a forward
edge (tail and head distinct, not reversed) clears every frame position.

Plain path replayed (forward branch of `route_run_clear_inlined`,
`RouteRunClearCases.lean:412`, as closed by `routeRunClear_closed`,
`RouteRunClearClosed.lean:76`):

* `placed_mem_unpack` (`RouteRunClearCases.lean:149`): membership in
  `placedLabels` unpacks to the source label, its edge, and the envelope
  equation. Reads no run spec; reused outright.
* `case_group_inside` (`RouteRunClearCases.lean:308`): a group frame
  containing the label dummy is strictly inside the label, via
  `StrictDummyFrameLinked` (`RouteRunClearCases.lean:203`) and
  `RouteLabelInDummy` (`RouteRunClearCases.lean:214`). Run-generic; reused
  outright.
* `case_plain_real` (`RouteRunClearCases.lean:364`): a non-group frame whose
  proper node is real and outside the edge scope is disjoint, via
  `RouteLabelRealClear` (`RouteRunClearCases.lean:245`). Run-generic; reused
  outright.
* `case_plain_zero` (`RouteRunClearCases.lean:388`): a non-group frame whose
  proper box has height zero misses every rect. Pure geometry; reused
  outright.
* `routeLabelInDummy_of_run` (`RouteRunClearCases.lean:525`): placed forward
  labels lie in their dummy rect. Reads the run spec through
  `forward_anchor_full` (`RunLocalSeparationsProof.lean:148`, via
  `hrun : componentRun .. = .ok run`) and `forward_envelope_eq`
  (`RunLocalSeparationsProof.lean:268`, envelope equation only). Exact
  replacement: `X_forward_anchor_full` (`ExactFlatC7Forward.lean:84`,
  private) over `componentRunX_spec` (`ExactFlatFacts.lean:284`).
  Residual: `XFR_RouteLabelInDummyX`.
* `routeLabelRealClear_of_run` (`RouteRunClearCases.lean:667`): a placed
  label misses every out-of-scope real box. The forward branch reads the run
  spec through `runLocalForwardSeparation`
  (`RunLocalSeparationsProof.lean:290`, rank bands plus same-rank layer
  order via `componentRun_slot_nonneg` and `measured_nonneg`). Exact
  replacement: `x_runLocalForwardSeparation_holds`
  (`ExactFlatC7Forward.lean:584`), whose bands come from
  `X_ReserveBands_holds` (`ExactFlatC2.lean:955`) over `X_pre_band`
  (`ExactFlatC2.lean:668`) and `componentRunX_node_band`
  (`ComponentRunGenGeometry.lean:626`). Residual: `XFR_RouteLabelRealClearX`.
* `dummy_ex_labeled_of_run` (`RouteRunClearCases.lean:780`): every labeled
  forward edge has its mid-rank anchor dummy. Reads the run spec through
  `forward_anchor_full` and `labelAnchorIndex_eq` (shared). Exact
  replacement: `X_forward_anchor_full` under the `sizeProperPortsX` guard
  (`ExactPipeline.lean:55`; key fields via `ExactPartBounded.lean`).
  Residual: `XFR_DummyExLabeledX`.
* `strictDummyFrame_of_run` (`StrictDummyFrameProof.lean:1091`): the linked
  strict dummy frame. Reads the run spec through the rank straddle and the
  order-stage `DummyMarkerBracket` seam
  (`StrictDummyFrameProof.lean:51`). Residual: `XFR_StrictDummyLinkedX`.
* `routeLabelForeignClear_of_run`
  (`RouteLabelForeignClearProof.lean:51`): outside labels miss foreign
  frames. Reads the run spec through the `RouteLabelDummyCellForeignClear`
  residual (`RouteLabelForeignClearProof.lean:36`) plus the span seams.
  Residual: `XFR_RouteLabelForeignClearX`.
* `routeLabelLeftoverPair_of_run`
  (`RouteLabelLeftoverPairProof.lean:446`): leftover (nonzero dummy or
  scope-failing real) positions clear. Composes strict, span, foreign, and
  nonforward facts; run-generic. Residual: `XFR_RouteLabelLeftoverPairX`.
* `bracketMarkersAtRank'` (`SideMarkerTopInCandidateProof.lean:508`) and
  `foreignClusterRankSpans'` (`ForeignMemberRankBoundsProof.lean:215`):
  closed span facts; reused outright (no exact replay needed).
* `ForeignBorderChainXAligned` (`ForeignBorderSpansProof.lean:140`): the one
  open span seam; kept as hypothesis exactly as `routeRunClear_closed`
  keeps it.
* `SeamsImplyForeign` (`RouteRunClearCases.lean:237`): the seam discharge
  contract (`foreignFramesDisjoint_of_run`, `RouteRunClearCases.lean:752`,
  from the group half plus the marker half). Residual:
  `XFR_SeamsImplyForeignX`.

Each residual below is a single fact over exact runs, strictly narrower than
the goal (one mechanism: dummy containment, real separation, dummy
existence, strict frame, foreign miss, leftover pair, seam discharge).
Probe: `proofs/wip/Probe/ExactRouteFwdClearTProbe.lean` evaluates every
residual on flat, self-loop-on-fixed, reversed-pair-into-group, and
wider-than-slot fixed inputs. -/

/-- Exact strict linked dummy frame: mirror of `StrictDummyFrameLinked`
(`RouteRunClearCases.lean:203`) over `componentRunX`. Plain original takes it
as the `h1` hypothesis of `route_run_clear_inlined`. -/
def XFR_StrictDummyLinkedX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    StrictDummyFrameLinked execution.params
      (componentCandidate execution.graph comp candidate) run

/-- Exact placed-in-dummy: mirror of `RouteLabelInDummy`
(`RouteRunClearCases.lean:214`) over `componentRunX`. Plain original takes it
as the `h2` hypothesis of `route_run_clear_inlined`. -/
def XFR_RouteLabelInDummyX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    RouteLabelInDummy execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured

/-- Exact real clearance: mirror of `RouteLabelRealClear`
(`RouteRunClearCases.lean:245`) over `componentRunX`. Plain original takes it
as the `hReal` hypothesis of `route_run_clear_inlined`. -/
def XFR_RouteLabelRealClearX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    RouteLabelRealClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured

/-- Exact foreign clearance: mirror of `RouteLabelForeignClear`
(`RouteRunClearCases.lean:261`) over `componentRunX`. Plain original takes it
as the `hforeign` hypothesis of `route_run_clear_inlined`. -/
def XFR_RouteLabelForeignClearX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    RouteLabelForeignClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured

/-- Exact leftover pair: mirror of `RouteLabelLeftoverPair`
(`RouteRunClearCases.lean:291`) over `componentRunX`. Plain original takes it
as the `hleftover` hypothesis of `route_run_clear_inlined`. -/
def XFR_RouteLabelLeftoverPairX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    RouteLabelLeftoverPair execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured

/-- Exact labeled-edge dummy existence: mirror of the `hdummy_ex` premise of
`route_run_clear_inlined` (`RouteRunClearCases.lean:414`) over
`componentRunX`. -/
def XFR_DummyExLabeledX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (edge : Nat) (e : Edge),
      (componentCandidate execution.graph comp candidate).edges[edge]? = some e →
      e.tail ≠ e.head → e.reversed = false →
      (∃ l, l ∈ execution.measured ∧ l.edge = e.decl) →
      ∃ ndd d, ndd.dummy = true ∧ run.proper.nodes.zipIdx.find?
        (fun q => q.1.edge == some edge && rk run.proper.rank q.2 ==
          rk run.proper.rank e.tail + Int.fdiv
            (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (ndd, d)

/-- Exact seam discharge: mirror of `SeamsImplyForeign`
(`RouteRunClearCases.lean:237`) over `componentRunX`. Plain original takes it
as the `himp` hypothesis of `route_run_clear_inlined` (discharged there by
`foreignFramesDisjoint_of_run`). -/
def XFR_SeamsImplyForeignX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    SeamsImplyForeign execution.params
      (componentCandidate execution.graph comp candidate) run

/-- Copy of the private `disjoint_symm'` (`RouteRunClearCases.lean:80`). -/
private theorem xfr_disjoint_symm' {a b : Rect} (h : Disjoint a b) :
    Disjoint b a :=
  fun hm => h ((Rect.meetsInterior_comm _ _).mpr hm)

/-- Copy of the private `frameRect_eq_nodeRect_of_plain`
(`RouteRunClearCases.lean:130`). -/
private theorem xfr_frameRect_eq_nodeRect_of_plain {P : Params} {cg : Graph}
    {run : Run} {pos : Nat} {nd : Node} (hnd : cg.nodes[pos]? = some nd)
    (hplain : nd.border ≠ -2) :
    frameRect P cg run pos = nodeRect cg run pos := by
  have hget : cg.nodes.getD pos default = nd := by
    rw [List.getD_eq_getElem?_getD, hnd, Option.getD_some]
  have hb : ((cg.nodes.getD pos default).border != -2) = true := by
    rw [hget]
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]

/-- Forward-only inlined clearance: the forward branch of
`route_run_clear_inlined` (`RouteRunClearCases.lean:412`), with the
nonforward dispatch removed. The edge form (`hne`, `hrev`) is a premise, so
no `RouteNonforwardLabelClear` hypothesis is needed. -/
private theorem xfr_forwardClearX {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel}
    (hdummy_ex : ∀ (edge : Nat) (e : Edge), cg.edges[edge]? = some e →
      e.tail ≠ e.head → e.reversed = false →
      (∃ l, l ∈ labels ∧ l.edge = e.decl) →
      ∃ ndd d, ndd.dummy = true ∧ run.proper.nodes.zipIdx.find?
        (fun q => q.1.edge == some edge && rk run.proper.rank q.2 ==
          rk run.proper.rank e.tail + Int.fdiv
            (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (ndd, d))
    (h1 : StrictDummyFrameLinked P cg run)
    (h2 : RouteLabelInDummy P cg run labels)
    (hbracket : BracketMarkersAtRank) (hrank : ForeignClusterRankSpans)
    (hxalign : ForeignBorderChainXAligned)
    (himp : SeamsImplyForeign P cg run)
    (hReal : RouteLabelRealClear P cg run labels)
    (hforeign : RouteLabelForeignClear P cg run labels)
    (hleftover : RouteLabelLeftoverPair P cg run labels)
    {k : Nat} {rect : Rect} {l₀ : MeasuredLabel} {edge : Nat} {e : Edge}
    (hmem : (k, rect) ∈ placedLabels P cg run labels)
    (hmem0 : l₀ ∈ labels) (hidx : l₀.index = k)
    (hedge : cg.edges[edge]? = some e) (hdecl : e.decl = l₀.edge)
    (hne : e.tail ≠ e.head) (hrev : e.reversed = false)
    {pos : Nat} (hpos : pos < cg.nodes.length) :
    Disjoint (frameRect P cg run pos) rect ∨
      (frameRect P cg run pos).StrictInside rect := by
  have hne' : cg.nodes[pos]? ≠ none := by
    intro h
    rw [List.getElem?_eq_none_iff] at h
    omega
  obtain ⟨nd, hnd⟩ := Option.ne_none_iff_exists'.mp hne'
  by_cases hgrp : nd.border = -2
  · -- Group frame at `pos`: the label dummy decides.
    obtain ⟨ndd, d, hddummy, hdfind⟩ :=
      hdummy_ex edge e hedge hne hrev ⟨l₀, hmem0, hdecl.symm⟩
    by_cases hpc : nd.decl ∈ ndd.node.clusterPath
    · exact Or.inr
        (case_group_inside hmem hmem0 hidx hedge hdecl hne hrev hnd hgrp
          hddummy hdfind hpc h1 h2)
    · exact Or.inl
        (hforeign hbracket hrank hxalign himp k rect l₀ edge e hmem hmem0
          hidx hedge hdecl hne hrev d ndd hddummy hdfind pos nd hnd hgrp hpc)
  · -- Non-group position: the node's own rect.
    cases hpp : run.proper.nodes[pos]? with
    | none =>
      have hget : run.proper.nodes.getD pos default = default := by
        simp only [List.getD_eq_getElem?_getD, hpp, Option.getD_none]
      have hfr : frameRect P cg run pos = nodeRect cg run pos :=
        xfr_frameRect_eq_nodeRect_of_plain hnd hgrp
      have hh0 : (nodeRect cg run pos).h = 0 := by
        unfold nodeRect
        rw [hget]
        show (default : ProperNode).node.h = 0
        rfl
      have hD : Disjoint rect (frameRect P cg run pos) := by
        rw [hfr]
        exact not_meetsInterior_of_box_zero_h hh0
      exact Or.inl (xfr_disjoint_symm' hD)
    | some pn =>
      by_cases hh0 : RouteImpl.nodeH run.proper pos = 0
      · exact Or.inl (case_plain_zero hnd hgrp hpp hh0 rect)
      · by_cases hreal : pn.dummy = false
        · have hI : RouteImpl.IsReal run.proper pos := fun nd' hnd' => by
            rw [hpp] at hnd'
            have heq : nd' = pn := Option.some.inj hnd'.symm
            rw [heq]
            exact hreal
          by_cases hsc : (RouteImpl.nodeDecl run.proper pos ∉
              ((cg.nodes[e.tail]?).map (fun n => n.clusterPath)).getD [] ∧
            RouteImpl.nodeDecl run.proper pos ∉
              ((cg.nodes[e.head]?).map (fun n => n.clusterPath)).getD [])
          · exact Or.inl
              (case_plain_real hmem hmem0 hidx hedge hdecl hnd hgrp hpp hI
                hsc.1 hsc.2 hReal)
          · exact hleftover k rect l₀ edge e hmem hmem0 hidx hedge hdecl
              pos hpos pn hpp (Or.inr ⟨hI, hsc⟩)
        · have hdt : pn.dummy = true := by
            cases hd : pn.dummy with
            | true => rfl
            | false => exact absurd hd hreal
          exact hleftover k rect l₀ edge e hmem hmem0 hidx hedge hdecl
            pos hpos pn hpp (Or.inl ⟨hdt, hh0⟩)

/-- Exact forward route clearance: placed labels of forward edges clear every
frame position. Replay of the forward branch of `route_run_clear_inlined`
over `componentRunX`; the composition reads no run spec. -/
theorem XF_routeForwardClearX_holds (exactIds : List String)
    (hstrict : XFR_StrictDummyLinkedX exactIds)
    (hinDummy : XFR_RouteLabelInDummyX exactIds)
    (hreal : XFR_RouteLabelRealClearX exactIds)
    (hforeign : XFR_RouteLabelForeignClearX exactIds)
    (hleftover : XFR_RouteLabelLeftoverPairX exactIds)
    (hdummy : XFR_DummyExLabeledX exactIds)
    (hxalign : ForeignBorderChainXAligned)
    (himp : XFR_SeamsImplyForeignX exactIds) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
      (k, rect) ∈ placedLabels execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured →
      l₀ ∈ execution.measured → l₀.index = k →
      (componentCandidate execution.graph comp candidate).edges[edge]? = some e →
      e.decl = l₀.edge → e.tail ≠ e.head → e.reversed = false →
      ∀ (pos : Nat), pos <
        (componentCandidate execution.graph comp candidate).nodes.length →
      Disjoint (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos) rect ∨
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos).StrictInside rect := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  have h1 := hstrict execution hcomp hrun
  have h2 := hinDummy execution hcomp hrun
  have hR := hreal execution hcomp hrun
  have hF := hforeign execution hcomp hrun
  have hL := hleftover execution hcomp hrun
  have hD := hdummy execution hcomp hrun
  have hI := himp execution hcomp hrun
  have hbr : BracketMarkersAtRank := bracketMarkersAtRank'
  have hrk : ForeignClusterRankSpans := foreignClusterRankSpans'
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev pos hpos
  exact xfr_forwardClearX hD h1 h2 hbr hrk hxalign hI hR hF hL hmem hmem0
    hidx hedge hdecl hne hrev hpos

end PipelineImpl
end Layered
end Elegant
