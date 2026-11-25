import Elegant.Layered.ExactNonfwdGroupHullProof
import Elegant.Layered.ExactRunFrameNestingProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import ElegantGeometry.Disjoint
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact non-forward group-hull facts (W form)

The unscoped hull predicates in `ExactNonfwdGroupHullProof.lean` quantify
over every `SceneExecutionX`. Intermediate runs with unframed parents can
violate the unscoped group-hull clearance even though `layoutFamilyX`
rejects those inputs.

The W predicates carry the local `WellFormed` and `framedParents` premises
available from successful family execution. The full predicate
`XNonfwd_GroupHullExtW` is defined in `ExactRouteNonforwardClearProof.lean`.
The probes in `wip/Probe/ExactNonfwdHullsTProbe.lean` and
`wip/Probe/ExactNonfwdGroupHullTProbe.lean` sample admitted cases, including
nested groups, zero-size owners, and fixed boxes; they do not close the
hull residual.

Gap analysis (why the ancestor `StrictInside` is not closed outright):
`loopFootprintExt` starts at its owner's right edge
(`(loopFootprintExt cg run labels v).x = (frameRect default cg run v).x +
(frameRect default cg run v).w` by definition), so no "footprint inside the
owner's frame" bound exists; the ancestor claim needs the hull-right cover
(`LoopHullRightCover`, open even in plain land modulo the R1 machinery) plus
positive hull margins (the plain strictness walk has no exact replay), and
group-owner transitivity needs an exact ancestor walk (only the direct
parent/child facts of `ExactRunFrameNesting` are proved). The non-ancestor
foreign sub-case needs the foreign-span seams plus the right-neighbour
extent bound (`LoopHullRightNeighborCover`, open).

Proved here (zero hypotheses): the self-position case, the plain-owner
ancestor containment core (`XNonfwd_AncPlainContainW`, via
`exactRunFrameNesting.1`), and the W split/closing dispatchers. The single
open residual `XNonfwd_HullRemW` conjoins the plain-owner strict upgrade
(given the proved containment), the non-ancestor disjointness, and the
group-owner ancestor case; all three conjuncts hold on every executed probe.
-/

/-- W twin of `XNonfwd_AncHull`: ancestor strict containment over the actual
executed run, with local `WellFormed` / `framedParents` after the execution
binder. -/
def XNonfwd_AncHullW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).StrictInside
        (loopFootprintExt cg run execution.measured t)

/-- W twin of `XNonfwd_NonAncHull`: non-ancestor disjointness over the actual
executed run, with local `WellFormed` / `framedParents` after the execution
binder. -/
def XNonfwd_NonAncHullW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∉ nt.clusterPath →
      Disjoint (frameRect execution.params cg run pos)
        (loopFootprintExt cg run execution.measured t)

/-- W twin of `XNonfwd_GroupHullExtNe`: off-self clearance over the actual
executed run. -/
def XNonfwd_GroupHullExtNeW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      Disjoint (frameRect execution.params cg run pos)
        (loopFootprintExt cg run execution.measured t) ∨
        (frameRect execution.params cg run pos).StrictInside
          (loopFootprintExt cg run execution.measured t)

/-- Proved narrower ancestor core: the ancestor group hull contains the plain
loop owner's frame. Strictly narrower than `XNonfwd_AncHullW` (plain owners
only, non-strict containment of the owner frame rather than strict
containment of the footprint); true on every probe. -/
def XNonfwd_AncPlainContainW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = 0 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).Contained
        (frameRect execution.params cg run t)

/-- Single open residual: the plain-owner strict upgrade given the proved
containment, the non-ancestor disjointness (foreign sub-case needs the
foreign-span seams plus the right-neighbour extent bound), and the
group-owner ancestor case (needs an exact ancestor walk). All three hold on
every executed probe. -/
def XNonfwd_HullRemW (exactIds : List String) : Prop :=
  (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border = 0 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).Contained
        (frameRect execution.params cg run t) →
      (frameRect execution.params cg run pos).StrictInside
        (loopFootprintExt cg run execution.measured t))
  ∧ XNonfwd_NonAncHullW exactIds
  ∧ (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (t pos : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    pos ≠ t →
    ∀ (nt : Node), nt.border ≠ 0 → cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∈ nt.clusterPath →
      (frameRect execution.params cg run pos).StrictInside
        (loopFootprintExt cg run execution.measured t))

/-- Prefixed copy of `xngh_self_disjoint` (`ExactNonfwdGroupHullProof`): the
extended footprint starts at its frame right edge, so it is disjoint from
that same frame. -/
private theorem xnhf_self_disjoint {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (t : Nat) :
    Disjoint (frameRect P cg run t) (loopFootprintExt cg run labels t) := by
  have hPP : frameRect P cg run t = frameRect default cg run t := rfl
  have hEx : (loopFootprintExt cg run labels t).x =
      (frameRect default cg run t).x + (frameRect default cg run t).w := rfl
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  rw [hPP, hEx] at hx
  omega

/-- Prefixed copy of `xngh_loopTail`: a self-loop tail is in bounds over an
exact run. -/
private theorem xnhf_loopTail {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {t : Nat}
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t) :
    t < (componentCandidate execution.graph comp candidate).nodes.length := by
  obtain ⟨e, hmem, ht, -⟩ := het
  have hbd := sceneExecutionX_edges_bounded execution
  have hb := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd hmem
  omega

/-- Plain-owner ancestor containment, proved fully via `exactRunFrameNesting`:
every plain loop owner inside a group lies in its frame. -/
theorem xnonfwd_ancPlainContainW_holds (exactIds : List String) :
    XNonfwd_AncPlainContainW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun _het _hpos _hne nt ntplain hnt gn hgn hgrp hmem
  subst hcg
  exact (exactRunFrameNesting execution hwf hfp).1 comp candidate run
    orderOptions hcomp hrun pos t gn nt hgn hgrp hnt ntplain
    (List.contains_iff_mem.mpr hmem)

/-- W off-self clearance from its two cases: ancestor positions use strict
containment, non-ancestor positions use disjointness. Replay of
`XNonfwd_groupHullExtNe_holds` with local well-formedness threaded through. -/
theorem XNonfwd_groupHullExtNeW_holds (exactIds : List String)
    (hAnc : XNonfwd_AncHullW exactIds)
    (hNon : XNonfwd_NonAncHullW exactIds) :
    XNonfwd_GroupHullExtNeW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne gn hg hgrp
  have hetC : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t := by
    rw [← hcg]
    exact het
  have htbC := xnhf_loopTail execution hcomp hetC
  rw [← hcg] at htbC
  obtain ⟨nt, hnt⟩ : ∃ n, cg.nodes[t]? = some n :=
    ⟨_, List.getElem?_eq_getElem htbC⟩
  by_cases hmem : gn.decl ∈ nt.clusterPath
  · exact Or.inr (hAnc inp o res execution hwf hfp comp candidate run
      orderOptions cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem)
  · exact Or.inl (hNon inp o res execution hwf hfp comp candidate run
      orderOptions cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem)

/-- W clearance modulo the self position: the self position is `x`-separated,
every other position is the residual. Replay of `XNonfwd_groupHullExt_holds`. -/
theorem XNonfwd_groupHullExtW_holds (exactIds : List String)
    (hNe : XNonfwd_GroupHullExtNeW exactIds) :
    XNonfwd_GroupHullExtW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos gn hg hgrp
  by_cases heq : pos = t
  · subst heq
    exact Or.inl (xnhf_self_disjoint _)
  · exact hNe inp o res execution hwf hfp comp candidate run orderOptions cg
      t pos hcomp hcg hrun het hpos heq gn hg hgrp

/-- Ancestor case from the proved containment core plus the residual's strict
upgrade (plain owners) or group-owner branch: plain owners chain the core
into the upgrade; group owners use the walk-free residual branch. -/
theorem xnonfwd_ancHullW_holds (exactIds : List String)
    (hRem : XNonfwd_HullRemW exactIds) :
    XNonfwd_AncHullW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem
  by_cases hplain : nt.border = 0
  · have hcont := xnonfwd_ancPlainContainW_holds exactIds inp o res execution
      hwf hfp comp candidate run orderOptions cg t pos hcomp hcg hrun het
      hpos hne nt hplain hnt gn hg hgrp hmem
    exact hRem.1 inp o res execution hwf hfp comp candidate run orderOptions
      cg t pos hcomp hcg hrun het hpos hne nt hplain hnt gn hg hgrp hmem hcont
  · exact hRem.2.2 inp o res execution hwf hfp comp candidate run
      orderOptions cg t pos hcomp hcg hrun het hpos hne nt hplain hnt gn hg
      hgrp hmem

/-- Non-ancestor case from the residual's disjointness branch (the foreign
sub-case needs the foreign-span seams plus the right-neighbour extent bound;
the nested-child sub-case is the residual's as well). -/
theorem xnonfwd_nonAncHullW_holds (exactIds : List String)
    (hRem : XNonfwd_HullRemW exactIds) :
    XNonfwd_NonAncHullW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem
  exact hRem.2.1 inp o res execution hwf hfp comp candidate run orderOptions
    cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem

/-- W clearance from the single residual: ancestor and non-ancestor cases
discharge through `XNonfwd_HullRemW`, then the proved split dispatchers
assemble the full clearance. -/
theorem xnonfwd_groupHullExtW_closed (exactIds : List String)
    (hRem : XNonfwd_HullRemW exactIds) :
    XNonfwd_GroupHullExtW exactIds :=
  XNonfwd_groupHullExtW_holds exactIds
    (XNonfwd_groupHullExtNeW_holds exactIds
      (xnonfwd_ancHullW_holds exactIds hRem)
      (xnonfwd_nonAncHullW_holds exactIds hRem))

end PipelineImpl
end Layered
end Elegant
