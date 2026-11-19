import Elegant.Layered.ExactRouteNonforwardClearProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.Pipeline
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Exact extended group-hull clearance away from the owner: the extended
footprint of a self-loop owner is disjoint from, or strictly contains, every
group frame at a different index. This is `XNonfwd_GroupHullExt` with the
trivial self position (`pos = t`) removed; the self case is proved below by
`x`-separation. Probe: `ExactRouteNonfwdClearHullProbe` (extended footprint
vs group frames, no violations on alone/sibling/group/wide/reversed inputs). -/
def XNonfwd_GroupHullExtNe (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
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

/-- Ancestor case of the extended group-hull clearance: the group frame of an
ancestor group strictly contains the extended loop footprint. One case of
`XNonfwd_GroupHullExtNe` (ancestor groups only). Probe:
`ExactNonfwdGroupHullTProbe` prints `rel=anc disj=S` on every ancestor pair
(flat/group/nested/loop-group/sibling/no-edge inputs, zero, sane, wide, and
tall fixed sizes): 60 of 60 ancestor checks are `StrictInside`. -/
def XNonfwd_AncHull (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
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

/-- Non-ancestor case of the extended group-hull clearance: the group frame of
a group that is not an ancestor of the loop owner is disjoint from the
extended loop footprint. The complementary case of `XNonfwd_AncHull`
(nested groups and foreign groups). Probe: `ExactNonfwdGroupHullTProbe`
prints `rel=for disj=D` on every foreign pair (10 of 10, sibling-group
inputs) and observes zero nested pairs; zero violations overall. -/
def XNonfwd_NonAncHull (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
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

/-- The extended footprint starts at its frame right edge, so it is disjoint
from that same frame at any `Params` (the frame ignores its `Params`
argument). Copy of the plain `loopFootprint_self_pos` shape for
`loopFootprintExt`. -/
private theorem xngh_self_disjoint {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (t : Nat) :
    Disjoint (frameRect P cg run t) (loopFootprintExt cg run labels t) := by
  have hPP : frameRect P cg run t = frameRect default cg run t := rfl
  have hEx : (loopFootprintExt cg run labels t).x =
      (frameRect default cg run t).x + (frameRect default cg run t).w := rfl
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  rw [hPP, hEx] at hx
  omega

/-- A self-loop tail is in bounds over an exact run: replay of the plain
`loopTail_bounded` through `sceneExecutionX_edges_bounded` and the
order-free `candidate_edge_endpoints_bounded_general`. -/
private theorem xngh_loopTail {exactIds : List String} {inp : Input}
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

/-- Exact extended group-hull clearance modulo the self position: the self
position is `x`-separated above, every other position is the residual. -/
theorem XNonfwd_groupHullExt_holds (exactIds : List String)
    (hNe : XNonfwd_GroupHullExtNe exactIds) :
    XNonfwd_GroupHullExt exactIds := by
  intro inp o res execution comp candidate run orderOptions cg t pos hcomp hcg hrun het hpos gn hg hgrp
  by_cases heq : pos = t
  · subst heq
    exact Or.inl (xngh_self_disjoint _)
  · exact hNe inp o res execution comp candidate run orderOptions cg t pos hcomp hcg hrun het hpos heq gn hg hgrp

/-- The off-owner residual from its two cases: ancestor positions use strict
containment, non-ancestor positions use disjointness. -/
theorem XNonfwd_groupHullExtNe_holds (exactIds : List String)
    (hAnc : XNonfwd_AncHull exactIds)
    (hNon : XNonfwd_NonAncHull exactIds) :
    XNonfwd_GroupHullExtNe exactIds := by
  intro inp o res execution comp candidate run orderOptions cg t pos hcomp hcg hrun het hpos hne gn hg hgrp
  have hetC : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t := by
    rw [← hcg]
    exact het
  have htbC := xngh_loopTail execution hcomp hetC
  rw [← hcg] at htbC
  obtain ⟨nt, hnt⟩ : ∃ n, cg.nodes[t]? = some n :=
    ⟨_, List.getElem?_eq_getElem htbC⟩
  by_cases hmem : gn.decl ∈ nt.clusterPath
  · exact Or.inr (hAnc inp o res execution comp candidate run orderOptions cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem)
  · exact Or.inl (hNon inp o res execution comp candidate run orderOptions cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem)

/-- Exact extended group-hull clearance from its two cases. -/
theorem XNonfwd_groupHullExt_closed (exactIds : List String)
    (hAnc : XNonfwd_AncHull exactIds)
    (hNon : XNonfwd_NonAncHull exactIds) :
    XNonfwd_GroupHullExt exactIds :=
  XNonfwd_groupHullExt_holds exactIds
    (XNonfwd_groupHullExtNe_holds exactIds hAnc hNon)

end PipelineImpl
end Layered
end Elegant
