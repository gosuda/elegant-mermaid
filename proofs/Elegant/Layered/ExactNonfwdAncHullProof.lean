import Elegant.Layered.ExactRunFrameNestingProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.Pipeline
import ElegantGeometry.Disjoint
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact non-forward ancestor/non-ancestor hull clearance (W form)

Targets: `XNonfwd_AncHull` / `XNonfwd_NonAncHull` of `ExactNonfwdGroupHullProof`
(ancestor StrictInside vs non-ancestor Disjoint of the extended loop footprint
against group frames), restated here with the local `WellFormed` /
`framedParents` premises that every helper needs (the W twins `XNonfwd_AncHullXW`
/ `XNonfwd_NonAncHullXW`).

Truth (`wip/Probe/ExactNonfwdAncHullTProbe.lean`, 10 executed inputs x 5
candidates: plain self-loop in a group, fixed group loop, multi-level nesting,
zero-size and wide owners, empty groups, sibling groups with and without a
connecting edge, unfixed group loop with a child group, and an ill-formed
fixed-parent input): 55 ancestor/nested/foreign checks, zero violations.
Ancestor pairs are `StrictInside` with positive margins; the ancestor hull
contains the owner frame (`ancCont = true`, plain and group owners, zero-size
included). Nested pairs (group owner with child group) are `Disjoint` with the
child frame in the owner frame (`nestCont = true`). Foreign pairs (connected
siblings) are `Disjoint` with the footprint kept left of the hull
(`keep = true`). Ill-formed and split-component inputs contribute no pairs.

Why the earlier draft (`ExactNonfwdHullFactsProof.lean`, read-only) stays
unused: its single residual conjoined the plain-owner strict upgrade, the
non-ancestor target verbatim as its second conjunct, and the group-owner case.
Restating the sibling target as a premise is an alias, and the bundle never
replays the closed plain pieces. This file instead keeps one residual per
target, each a conjunction of strictly narrower statements (extra border or
membership premises; a containment fact on the way to disjointness), and
replays the closed pieces (`exactRunFrameNesting.1`, footprint x-origin
x-separation) inside the reductions.

Open geometry named exactly (plain-land names): the ancestor side needs the
hull-right cover (`LoopHullRightCover`, non-plain part `LoopResGroupHullRight`)
plus positive hull margins for the strict upgrade, and the exact ancestor walk
(transitive `ExactRunFrameNesting`) for group owners; the non-ancestor side
needs the right-neighbour extent bound (`LoopHullRightNeighborCover`, through
`R3ExtentFitGap`) with the foreign-span seams for foreign hulls, and the exact
downward walk (`X_child_frame_contained` chained) for nested containment.
-/

/-- W twin of `XNonfwd_AncHull`: ancestor strict containment over the actual
executed run, with local `WellFormed` / `framedParents` after the execution
binder. Probe: `ExactNonfwdAncHullTProbe` ancestor pairs, all `StrictInside`. -/
def XNonfwd_AncHullXW (exactIds : List String) : Prop :=
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
binder. Probe: `ExactNonfwdAncHullTProbe` nested/foreign pairs, all
`Disjoint`. -/
def XNonfwd_NonAncHullXW (exactIds : List String) : Prop :=
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

/-- Single open residual for the ancestor target: the plain-owner strict
upgrade given the proved frame containment, plus the group-owner ancestor
case. Each conjunct is strictly narrower than `XNonfwd_AncHullXW` (extra
border premise; the upgrade carries the containment premise and concludes the
footprint claim). True on every executed probe (`r1m`/`botm` positive,
`ancCont` true). Open bounds named: `LoopHullRightCover` /
`LoopResGroupHullRight` plus positive hull margins (first conjunct), and the
exact ancestor walk (second conjunct). -/
def XNonfwd_AncRemXW (exactIds : List String) : Prop :=
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

/-- Single open residual for the non-ancestor target: the foreign disjointness
sub-case, plus the nested containment fact on the way to disjointness. Each
conjunct is strictly narrower than `XNonfwd_NonAncHullXW` (extra descendant
premise; the nested conjunct concludes containment rather than disjointness).
True on every executed probe (foreign `keep`, nested `nestCont`). Open bounds
named: `LoopHullRightNeighborCover` through `R3ExtentFitGap` with the
foreign-span seams (first conjunct), and the exact downward walk (second
conjunct). -/
def XNonfwd_NonAncRemXW (exactIds : List String) : Prop :=
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
    ∀ (nt : Node), cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∉ nt.clusterPath →
      nt.decl ∉ gn.clusterPath →
      Disjoint (frameRect execution.params cg run pos)
        (loopFootprintExt cg run execution.measured t))
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
    ∀ (nt : Node), cg.nodes[t]? = some nt →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      gn.decl ∉ nt.clusterPath →
      nt.decl ∈ gn.clusterPath →
      (frameRect execution.params cg run t).Contained
        (frameRect execution.params cg run pos))


/-- Prefixed copy of `xngh_self_disjoint` (`ExactNonfwdGroupHullProof`): the
extended footprint starts at its frame right edge, so `omega` closes the
x-gap once the `Params` equation is rewritten to `default`. -/
private theorem xnha_fpX {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (t : Nat) :
    (loopFootprintExt cg run labels t).x =
      (frameRect P cg run t).x + (frameRect P cg run t).w := by
  have hPP : frameRect P cg run t = frameRect default cg run t := rfl
  have hEx : (loopFootprintExt cg run labels t).x =
      (frameRect default cg run t).x + (frameRect default cg run t).w := rfl
  rw [hPP]
  exact hEx

/-- Nested x-separation: a group frame in the loop owner frame ends left of
the footprint origin. Closed by `omega` through `le_max_right` /
`min_le_left`; no footprint-width nonnegativity is needed. -/
private theorem xnha_nestedDisjoint {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {t pos : Nat}
    (hcont : (frameRect P cg run t).Contained (frameRect P cg run pos))
    (hfp : (loopFootprintExt cg run labels t).x =
      (frameRect P cg run t).x + (frameRect P cg run t).w) :
    Disjoint (frameRect P cg run pos) (loopFootprintExt cg run labels t) := by
  have hle : (frameRect P cg run pos).x + (frameRect P cg run pos).w ≤
      (loopFootprintExt cg run labels t).x :=
    calc (frameRect P cg run pos).x + (frameRect P cg run pos).w
        ≤ (frameRect P cg run t).x + (frameRect P cg run t).w := hcont.2.1
      _ = (loopFootprintExt cg run labels t).x := hfp.symm
  unfold Disjoint Rect.meetsInterior
  intro hmeet
  have hmax : (loopFootprintExt cg run labels t).x ≤
      max (frameRect P cg run pos).x (loopFootprintExt cg run labels t).x :=
    Int.le_max_right _ _
  have hmin : min ((frameRect P cg run pos).x + (frameRect P cg run pos).w)
      ((loopFootprintExt cg run labels t).x +
        (loopFootprintExt cg run labels t).w) ≤
      (frameRect P cg run pos).x + (frameRect P cg run pos).w :=
    Int.min_le_left _ _
  obtain ⟨hx, -⟩ := hmeet
  omega

/-- Plain-owner ancestor containment, proved outright through
`exactRunFrameNesting.1`: every plain loop owner inside a group lies in its
frame at any depth. Replay of the draft core `xnonfwd_ancPlainContainW_holds`. -/
private theorem xnha_plainContain {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t pos : Nat} {nt gn : Node}
    (hplain : nt.border = 0)
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (hgn : (componentCandidate execution.graph comp candidate).nodes[pos]? = some gn)
    (hgrp : gn.border = -2)
    (hmem : gn.decl ∈ nt.clusterPath) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run pos).Contained
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run t) := by
  have hinside : nt.clusterPath.contains gn.decl = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hmem
  exact (exactRunFrameNesting execution hwf hfp).1 comp candidate run orderOptions
    hcomp hrun pos t gn nt hgn hgrp hnt hplain hinside

/-- Ancestor case from the proved containment core plus the residual: plain
owners chain the core into the residual's strict upgrade; group owners use the
residual's second conjunct. -/
theorem XNonfwd_ancHull_holds (exactIds : List String)
    (hRem : XNonfwd_AncRemXW exactIds) :
    XNonfwd_AncHullXW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem
  subst hcg
  by_cases hplain : nt.border = 0
  · have hcont := xnha_plainContain execution hwf hfp hcomp hrun
      hplain hnt hg hgrp hmem
    exact hRem.1 inp o res execution hwf hfp comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) t pos
      hcomp rfl hrun het hpos hne nt hplain hnt gn hg hgrp hmem hcont
  · exact hRem.2 inp o res execution hwf hfp comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) t pos
      hcomp rfl hrun het hpos hne nt hplain hnt gn hg hgrp hmem

/-- Non-ancestor case from the residual plus closed x-separation: nested
positions chain the residual's containment fact into `xnha_nestedDisjoint`;
foreign positions use the residual's disjointness branch. -/
theorem XNonfwd_nonAncHull_holds (exactIds : List String)
    (hRem : XNonfwd_NonAncRemXW exactIds) :
    XNonfwd_NonAncHullXW exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
    hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem

  have hfx : (loopFootprintExt cg run execution.measured t).x =
      (frameRect execution.params cg run t).x +
        (frameRect execution.params cg run t).w :=
    xnha_fpX t
  by_cases hnest : nt.decl ∈ gn.clusterPath
  · have hcont := hRem.2 inp o res execution hwf hfp comp candidate run
      orderOptions cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp
      hmem hnest
    exact xnha_nestedDisjoint hcont hfx
  · exact hRem.1 inp o res execution hwf hfp comp candidate run orderOptions
      cg t pos hcomp hcg hrun het hpos hne nt hnt gn hg hgrp hmem hnest

end PipelineImpl
end Layered
end Elegant
