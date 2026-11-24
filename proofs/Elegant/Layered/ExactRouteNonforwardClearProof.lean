import Elegant.Layered.ExactRouteRunClearProof
import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.ExactFlatC7Reversed
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact nonforward route-label clearance (`XF_routeNonforwardClearX_holds`)

The W nonforward callback for `XF_routeRunClearXW_holds` and
`XFR_routeLabelLeftoverPairXW_holds` covers placed labels of self-loops and
reversed edges in a well-formed, framed `componentRunX` execution.

Plain path replayed (`routeNonforwardLabelClear_of_run`,
`RouteNonforwardLabelClearProof.lean:226`, as closed by `routeRunClear_closed`,
`RouteRunClearClosed.lean:76`):

* `placedLabels_pair_inv` (`LabelRunBridgeFacts.lean:362`): placed pair unpacks
  to label, edge, envelope, and stack rect. Run-generic; reused outright.
* `measureLabels_index_nodup` (`LabelRunBridgeFacts.lean:198`),
  `measured_eq_of_index_eq` (`LabelRunBridgeFacts.lean:336`),
  `componentCandidate_decls_nodup` (`PipelineFacts.lean:3175`) with
  `exactGraph_decls_nodup` (`ExactFlatFacts.lean:202`): edge identity from decl
  uniqueness (exact edges untouched). Run-generic; reused outright.
* `reversed_envelope_eq` (`RunLocalSeparationsProof.lean:604`): reversed
  envelope sits in the planned lane. Envelope equation only; reused outright.
* `RouteImpl.plannedLane_right_strict`, `RouteImpl.laneRight_bound`,
  `frameRect_group_span` (`ForeignSpansFacts.lean:83`),
  `boundsOf_right_le_of_all` (`ForeignSpansFacts.lean:133`),
  `fbs_groupBorderRects_spec` (`ForeignBorderSpansProof.lean:187`),
  `boxRect_left`, `boxRect_w` (`LabelsC7RunLocal.lean:61,72`),
  `fdiv2_ediv` (`LabelsC7RunLocal.lean:88`): lane right of every box and hull.
  Run-generic; reused outright with `componentRunX_spec`
  (`ExactFlatFacts.lean:284`) for the lane routing.
* `x_runLocalReversedSeparation_holds` (`ExactFlatC7Reversed.lean:19`):
  exact replacement for the reversed lane bound (same lane lemmas over
  `componentRunX_spec`); the reversed plain-box subcase below replays its
  argument inline (scope-free, as the plain proof notes).
* `componentRunX_slot_nonneg` (`ExactPartBounded.lean:181`),
  `SceneExecutionX.measured_nonneg` (`ExactPartBounded.lean:356`),
  `componentRunX_original_nodes_covered` (`ExactPartBounded.lean:202`),
  `plain_frame_eq_boxRect` (`ExecutedPortsFacts.lean:13`),
  `not_meetsInterior_of_left_le` (`LabelsC7RunLocal.lean:31`),
  `not_meetsInterior_of_box_zero_h` (`LabelsC7RunLocal.lean:433`),
  `not_meetsInterior_of_contained` (`LabelsC7RunLocal.lean:255`),
  `stackRects_entry` (`RunLocalSeparationsProof.lean:40`),
  `labelEnvelope_loop_size` (`SceneBounds.lean:1266`),
  `Labels.stackRects_contained` (`Labels.lean:405`): placement and frame
  transport. Run-generic; reused outright.
* Loop envelope inversion: prefixed copies `xnonfwd_loop_envelope_eq` and
  `xnonfwd_loop_exact_envelope_eq` of `XLoop_envelope_eq` and
  `XLoop_exact_envelope_eq` (`ExactFlatC7Loop.lean`), since the exact run
  carries a nonempty `run.exact` and the envelope branch is decided by
  `run.exact.contains e.tail` instead of `run.exact = []`.
* Loop envelope containment: `X_loopEnvelope_containedExt` and
  `X_loopExactEnvelope_containedExt`
  (`ExactLoopEnvelopeSeparationProof.lean:202,321`): the envelope sits in the
  extended footprint `loopFootprintExt` with no reservation hypothesis (the
  label centre lies in its row of the `n * band` stack, which
  `reserveExactRanks` grants). Reused outright.
* Plain `loop_envelope_eq` (`RunLocalSeparationsProof.lean:825`) and
  `loop_envelope_contained` (`RunLocalSeparationsProof.lean:843`) with
  `loopReservation_general` (`LoopFootprintGeneralOrder.lean:696`) are not
  used: the reservation `n * band <= frame.h` is false on fixed-size nodes
  (band 1536 against heights 100, 10, 0 in the probe), so the tracked
  `X_RunLocalLoopFootprint` (`ExactFlatC7Loop.lean:36`) is false and unused.

For self-loops the proof uses the extended footprint and two geometry
facts scoped to well-formed inputs with framed parents. The unscoped
predicates are retained for the legacy residual decompositions; unframed
intermediate runs can violate them and are rejected by `layoutFamilyX`. -/

/-- Unscoped extended-footprint miss, retained for the legacy residual
decomposition. The nonforward clearance assembler uses `XNonfwd_ExtMissW`
instead. -/
def XNonfwd_ExtMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Full proper-node clearance, scoped only to the well-formed, framed exact
execution already available to the C8b assembler. No scene-box, positivity,
rank, or ancestry hypothesis is imposed on the target index. -/
def XNonfwd_ExtMissW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e → e.tail = e.head → v < run.proper.nodes.length →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Unscoped extended group-hull clearance, retained for the legacy residual
decomposition. The nonforward clearance assembler uses
`XNonfwd_GroupHullExtW` instead. -/
def XNonfwd_GroupHullExt (exactIds : List String) : Prop :=
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
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      Disjoint (frameRect execution.params cg run pos)
        (loopFootprintExt cg run execution.measured t) ∨
        (frameRect execution.params cg run pos).StrictInside
          (loopFootprintExt cg run execution.measured t)

/-- W twin of `XNonfwd_GroupHullExt`: full clearance over the actual executed
run. -/
def XNonfwd_GroupHullExtW (exactIds : List String) : Prop :=
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
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      Disjoint (frameRect execution.params cg run pos)
        (loopFootprintExt cg run execution.measured t) ∨
        (frameRect execution.params cg run pos).StrictInside
          (loopFootprintExt cg run execution.measured t)

/-- Copy of the private `findIdxHitElem'` in `RouteNonforwardLabelClearProof`:
a `findIdx?` hit carries its element and the satisfied predicate. -/
private theorem xnonfwd_findIdxHitElem {α : Type} {l : List α} (p : α → Bool) (j : Nat) (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

/-- Copy of the private `strictInside_of_contained'` in
`RouteNonforwardLabelClearProof`: shrinking the inner rectangle preserves
strict-inside. -/
private theorem xnonfwd_inner_strict_of_sub {o m l : Rect} (h : o.StrictInside m) (hs : m.Contained l) : o.StrictInside l := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Copy of `XLoop_envelope_eq` (`ExactFlatC7Loop.lean`): invert the
plain-width loop envelope branch over an exact run. -/
private theorem xnonfwd_loop_envelope_eq {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect} (hloop : e.tail = e.head) (hnoex : run.exact.contains e.tail = false) (henv : labelEnvelope P cg run labels k e = some env) : env = (Loops.placement (frameRect P cg run e.tail) cg.slot (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot)) (loopEdges cg.edges e.tail).length (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl) (stackSize cg.slot (routeLabels labels e.decl))).label := by
  unfold labelEnvelope at henv
  obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, hnoex] at hrest
  exact (Option.some.inj hrest).symm

/-- Copy of `XLoop_exact_envelope_eq` (`ExactFlatC7Loop.lean`): invert the
exact-width loop envelope branch over an exact run. -/
private theorem xnonfwd_loop_exact_envelope_eq {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect} (hloop : e.tail = e.head) (hex : run.exact.contains e.tail = true) (henv : labelEnvelope P cg run labels k e = some env) : env = (Loops.exactPlacement (frameRect P cg run e.tail) cg.slot (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot)) (loopEdges cg.edges e.tail).length (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl) (stackSize cg.slot (routeLabels labels e.decl))).label := by
  unfold labelEnvelope at henv
  obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, hex] at hrest
  exact (Option.some.inj hrest).symm

-- (namespaces close after the main theorem below)
/-- Exact nonforward route clearance: placed labels of self-loops and
reversed lanes clear every in-bounds frame. Replay of
`routeNonforwardLabelClear_of_run`
(`RouteNonforwardLabelClearProof.lean:226`) over `componentRunX`. The
reversed branch is proved outright (lane bounds via `componentRunX_spec`);
the self-loop branch uses the local admission facts for the W predicates. -/
theorem XF_routeNonforwardClearX_holds (exactIds : List String)
    (hMiss : XNonfwd_ExtMissW exactIds)
    (hHull : XNonfwd_GroupHullExtW exactIds) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_ : WellFormed (inputModel inp o)) (_ : framedParents inp = true)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl hfw pos hpos
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
    placedLabels_pair_inv hnd hmem
  have hmlEq : ml = l₀ :=
    measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := xnonfwd_findIdxHitElem _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  subst hmlEq
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdeclsNodup : ((componentCandidate execution.graph comp candidate).edges.map (·.decl)).Nodup := by
    have hndE := exactGraph_decls_nodup execution.graph0_eq execution.graph_eq
    exact componentCandidate_decls_nodup _ _ _ hndE
  have heq : edge = edge' := by
    have hmap : ((componentCandidate execution.graph comp candidate).edges.map (·.decl))[edge]? =
        ((componentCandidate execution.graph comp candidate).edges.map (·.decl))[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map (·.decl)).length := by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdeclsNodup.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  have hslot := componentRunX_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hsizes : ∀ s ∈ (routeLabels execution.measured e'.decl).map fun l => (l.width, l.height),
      0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1, (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  have hrx : rect.x = env.x := (stackRects_entry hmemstk).1
  by_cases hloop : e.tail = e.head
  · have hloop' : e'.tail = e'.head := by rw [← hEE]; exact hloop
    have hcg : (componentCandidate execution.graph comp candidate) =
        componentCandidate execution.graph comp candidate := rfl
    have hcontExt : (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured e'.tail).Contained env := by
      by_cases htrue : run.exact.contains e'.tail = true
      · have hEq := xnonfwd_loop_exact_envelope_eq hloop' htrue henv
        exact X_loopExactEnvelope_containedExt hslot hlab he' hloop' hEq htrue
      · have hfalse : run.exact.contains e'.tail = false := by
          cases he : run.exact.contains e'.tail with
          | true => exact absurd he htrue
          | false => rfl
        have hEq := xnonfwd_loop_envelope_eq hloop' hfalse henv
        exact X_loopEnvelope_containedExt hslot hlab hfalse he' hloop' hEq
    obtain ⟨hw, hh⟩ := labelEnvelope_loop_size hloop' henv
    have hw' : Labels.stackWidth ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.w := by
      rw [hw, stackSize_width_eq]
      exact Int.le_refl _
    have hh' : Labels.stackHeight ((componentCandidate execution.graph comp candidate).slot) ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.h := by
      rw [hh, stackSize_height_eq]
      exact Int.le_refl _
    obtain ⟨_, _, hcont_rect⟩ :=
      Labels.stackRects_contained env ((componentCandidate execution.graph comp candidate).slot)
        hslot hsizes hw' hh' rect hmemstk
    have hcont : (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured e'.tail).Contained rect :=
      Rect.Contained.trans hcontExt hcont_rect
    have hne : (componentCandidate execution.graph comp candidate).nodes[pos]? ≠ none := by
      intro h
      rw [List.getElem?_eq_none_iff] at h
      omega
    obtain ⟨gn, hg⟩ := Option.ne_none_iff_exists'.mp hne
    by_cases hgrp : gn.border = -2
    · have hmemE : e' ∈ (componentCandidate execution.graph comp candidate).edges :=
        List.mem_of_getElem? he'
      have hwit : ∃ e_1 ∈ (componentCandidate execution.graph comp candidate).edges, e_1.tail = e'.tail ∧ e_1.head = e'.tail :=
        ⟨e', hmemE, rfl, hloop'.symm⟩
      rcases hHull inp o res execution hwf hfp comp candidate run orderOptions
        (componentCandidate execution.graph comp candidate) e'.tail pos hcomp hcg
        hrun hwit hpos gn hg hgrp with hD | hS
      · have hD' : ¬ (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured e'.tail).meetsInterior (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos) := fun hm => hD ((Rect.meetsInterior_comm _ _).mpr hm)
        have hclear : ¬ rect.meetsInterior (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos) :=
          _root_.Elegant.Layered.not_meetsInterior_of_contained hcont hD'
        exact Or.inl (fun hm => hclear ((Rect.meetsInterior_comm _ _).mp hm))
      · exact Or.inr (xnonfwd_inner_strict_of_sub hS hcont)
    · have hplen : pos < run.proper.nodes.length :=
        componentRunX_original_nodes_covered hrun pos hpos
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD pos default = gn := by
        rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
      have hfrP : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos = RouteImpl.boxRect run.proper run.xs run.ys pos :=
        plain_frame_eq_boxRect _ _ _ _ hplen (by rw [hget]; exact hgrp)
      have hmiss := hMiss inp o res execution hwf hfp comp candidate run orderOptions
        (componentCandidate execution.graph comp candidate) edge e' pos hcomp hcg
        hrun he' hloop' hplen
      have hclear : ¬ rect.meetsInterior (RouteImpl.boxRect run.proper run.xs run.ys pos) :=
        _root_.Elegant.Layered.not_meetsInterior_of_contained hcont hmiss
      rw [← hfrP] at hclear
      exact Or.inl (fun hm => hclear ((Rect.meetsInterior_comm _ _).mp hm))
  · have hne : e.tail ≠ e.head := hloop
    have hrev : e.reversed = true := by
      cases hfw with
      | inl h => exact absurd h hloop
      | inr h => exact h
    have hne' : e'.tail ≠ e'.head := by rw [← hEE]; exact hne
    have hrev' : e'.reversed = true := by rw [← hEE]; exact hrev
    have henvR := reversed_envelope_eq hne' hrev' henv
    obtain ⟨first, lane, hfirst, hlane, henv_eq⟩ := henvR
    have henvx : env.x = lane.lane + (componentCandidate execution.graph comp candidate).slot := by
      rw [henv_eq]
      rfl
    have hmem_lane : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hlane
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrLanes, _, _⟩ := componentRunX_spec hrun
    obtain ⟨base, _, h1slot, hlr⟩ := RouteImpl.routeWithLanes_spec hrLanes
    rw [hlr] at hmem_lane
    have hge := RouteImpl.plannedLane_right_strict (by omega : 0 ≤ execution.params.slot) hmem_lane
    have hne2 : (componentCandidate execution.graph comp candidate).nodes[pos]? ≠ none := by
      intro h
      rw [List.getElem?_eq_none_iff] at h
      omega
    obtain ⟨gn, hg⟩ := Option.ne_none_iff_exists'.mp hne2
    by_cases hgrp : gn.border = -2
    · have hspan := frameRect_group_span (P := execution.params) (run := run) hg hgrp
      have hright : (boundsOf (groupBorderRects (componentCandidate execution.graph comp candidate) run gn.decl) []).right ≤ RouteImpl.laneRight run.proper run.xs := by
        apply boundsOf_right_le_of_all (RouteImpl.laneRight_nonneg _ _)
        intro r hr
        obtain ⟨a, na, hna, _, _, hqr⟩ := fbs_groupBorderRects_spec hr
        have hqlen : a < run.proper.nodes.length :=
          (List.getElem?_eq_some_iff.mp hna).1
        have hget : run.proper.nodes.getD a default = na := by
          rw [List.getD_eq_getElem?_getD, hna, Option.getD_some]
        have hbound := RouteImpl.laneRight_bound run.proper run.xs hqlen
        rw [hget] at hbound
        have hrr : r.x + r.w = RouteImpl.xAt run.xs a - Int.fdiv (RouteImpl.nodeW run.proper a) 2 + RouteImpl.nodeW run.proper a := by
          rw [hqr]
          rfl
        have hle0 : (0 : Int) ≤ (na.node.loopExtent : Int) := Int.natCast_nonneg _
        omega
      have hle : (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x + (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).w ≤ rect.x := by
        rw [hspan]
        dsimp only
        omega
      have hD : ¬ rect.meetsInterior (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos) :=
        not_meetsInterior_of_left_le hle
      exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
    · have hplen : pos < run.proper.nodes.length :=
        componentRunX_original_nodes_covered hrun pos hpos
      obtain ⟨pn, hlook⟩ : ∃ p, run.proper.nodes[pos]? = some p :=
        ⟨_, List.getElem?_eq_getElem hplen⟩
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD pos default = gn := by
        rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
      have hfrP : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos = RouteImpl.boxRect run.proper run.xs run.ys pos :=
        plain_frame_eq_boxRect _ _ _ _ hplen (by rw [hget]; exact hgrp)
      by_cases hh0 : RouteImpl.nodeH run.proper pos = 0
      · have hhh : (RouteImpl.boxRect run.proper run.xs run.ys pos).h = 0 := hh0
        have hD : Disjoint rect (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos) := by
          rw [hfrP]
          exact not_meetsInterior_of_box_zero_h hhh
        exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
      · have hx : rect.x = lane.lane + (componentCandidate execution.graph comp candidate).slot := hrx.trans henvx
        have hbound := RouteImpl.laneRight_bound run.proper run.xs hplen
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys pos).x = RouteImpl.xAt run.xs pos - Int.fdiv (RouteImpl.nodeW run.proper pos) 2 :=
          boxRect_left _ _ _ _
        have hboxw : (RouteImpl.boxRect run.proper run.xs run.ys pos).w = RouteImpl.nodeW run.proper pos :=
          boxRect_w _ _ _ _
        have hloopnn : 0 ≤ (run.proper.nodes.getD pos default).node.loopExtent :=
          Nat.zero_le _
        have e2 : Int.fdiv (RouteImpl.nodeW run.proper pos) 2 = RouteImpl.nodeW run.proper pos / 2 := fdiv2_ediv _
        rw [e2] at hbound
        have hleBox : (RouteImpl.boxRect run.proper run.xs run.ys pos).x + (RouteImpl.boxRect run.proper run.xs run.ys pos).w ≤ rect.x := by
          omega
        have hle : (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x + (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).w ≤ rect.x := by
          rw [hfrP]; exact hleBox
        have hD : ¬ rect.meetsInterior (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos) :=
          not_meetsInterior_of_left_le hle
        exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))

end PipelineImpl
end Layered
end Elegant
