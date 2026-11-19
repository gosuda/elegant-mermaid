import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Run-level non-forward label clearance

`RouteNonforwardLabelClear` covers placed labels of self-loops and reversed
lanes against every in-bounds frame. This file discharges it for an executed
component run, plus the self-loop-against-group sub-case
(`LoopLabelGroupClear`) it dispatches through.

Proof outline, per edge form:

* reversed edge (`e.tail ≠ e.head`, `e.reversed = true`): the envelope sits in
  the planned lane (`reversed_envelope_eq`), strictly right of every node box
  (`plannedLane_right_strict` + `laneRight_bound`, scope-free replication of
  the `runLocalReversedSeparation` argument) and right of every group hull
  (each border-marker member sits left of `laneRight`, transported through
  `frameRect_group_span` and `boundsOf_right_le_of_all`).
* self-loop on a plain node: the envelope is contained in the loop footprint
  (`loop_envelope_contained` with the scope-free `loopReservation_general`
  reservation), and the placed rect is contained in the envelope
  (`stackRects_contained`). Against its own box the rect is x-separated to the
  right of the frame (footprint starts at the frame's right edge). Against any
  other plain box, out-of-scope positions use `RunLocalLoopFootprint` through
  `runLocalLoopSeparation`/`loop_branch_clear`, and in-scope positions use the
  scope-free `loopFootprintSeparation_general`.
* self-loop against a group frame (`LoopLabelGroupClear`): the rect is
  contained in the footprint, so the footprint-level residual below transports
  both disjuncts (`not_meetsInterior_of_contained` for disjointness,
  containment transitivity for strict-inside).

Residual: `LoopFootprintGroupHullClear` is the footprint-level form of
`LoopLabelGroupClear` (footprint vs group hull, no labels): it is strictly
narrower than the target (one placement-geometry fact about the
coordinate/frame stage), and it is the exact open `loopFootprint_group_hull`
bound named in `RouteRunClearCases` (the hull-right x-extent plus the
member-hull strictness padding).

Probe evidence (`wip/Probe/RouteNonforwardHullProbe.lean`, 4 inputs × 5
candidates: self-loop inside a group, nested groups, self-loop on a group
nested in another group, sibling groups with the loop in one of them; every
loop tail against every in-bounds frame plus every beyond-proper frame):
footprint-vs-hull `meets=false ∨ strictIn=true` holds everywhere, 0
violations. Member/ancestor hulls strictly contain the footprint; the loop's
own group frame is x-separated (footprint starts exactly at the hull's right
edge); foreign hulls are x-separated (footprint right edge stays left of the
right-hand hull by the coordinate gap); beyond-proper frames never meet the
footprint. The sibling-group probe answers the recipe's hull-right question:
against the loop's own group frame the label/footprint is DISJOINT (x-separated),
while member/ancestor hulls give strict-inside. The same probe census shows
`RunLocalLoopFootprint`'s Top instances (group-top-owned footprint vs plain
boxes) disjoint throughout. -/

/-- Footprint-level group-hull clearance for self-loop tails: the loop
footprint of a self-loop owner is disjoint from, or strictly contains the
group's point of view turned around (the group frame is disjoint from the
footprint or strictly inside it), for every in-bounds group frame. This is the
open `loopFootprint_group_hull` bound: the hull-right x-extent (a right-hand
foreign hull stays right of the footprint's full width) and the member-hull
strictness padding. Probe: `RouteNonforwardHullProbe`, 0 violations. -/
def LoopFootprintGroupHullClear (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t pos : Nat), (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    pos < cg.nodes.length →
    ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
      Disjoint (frameRect P cg run pos) (loopFootprint cg run labels t) ∨
        (frameRect P cg run pos).StrictInside (loopFootprint cg run labels t)

/-- Copy of the private `findIdxHitElem` helper in `RouteRunClearCases`
(which keeps it private): a `findIdx?` hit carries its element and the
satisfied predicate. -/
private theorem findIdxHitElem' {α : Type} {l : List α} (p : α → Bool) (j : Nat)
    (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
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

/-- Copy of the private `inner_strict_of_sub` helper in `RouteRunClearCases`:
shrinking the inner rectangle preserves strict-inside. -/
private theorem strictInside_of_contained' {o m l : Rect}
    (h : o.StrictInside m) (hs : m.Contained l) : o.StrictInside l := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Executed `LoopLabelGroupClear`: a placed self-loop label clears every
in-bounds group frame. The placed rect is contained in the loop footprint
(`loop_envelope_contained` with the scope-free reservation, then
`stackRects_contained`), so the footprint-level residual transports both
disjuncts. -/
theorem loopLabelGroupClear_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hres : LoopFootprintGroupHullClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    LoopLabelGroupClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl hloop pos hpos gn hg hgrp
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
    placedLabels_pair_inv hnd hmem
  have hml : ml = l₀ :=
    measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := findIdxHitElem' _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdecls : ((componentCandidate execution.graph comp candidate).edges.map Edge.decl).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  have heq : edge = edge' := by
    have hmap : ((componentCandidate execution.graph comp candidate).edges.map Edge.decl)[edge]? =
        ((componentCandidate execution.graph comp candidate).edges.map Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map Edge.decl).length := by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdecls.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  have hloop' : e'.tail = e'.head := by rw [← hEE]; exact hloop
  have hslot := componentRun_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  have hexact := run_exact_nil hrun
  have henv_eq := loop_envelope_eq hloop' hexact henv
  have hresv := loopReservation_general execution comp candidate orderOptions run e'.tail
    hcomp hrun
  unfold LoopReservation at hresv
  obtain ⟨_, hrsv⟩ := hresv
  have hcont_env := loop_envelope_contained hslot hlab hexact he' hloop' henv_eq hrsv
  have hsizes : ∀ s ∈ (routeLabels execution.measured e'.decl).map fun l => (l.width, l.height),
      0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1,
      (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  obtain ⟨hw, hh⟩ := labelEnvelope_loop_size hloop' henv
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hw' : Labels.stackWidth
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.w := by
    rw [hw, stackSize_width_eq]
    exact Int.le_refl _
  have hh' : Labels.stackHeight ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.h := by
    rw [hh, stackSize_height_eq]
    exact Int.le_refl _
  obtain ⟨_, _, hcont_rect⟩ :=
    Labels.stackRects_contained env ((componentCandidate execution.graph comp candidate).slot)
      hslot hsizes hw' hh' rect hmemstk
  have hcont : (loopFootprint (componentCandidate execution.graph comp candidate) run
      execution.measured e'.tail).Contained rect :=
    Rect.Contained.trans hcont_env hcont_rect
  have hmemE : e' ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? he'
  have hwit : ∃ e_1 ∈ (componentCandidate execution.graph comp candidate).edges,
      e_1.tail = e'.tail ∧ e_1.head = e'.tail :=
    ⟨e', hmemE, rfl, hloop'.symm⟩
  rcases hres e'.tail pos hwit hpos gn hg hgrp with hD | hS
  · have hD' : ¬ (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).meetsInterior
        (loopFootprint (componentCandidate execution.graph comp candidate) run
          execution.measured e'.tail) := hD
    have hnm : ¬ (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured e'.tail).meetsInterior
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos) :=
      fun hm => hD' ((Rect.meetsInterior_comm _ _).mp hm)
    have hclear : ¬ rect.meetsInterior (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos) :=
      _root_.Elegant.Layered.not_meetsInterior_of_contained hcont hnm
    exact Or.inl (fun hm => hclear ((Rect.meetsInterior_comm _ _).mp hm))
  · exact Or.inr (strictInside_of_contained' hS hcont)

/-- Executed `RouteNonforwardLabelClear`: placed labels of self-loops and
reversed lanes clear every in-bounds frame. Reversed edges use the planned-lane
bound (scope-free: the lane sits right of every box and every group hull).
Self-loop labels are contained in the loop footprint; the loop's own plain box
is x-separated to the left, out-of-scope plain boxes use `RunLocalLoopFootprint`,
in-scope plain boxes use the scope-free footprint separation, and group frames
use the executed `LoopLabelGroupClear`. -/
theorem routeNonforwardLabelClear_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hfoot : RunLocalLoopFootprint inp o res)
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res)
    (hres : LoopFootprintGroupHullClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    RouteNonforwardLabelClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl hfw pos hpos
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
    placedLabels_pair_inv hnd hmem
  have hml : ml = l₀ :=
    measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := findIdxHitElem' _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdecls : ((componentCandidate execution.graph comp candidate).edges.map Edge.decl).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  have heq : edge = edge' := by
    have hmap : ((componentCandidate execution.graph comp candidate).edges.map Edge.decl)[edge]? =
        ((componentCandidate execution.graph comp candidate).edges.map Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map Edge.decl).length := by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdecls.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  have hslot := componentRun_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  have hexact := run_exact_nil hrun
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
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1,
      (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  have hrx : rect.x = env.x := (stackRects_entry hmemstk).1
  by_cases hloop : e.tail = e.head
  · -- self-loop: the envelope is contained in the loop footprint.
    have hloop' : e'.tail = e'.head := by rw [← hEE]; exact hloop
    have henv_eq := loop_envelope_eq hloop' hexact henv
    have hresv := loopReservation_general execution comp candidate orderOptions run e'.tail
      hcomp hrun
    unfold LoopReservation at hresv
    obtain ⟨_, hrsv⟩ := hresv
    have hcont_env := loop_envelope_contained hslot hlab hexact he' hloop' henv_eq hrsv
    obtain ⟨hw, hh⟩ := labelEnvelope_loop_size hloop' henv
    have hw' : Labels.stackWidth
        ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.w := by
      rw [hw, stackSize_width_eq]
      exact Int.le_refl _
    have hh' : Labels.stackHeight ((componentCandidate execution.graph comp candidate).slot)
        ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.h := by
      rw [hh, stackSize_height_eq]
      exact Int.le_refl _
    obtain ⟨_, _, hcont_rect⟩ :=
      Labels.stackRects_contained env ((componentCandidate execution.graph comp candidate).slot)
        hslot hsizes hw' hh' rect hmemstk
    have hcont : (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured e'.tail).Contained rect :=
      Rect.Contained.trans hcont_env hcont_rect
    have hne : (componentCandidate execution.graph comp candidate).nodes[pos]? ≠ none := by
      intro h
      rw [List.getElem?_eq_none_iff] at h
      omega
    obtain ⟨gn, hg⟩ := Option.ne_none_iff_exists'.mp hne
    by_cases hgrp : gn.border = -2
    · -- group frame: the executed group sub-case.
      exact loopLabelGroupClear_of_run execution hcomp hrun hres k rect ml edge e
        hmem hmem0 hidx hedge hdecl hloop pos hpos gn hg hgrp
    · -- plain frame: the frame is the proper box.
      have hplen : pos < run.proper.nodes.length :=
        componentRun_original_nodes_covered hrun pos hpos
      obtain ⟨pn, hlook⟩ : ∃ p, run.proper.nodes[pos]? = some p :=
        ⟨_, List.getElem?_eq_getElem hplen⟩
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD pos
          default = gn := by
        rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
      have hfrP : frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos =
          RouteImpl.boxRect run.proper run.xs run.ys pos :=
        plain_frame_eq_boxRect _ _ _ _ hplen (by rw [hget]; exact hgrp)
      by_cases hb0 : gn.border = 0
      · by_cases hh0 : RouteImpl.nodeH run.proper pos = 0
        · have hhh : (RouteImpl.boxRect run.proper run.xs run.ys pos).h = 0 := hh0
          have hD : Disjoint rect (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos) := by
            rw [hfrP]
            exact not_meetsInterior_of_box_zero_h hhh
          exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
        · by_cases heqP : pos = e'.tail
          · -- own box: the footprint starts at the frame's right edge.
            have hfp : loopFootprint (componentCandidate execution.graph comp candidate)
                run execution.measured e'.tail =
                ⟨(frameRect default (componentCandidate execution.graph comp candidate)
                    run e'.tail).x +
                  (frameRect default (componentCandidate execution.graph comp candidate)
                    run e'.tail).w,
                 (frameRect default (componentCandidate execution.graph comp candidate)
                    run e'.tail).y,
                 Loops.extent ((componentCandidate execution.graph comp candidate).slot)
                   (loopSizes (componentCandidate execution.graph comp candidate).edges
                     execution.measured e'.tail
                     ((componentCandidate execution.graph comp candidate).slot)),
                 (frameRect default (componentCandidate execution.graph comp candidate)
                    run e'.tail).h⟩ := by
              have h1 : run.exact.contains e'.tail = false := by simp [hexact]
              unfold loopFootprint
              simp only [h1, Bool.false_eq_true, ↓reduceIte]
            have hFeq : frameRect execution.params
                (componentCandidate execution.graph comp candidate) run e'.tail =
                frameRect default (componentCandidate execution.graph comp candidate)
                  run e'.tail := rfl
            have hfx : (loopFootprint (componentCandidate execution.graph comp candidate)
                run execution.measured e'.tail).x =
                (frameRect default (componentCandidate execution.graph comp candidate)
                  run e'.tail).x +
                  (frameRect default (componentCandidate execution.graph comp candidate)
                  run e'.tail).w := by
              rw [hfp]
            have hle : (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run pos).x +
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).w ≤
                rect.x := by
              rw [heqP, hFeq]
              have hc1 := hcont_env.1
              omega
            have hD : ¬ rect.meetsInterior (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run pos) :=
              not_meetsInterior_of_left_le hle
            exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
          · -- other plain box: scope split on the footprint premise.
            by_cases hsc : RouteImpl.nodeDecl run.proper pos ∉
                ((((componentCandidate execution.graph comp candidate).nodes[e'.tail]?).map
                  (fun n => n.clusterPath))).getD []
            · obtain ⟨actual, _, hproper, hreal, _, _, _, _, _⟩ :=
                componentRun_original_plain_record hrun hg hb0
              have hI : RouteImpl.IsReal run.proper pos := fun nd' hnd' => by
                rw [hproper] at hnd'
                have heq2 : nd' = actual := Option.some.inj hnd'.symm
                rw [heq2]
                exact hreal
              have hsc2 : RouteImpl.nodeDecl run.proper pos ∉
                  ((((componentCandidate execution.graph comp candidate).nodes[e'.head]?).map
                    (fun n => n.clusterPath))).getD [] := by
                rw [← hloop']; exact hsc
              have hsep := runLocalLoopSeparation _ _ _ hfoot execution comp candidate
                run orderOptions (componentCandidate execution.graph comp candidate)
                edge e' env pos hcomp rfl hrun he' hloop' henv hplen hI hsc hsc2
              have hclear := loop_branch_clear he' hloop' henv hslot hlab hmemstk hsep
              rw [← hfrP] at hclear
              exact Or.inl (fun hm => hclear ((Rect.meetsInterior_comm _ _).mp hm))
            · have hbord : ((componentCandidate execution.graph comp candidate).nodes.getD
                  pos default).border = 0 := by
                rw [hget]; exact hb0
              have hsep := loopFootprintSeparation_general execution comp candidate
                orderOptions run e'.tail pos hcomp hbord hrun htop hbeyond
              have hnm : ¬ (loopFootprint (componentCandidate execution.graph comp candidate)
                  run execution.measured e'.tail).meetsInterior
                  (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos) := hsep
              have hclear : ¬ rect.meetsInterior (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos) :=
                _root_.Elegant.Layered.not_meetsInterior_of_contained hcont hnm
              exact Or.inl (fun hm => hclear ((Rect.meetsInterior_comm _ _).mp hm))
      · -- non-plain candidate node: its proper box has height zero.
        have hne0 : ((componentCandidate execution.graph comp candidate).nodes.getD pos
            default).border ≠ 0 := by
          rw [hget]; exact hb0
        have hzero := loopBoxZero_of_nonplain execution comp candidate orderOptions run pos
          hcomp hrun hpos hne0
        have hD : Disjoint rect (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run pos) := by
          rw [hfrP]
          exact not_meetsInterior_of_box_zero_h hzero
        exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
  · -- reversed edge: the envelope sits in the planned lane.
    have hne : e.tail ≠ e.head := hloop
    have hrev : e.reversed = true := by
      cases hfw with
      | inl h => exact absurd h hloop
      | inr h => exact h
    have hne' : e'.tail ≠ e'.head := by rw [← hEE]; exact hne
    have hrev' : e'.reversed = true := by rw [← hEE]; exact hrev
    have henvR := reversed_envelope_eq hne' hrev' henv
    obtain ⟨first, lane, hfirst, hlane, henv_eq⟩ := henvR
    have henvx : env.x = lane.lane +
        (componentCandidate execution.graph comp candidate).slot := by
      rw [henv_eq]
      rfl
    have hmem_lane : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hlane
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrLanes, _, _, _, _⟩ := componentRun_spec hrun
    obtain ⟨base, _, h1slot, hlr⟩ := RouteImpl.routeWithLanes_spec hrLanes
    rw [hlr] at hmem_lane
    have hge := RouteImpl.plannedLane_right_strict (by omega : 0 ≤ execution.params.slot)
      hmem_lane
    have hne2 : (componentCandidate execution.graph comp candidate).nodes[pos]? ≠ none := by
      intro h
      rw [List.getElem?_eq_none_iff] at h
      omega
    obtain ⟨gn, hg⟩ := Option.ne_none_iff_exists'.mp hne2
    by_cases hgrp : gn.border = -2
    · -- group hull: every border-marker member ends left of the lane.
      have hspan := frameRect_group_span (P := execution.params) (run := run) hg hgrp
      have hright : (boundsOf (groupBorderRects
          (componentCandidate execution.graph comp candidate) run gn.decl) []).right ≤
          RouteImpl.laneRight run.proper run.xs := by
        apply boundsOf_right_le_of_all (RouteImpl.laneRight_nonneg _ _)
        intro r hr
        obtain ⟨a, na, hna, _, _, hqr⟩ := fbs_groupBorderRects_spec hr
        have hqlen : a < run.proper.nodes.length :=
          (List.getElem?_eq_some_iff.mp hna).1
        have hget : run.proper.nodes.getD a default = na := by
          rw [List.getD_eq_getElem?_getD, hna, Option.getD_some]
        have hbound := RouteImpl.laneRight_bound run.proper run.xs hqlen
        rw [hget] at hbound
        have hrr : r.x + r.w = RouteImpl.xAt run.xs a -
            Int.fdiv (RouteImpl.nodeW run.proper a) 2 +
            RouteImpl.nodeW run.proper a := by
          rw [hqr]
          rfl
        have hle0 : (0 : Int) ≤ (na.node.loopExtent : Int) := Int.natCast_nonneg _
        omega
      have hle : (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos).x +
          (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run pos).w ≤
          rect.x := by
        rw [hspan]
        dsimp only
        omega
      have hD : ¬ rect.meetsInterior (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos) :=
        not_meetsInterior_of_left_le hle
      exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
    · -- plain box: the lane sits right of every box.
      have hplen : pos < run.proper.nodes.length :=
        componentRun_original_nodes_covered hrun pos hpos
      obtain ⟨pn, hlook⟩ : ∃ p, run.proper.nodes[pos]? = some p :=
        ⟨_, List.getElem?_eq_getElem hplen⟩
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD pos
          default = gn := by
        rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
      have hfrP : frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos =
          RouteImpl.boxRect run.proper run.xs run.ys pos :=
        plain_frame_eq_boxRect _ _ _ _ hplen (by rw [hget]; exact hgrp)
      by_cases hh0 : RouteImpl.nodeH run.proper pos = 0
      · have hhh : (RouteImpl.boxRect run.proper run.xs run.ys pos).h = 0 := hh0
        have hD : Disjoint rect (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run pos) := by
          rw [hfrP]
          exact not_meetsInterior_of_box_zero_h hhh
        exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
      · have hx : rect.x = lane.lane +
            (componentCandidate execution.graph comp candidate).slot := hrx.trans henvx
        have hbound := RouteImpl.laneRight_bound run.proper run.xs hplen
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys pos).x =
            RouteImpl.xAt run.xs pos - Int.fdiv (RouteImpl.nodeW run.proper pos) 2 :=
          boxRect_left _ _ _ _
        have hboxw : (RouteImpl.boxRect run.proper run.xs run.ys pos).w =
            RouteImpl.nodeW run.proper pos :=
          boxRect_w _ _ _ _
        have hloopnn : 0 ≤ (run.proper.nodes.getD pos default).node.loopExtent :=
          Nat.zero_le _
        have e2 : Int.fdiv (RouteImpl.nodeW run.proper pos) 2 =
            RouteImpl.nodeW run.proper pos / 2 := fdiv2_ediv _
        rw [e2] at hbound
        have hleBox : (RouteImpl.boxRect run.proper run.xs run.ys pos).x +
            (RouteImpl.boxRect run.proper run.xs run.ys pos).w ≤ rect.x := by
          omega
        have hle : (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run pos).x +
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).w ≤
            rect.x := by
          rw [hfrP]; exact hleBox
        have hD : ¬ rect.meetsInterior (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run pos) :=
          not_meetsInterior_of_left_le hle
        exact Or.inl (fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm))
end Elegant.Layered.PipelineImpl
