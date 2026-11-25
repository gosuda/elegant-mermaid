import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Run-local label clearance for the layered label-runs seam

`Elegant.Layered.RunLocalLabelClearance` (the run-local half of
`LabelRunsClearExclusiveBoxes`) is proved here from the executed
`componentRun` facts plus three per-branch separation residuals, one per
`labelEnvelope` branch.  The scope is stated through the label's own edge
(`edge`/`decl`/`e`): the run side matches the dump-side `labelOwnerAnc`
scope by asking that the node's declaration lie in neither endpoint cluster
path.  Endpoints are included — the free proper-edge indices that used to
exclude exactly the endpoint boxes are gone (see
`proofs/wip/Layered/ExclusiveBoxInLabelRunRefuted.lean`).

The main theorem (`runLocalLabelClearance_holds`) does the execution
plumbing: a placed label unfolds through `placedLabels` into its executed
find/lookup/envelope/stack chain, and the unplaced fallback is the empty
rect, which meets nothing.  Each branch then applies
`Elegant.Layered.runLocalLabelClearance` with the matching residual:

* `RunLocalLoopSeparation` — the self-loop envelope misses the foreign box;
* `RunLocalForwardSeparation` — a forward stack rect is axis-separated from
  the foreign box (same-layer `coordSep` or rank-band separation, covering
  the edge's own endpoints by rank);
* `RunLocalReversedSeparation` — the foreign box ends left of a reversed
  stack rect (the planned-lane bound).

Every variable a residual constrains is pinned by an execution equation
(`comp ∈ components`, the candidate equation, `componentRun = .ok`,
the edge lookup, the envelope equation, stack membership), and each residual
is strictly weaker than the goal: it covers one placement branch only. -/

/-- Loop-branch residual: the executed self-loop label envelope misses the
frame rect of every real node outside the edge's endpoint cluster paths. -/
def RunLocalLoopSeparation (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRun execution.params cg execution.measured orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    labelEnvelope execution.params cg run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    Elegant.Layered.LoopFootprintSeparation execution.params cg run
      execution.measured k e env v

/-- Forward-branch residual: every stack rect of a forward label envelope is
axis-separated from the frame rect of every real node outside the edge's
endpoint cluster paths.  The edge's own endpoints are covered by the same
rank-band separation (a forward label sits at a middle rank, its endpoints
in strictly earlier/later bands). -/
def RunLocalForwardSeparation (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRun execution.params cg execution.measured orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail ≠ e.head →
    e.reversed = false →
    labelEnvelope execution.params cg run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    Elegant.Layered.RectAxisSeparated r (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Reversed-branch residual: the frame rect of every real node outside the
edge's endpoint cluster paths ends left of every stack rect of a reversed
label envelope (the planned-lane bound). -/
def RunLocalReversedSeparation (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRun execution.params cg execution.measured orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail ≠ e.head →
    e.reversed = true →
    labelEnvelope execution.params cg run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ r.x

/-- The empty rect meets nothing: the unplaced-label fallback case. -/
theorem emptyRect_meets_none {b : Rect} : ¬ (⟨0, 0, 0, 0⟩ : Rect).meetsInterior b := by
  rw [Rect.meetsInterior_comm]
  exact Elegant.Layered.not_meetsInterior_of_box_zero_h rfl

/-- Run-local label clearance holds for every executed flat layout modulo
the three per-branch separation residuals above. -/
theorem runLocalLabelClearance_holds {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : Elegant.WellFormed (Elegant.Layered.inputModel inp o))
    (_hfp : Elegant.Layered.framedParents inp = true)
    (hloop : RunLocalLoopSeparation inp o res)
    (hfwd : RunLocalForwardSeparation inp o res)
    (hrev : RunLocalReversedSeparation inp o res) :
    Elegant.Layered.RunLocalLabelClearance inp o res := by
  intro execution comp candidate run orderOptions cg edge decl v e l
    hcomp hcg hrun he hedge hl hlen hreal hscope₀ hscope₁
  have hlab := execution.measured_nonneg
  have hslot := componentRun_slot_nonneg hrun
  have hnd : (execution.measured.map (·.index)).Nodup :=
    measureLabels_index_nodup execution.measured_eq
  by_cases hex : ∃ rect, (l.index, rect) ∈
      placedLabels execution.params cg run execution.measured
  · obtain ⟨rect, hmem⟩ := hex
    have hroute : Elegant.Layered.routeLabelRect execution.params cg run
        execution.measured l = rect :=
      routeLabelRect_of_mem hnd hmem
    rw [hroute]
    obtain ⟨ml, edge', e', env, rect', hmlmem, hmlidx, hfind, he', henv,
        hfindstk, hreq⟩ := placedLabels_pair_inv hnd hmem
    subst hreq
    have hml : ml = l :=
      measured_eq_of_index_eq execution.measured hnd ml l hmlmem
        (Elegant.Layered.mem_measured_of_mem_routeLabels hl) hmlidx
    subst hml
    have hmemstk := List.mem_of_find?_eq_some hfindstk
    have hr : rect ∈ Labels.stackRects env.x env.y cg.slot
        ((routeLabels execution.measured e'.decl).map fun q => (q.width, q.height)) :=
      (List.of_mem_zip hmemstk).2
    -- The witness edge carries the same declaration as the outer edge.
    have hedecl : e.decl = decl := by
      rw [he] at hedge
      simpa using hedge
    have hedge' : e'.decl = decl := by
      obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hgg : cg.edges[edge'] = e' := (List.getElem?_eq_some_iff.mp he').2
      have hpred : e'.decl = ml.edge :=
        beq_iff_eq.mp (by have hmatch' := hmatch; rw [hgg] at hmatch'; simpa using hmatch')
      have hll : ml.edge = decl := by
        have hp := (List.mem_filter.mp hl).2
        simpa using hp
      exact hpred.trans hll
    have hnd_decl : (cg.edges.map (·.decl)).Nodup := by
      rw [hcg]
      exact componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
    have hEE : e = e' :=
      nodup_map_eq_of_mem hnd_decl (List.mem_of_getElem? he)
        (List.mem_of_getElem? he') (hedecl.trans hedge'.symm)
    rw [hEE] at hscope₀ hscope₁
    have hsep_loop : e'.tail = e'.head →
        Elegant.Layered.LoopFootprintSeparation execution.params cg run
          execution.measured edge' e' env v :=
      fun heq => hloop execution comp candidate run orderOptions cg edge' e' env v
        hcomp hcg hrun he' heq henv hlen hreal hscope₀ hscope₁
    have hsep_forward : e'.tail ≠ e'.head → e'.reversed = false →
        Elegant.Layered.RectAxisSeparated rect
          (RouteImpl.boxRect run.proper run.xs run.ys v) :=
      fun hne hrev' => hfwd execution comp candidate run orderOptions cg edge' e' env v rect
        hcomp hcg hrun he' hne hrev' henv hlen hreal hscope₀ hscope₁ hr
    have hsep_reversed : e'.tail ≠ e'.head → e'.reversed = true →
        (RouteImpl.boxRect run.proper run.xs run.ys v).x +
          (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ rect.x :=
      fun hne hrev' => hrev execution comp candidate run orderOptions cg edge' e' env v rect
        hcomp hcg hrun he' hne hrev' henv hlen hreal hscope₀ hscope₁ hr
    exact Elegant.Layered.runLocalLabelClearance he' henv hslot hlab hr
      hsep_loop hsep_forward hsep_reversed
  · have hfilter : (placedLabels execution.params cg run execution.measured).filter
        (fun q => q.1 == l.index) = [] := by
      rw [List.filter_eq_nil_iff]
      intro qq hqq hcond
      simp only [beq_iff_eq] at hcond
      exact hex ⟨qq.2, by rw [← hcond]; exact hqq⟩
    have hroute0 : Elegant.Layered.routeLabelRect execution.params cg run
        execution.measured l = ⟨0, 0, 0, 0⟩ := by
      unfold Elegant.Layered.routeLabelRect
      rw [hfilter]
      rfl
    rw [hroute0]
    exact emptyRect_meets_none

end Elegant.Layered.PipelineImpl
