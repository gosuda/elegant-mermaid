import Elegant.Layered.RegionC5Endpoints
import Elegant.Layered.RegionReduction
import Elegant.Layered.ExactFlatC5Closed

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private def c5RegionSpec (idSets : List (String × List String)) (P : Params)
    (o : Options) (lines : List (List Measure.Line)) : Option RegionSpec :=
  if idSets.isEmpty then none
  else some ⟨idSets, lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)⟩

def R_AllComponentsFallbackR {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ comp ∈ components execution.graph,
    newComponentRegions (c5RegionSpec idSets execution.params o execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok none

private theorem c5ComponentFallback (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph) (acc : Acc)
    (comp : List Nat) (labels : List MeasuredLabel)
    (h : newComponentRegions spec P inp (componentGraph g comp) = .ok none) :
    layoutComponentR P exactIds spec inp o g acc comp labels =
      layoutComponentX P exactIds inp o g acc comp labels := by
  have htrial : componentTrialR P exactIds spec inp o g comp labels =
      componentTrialR P exactIds none inp o g comp labels := by
    funext i
    have hnone : newComponentRegions none P inp (componentGraph g comp) = .ok none := rfl
    unfold componentTrialR
    rw [h, hnone] <;> rfl
  rw [← layoutComponentR_none P exactIds inp o g acc comp labels]
  simp only [layoutComponentR, htrial]

private theorem c5FoldlM_congr {α β ε : Type} (f g : α → β → Except ε α)
    (xs : List β) (h : ∀ x ∈ xs, ∀ acc, f acc x = g acc x) (acc : α) :
    xs.foldlM f acc = xs.foldlM g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, h x List.mem_cons_self acc]
    cases g acc x with
    | error _ => rfl
    | ok next => exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) next

theorem layoutRIds_eq_layoutX_of_allComponentsFallbackR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hFallback : R_AllComponentsFallbackR execution) :
    layoutRIds exactIds idSets inp o = layoutX exactIds inp o := by
  let spec := c5RegionSpec idSets execution.params o execution.lines
  let start : Acc :=
    ⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [],
      Array.replicate inp.labels.length default, false, [], []⟩
  have hfold :
      (components execution.graph).foldlM
        (fun a comp => layoutComponentR execution.params exactIds spec inp o
          execution.graph a comp execution.measured) start =
      (components execution.graph).foldlM
        (fun a comp => layoutComponentX execution.params exactIds inp o
          execution.graph a comp execution.measured) start :=
    c5FoldlM_congr _ _ _ (fun comp hc a =>
      c5ComponentFallback _ _ _ _ _ _ a comp _ (hFallback comp hc)) start
  let finish (folded : Except LayoutError Acc) : Except LayoutError FamilyResult := do
    let acc ← folded
    let acc ← packAcc execution.params o acc
    let scene := sceneOf execution.params inp o execution.lines acc execution.measured
    if I32_MAX < scene.canvas.w ∨ I32_MAX < scene.canvas.h then throw .overflow
    else pure ⟨scene, acc.budget, acc.parts.foldl (fun area part => area + part.2.area) 0⟩
  simp only [layoutRIds, layoutX, execution.checked, execution.metric_eq,
    execution.lines_eq, execution.measured_eq, execution.graph0_eq,
    execution.graph_eq, bind, Except.bind]
  exact congrArg finish hfold

theorem r_allComponentsFallbackR_nil {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionR exactIds [] inp o res) :
    R_AllComponentsFallbackR execution := by
  intro comp _
  rfl

def R_ActiveBoundaryR (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ¬ R_AllComponentsFallbackR execution →
    ∀ out ∈ res.scene.routes, ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧ Validator.onBoundary finish toBox.rect

theorem flatC5B_layoutRIds_activeOnly (exactIds : List String) (idSets : List (String × List String))
    (hActive : R_ActiveBoundaryR exactIds idSets) : FlatC5B (layoutRIds exactIds idSets) := by
  intro inp o res hwf hfp hok
  obtain ⟨execution⟩ := layoutRIds_sceneExecution hok
  by_cases hFallback : R_AllComponentsFallbackR execution
  · have hx := (layoutRIds_eq_layoutX_of_allComponentsFallbackR execution hFallback).symm.trans hok
    exact flatC5B_layoutX_closed exactIds hwf hfp hx
  · obtain ⟨hboxes, hroutes⟩ := RB_layout_ids hok
    refine ⟨hboxes, hroutes, ?_⟩
    intro out hout
    obtain ⟨source, hsmem, hsid⟩ := r_tailLookupR_holds exactIds idSets execution hwf hfp out hout
    obtain ⟨target, htmem, htid⟩ := r_headLookupR_holds exactIds idSets execution hwf hfp out hout
    obtain ⟨start, finish, fromBox, toBox, h1, h2, h3, h4, h5, h6⟩ :=
      hActive execution hwf hfp hFallback out hout
    exact ⟨source, hsmem, target, htmem, hsid, htid, start, finish, fromBox, toBox,
      h1, h2, h3, h4, h5, h6⟩

end Elegant.Layered.PipelineImpl
