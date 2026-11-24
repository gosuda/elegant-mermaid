import Elegant.Layered.RegionC5ContributorRank

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def SelectedC5SemanticGroupTerminal (cg : Graph) (v t : Nat) : Prop :=
  ∃ n top, cg.nodes[v]? = some n ∧ cg.nodes[t]? = some top ∧ top.border = -2 ∧
    ((v = t ∧ n.border = -2) ∨ n.border = 2) ∧ n.decl = top.decl

private theorem activeC5MarkerRankExtreme
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph comp index) execution.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph comp index) = .ok (some rm))
    {v t : Nat} (hm : SelectedC5SemanticGroupTerminal cg v t) : SelectedC5GroupMarker cg run v t := by
  obtain ⟨n, top, hn, ht, htb, hvb, hd⟩ := hm
  obtain ⟨_, _, _, _, _, _, huniq, hwindow⟩ :=
    activeCandidateOriginalFrameRankWindow execution hwf hfp hcomp hrun hactive ht htb
  refine ⟨n, top, hn, ht, htb, hvb, hd, ?_⟩
  intro q hq hown
  rw [hd] at hown
  obtain ⟨_, _, _, _, ha, hc, hna, hnc, hlo, hhi⟩ :=
    activeFrameContributorRankSources execution hcomp hrun hactive
      (List.mem_zipIdx_iff_getElem?.mp hq) hown
  rcases hvb with ⟨hvt, hb⟩ | hb
  · rw [ite_eq_left hb, hvt]
    exact Int.le_trans (hwindow ha hna).1 hlo
  · rw [ite_eq_right (show n.border ≠ -2 by omega), huniq hn hb hd]
    exact Int.le_trans hhi (hwindow hc hnc).2

def SelectedC5SemanticRouteGroupAttachment (P : Params) (cg : Graph) (run : Run)
    (i first last : Nat) : Prop :=
  ∃ rt, run.routes[i]? = some rt ∧
    let tail := (RouteImpl.edgeAt run.proper first).tail
    let head := (RouteImpl.edgeAt run.proper last).head
    let reversed := (cg.edges.map (·.reversed)).getD i false
    (∀ t, SelectedC5SemanticGroupTerminal cg tail t →
      ∃ p, (if reversed then rt.points.getLast? else rt.points.head?) = some p ∧
        Validator.onBoundary p (frameRect P cg run t)) ∧
    (∀ t, SelectedC5SemanticGroupTerminal cg head t →
      ∃ p, (if reversed then rt.points.head? else rt.points.getLast?) = some p ∧
        Validator.onBoundary p (frameRect P cg run t))

def selectedC5TerminalSpec (idSets : List (String × List String)) (P : Params)
    (o : Options) (lines : List (List Measure.Line)) : Option RegionSpec :=
  if idSets.isEmpty then none
  else some ⟨idSets, lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)⟩

/-- No rank premise on either semantic group terminal. The run, chain, route entry and
orientation all belong to the portfolio-selected active part of the successful execution. -/
theorem regionC5ChosenActiveRouteGroupTerminals
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {rm : ComponentRegions}
    (hregion : newComponentRegions (selectedC5TerminalSpec idSets execution.params o execution.lines)
      execution.params inp (componentGraph execution.graph part.1) = .ok (some rm)) :
    ∃ s index chosen cg run loops area,
      selectedC5TerminalSpec idSets execution.params o execution.lines = some s ∧ index < 5 ∧
      Portfolio.portfolio o.thoroughness (componentTrialR execution.params exactIds (some s)
        inp o execution.graph part.1 execution.measured) = .ok chosen ∧
      chosen.value = (cg, run) ∧
      componentRunR execution.params (exactDecls exactIds inp) (some s) inp
        (componentCandidateR (some s) execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok (cg, run) ∧
      newComponentRegions (some s) execution.params inp
        (componentCandidateR (some s) execution.graph part.1 index) = .ok (some rm) ∧
      componentLoops execution.params cg run execution.measured = .ok loops ∧
      part.2 = { placeComponentExact execution.params cg run 0 execution.measured loops
        with area := area } ∧
      ∀ {i first last : Nat}, i < cg.edges.length →
        (RouteImpl.edgesOf run.proper i).head? = some first →
        (RouteImpl.edgesOf run.proper i).getLast? = some last →
        SelectedC5SemanticRouteGroupAttachment execution.params cg run i first last := by
  obtain ⟨hkeys, _⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hkeys]
    exact List.mem_map_of_mem hpart
  obtain ⟨s, index, chosen, cg, run, loops, area, hs, hindex, hport, hvalue,
    hrun, hactive, hloops, hplacement, hattach⟩ :=
    regionC5ChosenActiveRouteGroups_of_rank execution hpart hregion
  refine ⟨s, index, chosen, cg, run, loops, area, hs, hindex, hport, hvalue, hrun,
    hactive, hloops, hplacement, ?_⟩
  intro i first last hi hf hl
  obtain ⟨rt, hrt, htail, hhead⟩ := hattach hi hf hl
  refine ⟨rt, hrt, ?_, ?_⟩
  · intro t ht
    exact htail t (activeC5MarkerRankExtreme execution hwf hfp hcomp hrun hactive ht)
  · intro t ht
    exact hhead t (activeC5MarkerRankExtreme execution hwf hfp hcomp hrun hactive ht)

end Elegant.Layered.PipelineImpl
