import Elegant.Layered.RegionFlatC8b
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionPlacement
import Elegant.Layered.RegionReduction
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.LabelsC8b

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! Region stored-title caption fit: twin of `X_ExactTitleCaptionFit`.
Truth probes: two-region witness plus nested, titled, empty-group, and
self-loop variants. Each probe checks every executed part title covers its
measured caption (`r8bCaptionFitPartB` mirror). -/

private def rtcfProbeInp : Input :=
  { kind := "state"
    boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
      { id := "A", role := .group, parent := "G1", exclusive := false },
      { id := "B", role := .group, parent := "G1", exclusive := false },
      { id := "G2", role := .group, parent := "", exclusive := false },
      { id := "C", role := .group, parent := "G2", exclusive := false },
      { id := "D", role := .group, parent := "G2", exclusive := false },
      { id := "a1", parent := "A", exclusive := false },
      { id := "b1", parent := "B", exclusive := false },
      { id := "c1", parent := "C", exclusive := false },
      { id := "d1", parent := "D", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "c1" },
      { id := "e2", fromId := "b1", toId := "d1" },
      { id := "e3", fromId := "c1", toId := "b1" }]
    texts := ["G1", "A", "B", "G2", "C", "D", "a1", "b1", "c1", "d1"]
    edges := [.plain, .plain, .plain]
    labels := [] }

private def rtcfCaptionFitPartB (P : Params) (o : Options)
    (lines : List (List Measure.Line)) (comp : List Nat) (part : Part) : Bool :=
  part.titles.all fun title =>
    let size := titleCaptionSize P o (lines.getD (comp.getD title.1 0) [])
    decide (0 <= size.w) && decide (0 <= size.h) &&
      decide (size.w <= title.2.w) && decide (size.h <= title.2.h)

private def rtcfProbeC8bB (inp : Input) (sets : List ModelRegionSet) :
    Except LayoutError (List Bool) := do
  let P ← checkedParams .vector inp.kind
  let m ← metricOf .vector
  let target := Measure.wrapTarget m.profile P.wrapWidth 0
  let lines ← boxLines m target inp
  let measured ← measureLabels P m target inp .TB
  let g0 ← measuredGraph P inp {} lines
  let g ← exactGraph P [] inp {} measured g0
  let idSets ← graphRegions inp sets
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    (width, height)
  let spec := RegionSpec.mk idSets titles
  (components g).mapM fun comp => do
    let (cg, run) ← RegionImpl.componentRunR P [] (some spec) inp (componentGraph g comp) [] {}
    let loops ← componentLoops P cg run []
    let placed := placeComponentExact P cg run 0 [] loops
    pure (rtcfCaptionFitPartB P {} lines comp placed)

private def rtcfProbeTitleCount (inp : Input) (sets : List ModelRegionSet) :
    Except LayoutError (List Nat) := do
  let P ← checkedParams .vector inp.kind
  let m ← metricOf .vector
  let target := Measure.wrapTarget m.profile P.wrapWidth 0
  let lines ← boxLines m target inp
  let measured ← measureLabels P m target inp .TB
  let g0 ← measuredGraph P inp {} lines
  let g ← exactGraph P [] inp {} measured g0
  let idSets ← graphRegions inp sets
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    (width, height)
  let spec := RegionSpec.mk idSets titles
  (components g).mapM fun comp => do
    let (cg, run) ← RegionImpl.componentRunR P [] (some spec) inp (componentGraph g comp) [] {}
    let loops ← componentLoops P cg run []
    pure (placeComponentExact P cg run 0 [] loops).titles.length

#eval rtcfProbeC8bB rtcfProbeInp [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]
#eval rtcfProbeTitleCount rtcfProbeInp [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]

private def rtcfNestedInp : Input :=
  { kind := "state"
    boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
      { id := "A", role := .group, parent := "G1", exclusive := false },
      { id := "A1", role := .group, parent := "A", exclusive := false },
      { id := "A2", role := .group, parent := "A", exclusive := false },
      { id := "B", role := .group, parent := "G1", exclusive := false },
      { id := "a1", parent := "A1", exclusive := false },
      { id := "a2", parent := "A2", exclusive := false },
      { id := "b1", parent := "B", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "b1" },
      { id := "e2", fromId := "a2", toId := "b1" }]
    texts := ["G1", "A", "A1", "A2", "B", "a1", "a2", "b1"]
    edges := [.plain, .plain]
    labels := [] }

#eval rtcfProbeC8bB rtcfNestedInp [{ parent := 0, regions := [1, 4] }, { parent := 1, regions := [2, 3] }]
#eval rtcfProbeTitleCount rtcfNestedInp [{ parent := 0, regions := [1, 4] }, { parent := 1, regions := [2, 3] }]

private def rtcfTitledInp : Input :=
  { rtcfProbeInp with texts := ["G1", "ALONGTITLE0123456789INSIDE", "B", "G2", "C", "D", "a1", "b1", "c1", "d1"] }

#eval rtcfProbeC8bB rtcfTitledInp [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]
#eval rtcfProbeTitleCount rtcfTitledInp [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]

private def rtcfEmptyInp : Input :=
  { kind := "state"
    boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
      { id := "A", role := .group, parent := "G1", exclusive := false },
      { id := "B", role := .group, parent := "G1", exclusive := false },
      { id := "G2", role := .group, parent := "", exclusive := false },
      { id := "C", role := .group, parent := "G2", exclusive := false },
      { id := "D", role := .group, parent := "G2", exclusive := false },
      { id := "a1", parent := "A", exclusive := false },
      { id := "b1", parent := "B", exclusive := false },
      { id := "c1", parent := "C", exclusive := false },
      { id := "d1", parent := "D", exclusive := false },
      { id := "E", role := .group, parent := "G1", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "c1" },
      { id := "e2", fromId := "b1", toId := "d1" },
      { id := "e3", fromId := "c1", toId := "b1" }]
    texts := ["G1", "A", "B", "G2", "C", "D", "a1", "b1", "c1", "d1", "E"]
    edges := [.plain, .plain, .plain]
    labels := [] }

#eval rtcfProbeC8bB rtcfEmptyInp [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]

private def rtcfSelfInp : Input :=
  { rtcfProbeInp with routes := [{ id := "e1", fromId := "a1", toId := "a1" },
    { id := "e2", fromId := "b1", toId := "d1" }, { id := "e3", fromId := "c1", toId := "b1" }] }

#eval rtcfProbeC8bB rtcfSelfInp [{ parent := 0, regions := [1, 2] }, { parent := 3, regions := [4, 5] }]
private theorem rtcf_place_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).titles =
      (componentTitles P cg run).map fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2) := by
  simp only [placeComponentExact, placeBoundsX]
private theorem rtcf_candidateR_nodes (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (RegionImpl.componentCandidateR spec g comp index).nodes =
      (componentGraph g comp).nodes := by
  cases spec with
  | none => exact componentCandidate_nodes g comp index
  | some _ => unfold RegionImpl.componentCandidateR componentGraph; dsimp only
private theorem rtcf_run_nodes_eq {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : RegionImpl.componentRunR P exact spec inp cg labels orderOptions =
      .ok (cg', run)) :
    cg'.nodes = cg.nodes := by
  unfold RegionImpl.componentRunR at h
  obtain ⟨rs, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨rr, _, h⟩ := bind_ok h
    obtain ⟨ranked, hranked, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        obtain ⟨xs, _, h⟩ := bind_ok h
        obtain ⟨placed, _, h⟩ := bind_ok h
        obtain ⟨routed, _, h⟩ := bind_ok h
        split at h
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
          have h1 : cg = cg1 :=
            congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
          rw [hfst, h1]
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
          have h1 : cg = cg1 :=
            congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
          rw [hfst, h1]
  · obtain ⟨ranked, hranked, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        split at h
        · simp only [bind, Except.bind] at h
          exact absurd h (by simp)
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨placed, _, h⟩ := bind_ok h
          obtain ⟨routed, _, h⟩ := bind_ok h
          split at h
          · obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
            have hnodes := rankEquivalentR_nodes_eq hranked
            rw [hfst, hnodes]

          · obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
            have hnodes := rankEquivalentR_nodes_eq hranked
            rw [hfst, hnodes]
private theorem rtcf_candidate_get {g : Graph} {comp : List Nat}
    {spec : Option RegionSpec} {index i : Nat} {top : Node}
    (h : (RegionImpl.componentCandidateR spec g comp index).nodes[i]? = some top) :
    ∃ j, comp[i]? = some j ∧ g.nodes.getD j default = top := by
  rw [rtcf_candidateR_nodes] at h
  have hmap : (componentGraph g comp).nodes = comp.map fun v => g.nodes.getD v default := rfl
  rw [hmap, List.getElem?_map] at h
  cases hc : comp[i]? with
  | none => simp [hc] at h
  | some j =>
    simp only [hc, Option.map_some] at h
    exact ⟨j, rfl, Option.some.inj h⟩
private theorem rtcf_candidate_title_graph0 {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {spec' : Option RegionSpec} {index i : Nat} {top : Node}
    (htop : (RegionImpl.componentCandidateR spec' execution.graph comp index).nodes[i]? =
      some top)
    (hborder : top.border = -2) :
    (componentCandidate execution.graph0 comp index).nodes[i]? = some top := by
  obtain ⟨j, hj, hgetD⟩ := rtcf_candidate_get htop
  have hlen : j < execution.graph.nodes.length := by
    by_cases hjlen : j < execution.graph.nodes.length
    · exact hjlen
    · have hnone : execution.graph.nodes[j]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      have hdefault : (default : Node) = top := by
        simpa [List.getD, hnone] using hgetD
      rw [← hdefault] at hborder
      have hz : (default : Node).border = 0 := rfl
      rw [hz] at hborder
      omega
  have hget : execution.graph.nodes[j]? = some top := by
    have he : execution.graph.nodes[j] = top := by
      simpa [List.getD, hlen] using hgetD
    simpa [hlen] using congrArg some he
  have hlen0 : j < execution.graph0.nodes.length := by
    have hlg := exactGraph_length execution.graph_eq
    omega
  have hget0 : execution.graph0.nodes[j]? = some (execution.graph0.nodes[j]) :=
    List.getElem?_eq_some_iff.mpr ⟨hlen0, rfl⟩
  obtain ⟨nd', hnd', hnb, _, _⟩ := exactGraph_node_key execution.graph_eq hget0
  have htopEq : top = nd' := Option.some.inj (hget.symm.trans hnd')
  have hborder0 : (execution.graph0.nodes[j]).border = -2 := by
    rw [← hnb, ← htopEq]
    exact hborder
  have hA := exactGraph_border2_unchangedX execution.graph0_eq execution.graph_eq
    hget0 hborder0
  have htop0eq : top = execution.graph0.nodes[j] :=
    Option.some.inj (hget.symm.trans hA)
  have htop0 : (componentCandidate execution.graph0 comp index).nodes[i]? = some top := by
    rw [componentCandidate_nodes]
    have hmap : (componentGraph execution.graph0 comp).nodes =
        comp.map fun v => execution.graph0.nodes.getD v default := rfl
    rw [hmap, List.getElem?_map, hj]
    have hget0' : execution.graph0.nodes[j]? = some top := by
      rw [htop0eq]
      exact hget0
    have hgd : execution.graph0.nodes.getD j default = top := by
      rw [List.getD_eq_getElem?_getD, hget0', Option.getD_some]
    simp only [Option.map_some, hgd]
  exact htop0
theorem R_exactTitleCaptionFitB8_holds (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ExactTitleCaptionFitB8 exactIds idSets := by
  intro inp o res execution part hpart title htitle
  obtain ⟨index, _, cg, run, loops, _, spec', _, _, _, _, hrun, _, hpartdef⟩ :=
    (actual_components_parts_geometryR (by rfl) execution.components_eq).2 part hpart
  have ht2 : title ∈ (placeComponentExact execution.params cg run 0
      execution.measured loops).titles := by
    have h2 := htitle
    rw [hpartdef] at h2
    exact h2
  rw [rtcf_place_titles_eq] at ht2
  obtain ⟨raw, hraw, heTitle⟩ := List.mem_map.mp ht2
  subst title
  obtain ⟨top, htop, hborder, hindex, hw, hh⟩ :=
    componentTitles_dimension_source execution.params cg run hraw
  have hcgGet : cg.nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htop
  have hnodesEq := rtcf_run_nodes_eq hrun
  have htopR : (RegionImpl.componentCandidateR spec' execution.graph part.1 index).nodes[top.2]? =
      some top.1 := by
    rw [← hnodesEq]
    exact hcgGet
  have htop0 : (componentCandidate execution.graph0 part.1 index).nodes[top.2]? =
      some top.1 :=
    rtcf_candidate_title_graph0 execution htopR hborder
  have hfit := actual_title_caption_fit execution.graph0_eq htop0 hborder
  have width_nonneg : ∀ (lines : List Measure.Line) (start : Int),
      0 ≤ start → 0 ≤ lines.foldl (fun width line => max width line.width) start := by
    intro lines
    induction lines with
    | nil => intro start hs; exact hs
    | cons line lines ih =>
      intro start hs
      exact ih _ (Int.le_trans hs (Int.le_max_left _ _))
  have hw0 := width_nonneg
    (execution.lines.getD (part.1.getD top.2 0) []) 0 (by omega)
  have hh0 : 0 ≤
      (max 1 (execution.lines.getD (part.1.getD top.2 0) []).length : Int) *
        execution.params.lineH :=
    Int.mul_nonneg (by omega) (checkedParams_sizing_nonneg execution.checked).1
  dsimp only [shiftRect]
  rw [hindex, hw, hh]
  cases hd : o.direction <;> simp only [hd] at hfit ⊢ <;>
    exact ⟨by omega, by omega, by omega, by omega⟩
theorem R_packedPartTransportBounded_closed' (exactIds : List String)
    (idSets : List (String × List String))
    (hsize : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionR exactIds idSets inp o res),
      R_PartSizingR execution) :
    R_PackedPartTransportBoundedB8 exactIds idSets :=
  R_packedPartTransportBounded_closed exactIds idSets hsize
    (R_exactTitleCaptionFitB8_holds exactIds idSets)







end PipelineImpl
end Layered
end Elegant
