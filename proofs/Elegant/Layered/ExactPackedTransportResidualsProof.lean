import Elegant.Layered.ExactPackedTransportProof
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Pack

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact packed-part transport residuals, closed.

Replays the three plain facts consumed by
`X_packedPartTransportBounded_holds` (`ExactPackedTransportProof.lean`)
over `SceneExecutionX`:

* `X_PackedLabelsTransport`: replay of `packedLabelsTransport_of_bridge`
  (`FrameLabelsProof.lean`) with the exact component-fold size/no-carry
  mirrors `X_components_fold_labels_size` / `X_fold_labels_getD_of_no_carry`
  (`ExactFlatC7.lean`). Label provenance never inspects placement, so the
  exact run shape (`placeComponentExact` differing from the plain placement
  only for nonempty `run.exact`) is irrelevant here.
* `X_PackedTitlesMemSource`: replay of `packed_titles_mem_source` with the
  exact part-geometry witness `X_execution_part_run` (which discharges the
  border premise internally) and the shared `componentTitles` projection.
* `X_ExactTitleCaptionFit`: replay of
  `SceneExecution.component_title_caption_fit` with the exact part-geometry
  witness plus the candidate-node transfer `xpr_candidate_title_graph0`
  from the exact graph to the measured graph, where the shared
  `actual_title_caption_fit` applies.

The per-execution border premise `ExactBorder2Unchanged` discharges outright
via `exactBorder2Unchanged_discharge`, so the closed transport needs no
residual hypothesis. -/

/-- Prefixed copy of the private `pack_titles_fold` in
`FrameLabelsProof.lean`. -/
private theorem xpr_pack_titles_fold (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).titles =
      start.titles ++
        pairs.flatMap (fun pair => pair.1.2.titles.map
          (fun title => (pair.1.1.getD title.1 0,
            shiftRect pair.2.x pair.2.y title.2))) := by
  induction pairs generalizing start with
  | nil => simp
  | cons pair rest ih =>
    simp [List.foldl_cons, ih, packStep, List.append_assoc]

/-- Prefixed copy of the private `packFold_labels_size_hold` in
`FrameLabelsProof.lean`. -/
private theorem xpr_packFold_labels_size_hold
    (qs : List ((List Nat × Part) × Rect)) (arr : Array Rect) :
    (qs.foldl (fun a q => q.1.2.labels.foldl
      (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) a) arr).size =
      arr.size := by
  revert arr
  induction qs with
  | nil => intro arr; rfl
  | cons q rest ih =>
    intro arr
    rw [List.foldl_cons, ih]
    exact size_keyFold_rects_eq _ _ _

/-- Prefixed copy of the private `xpptb_packedShelfExistence_of_execution`
in `ExactPackedTransportProof.lean`. -/
private theorem xpr_packedShelfExistence_of_execution {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed ∧
      packed.boxes.length = execution.componentsAcc.parts.length := by
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  refine ⟨packed, hpacked, ?_⟩
  rw [Pack.pack_count hpacked, List.length_map]

/-- Prefixed copy of the private `candidate_nodes_getElem?` in
`ExactPartBounded.lean`. -/
private theorem xpr_candidate_nodes_getElem? {g : Graph} {comp : List Nat} {index i : Nat}
    {top : Node} (h : (componentCandidate g comp index).nodes[i]? = some top) :
    ∃ j, comp[i]? = some j ∧ g.nodes.getD j default = top := by
  rw [componentCandidate_nodes] at h
  have hmap : (componentGraph g comp).nodes =
      comp.map fun v => g.nodes.getD v default := rfl
  rw [hmap, List.getElem?_map] at h
  cases hc : comp[i]? with
  | none => simp [hc] at h
  | some j =>
    simp only [hc, Option.map_some] at h
    exact ⟨j, rfl, Option.some.inj h⟩

/-- A border `-2` candidate node of the exact graph is the same node of the
measured graph. Prefix-copy of the transfer inside
`actual_title_dims_nonnegX` (`ExactPartBounded.lean`). -/
private theorem xpr_candidate_title_graph0 {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hX : ExactBorder2Unchanged execution)
    {comp : List Nat} {index i : Nat} {top : Node}
    (htop : (componentCandidate execution.graph comp index).nodes[i]? = some top)
    (hborder : top.border = -2) :
    (componentCandidate execution.graph0 comp index).nodes[i]? = some top := by
  obtain ⟨j, hj, hgetD⟩ := xpr_candidate_nodes_getElem? htop
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
  have hA := hX hget0 hborder0
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
/-- Exact placed-component titles are the shared `componentTitles` shifted by
the exact placement bounds. -/
private theorem xpr_placeComponentExact_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).titles =
      (componentTitles P cg run).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := by
  simp only [placeComponentExact, placeBoundsX]


/-- Exact packed-label provenance holds outright: replay of
`packedLabelsTransport_of_bridge` over `SceneExecutionX`. -/
theorem X_packedLabelsTransport_closed (exactIds : List String) :
    X_PackedLabelsTransport exactIds := by
  intro inp o res execution
  obtain ⟨packed, hpackE, hlenE⟩ := xpr_packedShelfExistence_of_execution execution
  refine ⟨packed, hpackE, ?_⟩
  intro index r hget
  have hpackeq := execution.packed_eq
  unfold packAcc at hpackeq
  obtain ⟨packed', hpacked', hfold⟩ := bind_ok hpackeq
  have heq : packed = packed' := Except.ok.inj (hpackE.symm.trans hpacked')
  subst heq
  have hout : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] } := by
    have he := Except.ok.inj hfold
    rw [inlineFold_eq_packStep] at he
    exact he.symm
  have hlen : execution.componentsAcc.parts.length = packed.boxes.length := by
    rw [Pack.pack_count hpackE, List.length_map]
  have hcomplabelssize : execution.componentsAcc.labels.size = inp.labels.length := by
    have h := X_components_fold_labels_size (components execution.graph) _ _
      execution.components_eq
    rw [h]
    simp
  by_cases hi : index < execution.componentsAcc.labels.size
  · have hprov := packFold_labels_provenance
      (execution.componentsAcc.parts.zip packed.boxes)
      { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] }
      index r
      (by change index < execution.componentsAcc.labels.size; exact hi)
      (by rwa [← hout])
    rcases hprov with ⟨q, hqzip, r0, hmem, hr⟩ | ⟨hno, hst⟩
    · obtain ⟨pl, hplpart, hplbox⟩ := mem_zip_pairing hlen q hqzip
      exact Or.inl ⟨pl, q.1, r0, q.2, hplpart, hmem, hplbox, hr⟩
    · have hnoparts : ∀ p ∈ execution.componentsAcc.parts, ∀ r0 : Rect,
          (index, r0) ∉ p.2.labels := by
        intro p hpmem r0 hmem
        obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpmem
        have hcbox : c < packed.boxes.length := by
          rw [← hlen]
          exact (List.getElem?_eq_some_iff.mp hc).1
        have hboxget : packed.boxes[c]? = some packed.boxes[c] :=
          List.getElem?_eq_getElem hcbox
        have hqzip : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
            some (p, packed.boxes[c]) :=
          List.getElem?_zip_eq_some.mpr ⟨hc, hboxget⟩
        exact hno (p, packed.boxes[c]) (List.mem_of_getElem? hqzip) r0 hmem
      have hcomp := X_fold_labels_getD_of_no_carry (components execution.graph) _ _
        index execution.components_eq hnoparts
      have hst2 : execution.componentsAcc.labels.getD index default = r := hst
      rw [hcomp] at hst2
      dsimp only at hst2
      have hrep : (Array.replicate inp.labels.length (default : Rect)).getD index
          default = default := by
        rw [Array.getD_eq_getD_getElem?]
        cases h : (Array.replicate inp.labels.length (default : Rect))[index]? with
        | none => rfl
        | some x =>
          have hx : x = default := (layout_startAcc_defaults inp).2.2 index x h
          simp [hx]
      rw [hrep] at hst2
      exact Or.inr hst2.symm
  · have hle : execution.componentsAcc.labels.size ≤ index := by omega
    have hpacksize : execution.packedAcc.labels.size =
        execution.componentsAcc.labels.size := by
      rw [hout, pack_labels_eq_fold, xpr_packFold_labels_size_hold]
    have hle' : execution.packedAcc.labels.size ≤ index := by
      rw [hpacksize]; exact hle
    have hdef : execution.packedAcc.labels.getD index default = default :=
      array_getD_of_size_le hle'
    exact Or.inr (hget.symm.trans hdef)

/-- Exact packed-title membership holds outright: replay of
`packed_titles_mem_source` over `SceneExecutionX`. -/
theorem X_packedTitlesMemSource_closed (exactIds : List String) :
    X_PackedTitlesMemSource exactIds := by
  intro inp o res execution packed hpacked key stored hmem
  have hpackeq := execution.packed_eq
  unfold packAcc at hpackeq
  obtain ⟨packed', hpacked', hfold⟩ := bind_ok hpackeq
  have heqpacked : packed = packed' := Except.ok.inj (hpacked.symm.trans hpacked')
  subst heqpacked
  have hout : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] } :=
    (Except.ok.inj hfold).symm
  rw [hout, xpr_pack_titles_fold] at hmem
  have hstart : ({ execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] } : Acc).titles
      = [] := rfl
  rw [hstart, List.nil_append] at hmem
  obtain ⟨pair, hpair, htitle⟩ := List.mem_flatMap.mp hmem
  obtain ⟨⟨i, stored0⟩, ht, hteq⟩ := List.mem_map.mp htitle
  have hlen : execution.componentsAcc.parts.length = packed.boxes.length := by
    rw [Pack.pack_count hpacked, List.length_map]
  obtain ⟨pl, hplpart, hplbox⟩ := mem_zip_pairing hlen pair hpair
  have hkeyeq : pair.1.1.getD i 0 = key := congrArg Prod.fst hteq
  have hstoreq : shiftRect pair.2.x pair.2.y stored0 = stored := congrArg Prod.snd hteq
  have hpartmem : pair.1 ∈ execution.componentsAcc.parts := List.mem_of_getElem? hplpart
  obtain ⟨index, run, loops, area, hcomp, hrun, hpartdef⟩ :=
    X_execution_part_run execution hpartmem
  have ht2 : (i, stored0) ∈ (placeComponentExact execution.params
      (componentCandidate execution.graph pair.1.1 index) run 0 execution.measured loops).titles := by
    have h2 := ht
    rw [hpartdef] at h2
    exact h2
  rw [xpr_placeComponentExact_titles_eq] at ht2
  obtain ⟨raw, hraw, hreq⟩ := List.mem_map.mp ht2
  obtain ⟨top, htop, _, hindex, _, _⟩ := componentTitles_dimension_source
    execution.params (componentCandidate execution.graph pair.1.1 index) run hraw
  have hi := (List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp htop)).1
  have hlen2 : (componentCandidate execution.graph pair.1.1 index).nodes.length =
      pair.1.1.length := by
    rw [componentCandidate_nodes]
    show (componentGraph execution.graph pair.1.1).nodes.length = _
    unfold componentGraph
    dsimp only
    rw [List.length_map]
  have hkey : raw.1 = i := congrArg Prod.fst hreq
  have hi2 : i = top.2 := hkey.symm.trans hindex
  have hrange : i < pair.1.1.length := by
    rw [hi2, ← hlen2]
    exact hi
  have hgetElem : pair.1.1[i]? = some pair.1.1[i] :=
    List.getElem?_eq_getElem hrange
  have hgetD : pair.1.1.getD i 0 = pair.1.1[i] := by
    rw [List.getD_eq_getElem?_getD, hgetElem, Option.getD_some]
  have hget : pair.1.1[i]? = some key := by
    rw [← hkeyeq, hgetD]
    exact List.getElem?_eq_getElem hrange
  exact ⟨pl, pair.1, i, stored0, pair.2, hplpart, hget, ht, hplbox, hstoreq.symm⟩

/-- Exact stored-title caption fit holds outright: replay of
`SceneExecution.component_title_caption_fit` over `SceneExecutionX`, moving
the candidate node to the measured graph where the shared
`actual_title_caption_fit` applies. -/
theorem X_exactTitleCaptionFit_closed (exactIds : List String) :
    X_ExactTitleCaptionFit exactIds := by
  intro inp o res execution part hpart title htitle
  have hX : ExactBorder2Unchanged execution := exactBorder2Unchanged_discharge execution
  obtain ⟨index, run, loops, area, hcomp, hrun, hpartdef⟩ :=
    X_execution_part_run execution hpart
  have ht2 : title ∈ (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured loops).titles := by
    have h2 := htitle
    rw [hpartdef] at h2
    exact h2
  rw [xpr_placeComponentExact_titles_eq] at ht2
  obtain ⟨raw, hraw, heTitle⟩ := List.mem_map.mp ht2
  subst title
  obtain ⟨top, htop, hborder, hindex, hw, hh⟩ := componentTitles_dimension_source
    execution.params (componentCandidate execution.graph part.1 index) run hraw
  have htop0 : (componentCandidate execution.graph0 part.1 index).nodes[top.2]? = some top.1 :=
    xpr_candidate_title_graph0 execution hX
      (List.mem_zipIdx_iff_getElem?.mp htop) hborder
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

/-- The exact packed-part transport holds outright: the three closed
residuals plus the discharged border premise feed
`X_packedPartTransportBounded_holds`. -/
theorem X_packedPartTransportBounded_closed (exactIds : List String) :
    X_PackedPartTransportBoundedB8 exactIds := by
  intro inp o res execution
  exact X_packedPartTransportBounded_holds exactIds
    (X_packedLabelsTransport_closed exactIds)
    (X_packedTitlesMemSource_closed exactIds)
    (X_exactTitleCaptionFit_closed exactIds)
    execution (exactBorder2Unchanged_discharge execution)

/-- The closed theorem has exactly the B8 transport type. -/
example (exactIds : List String) : X_PackedPartTransportBoundedB8 exactIds :=
  X_packedPartTransportBounded_closed exactIds

end PipelineImpl
end Layered
end Elegant
