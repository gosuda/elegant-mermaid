import Elegant.Layered.RegionLabelPlacementProof
import Elegant.Layered.RegionFlatC8b
import Elegant.Layered.RegionGroupEndpointProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- A measured scene label comes from an edge of the selected region run and
from that run's placed label on an actual pack shelf. -/
def R7_LabelBelongsToRun (exactIds : List String) (idSets : List (String × List String))
    (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionR exactIds idSets inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : MeasuredLabel),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    ∃ (comp : List Nat) (candidate : Nat) (run : Run) (orderOptions : OrderOptions)
      (cg cg' : Graph) (edge decl : Nat) (e : Edge) (px py m h : Int) (d : Direction)
      (packed : Pack.State) (c : Nat) (labelPart : List Nat × Part) (shelfc : Rect)
      (loops : List (Nat × LoopPlacement)) (area : Int) (rl : Nat × Rect)
      (rs : Option ComponentRegions),
      comp ∈ components execution.graph ∧
      newComponentRegions (r7Spec idSets o execution.params execution.lines)
        execution.params inp (componentGraph execution.graph comp) = .ok rs ∧
      cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
        execution.graph comp candidate ∧
      componentRunR execution.params (exactDecls exactIds inp)
        (r7Eff idSets o execution.params execution.lines rs)
        inp cg execution.measured orderOptions = .ok (cg', run) ∧
      orderOptions = candidateOrder candidate ∧
      cg'.edges[edge]? = some e ∧
      (cg'.edges[edge]?).map (·.decl) = some decl ∧
      measured ∈ routeLabels execution.measured decl ∧
      l.rect = shiftRect m m
        (orientRect d h (shiftRect px py
          (Elegant.Layered.routeLabelRect execution.params cg' run execution.measured measured))) ∧
      m = execution.params.canvasMargin ∧
      h = execution.packedAcc.canvasH ∧
      d = o.direction ∧
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (labelPart, shelfc) ∧
      labelPart.1 = comp ∧
      componentLoops execution.params cg' run execution.measured = .ok loops ∧
      labelPart.2 = { placeComponentExact execution.params cg' run 0
        execution.measured loops with area := area } ∧
      px = shelfc.x + (0 - (placeBoundsX execution.params cg' run execution.measured
        loops).minX) ∧
      py = shelfc.y + (-(placeBoundsX execution.params cg' run execution.measured
        loops).minY) ∧
      rl.1 = measured.index ∧
      rl ∈ labelPart.2.labels ∧
      l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfc.x shelfc.y rl.2))

private theorem r7SceneRouteLabelRect {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {l : SceneLabel} {index : Nat} {source : ModelLabel} {measured : MeasuredLabel}
    (hwf : WellFormed (inputModel inp o))
    (hl : l ∈ res.scene.labels) (hin : inp.labels[index]? = some source)
    (hid : l.id = source.id)
    (hmeasured : execution.measured.find? (fun label => label.index == index) = some measured) :
    l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.labels.getD measured.index default)) := by
  have hids : (inp.labels.map (·.id)).Nodup := Elegant.Layered.labelIds_nodup hwf
  rw [execution.scene_eq] at hl
  obtain ⟨⟨label, j⟩, hzip, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨hj, hlabel⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hzip)
  obtain ⟨hi, hsource⟩ := List.getElem?_eq_some_iff.mp hin
  have hindex (h : l.id = label.id) : j = index := by
    refine hids.eq_of_getElem_eq
      (by simpa only [List.length_map] using hj)
      (by simpa only [List.length_map] using hi) ?_
    rw [List.getElem_map, List.getElem_map, hlabel, hsource]
    exact h.symm.trans hid
  dsimp only at hemitted
  split at hemitted
  · simp at hemitted
  · split at hemitted
    · next selected hfind =>
      have h := hindex ((congrArg (fun s => s.toLabel.id) (Option.some.inj hemitted)).symm)
      rw [h] at hfind
      have heq : selected = measured := Option.some.inj (hfind.symm.trans hmeasured)
      have hrect := (congrArg (fun s => s.toLabel.rect) (Option.some.inj hemitted)).symm
      dsimp only at hrect
      rw [heq] at hrect
      exact hrect
    · next hfind =>
      split at hemitted
      · simp at hemitted
      · have h := hindex ((congrArg (fun s => s.toLabel.id) (Option.some.inj hemitted)).symm)
        rw [h, hmeasured] at hfind
        cases hfind

theorem r7_labelBelongsToRun {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) : R7_LabelBelongsToRun exactIds idSets inp o res := by
  intro execution l index source measured hl hin hid hmeasured
  have hmem := List.mem_of_find?_eq_some hmeasured
  obtain ⟨hindex, hedgeSource⟩ := measureLabels_source execution.measured_eq hmem
  have hnd := measureLabels_index_nodup execution.measured_eq
  have hscene := r7SceneRouteLabelRect execution hwf hl hin hid hmeasured
  have hp := execution.packed_eq
  unfold packAcc at hp
  obtain ⟨packed, hpack, hfold⟩ := bind_ok hp
  let packStart : Acc := { execution.componentsAcc with
    canvasW := packed.width
    canvasH := packed.height
    titles := [] }
  have hpackedAcc : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep packStart := by
    have hout := Except.ok.inj hfold
    rw [inlineFold_eq_packStep] at hout
    exact hout.symm
  have hsize : execution.componentsAcc.labels.size = inp.labels.length := by
    simpa only [Array.size_replicate] using
      r8b_components_fold_labels_sizeR execution.params exactIds _ inp o execution.graph
        execution.measured (components execution.graph) _ _ execution.components_eq
  have hprovenance := packFold_labels_provenance
    (execution.componentsAcc.parts.zip packed.boxes)
    packStart
    measured.index (execution.packedAcc.labels.getD measured.index default)
    (by change measured.index < execution.componentsAcc.labels.size; rwa [hsize])
    (by rw [hpackedAcc])
  have hcarry : ∃ q ∈ execution.componentsAcc.parts.zip packed.boxes, ∃ stored : Rect,
      (measured.index, stored) ∈ q.1.2.labels ∧
      execution.packedAcc.labels.getD measured.index default = shiftRect q.2.x q.2.y stored := by
    rcases hprovenance with h | ⟨hnone, _⟩
    · exact h
    · obtain ⟨packed', _, q, candidate, run, loops, _, spec', cg', edge, e, hp', hq, hrun, _,
        hpart, hedge, hdecl⟩ := rgeRouteSourceR execution hedgeSource
      have heq : packed' = packed := Except.ok.inj (hp'.symm.trans hpack)
      subst packed'
      have hroute : measured ∈ routeLabels execution.measured e.decl :=
        List.mem_filter.mpr ⟨hmem, by simp [hdecl]⟩
      obtain ⟨rect, hrect⟩ := regionLabel_routeLabelsPlaced execution.params
        (exactDecls exactIds inp) spec' inp (componentCandidateR spec' execution.graph q.1.1 candidate)
        cg' execution.measured (candidateOrder candidate) run measured edge e hrun hedge hroute
      let bounds := placeBoundsX execution.params cg' run execution.measured loops
      have hstored : (measured.index, shiftRect (0 - bounds.minX) (-bounds.minY) rect) ∈
          q.1.2.labels := by
        rw [hpart, X_placeComponentExact_labels_eq]
        exact List.mem_map.mpr ⟨(measured.index, rect), hrect, rfl⟩
      exact (hnone q (List.mem_of_getElem? hq) _ hstored).elim
  obtain ⟨q, hq, stored, hstored, hpackedRect⟩ := hcarry
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hq
  have hqpart := (List.of_mem_zip hq).1
  obtain ⟨hparts, hactual⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hcomp : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hqpart
  obtain ⟨candidate, _, cg', run, loops, area, spec', _, _, _, ⟨rs, hnew, hspec⟩,
    hrun, hloops, hpart⟩ := hactual q.1 hqpart
  change newComponentRegions (r7Spec idSets o execution.params execution.lines)
    execution.params inp (componentGraph execution.graph q.1.1) = .ok rs at hnew
  change spec' = r7Eff idSets o execution.params execution.lines rs at hspec
  subst spec'
  let cg := componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
    execution.graph q.1.1 candidate
  let bounds := placeBoundsX execution.params cg' run execution.measured loops
  have hlabels : q.1.2.labels = (placedLabels execution.params cg' run execution.measured).map
      (fun p => (p.1, shiftRect (0 - bounds.minX) (-bounds.minY) p.2)) := by
    rw [hpart]
    exact X_placeComponentExact_labels_eq
  have hmap := hstored
  rw [hlabels] at hmap
  obtain ⟨⟨k, rect⟩, hlocal, hshifted⟩ := List.mem_map.mp hmap
  have hk : k = measured.index := congrArg Prod.fst hshifted
  have hshift : shiftRect (0 - bounds.minX) (-bounds.minY) rect = stored :=
    congrArg Prod.snd hshifted
  subst k
  obtain ⟨placed, edge, e, _, _, hplaced, hkey, _, hedge, _, hstack, _⟩ :=
    placedLabels_pair_inv hnd hlocal
  have heq : placed = measured :=
    measured_eq_of_index_eq execution.measured hnd placed measured hplaced hmem hkey
  subst placed
  have hroute : measured ∈ routeLabels execution.measured e.decl :=
    (List.of_mem_zip (List.mem_of_find?_eq_some hstack)).1
  have hrouteRect := routeLabelRect_of_mem (l := measured) hnd hlocal
  have hshelfRect : l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH (shiftRect q.2.x q.2.y stored)) := by
    rw [hscene, hpackedRect]
  have hrunRect : l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect (q.2.x + (0 - bounds.minX)) (q.2.y + (-bounds.minY))
          (Elegant.Layered.routeLabelRect execution.params cg' run execution.measured measured))) := by
    rw [hshelfRect, ← hshift, shiftRect_shiftRect, hrouteRect]
  exact ⟨q.1.1, candidate, run, candidateOrder candidate, cg, cg', edge, e.decl, e,
    q.2.x + (0 - bounds.minX), q.2.y + (-bounds.minY), execution.params.canvasMargin,
    execution.packedAcc.canvasH, o.direction, packed, c, q.1, q.2, loops, area,
    (measured.index, stored), rs, hcomp, hnew, rfl, hrun, rfl, hedge,
    by simp only [hedge, Option.map_some], hroute, hrunRect, rfl, rfl, rfl,
    hpack, hc, rfl, hloops, hpart, rfl, rfl, rfl, hstored, hshelfRect⟩

end Elegant.Layered.PipelineImpl
