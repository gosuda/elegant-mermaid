import Elegant.Layered.StatePipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Helper: region candidate with no spec is the plain candidate. -/
theorem componentCandidateR_none (g : Graph) (comp : List Nat) (index : Nat) :
    RegionImpl.componentCandidateR none g comp index = componentCandidate g comp index := rfl

/-- Helper: region coordinate graph with no spec is the exact one. -/
theorem coordinateGraphR_none (P : Params) (exact : List Nat) (p : Proper) :
    RegionImpl.coordinateGraphR P exact none p = coordinateGraphX P exact p := rfl

/-- Helper: no region sets means no component regions. -/
theorem newComponentRegions_none (P : Params) (inp : Input) (cg : Graph) :
    RegionImpl.newComponentRegions none P inp cg = pure none := rfl


/-- The region-aware run with no spec coincides with the exact run. -/
theorem componentRunR_none (P : Params) (exact : List Nat) (inp : Input) (cg : Graph)
    (labels : List MeasuredLabel) (orderOptions : OrderOptions) :
    RegionImpl.componentRunR P exact none inp cg labels orderOptions =
      (componentRunX P exact cg labels orderOptions).map (fun run => (cg, run)) := by
  simp only [RegionImpl.componentRunR, componentRunX, RegionImpl.newComponentRegions,
    RegionImpl.coordinateGraphR]
  simp only [bind, Except.bind, pure, Except.pure]
  simp
  repeat' (first | rfl | split)

/-- The region-aware trial with no spec coincides with the exact trial. -/
theorem componentTrialR_none (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (g : Graph) (comp : List Nat) (labels : List MeasuredLabel)
    (index : Nat) :
    componentTrialR P exactIds none inp o g comp labels index =
      componentTrialX P exactIds inp o g comp labels index := by
  simp only [componentTrialR, componentTrialX, RegionImpl.componentCandidateR,
    RegionImpl.newComponentRegions] at *
  simp only [bind, Except.bind, pure, Except.pure] at *
  simp at *
  cases hX : componentRunX P (exactDecls exactIds inp) (componentCandidate g comp index)
      labels (candidateOrder index) with
  | error e =>
    have hR : RegionImpl.componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidate g comp index) labels (candidateOrder index) = .error e := by
      simp only [componentRunR_none, hX, Except.map]
    rw [hR]
  | ok run =>
    have hR : RegionImpl.componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidate g comp index) labels (candidateOrder index) =
        .ok (componentCandidate g comp index, run) := by
      simp only [componentRunR_none, hX, Except.map]
    rw [hR]

theorem layoutComponentR_none (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (g : Graph) (acc : Acc) (comp : List Nat)
    (labels : List MeasuredLabel) :
    layoutComponentR P exactIds none inp o g acc comp labels =
      layoutComponentX P exactIds inp o g acc comp labels := by
  have hfun : (componentTrialR P exactIds none inp o g comp labels) =
      (componentTrialX P exactIds inp o g comp labels) := by
    funext index
    exact componentTrialR_none P exactIds inp o g comp labels index
  simp only [layoutComponentR, layoutComponentX, hfun]

/-- Empty region spec runs the exact pipeline. -/
theorem layoutRIds_nil (exactIds : List String) (inp : Input) (o : Options) :
    layoutRIds exactIds [] inp o = layoutX exactIds inp o := by
  simp only [layoutRIds, layoutX]
  simp
  simp only [layoutComponentR_none]

/-- With no attached notes, the note wrapper runs its base. -/
theorem layoutNotes_noBundles (base : List String → Input → Options → Except LayoutError FamilyResult)
    (exactIds : List String) (fuel : Nat) (inp : Input) (o : Options)
    (h : attachmentsOf inp.boxes = []) :
    layoutNotes base exactIds fuel inp o = base exactIds inp o := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hb : bundlesOf inp.boxes (attachmentsOf inp.boxes) = [] := by
      simp [bundlesOf, h]
    simp [layoutNotes, hb]

/-- Sub-input boxes come from the original boxes with id, shape and direction kept. -/
theorem selectInput_mem (inp : Input) (keep : ModelBox → Bool) (root : String)
    (b : ModelBox) (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ b' ∈ inp.boxes, b.id = b'.id ∧ b.shape = b'.shape ∧ b.direction = b'.direction := by
  have hb' : b ∈ ((inp.boxes.zipIdx.filter fun q => keep q.1).map fun q =>
      if q.1.parent == root then { q.1 with parent := "" } else q.1) := by
    simpa [selectInput] using hb
  obtain ⟨q, hq_mem, rfl⟩ := List.mem_map.mp hb'
  obtain ⟨hq_zip, _hkeep⟩ := (List.mem_filter.mp hq_mem)
  have hfst : q.1 ∈ List.map Prod.fst (List.zipIdx inp.boxes) :=
    List.mem_map.mpr ⟨q, hq_zip, rfl⟩
  simp only [List.zipIdx_map_fst] at hfst
  refine ⟨q.1, hfst, ?_, ?_, ?_⟩ <;> by_cases hpar : q.1.parent == root <;> simp [hpar]

theorem attachmentsOf_selectInput (inp : Input) (keep : ModelBox → Bool) (root : String)
    (h : attachmentsOf inp.boxes = []) :
    attachmentsOf (selectInput inp keep root).boxes = [] := by
  simp only [attachmentsOf, List.filterMap_eq_nil_iff] at h ⊢
  intro q hq
  have hq_mem : q.1 ∈ (selectInput inp keep root).boxes := by
    have hfst : q.1 ∈ List.map Prod.fst (List.zipIdx (selectInput inp keep root).boxes) :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    simp only [List.zipIdx_map_fst] at hfst
    exact hfst
  obtain ⟨b', hb'_mem, hid, hshape, hdir⟩ := selectInput_mem inp keep root q.1 hq_mem
  have hq'_ex : ∃ q' ∈ List.zipIdx inp.boxes, q'.1.id = q.1.id ∧ q'.1.shape = q.1.shape ∧
      q'.1.direction = q.1.direction := by
    have hfst' : b' ∈ List.map Prod.fst (List.zipIdx inp.boxes) := by
      simp only [List.zipIdx_map_fst]
      exact hb'_mem
    obtain ⟨q', hq'_mem, hfst'_eq⟩ := List.mem_map.mp hfst'
    refine ⟨q', hq'_mem, ?_, ?_, ?_⟩
    · simp only [hfst'_eq] at hid ⊢
      exact hid.symm
    · simp only [hfst'_eq] at hshape ⊢
      exact hshape.symm
    · simp only [hfst'_eq] at hdir ⊢
      exact hdir.symm
  obtain ⟨q', hq'_mem, hid', hshape', hdir'⟩ := hq'_ex
  have hqp : (if q'.1.shape == "note" && (q'.1.direction == "left" || q'.1.direction == "right")
      then (noteTargetId q'.1.id).bind fun target =>
        (inp.boxes.findIdx? (·.id == target)).map fun t => (⟨t, q'.2, q'.1.direction == "right"⟩ : Attach)
      else none) = none := h q' hq'_mem
  have hgoal : (if q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right")
      then (noteTargetId q.1.id).bind fun target =>
        ((selectInput inp keep root).boxes.findIdx? (·.id == target)).map fun t =>
          (⟨t, q.2, q.1.direction == "right"⟩ : Attach)
      else none) = none := by
    by_cases hnote : (q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right")) = true
    · have hnote' : (q'.1.shape == "note" && (q'.1.direction == "left" || q'.1.direction == "right")) = true := by
        rw [hshape', hdir']
        exact hnote
      have htid_eq : noteTargetId q'.1.id = noteTargetId q.1.id := by rw [hid']
      simp [hnote'] at hqp
      simp [hnote]
      cases htid : noteTargetId q.1.id with
      | none =>
        intro a ha
        cases ha
      | some t =>
        have htid' : noteTargetId q'.1.id = some t := by rw [htid_eq, htid]
        intro a ha x hx
        have hat : t = a := Option.some_inj.mp ha
        obtain ⟨x', hx'_mem, hxid, _, _⟩ := selectInput_mem inp keep root x hx
        have hx_all := hqp t htid' x' hx'_mem
        rw [hxid, ←hat]
        exact hx_all
    · simp [hnote]
  exact hgoal

/-- Empty region list reindexes to empty. -/
theorem reindex_nil (sub : Input) : reindexRegionSets [] sub = [] := rfl

/-- Fixed-size bookkeeping never creates attached notes. -/
theorem attachmentsOf_withFixedSizes (inp : Input) (l1 : List (String × Size))
    (l2 : List (String × Scene)) (l3 : List (String × Int))
    (h : attachmentsOf inp.boxes = []) :
    attachmentsOf ({ inp with fixedSizes := l1, fixedChildren := l2, fixedAreas := l3 }).boxes = [] :=
  h

/-- The state base with no regions runs the exact base on note-free inputs. -/
theorem baseRN_eq_baseX (exactIds : List String) (outerFuel : Nat) (sub : Input) (o' : Options)
    (hsub : attachmentsOf sub.boxes = []) :
    (layoutNotes (fun ids s => layoutRIds ids (reindexRegionSets [] s) s) exactIds outerFuel) sub o' =
      layoutX exactIds sub o' := by
  have hnotes : layoutNotes (fun ids s => layoutRIds ids (reindexRegionSets [] s) s) exactIds outerFuel sub o' =
      (fun ids s => layoutRIds ids (reindexRegionSets [] s) s) exactIds sub o' :=
    layoutNotes_noBundles _ _ _ _ _ hsub
  simp only [reindex_nil, layoutRIds_nil] at hnotes
  exact hnotes

/-- Recursion with the state base coincides with the exact recursion on note-free inputs. -/
theorem layoutRecursiveB_eq_of_noNotes (exactIds : List String) (outerFuel : Nat)
    (fuel : Nat) (inp : Input) (o : Options) (h : attachmentsOf inp.boxes = []) :
    layoutRecursiveB (layoutNotes (fun ids s => layoutRIds ids (reindexRegionSets [] s) s) exactIds outerFuel)
      fuel inp o =
      layoutRecursiveB (layoutX exactIds) fuel inp o := by
  induction fuel generalizing inp o with
  | zero =>
    simp only [layoutRecursiveB]
    exact baseRN_eq_baseX _ _ _ _ h
  | succ fuel ih =>
    cases hfind : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none =>
      simp only [layoutRecursiveB, hfind]
      exact baseRN_eq_baseX _ _ _ _ h
    | some group =>
      have hchild_no : attachmentsOf
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes = [] :=
        attachmentsOf_selectInput _ _ _ h
      have hchild_eq : layoutRecursiveB
          (layoutNotes (fun ids s => layoutRIds ids (reindexRegionSets [] s) s) exactIds outerFuel)
          fuel (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } =
          layoutRecursiveB (layoutX exactIds)
          fuel (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } :=
        ih _ _ hchild_no
      have hparent_no_all : ∀ (P : Params) (titleLines : List Measure.Line) (child : FamilyResult),
          attachmentsOf
            ({ (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)) with
              fixedSizes := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedSizes ++
                [(group.id,
                  childFrameSize group.direction P.clusterPad
                    (List.foldl (fun (width : Int) (line : Measure.Line) => max width line.width) 0 titleLines)
                    (max 1 ↑titleLines.length * P.lineH)
                    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩)],
              fixedChildren := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedChildren ++
                [(group.id, child.scene)],
              fixedAreas := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedAreas ++
                [(group.id, child.itemArea)] }).boxes
            = [] := by
        intro _ _ _
        simpa using attachmentsOf_selectInput _ _ _ h
      have hparent_eq_all : ∀ (P : Params) (titleLines : List Measure.Line) (child : FamilyResult),
          layoutRecursiveB
            (layoutNotes (fun ids s => layoutRIds ids (reindexRegionSets [] s) s) exactIds outerFuel)
            fuel
            ({ (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)) with
              fixedSizes := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedSizes ++
                [(group.id,
                  childFrameSize group.direction P.clusterPad
                    (List.foldl (fun (width : Int) (line : Measure.Line) => max width line.width) 0 titleLines)
                    (max 1 ↑titleLines.length * P.lineH)
                    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩)],
              fixedChildren := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedChildren ++
                [(group.id, child.scene)],
              fixedAreas := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedAreas ++
                [(group.id, child.itemArea)] })
            o =
            layoutRecursiveB (layoutX exactIds)
            fuel
            ({ (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)) with
              fixedSizes := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedSizes ++
                [(group.id,
                  childFrameSize group.direction P.clusterPad
                    (List.foldl (fun (width : Int) (line : Measure.Line) => max width line.width) 0 titleLines)
                    (max 1 ↑titleLines.length * P.lineH)
                    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩)],
              fixedChildren := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedChildren ++
                [(group.id, child.scene)],
              fixedAreas := (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedAreas ++
                [(group.id, child.itemArea)] })
            o :=
        fun P titleLines child => ih _ _ (hparent_no_all P titleLines child)
      simp only [layoutRecursiveB, hfind]
      simp [hchild_eq, hparent_eq_all]
end PipelineImpl

/-- The state family with no regions and no side notes runs the exact family. -/
theorem state_reduces_exact (exactIds : List String) (sets : List ModelRegionSet)
    (inp : Input) (o : Options) (r : FamilyResult)
    (hfam : layoutFamilyRN exactIds sets inp o = .ok r)
    (hreg : RegionImpl.graphRegions inp sets = .ok [])
    (hnotes : PipelineImpl.attachmentsOf inp.boxes = []) :
    layoutFamilyX exactIds inp o = .ok r := by
  have hRN : layoutFamilyRN exactIds sets inp o =
      layoutFamilyB
        (PipelineImpl.layoutNotes
          (fun ids s => PipelineImpl.layoutRIds ids (PipelineImpl.reindexRegionSets [] s) s)
          exactIds (inp.boxes.length + 1)) inp o := by
    simp only [layoutFamilyRN, hreg]
  have hrec : PipelineImpl.layoutRecursiveB
        (PipelineImpl.layoutNotes
          (fun ids s => PipelineImpl.layoutRIds ids (PipelineImpl.reindexRegionSets [] s) s)
          exactIds (inp.boxes.length + 1))
        (inp.boxes.length + 1) inp o =
        PipelineImpl.layoutRecursiveB (PipelineImpl.layoutX exactIds) (inp.boxes.length + 1) inp o :=
    PipelineImpl.layoutRecursiveB_eq_of_noNotes _ _ _ _ _ hnotes
  have hfam_eq : layoutFamilyB
        (PipelineImpl.layoutNotes
          (fun ids s => PipelineImpl.layoutRIds ids (PipelineImpl.reindexRegionSets [] s) s)
          exactIds (inp.boxes.length + 1)) inp o =
        layoutFamilyB (PipelineImpl.layoutX exactIds) inp o := by
    simp only [layoutFamilyB, hrec]
  rw [hRN] at hfam
  rw [hfam_eq] at hfam
  exact hfam
end Layered
end Elegant
