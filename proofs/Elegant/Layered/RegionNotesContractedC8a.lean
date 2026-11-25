import Elegant.Layered.RegionNotesContractedRootPortfolio
import Elegant.Layered.RegionC8aGroupPlainCutover

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl.ContractedC8a

def rootBox (ids : List String) (b : Box) : Box :=
  { b with parent := rootParent ids b.parent }

def rootDump (d : LayoutDump) : LayoutDump :=
  { d with boxes := d.boxes.map (rootBox d.boxIds) }

private theorem rootDump_box (d : LayoutDump) (id : String) :
    (rootDump d).box? id = (d.box? id).map (rootBox d.boxIds) := by
  simp only [rootDump, LayoutDump.box?, List.find?_map] <;> rfl

private theorem absent_box (d : LayoutDump) (id : String) (h : id ∉ d.boxIds) :
    d.box? id = none := by
  apply List.find?_eq_none.mpr
  intro b hb hmatch
  exact h (List.mem_map.mpr ⟨b, hb, beq_iff_eq.mp hmatch⟩)

private theorem missing_ancestors (d : LayoutDump) (id : String) (h : d.box? id = none) (fuel : Nat) :
    LayoutDump.ancestors.go d fuel id = [] := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [LayoutDump.ancestors.go, h]

private theorem rootDump_ancestor_live (d : LayoutDump) (id : String) (hLive : id ∈ d.boxIds) :
    ∀ (fuel : Nat) (start : String),
      id ∈ LayoutDump.ancestors.go (rootDump d) fuel start ↔
        id ∈ LayoutDump.ancestors.go d fuel start := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
    intro start
    simp only [LayoutDump.ancestors.go, rootDump_box]
    cases he : d.box? start with
    | none => rfl
    | some b =>
      change (id ∈ (if rootParent d.boxIds b.parent = "" then [] else
        rootParent d.boxIds b.parent :: LayoutDump.ancestors.go (rootDump d) fuel
          (rootParent d.boxIds b.parent))) ↔
        id ∈ (if b.parent = "" then [] else b.parent :: LayoutDump.ancestors.go d fuel b.parent)
      by_cases hn : b.parent = ""
      · simp only [hn, rootParent_empty, ↓reduceIte]
      by_cases hm : b.parent ∈ d.boxIds
      · rw [rootParent, ite_eq_left hm]
        simp only [ite_eq_right hn, List.mem_cons, ih]
      have hne : id ≠ b.parent := fun he => hm (he ▸ hLive)
      rw [rootParent, ite_eq_right hm, ite_eq_right hn]
      simp [missing_ancestors d b.parent (absent_box d b.parent hm) fuel, hne]

private theorem rootDump_c8a (d : LayoutDump) (h : Validator.C8a (rootDump d)) : Validator.C8a d := by
  intro g hg hrole b hb hne hgb hbg
  have hgb' : g.id ∉ (rootDump d).ancestors b.id :=
    fun hm => hgb ((rootDump_ancestor_live d g.id (List.mem_map_of_mem hg) d.boxes.length b.id).mp
      (by simpa only [LayoutDump.ancestors, rootDump, List.length_map] using hm))
  have hbg' : b.id ∉ (rootDump d).ancestors g.id :=
    fun hm => hbg ((rootDump_ancestor_live d b.id (List.mem_map_of_mem hb) d.boxes.length g.id).mp
      (by simpa only [LayoutDump.ancestors, rootDump, List.length_map] using hm))
  exact h (rootBox d.boxIds g) (List.mem_map_of_mem hg) hrole
    (rootBox d.boxIds b) (List.mem_map_of_mem hb) hne hgb' hbg'

private theorem ancestors_eq_of_boxes_eq {d e : LayoutDump} (h : d.boxes = e.boxes) (id : String) :
    d.ancestors id = e.ancestors id := by
  have hgo : ∀ (fuel : Nat) (start : String),
      LayoutDump.ancestors.go d fuel start = LayoutDump.ancestors.go e fuel start := by
    intro fuel
    induction fuel with
    | zero => intro start; rfl
    | succ n ih =>
      intro start
      have hf : d.box? start = e.box? start := by simp only [LayoutDump.box?, h]
      simp only [LayoutDump.ancestors.go, hf]
      cases e.box? start with
      | none => rfl
      | some b =>
        by_cases hp : b.parent = ""
        · simp only [hp, ↓reduceIte]
        · simp only [ite_eq_right hp, ih]
  unfold LayoutDump.ancestors
  rw [h]
  exact hgo _ id

theorem c8a_of_boxes_eq {d e : LayoutDump} (h : d.boxes = e.boxes)
    (hc : Validator.C8a d) : Validator.C8a e := by
  intro g hg hrole b hb hne hgb hbg
  exact hc g (h.symm ▸ hg) hrole b (h.symm ▸ hb) hne
    (by rwa [ancestors_eq_of_boxes_eq h]) (by rwa [ancestors_eq_of_boxes_eq h])

private theorem sceneOf_boxIds (P : Params) (inp : Input) (o : Options) (lines : List (List Measure.Line))
    (acc : Acc) (measured : List MeasuredLabel) :
    (sceneOf P inp o lines acc measured).layoutDump.boxIds = inp.boxes.map (·.id) := by
  simp only [sceneOf, Scene.layoutDump, LayoutDump.boxIds, List.map_map]
  change inp.boxes.zipIdx.map (fun q => q.1.id) = _
  rw [← show (inp.boxes.zipIdx.map Prod.fst).map ModelBox.id =
    inp.boxes.zipIdx.map (fun q => q.1.id) from List.map_map]
  rw [List.zipIdx_map_fst]

private theorem sceneOf_rootInput_boxes (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel) :
    (sceneOf P (rootInput inp) o lines acc measured).layoutDump.boxes =
      (rootDump (sceneOf P inp o lines acc measured).layoutDump).boxes := by
  rw [show (rootDump (sceneOf P inp o lines acc measured).layoutDump).boxes =
    (sceneOf P inp o lines acc measured).layoutDump.boxes.map
      (rootBox (sceneOf P inp o lines acc measured).layoutDump.boxIds) from rfl,
      sceneOf_boxIds]
  simp only [sceneOf, Scene.layoutDump, rootInput, List.zipIdx_map, List.map_map] <;> rfl

private theorem rootLayout_success {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {r : FamilyResult}
    (h : layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok r) :
    ∃ r', layoutRIds exactIds (reindexRegionSets idSets (rootInput inp)) (rootInput inp) o = .ok r' ∧
      r'.scene.layoutDump.boxes = (rootDump r.scene.layoutDump).boxes := by
  obtain ⟨P, metric, lines, measured, graph0, graph, mid, packed, hP, hm, hl, hmeasure,
    hg0, hg, hcomponents, hp, hs, _, _⟩ := layoutRIds_success_phases h
  let rootScene := sceneOf P (rootInput inp) o lines packed measured
  have hmeasureRoot : measureLabels P metric
      (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
      (rootInput inp) o.direction = .ok measured := hmeasure
  let finish (input : Input) (acc : Acc) : Except LayoutError FamilyResult :=
    let scene := sceneOf P input o lines acc measured
    if I32_MAX < scene.canvas.w ∨ I32_MAX < scene.canvas.h then .error .overflow
    else .ok ⟨scene, acc.budget, acc.parts.foldl (fun area part => area + part.2.area) 0⟩
  have htail (input : Input) :=
    (congrArg (fun (run : Except LayoutError Acc) =>
      run.bind (fun acc => (packAcc P o acc).bind (finish input))) hcomponents).trans
      (congrArg (fun (run : Except LayoutError Acc) => run.bind (finish input)) hp)
  have hcanvas : ¬ (I32_MAX < rootScene.canvas.w ∨ I32_MAX < rootScene.canvas.h) := by
    intro hbad
    have hbad' : I32_MAX < (sceneOf P inp o lines packed measured).canvas.w ∨
        I32_MAX < (sceneOf P inp o lines packed measured).canvas.h := hbad
    have hrun : layoutRIds exactIds (reindexRegionSets idSets inp) inp o = finish inp packed := by
      simp only [layoutRIds, hP, hm, hl, hmeasure, hg0, hg, bind, Except.bind]
      exact htail inp
    have herror : finish inp packed = .error .overflow := ite_eq_left hbad'
    cases herror.symm.trans (hrun.symm.trans h)
  refine ⟨⟨rootScene, packed.budget, packed.parts.foldl (fun area part => area + part.2.area) 0⟩, ?_, ?_⟩
  · have hkind : (rootInput inp).kind = inp.kind := rfl
    have hroutes : (rootInput inp).routes = inp.routes := rfl
    have hcanvas' : ¬ (I32_MAX < (sceneOf P (rootInput inp) o lines packed measured).canvas.w ∨
        I32_MAX < (sceneOf P (rootInput inp) o lines packed measured).canvas.h) := hcanvas
    have hlabels : (rootInput inp).labels = inp.labels := rfl
    have hrun : layoutRIds exactIds (reindexRegionSets idSets (rootInput inp)) (rootInput inp) o =
        finish (rootInput inp) packed := by
      simp only [layoutRIds, hkind, hP, hm, rooted_boxLines, hl, hmeasureRoot, rooted_measuredGraph,
        hg0, rooted_exactGraph, hg, rooted_reindex, rooted_layoutComponent, rootInput_length,
        hroutes, hlabels, bind, Except.bind]
      exact htail (rootInput inp)
    exact hrun.trans (ite_eq_right hcanvas')
  · rw [hs]
    exact sceneOf_rootInput_boxes P inp o lines packed measured

end ContractedC8a

/-- Contracted C8a of the actual note run; the proof-only root projection does not enter admission. -/
theorem regionNotes_contractedC8aAligned {exactIds : List String}
    {idSets : List (String × List String)} (_fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids (reindexRegionSets idSets sub) sub opt)
      exactIds _fuel inp o res) (hwf : WellFormed (inputModel inp o))
    (hfr : framedParents inp = true) (_hparents : attachedNoteParents inp = true) :
    Validator.C8a e.contracted.scene.layoutDump := by
  have hc : layoutRIds (exactIds ++ e.layouts.map (·.top.id))
      (reindexRegionSets idSets e.contractedInput) e.contractedInput o = .ok e.contracted :=
    e.contracted_eq
  obtain ⟨r', h', hboxes⟩ := ContractedC8a.rootLayout_success (idSets := idSets) hc
  obtain ⟨hwf', hfr'⟩ := ContractedC8a.contracted_rooted_guards e hwf hfr
  have hC8 : Validator.C8a r'.scene.layoutDump :=
    flatC8aB_layoutRIds_reindex_closed (exactIds ++ e.layouts.map (·.top.id)) idSets _ o r'
      hwf' hfr' h'
  exact ContractedC8a.rootDump_c8a _ (ContractedC8a.c8a_of_boxes_eq hboxes hC8)

end Elegant.Layered.PipelineImpl
