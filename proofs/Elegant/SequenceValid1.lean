import Elegant.SequenceDump

set_option autoImplicit false

/-! The final state of a checked sequence layout: the facts about the plan, the model, the walk
invariant, and the header clearance that the eight clauses of the validator read
(`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem Plan.build_m (m : Model) (pl : Plan) (h : Plan.build m = .ok pl) : pl.m = m := by
  unfold Plan.build at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

theorem restore_ids (m : Model) :
    (restoreFragmentShapes m).boxes.map (·.id) = m.boxes.map (·.id) := by
  unfold restoreFragmentShapes
  simp only [List.map_map]
  have h := List.zipIdx_map_fst 0 m.boxes
  calc _ = (m.boxes.zipIdx.map Prod.fst).map (·.id) := by
        rw [List.map_map]
        congr 1
        funext x
        simp only [Function.comp]
        split <;> rfl
    _ = m.boxes.map (·.id) := by rw [h]

/-- The facts that a passing layout leaves behind at the end of its walk. -/
structure FinFacts (pl : Plan) (cs : List Int) (steps : List Step) (w : Walk) (ck : CheckState)
    (E : List Ent) : Prop where
  wf : pl.Wf
  pf : PlanFacts pl
  fm : ModelFacts pl.m
  hcs : cs = columns pl steps
  inv : Inv pl (headerRects pl cs) (headerLabels pl (headerRects pl cs)) [] ck.placed w E
  rinv : RInv pl cs ⟨[], ck.placed, ck.routes⟩ w
  fin : finalOk pl ck = true
  hdr : headersOk pl cs = true
  plcls : PlacedCls pl ck.placed

theorem layoutOk_spec {model : Model} (hk : layoutOk model = true) {pl : Plan}
    (hp : Plan.build (restoreFragmentShapes model) = .ok pl) :
    ∃ ck, (decodeSteps (restoreFragmentShapes model).regionSets).foldlM (stepCheck pl)
        ⟨[], [], 0⟩ = some ck ∧ finalOk pl ck = true ∧
      headersOk pl (columns pl (decodeSteps (restoreFragmentShapes model).regionSets)) = true := by
  unfold layoutOk at hk
  simp only [hp] at hk
  cases hc : (decodeSteps (restoreFragmentShapes model).regionSets).foldlM (stepCheck pl)
      { stack := [], placed := [], routes := 0 } with
  | none => simp [hc] at hk
  | some ck =>
    simp only [hc, Bool.and_eq_true] at hk
    exact ⟨ck, rfl, hk.1, hk.2⟩

theorem layout_unfold {model : Model} {s : Scene} (h : layout model = .ok s) :
    ∃ pl w, Plan.build (restoreFragmentShapes model) = .ok pl ∧
      walk pl (columns pl (decodeSteps (restoreFragmentShapes model).regionSets))
        (decodeSteps (restoreFragmentShapes model).regionSets) = .ok w ∧
      s.layoutDump = dumpOf pl (columns pl (decodeSteps (restoreFragmentShapes model).regionSets)) w := by
  have hk := layout_admissible h
  unfold layout at h
  simp only [hk, ↓reduceIte] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hp : Plan.build (restoreFragmentShapes model) with
  | error e => simp [hp] at h
  | ok pl =>
    simp only [hp] at h
    cases hw : walk pl (columns pl (decodeSteps (restoreFragmentShapes model).regionSets))
        (decodeSteps (restoreFragmentShapes model).regionSets) with
    | error e => simp [hw] at h
    | ok w =>
      simp only [hw, Except.ok.injEq] at h
      subst h
      exact ⟨pl, w, rfl, hw, rfl⟩

theorem final_facts {model : Model} (hwf : modelWellFormed model = true) (hk : layoutOk model = true)
    {s : Scene} (h : layout model = .ok s) :
    ∃ pl steps cs w ck E, FinFacts pl cs steps w ck E ∧ s.layoutDump = dumpOf pl cs w := by
  obtain ⟨pl, w, hp, hw, hd⟩ := layout_unfold h
  obtain ⟨ck, hck, hfin, hhdr⟩ := layoutOk_spec hk hp
  have hpl := Plan.build_wf _ _ hp
  have hpf := Plan.build_facts _ _ hp
  have hm := Plan.build_m _ _ hp
  have hnd : (pl.m.boxes.map (·.id)).Nodup := by
    rw [hm, restore_ids]
    exact ids_nodup hwf
  have hfm : ModelFacts pl.m :=
    ⟨hnd, fun i hi => by
      obtain ⟨b, hb⟩ : ∃ b, pl.m.boxes[i]? = some b := ⟨pl.m.boxes[i], List.getElem?_eq_getElem hi⟩
      rw [boxId_of_getElem pl.m i b hb]
      exact (boxFinalOk_cls (finalOk_box hfin i b hb)).1⟩
  obtain ⟨E, hI, hR⟩ := walk_final hpl hpf hfm rfl hw hck
  have hpc : PlacedCls pl ck.placed :=
    foldCheck_placedCls hpf _ ⟨[], [], 0⟩ ck hck (fun i hi => by simp at hi)
  exact ⟨pl, _, _, w, ck, E, ⟨hpl, hpf, hfm, rfl, hI, hR, hfin, hhdr, hpc⟩, hd⟩

end Sequence
end Elegant
