import Elegant.Layered.FamilyAssembly
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.StatePipeline
import Elegant.Kinds.State
import Elegant.Kinds.StateRegions
import Elegant.Kinds.StateValidExact
import ElegantGeometry.Validator

set_option autoImplicit false
/-! State validity from the layered family result.

The adapter feeds the model boxes, routes, labels, exact pseudo-state sizes, and
concurrent-region sets verbatim to the region-and-note family entry
`Layered.layoutFamilyRN`, projects cell attachments, redraws pseudo-state symbols
and note frames (`State.decorate`), then paints concurrent-region dividers
(`StateRegions.paintRegions`). The family call runs under `Layered.admit` on the
built input, so a successful run yields `Layered.layeredAdmissibleB` truth
(`layout_spec`); the id, disjointness, and fit premises are derived from it via
`Layered.layeredAdmissibleB_spec`, and no interim premises remain. Projection,
symbol redraw, and divider painting rewrite the display list only, so they
preserve the layout dump (proved below); the family run's validity is the
transfer premise `state_valid_of_family`, discharged for exact inputs by
`state_valid_of_exactSeams`. -/

namespace Elegant
namespace Kinds
namespace State

/-- Symbol and note redraw touches the display list only. -/
theorem decorate_layoutDump {m : Model} {s s' : Scene}
    (h : decorate m s = .ok s') :
    s'.layoutDump = s.layoutDump := by
  unfold decorate at h
  cases hm : s.items.mapM (decorateGroup m s) with
  | error e => rw [hm] at h; simp at h
  | ok items =>
    rw [hm] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl

/-- One region set clears its region groups and inserts dividers: display list only. -/
theorem paintRegionSet_layoutDump {m : Model} {s s' : Scene}
    {set : ModelRegionSet} {inset : Int}
    (h : StateRegions.paintRegionSet m s set inset = .ok s') :
    s'.layoutDump = s.layoutDump := by
  unfold StateRegions.paintRegionSet at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst h
          rfl

theorem paintRegions_fold_layoutDump (m : Model) (sets : List ModelRegionSet)
    (inset : Int) {s s' : Scene}
    (h : sets.foldlM (fun s set => StateRegions.paintRegionSet m s set inset) s
      = .ok s') :
    s'.layoutDump = s.layoutDump := by
  revert s h
  induction sets with
  | nil =>
    intro s h
    have hok : Except.ok s = Except.ok s' := h
    simp only [Except.ok.injEq] at hok
    subst hok
    rfl
  | cons set rest ih =>
    intro s h
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    cases hstep : StateRegions.paintRegionSet m s set inset with
    | error e => simp [hstep] at h
    | ok mid =>
      simp only [hstep] at h
      exact (ih h).trans (paintRegionSet_layoutDump hstep)

/-- Painting all dividers touches the display list only. -/
theorem paintRegions_layoutDump {m : Model} {s s' : Scene}
    (h : StateRegions.paintRegions m s = .ok s') :
    s'.layoutDump = s.layoutDump := by
  unfold StateRegions.paintRegions at h
  by_cases hempty : m.regionSets.isEmpty = true
  · simp only [hempty, ↓reduceIte] at h
    have hok : Except.ok s = Except.ok s' := h
    simp only [Except.ok.injEq] at hok
    subst hok
    rfl
  · simp only [hempty] at h
    exact paintRegions_fold_layoutDump m _ _ h

/-- The adapter's scene has the family scene's dump; only the display list differs.
A successful run also yields the admission guard on the built input, via
`Layered.admit_ok` on the guarded family call. -/
theorem layout_spec {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) :
    ∃ res, Layered.layeredAdmissibleB (input m (sizes m)) = true ∧
      Layered.layoutFamilyRN ((sizes m).map (·.1)) m.regionSets
        (input m (sizes m)) m.options = .ok res ∧
      r.scene.layoutDump = res.scene.layoutDump := by
  unfold layout at h
  cases ha : Layered.admit (input m (sizes m)) (Layered.layoutFamilyRN
      ((sizes m).map (·.1)) m.regionSets (input m (sizes m)) m.options) with
  | error e =>
    rw [ha] at h
    simp at h
  | ok res =>
    rw [ha] at h
    obtain ⟨hadm, hf⟩ := Layered.admit_ok ha
    dsimp only at h
    cases hd : decorate m (res.scene.projectCellAttachments (Common.routeMarkers m)) with
    | error e =>
      rw [hd] at h
      simp at h
    | ok dscene =>
      rw [hd] at h
      dsimp only at h
      cases hp : StateRegions.paintRegions m dscene with
      | error e =>
        rw [hp] at h
        simp at h
      | ok pscene =>
        rw [hp] at h
        dsimp only at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨res, hadm, hf,
          (paintRegions_layoutDump hp).trans
            ((decorate_layoutDump hd).trans
              (Scene.projectCellAttachments_layoutDump _ _))⟩

theorem state_valid_of_family {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r)
    (hfam : ∀ res, Layered.layoutFamilyRN ((sizes m).map (·.1)) m.regionSets
      (input m (sizes m)) m.options = .ok res →
      HardConstraints res.scene.layoutDump) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨res, _, hf, hd⟩ := layout_spec h
  rw [hd]
  exact hfam res hf

/-- State validity from the exact seams: for a model with no regions and no
notes, the family premise of `state_valid_of_family` follows from
`state_family_valid_of_exactSeams`, with the admission guard recovered from the
successful run by `layout_spec`. -/
theorem state_valid_of_exactSeams {m : Model} {r : Layered.FamilyResult}
    (R : Usecase.ExactSeams ((sizes m).map (·.1)))
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hreg : Layered.RegionImpl.graphRegions (input m (sizes m)) m.regionSets
      = .ok [])
    (hnotes : Layered.PipelineImpl.attachmentsOf (input m (sizes m)).boxes = [])
    (h : layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  apply state_valid_of_family h
  intro res hf
  obtain ⟨_, hadm, _, _⟩ := layout_spec h
  exact (Validator.check_iff _).mp
    (state_family_valid_of_exactSeams R hadm hwf hlim hf hreg hnotes)

end State

end Kinds

end Elegant
