import Elegant.Layered.FamilyAssembly
import Elegant.Kinds.ClassFacts
import Elegant.Kinds.Er
import Elegant.Kinds.C4
import Elegant.Kinds.Requirement
import Elegant.Kinds.Agentflow
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.LayeredAdmission
import ElegantGeometry.Validator
set_option autoImplicit false

/-! Validity of the layered family kind adapters.

Each kind adapter below answers `.error (.geometry .domain)` unless the layered
`Input` it builds is admissible (`Layered.layeredAdmissibleB`): every box id is
nonempty, no box id names a route id, every fixed-size box is exclusive, and every
fixed size has positive width and height. The guard is parity-neutral on real inputs
(engine-built models never hit it). `Layered.PipelineImpl.layoutFamily_valid_of_seams`
proves family validity, and `layoutFamily_check_of_seams`
is its `Validator.check` form. Each `*_valid_of_seams` theorem below derives the admission
fact (`layeredAdmissibleB _ = true`) from a successful adapter run via `Layered.admit_ok`,
derives its input premises with `Layered.layeredAdmissibleB_spec`, and converts the
`Validator.check` conclusion to `HardConstraints` with `check_iff`. -/

namespace Elegant
namespace Kinds

/-- Family validity in `Validator.check` form: a successful family run whose
input has nonempty box ids, fixed-size room, and disjoint route ids passes the validator. -/
theorem layoutFamily_check_of_seams :
    ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
    (∀ b ∈ inp.boxes, b.id ≠ "") →
    Layered.PipelineImpl.InputFixedFit inp o →
    Layered.PipelineImpl.BoxRouteIdsDisjoint inp →
    Layered.layoutFamily inp o = .ok res →
    Validator.check res.scene.layoutDump = true :=
  fun _ _ _ hids hfix hdisj h =>
  (Validator.check_iff _).mpr
    (Layered.PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h)

/-- A successful Class layout ran the family on an admissible
input, so `Layered.layeredAdmissibleB_spec` supplies the family premises and the scene satisfies
the hard constraints. -/
theorem class_valid_of_seams
    {m : Model} {r : Layered.FamilyResult}
    (h : Class.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨sizes, res, hs, hadm, hf, hd, _⟩ := Class.layout_spec h
  obtain ⟨hids, hdisj, hfix, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  rw [hd]
  exact (Validator.check_iff _).mp
    (layoutFamily_check_of_seams _ _ _ hids hfix hdisj hf)

/-- A successful ER layout ran the family on an admissible
input, so `Layered.layeredAdmissibleB_spec` supplies the family premises and the scene satisfies
the hard constraints. -/
theorem er_valid_of_seams
    {m : Model} {r : Layered.FamilyResult}
    (h : Er.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨fixed, res, hs, hadm, hf, hd, _⟩ := Er.layout_spec h
  obtain ⟨hids, hdisj, hfix, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  rw [hd]
  exact (Validator.check_iff _).mp
    (layoutFamily_check_of_seams _ _ _ hids hfix hdisj hf)

/-- The C4 adapter re-routes the pinned relations only when the
validator accepts the result, redraws node outlines, and projects cell attachments, and neither
of the last two touches the layout dump. A successful layout ran the family on an admissible
input, so `Layered.layeredAdmissibleB_spec` supplies the family premises. -/
theorem c4_valid_of_seams
    {m : Model} {r : Layered.FamilyResult}
    (h : C4.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  unfold C4.layout at h
  cases ha : Layered.admit (C4.input m) (Layered.layoutFamily (C4.input m) m.options) with
  | error e => simp [ha] at h
  | ok res =>
    obtain ⟨hadm, hf⟩ := Layered.admit_ok ha
    obtain ⟨hids, hdisj, hfix, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
    cases hr : C4.rerouteEndpoints m res.scene with
    | error e => simp [ha, hr] at h
    | ok routed =>
      cases hs : C4.shapeScene m routed with
      | error e => simp [ha, hr, hs] at h
      | ok shaped =>
        simp only [ha, hr, hs, Except.ok.injEq] at h
        subst h
        show HardConstraints (shaped.projectCellAttachments (Common.routeMarkers m)).layoutDump
        rw [Scene.projectCellAttachments_layoutDump, C4.shapeScene_layoutDump hs]
        exact (Validator.check_iff _).mp (C4.rerouteEndpoints_valid hr
          (layoutFamily_check_of_seams _ _ _ hids hfix hdisj hf))

/-- A successful Requirement layout ran the family on an
admissible input, so `Layered.layeredAdmissibleB_spec` supplies the family premises and the
scene satisfies the hard constraints. -/
theorem requirement_valid_of_seams
    {m : Model} {r : Layered.FamilyResult}
    (h : Requirement.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨fixed, res, hs, hadm, hf, hd, _⟩ := Requirement.layout_spec h
  obtain ⟨hids, hdisj, hfix, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  rw [hd]
  exact (Validator.check_iff _).mp
    (layoutFamily_check_of_seams _ _ _ hids hfix hdisj hf)

/-- The Agentflow adapter fixes sizes, projects cell
attachments, and redraws node outlines, which keeps the layout dump. A successful layout ran
the family on an admissible input, so `Layered.layeredAdmissibleB_spec` supplies the family
premises. -/
theorem agentflow_valid_of_seams
    {m : Model} {r : Layered.FamilyResult}
    (h : Agentflow.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  unfold Agentflow.layout at h
  cases hs : Agentflow.sizes m with
  | error e => simp [hs] at h
  | ok fixed =>
    cases ha : Layered.admit (Agentflow.input m fixed)
        (Layered.layoutFamily (Agentflow.input m fixed) m.options) with
    | error e => simp [hs, ha] at h
    | ok res =>
      obtain ⟨hadm, hf⟩ := Layered.admit_ok ha
      obtain ⟨hids, hdisj, hfix, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
      cases hd : Agentflow.shapeScene m
          (res.scene.projectCellAttachments (Common.routeMarkers m)) with
      | error e => simp [hs, ha, hd] at h
      | ok scene =>
        simp only [hs, ha, hd, Except.ok.injEq] at h
        subst h
        show HardConstraints scene.layoutDump
        rw [Agentflow.shapeScene_layoutDump hd, Scene.projectCellAttachments_layoutDump]
        exact (Validator.check_iff _).mp (layoutFamily_check_of_seams _ _ _ hids
          hfix hdisj hf)

end Kinds
end Elegant
