import Elegant.Layered.FamilyAssembly
import Elegant.Kinds.ClassFacts
import Elegant.Kinds.Er
import Elegant.Kinds.C4
import Elegant.Kinds.Requirement
import Elegant.Kinds.Agentflow
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import ElegantGeometry.Validator
set_option autoImplicit false

/-! Seam adapters for the layered family kinds.

`Layered.PipelineImpl.layoutFamily_valid_of_seams` proves family validity modulo the
`LayeredSeams` record, under input premises: every box id is nonempty (`modelWellFormed`
admits an empty box id, while the C2 merge of the recursion needs nonempty ids), fixed-size
entries leave room for labeled boxes (`InputFixedFit`), and no box id names a route id
(`BoxRouteIdsDisjoint`).  Each kind adapter below feeds its model's boxes verbatim to
`Layered.layoutFamily` (`input` sets `boxes := m.boxes`), so the box-id premises are stated
on the kind's model and cannot be dropped for any of these kinds; no decoder in this library
supplies them.  These theorems replace the unconditional family hypothesis `hfam` of the
per-kind `layout_valid_of_family` statements and convert the `Validator.check` conclusion
to `HardConstraints` with `check_iff`. -/

namespace Elegant
namespace Kinds

/-- Family validity in `Validator.check` form, modulo the seams: a successful family run whose
input has nonempty box ids, fixed-size room, and disjoint route ids passes the validator. -/
theorem layoutFamily_check_of_seams (S : Layered.PipelineImpl.LayeredSeams) :
    ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
    (∀ b ∈ inp.boxes, b.id ≠ "") →
    Layered.PipelineImpl.InputFixedFit inp o →
    Layered.PipelineImpl.BoxRouteIdsDisjoint inp →
    Layered.layoutFamily inp o = .ok res →
    Validator.check res.scene.layoutDump = true :=
  fun _ _ _ hids hfix hdisj h =>
  (Validator.check_iff _).mpr
    (Layered.PipelineImpl.layoutFamily_valid_of_seams S hids hfix hdisj h)

/-- Class validity from the family seams: the adapter changes sizes and the display list only,
so a successful layout of a model with nonempty box ids satisfies the hard constraints. -/
theorem class_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfix : ∀ fixed, Class.classSizes m = .ok fixed →
      Layered.PipelineImpl.InputFixedFit (Class.input m fixed) m.options)
    (hdisj : ∀ fixed, Class.classSizes m = .ok fixed →
      Layered.PipelineImpl.BoxRouteIdsDisjoint (Class.input m fixed))
    (h : Class.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨sizes, res, hs, hf, hd, _⟩ := Class.layout_spec h
  rw [hd]
  exact (Validator.check_iff _).mp
    (layoutFamily_check_of_seams S _ _ _ hids (hfix sizes hs) (hdisj sizes hs) hf)

/-- ER validity from the family seams: the adapter changes sizes and the display list only,
so a successful layout of a model with nonempty box ids satisfies the hard constraints. -/
theorem er_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfix : ∀ fixed, Er.sizes m = .ok fixed →
      Layered.PipelineImpl.InputFixedFit (Er.input m fixed) m.options)
    (hdisj : ∀ fixed, Er.sizes m = .ok fixed →
      Layered.PipelineImpl.BoxRouteIdsDisjoint (Er.input m fixed))
    (h : Er.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨fixed, res, hs, hf, hd, _⟩ := Er.layout_spec h
  rw [hd]
  exact (Validator.check_iff _).mp
    (layoutFamily_check_of_seams S _ _ _ hids (hfix fixed hs) (hdisj fixed hs) hf)

/-- C4 validity from the family seams: the adapter re-routes the pinned relations only when the
validator accepts the result, redraws node outlines, and projects cell attachments, and neither
of the last two touches the layout dump. -/
theorem c4_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint (C4.input m))
    (h : C4.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  unfold C4.layout at h
  cases hf : Layered.layoutFamily (C4.input m) m.options with
  | error e => simp [hf] at h
  | ok res =>
    cases hr : C4.rerouteEndpoints m res.scene with
    | error e => simp [hf, hr] at h
    | ok routed =>
      cases hs : C4.shapeScene m routed with
      | error e => simp [hf, hr, hs] at h
      | ok shaped =>
        simp only [hf, hr, hs, Except.ok.injEq] at h
        subst h
        show HardConstraints (shaped.projectCellAttachments (Common.routeMarkers m)).layoutDump
        rw [Scene.projectCellAttachments_layoutDump, C4.shapeScene_layoutDump hs]
        exact (Validator.check_iff _).mp (C4.rerouteEndpoints_valid hr
          (layoutFamily_check_of_seams S _ _ _ hids
            (Layered.PipelineImpl.inputFixedFit_of_nil (inp := C4.input m) rfl)
            hdisj hf))

/-- Requirement validity from the family seams: the adapter changes sizes and the display list
only, so a successful layout of a model with nonempty box ids satisfies the hard constraints. -/
theorem requirement_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfix : ∀ fixed, Requirement.sizes m = .ok fixed →
      Layered.PipelineImpl.InputFixedFit (Requirement.input m fixed) m.options)
    (hdisj : ∀ fixed, Requirement.sizes m = .ok fixed →
      Layered.PipelineImpl.BoxRouteIdsDisjoint (Requirement.input m fixed))
    (h : Requirement.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨fixed, res, hs, hf, hd, _⟩ := Requirement.layout_spec h
  rw [hd]
  exact (Validator.check_iff _).mp
    (layoutFamily_check_of_seams S _ _ _ hids (hfix fixed hs) (hdisj fixed hs) hf)

/-- Agentflow validity from the family seams: the adapter fixes sizes, projects cell
attachments, and redraws node outlines, which keeps the layout dump. -/
theorem agentflow_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfix : ∀ fixed, Agentflow.sizes m = .ok fixed →
      Layered.PipelineImpl.InputFixedFit (Agentflow.input m fixed) m.options)
    (hdisj : ∀ fixed, Agentflow.sizes m = .ok fixed →
      Layered.PipelineImpl.BoxRouteIdsDisjoint (Agentflow.input m fixed))
    (h : Agentflow.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  unfold Agentflow.layout at h
  cases hs : Agentflow.sizes m with
  | error e => simp [hs] at h
  | ok fixed =>
    cases hf : Layered.layoutFamily (Agentflow.input m fixed) m.options with
    | error e => simp [hs, hf] at h
    | ok res =>
      cases hd : Agentflow.shapeScene m
          (res.scene.projectCellAttachments (Common.routeMarkers m)) with
      | error e => simp [hs, hf, hd] at h
      | ok scene =>
        simp only [hs, hf, hd, Except.ok.injEq] at h
        subst h
        show HardConstraints scene.layoutDump
        rw [Agentflow.shapeScene_layoutDump hd, Scene.projectCellAttachments_layoutDump]
        exact (Validator.check_iff _).mp (layoutFamily_check_of_seams S _ _ _ hids
          (hfix fixed hs) (hdisj fixed hs) hf)

end Kinds
end Elegant
