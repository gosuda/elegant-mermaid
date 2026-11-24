import Elegant.Layered.FamilyAssembly
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered

/-- Canvas clause (C1) of a successful `layoutFamily` run, projected from
`PipelineImpl.layoutFamily_valid_of_seams` under its public premises: nonempty box ids,
fixed-size room, and box/route id disjointness. -/
theorem layoutFamily_c1 {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "") (hfix : PipelineImpl.InputFixedFit inp o)
    (hdisj : PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    Validator.C1 res.scene.layoutDump := by
  exact (PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h).1

/-- Exclusive-sibling clause (C2) of a successful `layoutFamily` run. -/
theorem layoutFamily_c2 {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "") (hfix : PipelineImpl.InputFixedFit inp o)
    (hdisj : PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    Validator.C2 res.scene.layoutDump := by
  exact (PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h).2.1

/-- Parent-containment clause (C3) of a successful `layoutFamily` run. -/
theorem layoutFamily_c3 {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "") (hfix : PipelineImpl.InputFixedFit inp o)
    (hdisj : PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    Validator.C3 res.scene.layoutDump := by
  exact (PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h).2.2.1

/-- Route-clearance clause (C6) of a successful `layoutFamily` run. -/
theorem layoutFamily_c6 {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "") (hfix : PipelineImpl.InputFixedFit inp o)
    (hdisj : PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    Validator.C6 res.scene.layoutDump := by
  exact (PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h).2.2.2.2.2.1

/-- Label-clearance clause (C7) of a successful `layoutFamily` run. -/
theorem layoutFamily_c7 {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "") (hfix : PipelineImpl.InputFixedFit inp o)
    (hdisj : PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    Validator.C7 res.scene.layoutDump := by
  exact (PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h).2.2.2.2.2.2.1

/-- Frame-clearance clause (C8) of a successful `layoutFamily` run. -/
theorem layoutFamily_c8 {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "") (hfix : PipelineImpl.InputFixedFit inp o)
    (hdisj : PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    Validator.C8 res.scene.layoutDump := by
  exact (PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj h).2.2.2.2.2.2.2

end Elegant.Layered
