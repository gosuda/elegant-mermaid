import Elegant.GridArchitectureValidity
import Elegant.Kinds.ArchitectureRouteClearance

set_option autoImplicit false

namespace Elegant.Kinds.Architecture

/-! ### Assembling the hard constraints for the architecture adapter

Clauses C1 and C4 (`Grid.Architecture.build_scene_C1`, `build_scene_C4`), C5
(`Grid.Architecture.layout_scene_C5`), and C7 (`architecture_c7`) are proved from a
successful `layout`. The remaining clauses C2, C3, C6, C8a, and C8b are still open; this
theorem takes each one as an explicit hypothesis, each stated exactly as the
corresponding conjunct of `HardConstraints result.scene.layoutDump`, so a caller that
discharges them obtains the full validity statement `grid_valid_of_members` expects. -/

/-- From the proved clauses C1, C4, C5, and C7 of a successful architecture layout,
together with the still-open clauses C2, C3, C6, C8a, and C8b as hypotheses, the layout
dump satisfies every hard constraint. -/
theorem architecture_valid_of_clauses {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (h : layout m = .ok result)
    (hC2 : _root_.Validator.C2 result.scene.layoutDump)
    (hC3 : _root_.Validator.C3 result.scene.layoutDump)
    (hC6 : _root_.Validator.C6 result.scene.layoutDump)
    (hC8a : _root_.Validator.C8a result.scene.layoutDump)
    (hC8b : _root_.Validator.C8b result.scene.layoutDump) :
    _root_.HardConstraints result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := Grid.Architecture.public_layout_dump m result h
  have hC1 := Grid.Architecture.build_scene_C1 m scene capped built
  have hC4 := Grid.Architecture.build_scene_C4 m scene capped built
  have hC5 := Grid.Architecture.layout_scene_C5 m result hwf h
  have hC7 := architecture_c7 m result hwf hlim h
  rw [dump] at hC2 hC3 hC5 hC6 hC7 hC8a hC8b
  rw [dump]
  exact ⟨hC1, hC2, hC3, hC4, hC5, hC6, hC7, ⟨hC8a, hC8b⟩⟩

end Elegant.Kinds.Architecture
