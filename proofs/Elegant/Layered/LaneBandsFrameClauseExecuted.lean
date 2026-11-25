import Elegant.Layered.LaneBandsFrameClause
import Elegant.Layered.LaneBandsCoverageProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-- C8a survives pinning for an executed swimlane layout. Every premise of
`pinBands_c8a` is discharged from the executed run except the scene-parents
bridge `PinSceneParents`, which is stated identically to the kept-clear lane's
`PinSceneParents` so one proof serves both: model nodup from `WellFormed`,
model nonempty from `hNeModel`, scene nodup/nonempty from `layoutFamily_ids`
plus the swimlane input keeping model boxes, and coverage from
`swimlane_pinBoxCoverage`. The base scene's C8a clause and the pinning run are
per-run premises, as is the spacing value. -/
theorem swimlane_pinBands_c8a {m : Model} {base : FamilyResult} {pinned : Scene}
    {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned)
    (hbase : Validator.C8a base.scene.layoutDump)
    (hadm : NestedInLane m.boxes)
    (hWf : WellFormed m)
    (hNeModel : ∀ b ∈ m.boxes, b.id ≠ "")
    (hParents : PinSceneParents m.boxes base.scene
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes))) :
    Validator.C8a pinned.layoutDump := by
  have hNodupS : (base.scene.boxes.map fun b => b.id).Nodup := by
    have hids := (layoutFamily_ids hfam).1
    rw [hids]
    exact Model.boxIds_nodup hWf
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" := by
    intro b hb
    have hids := (layoutFamily_ids hfam).1
    have hmem : b.id ∈ (Kinds.Swimlane.input m).boxes.map (fun b => b.id) := by
      rw [← hids]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hmem
    have hmb' : mb ∈ m.boxes := hmb
    have hEq : b.id = mb.id := hid.symm
    rw [hEq]
    exact hNeModel mb hmb'
  have hcover : ∀ sp' : Spacing, spacingOf m.options.profile = .ok sp' →
      PinBoxCoverage m.boxes base.scene (Axis.ofDirection m.options.direction)
        sp' := by
    intro sp' hsp'
    have hEq : sp' = sp := by
      have h := hsp.symm.trans hsp'
      simp only [Except.ok.injEq] at h
      exact h.symm
    subst hEq
    exact swimlane_pinBoxCoverage hfam hsp' hadm
  have hpar : ∀ sp' : Spacing, ∀ bands : List Band,
      spacingOf m.options.profile = .ok sp' →
      bands = layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
        sp' (lanesOf m.boxes) →
      PinSceneParents m.boxes base.scene bands := by
    intro sp' bands hsp' hb
    have hEq : sp' = sp := by
      have h := hsp.symm.trans hsp'
      simp only [Except.ok.injEq] at h
      exact h.symm
    subst hEq
    rw [hb]
    exact hParents
  exact pinBands_c8a hbase (Model.boxIds_nodup hWf) hNeModel hNodupS hNoEmpty
    hcover hpar hpin

end LaneBands
end Layered
end Elegant
