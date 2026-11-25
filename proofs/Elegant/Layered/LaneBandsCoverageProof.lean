import Elegant.Layered.LaneBandsCoverage
import Elegant.Layered.PipelineFacts
import Elegant.Kinds.Swimlane

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-- Admission: every nested box sits in some lane. Top-level boxes need no
    condition: a top-level group is itself a lane band, and `layBands` gives
    the top-level nodes their own loose band. The probe
    (`wip/Probe/PinCoverageProbe.lean`) evaluates `cov=true adm=true` on all
    18 executed swimlane layouts and `family-error` on the two models that
    violate this shape (nested under a loose node, dangling parent). -/
def NestedInLane (boxes : List ModelBox) : Prop :=
  ∀ b ∈ boxes, b.parent ≠ "" → ∃ lane ∈ lanesOf boxes, inLane boxes b.id lane = true

theorem laneBand_id (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lane : String) (start : Int) :
    (laneBand boxes s axis sp lane start).id = lane := rfl

theorem laneBand_members (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lane : String) (start : Int) :
    (laneBand boxes s axis sp lane start).members =
      (boxes.filter fun b => inLane boxes b.id lane).map (·.id) := rfl

theorem looseBand_members (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (loose : List String) (start : Int) :
    (looseBand boxes s axis sp loose start).members = loose := by
  unfold looseBand
  split <;> rfl

theorem mem_lanesOf_of_group {b : ModelBox} {boxes : List ModelBox}
    (hrole : b.role = .group) (hpar : b.parent = "") (hmem : b ∈ boxes) :
    b.id ∈ lanesOf boxes := by
  unfold lanesOf
  refine List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hmem, ?_⟩, rfl⟩
  rw [hrole, hpar]
  simp

theorem mem_looseNodes_of_node {b : ModelBox} {boxes : List ModelBox}
    (hpar : b.parent = "") (hrole : b.role = .node) (hmem : b ∈ boxes) :
    b.id ∈ looseNodes boxes := by
  unfold looseNodes
  refine List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hmem, ?_⟩, rfl⟩
  rw [hpar, hrole]
  simp

theorem mem_filter_map_inLane {boxes : List ModelBox} {mb : ModelBox} {lane : String}
    (hmem : mb ∈ boxes) (h : inLane boxes mb.id lane = true) :
    mb.id ∈ (boxes.filter fun b => inLane boxes b.id lane).map (·.id) :=
  List.mem_map.mpr ⟨mb, List.mem_filter.mpr ⟨hmem, h⟩, rfl⟩

theorem layLanes_has_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    {lane : String} (lanes : List String) (h : lane ∈ lanes) (start : Int) :
    ∃ band ∈ layLanes boxes s axis sp lanes start, band.id = lane := by
  induction lanes generalizing start with
  | nil => simp at h
  | cons hd tl ih =>
    have heq : layLanes boxes s axis sp (hd :: tl) start =
        laneBand boxes s axis sp hd start ::
          layLanes boxes s axis sp tl (start + (laneBand boxes s axis sp hd start).thickness) := by
      simp only [layLanes]
    rw [List.mem_cons] at h
    rcases h with rfl | hmem
    · exact ⟨laneBand boxes s axis sp lane start,
        by rw [heq]; exact List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨band, hband, hid⟩ := ih hmem _
      exact ⟨band, by rw [heq]; exact List.mem_cons.mpr (Or.inr hband), hid⟩

theorem layLanes_has_member {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    {lanes : List String} {mb : ModelBox} {lane : String}
    (hmem : mb ∈ boxes) (hlane : lane ∈ lanes) (hin : inLane boxes mb.id lane = true)
    (start : Int) :
    ∃ band ∈ layLanes boxes s axis sp lanes start, mb.id ∈ band.members := by
  induction lanes generalizing start with
  | nil => simp at hlane
  | cons hd tl ih =>
    have heq : layLanes boxes s axis sp (hd :: tl) start =
        laneBand boxes s axis sp hd start ::
          layLanes boxes s axis sp tl (start + (laneBand boxes s axis sp hd start).thickness) := by
      simp only [layLanes]
    rw [List.mem_cons] at hlane
    rcases hlane with rfl | hmem2
    · refine ⟨laneBand boxes s axis sp lane start,
        by rw [heq]; exact List.mem_cons.mpr (Or.inl rfl), ?_⟩
      rw [laneBand_members]
      exact mem_filter_map_inLane hmem hin
    · obtain ⟨band, hband, hcov⟩ := ih hmem2 _
      exact ⟨band, by rw [heq]; exact List.mem_cons.mpr (Or.inr hband), hcov⟩

/-- Nonempty-loose unfolding of `layBands`: the lane bands followed by the loose band. -/
theorem layBands_append (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lanes : List String) (hf : (looseNodes boxes).isEmpty = false) :
    layBands boxes s axis sp lanes =
      layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) ++
        [looseBand boxes s axis sp (looseNodes boxes)
          (firstLaneStart s lanes axis +
            ((layLanes boxes s axis sp lanes (firstLaneStart s lanes axis)).map
              (·.thickness)).sum)] := by
  have hF : ((looseNodes boxes).isEmpty = true) = False := by simp [hf]
  simp only [layBands, hF, ↓reduceIte]

theorem layLanes_subset_layBands {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {band : Band}
    (h : band ∈ layLanes boxes s axis sp lanes (firstLaneStart s lanes axis)) :
    band ∈ layBands boxes s axis sp lanes := by
  by_cases hf : (looseNodes boxes).isEmpty = false
  · rw [layBands_append boxes s axis sp lanes hf]
    exact List.mem_append.mpr (Or.inl h)
  · have hnil : looseNodes boxes = [] := by
      revert hf
      cases hbb : looseNodes boxes with
      | nil => intro _; rfl
      | cons hd tl =>
        intro hf
        have hcon : (hd :: tl).isEmpty = false := rfl
        exact absurd hcon hf
    have heq : layBands boxes s axis sp lanes =
        layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) := by
      have h0 : (([] : List String).isEmpty) = true := rfl
      simp only [layBands, hnil, h0, ↓reduceIte]
    rw [heq]
    exact h

theorem loose_covers {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    {id : String} (hmem : id ∈ looseNodes boxes) :
    ∃ band ∈ layBands boxes s axis sp (lanesOf boxes), id ∈ band.members := by
  have hempty : looseNodes boxes ≠ [] := by
    intro hcon
    simp [hcon] at hmem
  have hf : (looseNodes boxes).isEmpty = false := by
    revert hempty
    cases hbb : looseNodes boxes with
    | nil => intro hempty; exact absurd rfl hempty
    | cons hd tl => intro _; rfl
  have hlay := layBands_append boxes s axis sp (lanesOf boxes) hf
  rw [hlay]
  refine ⟨looseBand boxes s axis sp (looseNodes boxes)
      (firstLaneStart s (lanesOf boxes) axis +
        (((layLanes boxes s axis sp (lanesOf boxes)
          (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)), ?_, ?_⟩
  · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  · rw [looseBand_members]
    exact hmem

theorem top_covered {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    {mb : ModelBox} (hmem : mb ∈ boxes) (hpar : mb.parent = "") :
    ∃ band ∈ layBands boxes s axis sp (lanesOf boxes),
      band.id = mb.id ∨ mb.id ∈ band.members := by
  cases hr : mb.role with
  | group =>
    have hmem2 : mb.id ∈ lanesOf boxes := mem_lanesOf_of_group hr hpar hmem
    obtain ⟨band, hband, hid⟩ :=
      layLanes_has_lane (lanesOf boxes) hmem2 (firstLaneStart s (lanesOf boxes) axis)
    exact ⟨band, layLanes_subset_layBands hband, Or.inl hid⟩
  | node =>
    have hmem2 : mb.id ∈ looseNodes boxes := mem_looseNodes_of_node hpar hr hmem
    obtain ⟨band, hband, hcov⟩ := loose_covers hmem2
    exact ⟨band, hband, Or.inr hcov⟩

theorem swimlane_pinBoxCoverage {m : Model} {base : FamilyResult} {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (_hsp : spacingOf m.options.profile = .ok sp)
    (hadm : NestedInLane m.boxes) :
    PinBoxCoverage m.boxes base.scene (Axis.ofDirection m.options.direction) sp := by
  intro b hb
  have hids := layoutFamily_ids hfam
  have hin : b.id ∈ (Kinds.Swimlane.input m).boxes.map (·.id) := by
    rw [← hids.1]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hin2 : b.id ∈ m.boxes.map (·.id) := hin
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hin2
  rw [← hid]
  by_cases hpar : mb.parent = ""
  · exact top_covered hmb hpar
  · obtain ⟨lane, hlane, hinlane⟩ := hadm mb hmb hpar
    obtain ⟨band, hband, hcov⟩ :=
      layLanes_has_member hmb hlane hinlane (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))
    exact ⟨band, layLanes_subset_layBands hband, Or.inr hcov⟩

end LaneBands
end Layered
end Elegant
