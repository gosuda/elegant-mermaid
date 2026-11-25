import Elegant.Layered.Pipeline
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildFrameLiftResiduals
import Elegant.Layered.ExpandChildParentRouteClearProof
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.ExpandChildAncestryProof
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Parent-frame facts for one executed `expandChild` call.

`parentFixedDisjointGroup_of_parentC8a` proves `ExpandChildParentFixedDisjointGroup`
from the parent scene's own C8a clause plus two single-rect residuals
(positivity of the group frame, foreignness of the fixed box from the group
chain). `parentStrictMissGroup_of_frame_attached` proves
`ExpandChildParentStrictMissGroup` from the two split route parts
(frame-level for out-of-scope routes via `hitsRect` monotonicity, attached
part verbatim); both parts are single-scene residuals.

Probe evidence (`proofs/wip/Probe/ParentFixedMissProbe.lean`: nested three
deep, sibling groups, long titles, fixed sizes 0 and negative, crossing
routes, self-loops on groups, all four directions, vector and cell profiles):
no POS/ROLE/EXCL/FIXED/STRICT violations over all executed calls, including
all non-vacuous fixed instances.
-/

/-- The expanded group is not a fixed entry of the call input: the recursion
selects groups with `!fixedSizes.any`. -/
private theorem pfm_group_not_fixed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
  obtain ⟨_, hfind, _, _, _, _⟩ := hctx
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨_, hnotfixed⟩ := hpred
  simpa using hnotfixed

/-- A fixed entry names a different id than the expanded group. -/
private theorem pfm_fixed_ne_group
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} {g : ModelBox}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hg : ∃ _entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) :
    g.id ≠ group.id := by
  have hnf := pfm_group_not_fixed hctx
  obtain ⟨entry, hentry⟩ := hg
  intro heq
  have hentry' : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = some entry := by
    rwa [heq] at hentry
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnf)
  rw [hentry'] at hnone
  cases hnone

/-- The located parent frame carries the group id. -/
private theorem pfm_frame_id_eq {group : ModelBox} {parent : FamilyResult}
    {frame : Box}
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.id = group.id := by
  simpa using List.find?_some hframe

/-- The located frame has group role and the group is isolated from other
parent boxes' ancestor chains (from the proved structure + ancestry). -/
private theorem pfm_frame_role_isolation
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} {frame : Box}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.role = "group" ∧
      (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
        group.id ∉ parent.scene.layoutDump.ancestors pb.id) := by
  have hanc := stepC8aAncestry_holds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams
  obtain ⟨_, _, _, _, hrole, _, _, hiso⟩ :=
    expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hanc frame titleLines _ _ hframe rfl rfl hparams.2.2
  exact ⟨hrole, hiso⟩

/-- Fixed-disjoint restatement: the group frame is disjoint from every other
fixed frame in the parent scene, from the parent C8a clause. The positivity
and foreign-chain residuals are single-rect / single-chain facts that pass
the wide probe. -/
theorem parentFixedDisjointGroup_of_parentC8a
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult) (g : ModelBox) (gFrame frame : Box)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (_hg : ∃ _entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry)
    (hgFrame : parent.scene.boxes.find? (fun box => box.id == g.id) = some gFrame)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hC8a : Validator.C8a parent.scene.layoutDump)
    (hpos : 0 < frame.rect.w ∧ 0 < frame.rect.h)
    (hforeign : g.id ∉ parent.scene.layoutDump.ancestors group.id) :
    ExpandChildParentFixedDisjointGroup frame gFrame := by
  have hne : g.id ≠ group.id :=
    pfm_fixed_ne_group hctx _hg
  have hfid := pfm_frame_id_eq hframe
  obtain ⟨hrole, hiso⟩ :=
    pfm_frame_role_isolation hexpand hframed hctx hparams hframe
  have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
    List.mem_of_find?_eq_some hframe
  have hgMem : gFrame ∈ parent.scene.layoutDump.boxes :=
    List.mem_of_find?_eq_some hgFrame
  have hneBox : gFrame.id ≠ frame.id := by
    have hgId : gFrame.id = g.id := by simpa using List.find?_some hgFrame
    rw [hgId, hfid]
    exact hne
  have h1 : frame.id ∉ parent.scene.layoutDump.ancestors gFrame.id := by
    rw [hfid]
    have hgId : gFrame.id = g.id := by simpa using List.find?_some hgFrame
    have hne' : gFrame.id ≠ group.id := by rw [hgId]; exact hne
    exact hiso gFrame (List.mem_of_find?_eq_some hgFrame) hne'
  have h2 : gFrame.id ∉ parent.scene.layoutDump.ancestors frame.id := by
    have hgId : gFrame.id = g.id := by simpa using List.find?_some hgFrame
    rw [hgId, hfid]
    exact hforeign
  exact ⟨hC8a frame hframeMem hrole gFrame hgMem hneBox h1 h2, hpos.1, hpos.2⟩

/-- Strict-miss restatement: every parent route misses every strict interior
rect of the group frame, from the frame-level part (out-of-scope routes miss
the frame itself, transported inward by `hitsRect` monotonicity) and the
attached part (verbatim). -/
theorem parentStrictMissGroup_of_frame_attached
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hFrame : ExpandChildParentRouteFrameClear group parent)
    (hAtt : ExpandChildParentRouteAttachedClear group parent) :
    ExpandChildParentStrictMissGroup group parent := by
  intro frame hfind pr hpr r hSI
  by_cases hfrom : pr.fromId = group.id
  · exact hAtt frame hfind pr hpr (Or.inl hfrom) r hSI
  · by_cases hto : pr.toId = group.id
    · exact hAtt frame hfind pr hpr (Or.inr hto) r hSI
    · exact parentRoute_outside_inner hFrame hfind hpr hfrom hto hSI

end PipelineImpl
end Layered
end Elegant
