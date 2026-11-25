import Elegant.Layered.RegionLoopFrameLabelTransfer
import Elegant.Layered.RegionForwardAnchorTrace

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Same-part clearance for admitted executions after the selected reversed,
self-loop, and forward-child cases. Stored-title captions are unchanged. -/
def R_ExecutedPartFrameCoresB8LoopForwardChildRemainder (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ part ∈ execution.componentsAcc.parts,
      (∀ (selected : R8b_ChosenPart execution part)
        (index : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (index, stored) ∈ part.2.labels →
        part.1[pos]? = some key →
        inp.boxes[key]? = some src →
        src.role = .group →
        part.2.rects[pos]? = some frame →
        ¬ R8b_EmittedOuterReversedAt selected index stored pos →
        ¬ R8b_EmittedReservedChildAt selected index pos →
        ¬ R8b_EmittedDemotedReversedAt selected index stored pos src →
        ¬ R8b_EmittedSelectedLoopFrameAt selected index pos →
        ¬ R8b_EmittedForwardChildAt selected index pos →
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

theorem R_loopForwardChildRemainder_of_loopRemainder {exactIds : List String}
    {idSets : List (String × List String)}
    (h : R_ExecutedPartFrameCoresB8LoopRemainder exactIds idSets) :
    R_ExecutedPartFrameCoresB8LoopForwardChildRemainder exactIds idSets := by
  intro inp o res execution _hwf _hfp part hpart
  obtain ⟨hroute, hcaption⟩ := h execution part hpart
  refine ⟨?_, hcaption⟩
  intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
    houter hchild hdemoted hloop _
  exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
    houter hchild hdemoted hloop

theorem R_executedPartFrameCoresB8W_iff_loopForwardChildRemainder (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8W exactIds idSets ↔
      R_ExecutedPartFrameCoresB8LoopForwardChildRemainder exactIds idSets := by
  classical
  constructor
  · intro cores inp o res execution hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := cores execution hwf hfp part hpart
    refine ⟨?_, hcaption⟩
    intro _ index stored pos key src frame hlabel hkey hsrc hgroup hframe _ _ _ _ _
    exact hroute index stored pos key src frame hlabel hkey hsrc hgroup hframe
  · intro remainder inp o res execution hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := remainder execution hwf hfp part hpart
    obtain ⟨selected⟩ := r8b_chosenPart execution hpart
    refine ⟨?_, hcaption⟩
    intro index stored pos key src frame hlabel hkey hsrc hgroup hframe
    by_cases houter : R8b_EmittedOuterReversedAt selected index stored pos
    · exact Or.inl (r8b_emittedOuter_part_disjoint hframe houter)
    by_cases hchild : R8b_EmittedReservedChildAt selected index pos
    · exact Or.inl (r8b_reservedChild_geometry selected hpart hlabel hframe hchild).1
    by_cases hdemoted : R8b_EmittedDemotedReversedAt selected index stored pos src
    · exact Or.inl (r8b_demotedReversed_part_disjoint hframe hdemoted)
    by_cases hloop : R8b_EmittedSelectedLoopFrameAt selected index pos
    · exact r8b_selectedLoopFrame_part_clear selected hpart hlabel hframe hloop
    by_cases hforward : R8b_EmittedForwardChildAt selected index pos
    · obtain ⟨_, _, _, _, _, hclear⟩ :=
        regionC8b_selectedForwardChild_stored_actual selected hwf hfp hpart hlabel hframe hforward
      exact Or.inl hclear
    exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
      houter hchild hdemoted hloop hforward

theorem flatC8bB_layoutRIds_loopForwardChildRemainder (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8LoopForwardChildRemainder exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (layoutRIds exactIds idSets) :=
  flatC8bB_layoutRIds_W exactIds idSets
    ((R_executedPartFrameCoresB8W_iff_loopForwardChildRemainder exactIds idSets).mpr hcores)
    hfallW hres hcap

end Elegant.Layered.PipelineImpl
