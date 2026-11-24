import Elegant.Layered.RegionLabelRunBridge
import Elegant.Layered.RegionExclusiveRunBridge
import Elegant.Layered.RegionPartSizingClosed

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

theorem r7_routeLabelDumpBridges {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) : R7_RouteLabelDumpBridges exactIds idSets inp o res := by
  intro execution l index source measured b hlmem hin hid hmeasured hdump hex hscope
  have hlabel : R7_LabelBelongsToRun exactIds idSets inp o res := r7_labelBelongsToRun hwf
  have hbox : R7_ExclusiveBoxInLabelRun exactIds idSets inp o res :=
    r7_exclusiveBoxInLabelRun hwf hfp
  obtain ⟨comp, candidate, run, orderOptions, cg, cg', edge, decl, e, px, py, m, h, d,
    packed, c, labelPart, shelfc, loops, area, rl, rs, hcomp, hnew, hcg, hrun, _hord,
    hedge, hdecl, hroute, hlrect, hm, hh, hd, hpacked, hselected, hpart1, _hloops,
    hpartdef, hpx, hpy, _hrlindex, hrlmem, hshelfRect⟩ :=
    hlabel execution l index source measured hlmem hin hid hmeasured
  rcases hbox execution l index source measured comp candidate run orderOptions cg cg'
    edge decl e packed c labelPart shelfc loops area rl hlmem hin hid hmeasured hcomp
    rs hnew hcg hrun hedge hdecl hroute hpacked hselected hpart1 hpartdef hrlmem
    hshelfRect b hdump hex hscope with ⟨v, hv, hreal, _, htail, hhead, hbrect⟩ | hother
  · refine Or.inl ⟨comp, candidate, run, orderOptions, cg, cg', edge, decl, v, e,
      px, py, m, h, d, hcomp, rs, hnew, hcg, hrun, hedge, hdecl, hroute,
      hv, hreal, htail, hhead, hlrect, ?_⟩
    simpa only [hm, hd, hh, hpx, hpy] using hbrect
  · exact Or.inr hother

theorem flatC7B_layoutRIds_closedBridges (exactIds : List String)
    (idSets : List (String × List String))
    (hloop : R7_RunLocalLoopSeparation exactIds idSets)
    (hfwd : R7_RunLocalForwardSeparation exactIds idSets)
    (hrev : R7_RunLocalReversedSeparation exactIds idSets)
    (hcapFitW : R7_CaptionScopeClearanceFitW exactIds idSets) :
    FlatC7B (layoutRIds exactIds idSets) :=
  flatC7B_layoutRIds_W exactIds idSets hloop hfwd hrev
    (fun _ _ _ hwf hfp => r7_routeLabelDumpBridges hwf hfp)
    (R_partSizingRResidual_holds exactIds idSets) hcapFitW

end Elegant.Layered.PipelineImpl
