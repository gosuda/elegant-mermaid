import Elegant.Layered.ExactCaptionCapBandProof
import Elegant.Layered.ExactCaptionMarkerBandProof
import Elegant.Layered.ExactCaptionAncestorFactsProof
import Elegant.Layered.ExactCaptionBandsProof
import Elegant.Layered.ExactFallbackStructuralProof
import Elegant.Layered.ExactCaptionFitFactsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact caption band facts: closure census for the `XCA_markerBelowX_holds`
residuals and the descendant fallback band

Census of the three leaves (2026-11-20):

* `XC_CapBandX` (`ExactCaptionMembersProof.lean:389`): **closed outright** by
  `XC_capBandX_holds` (`ExactCaptionCapBandProof.lean:496`), premise-free over
  one `SceneExecutionX`. No admission premises needed: the proof replays the
  plain `captionInTopBand_executed` upper bound through the exact machinery.

* `XCA_MarkerBandBelowX` (`ExactCaptionAncestorsProof.lean:98`-style def in
  `ExactCaptionAncestorFactsProof.lean`): the X form (no local admission
  premises) is **not provable from the executed run alone** — the W proof
  `excm_markerBandBelowXW_holds` (`ExactCaptionMarkerBandProof.lean:409`)
  needs `WellFormed`/`framedParents` for the nested-bottom rank chain
  (`excm_nested_bottom_rank` → `X_candidate_parent_top_exists` and
  `X_cg_scope_prefix` → `Compound.path_ancestor_prefix`). Narrowed here to
  the proved W band plus the two global admission premise defs
  (`XCA_WellFormedX`, `XCA_FramedX`), which every sibling exact theorem
  already carries and which the family entry supplies per instance from
  `layoutFamilyX` (`XCA_WellFormedX_of_family`, `XCA_FramedX_of_family`).
  Reduction: `XCA_markerBandBelowX_of_W`.

* `X_DescendantFallbackBandX`: the X form was **deleted** in the W cutover
  (`ExactCaptionFitFactsProof.lean:67-69`): its only proof needed the
  admission premises, and the plain `DescendantFallbackClear` already
  carries `_hwf`/`_hfp` binders. The W form `X_DescendantFallbackBandXW` is
  **closed outright** here (`xcb_descendantFallbackBandXW_closed`) from the
  premise-free `X_NonfixedGroupTitleX_holds` via `X_FallbackOwnerCasesX_holds`
  and `xcb_descendantFallbackBandXW_of_cases` — the band holds vacuously
  because a no-installed-title owner with an exclusive descendant is a
  non-fixed group parent. Per executed run with local admission, the W
  statement IS the band conclusion, so no separate X-form reduction exists
  to state.

Probe evidence: `proofs/wip/Probe/ExactCapBandT2Probe.lean` evaluates the W
marker-band and W fallback-band conclusions on nested groups, a self-loop
route, a zero-size fixed box, an empty-nested input, a caption on a nested
part, and a group-exclusive box, with nonempty `exactIds`; zero violations.
The earlier `ExactCaptionAncestorFactsTProbe` counted the same marker-band
inequality (both the X conclusion and the W band bound) on flat, nested,
sane-fixed, wider-than-slot, empty-nested, fixed-child, and three-level
inputs with `exactIds = []` and `["c"]`, zero violations.
-/

/-- Marker band, admission-local to premise-free: the proved W marker band
(`excm_markerBandBelowXW_holds`) plus the two global admission premise defs
(`XCA_WellFormedX`, `XCA_FramedX`) discharge the X-form marker band. This is
the narrowing of `XCA_MarkerBandBelowX`: the residual is strictly the W band
(already proved), and the reduction supplies the admission premises that
every sibling exact theorem (`XC_ancestorGroupFrameX_holds`,
`XC_ancestorOtherX_holds`, `XC_foreignSpansX_holds`) already takes. -/
theorem XCA_markerBandBelowX_of_W (exactIds : List String)
    (hmarkW : XCA_MarkerBandBelowXW exactIds)
    (hwfX : XCA_WellFormedX exactIds) (hfpX : XCA_FramedX exactIds) :
    XCA_MarkerBandBelowX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2
  exact hmarkW execution (hwfX execution) (hfpX execution) hcomp hrun
    i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2

/-- `XCA_MarkerBelowX` closed modulo the two global admission premise defs:
the shared caption band is proved outright (`XC_capBandX_holds`), the marker
band is the W band (`excm_markerBandBelowXW_holds`) discharged per execution
by `XCA_markerBandBelowX_of_W`, and `XCA_markerBelowX_holds` composes them.
This is what fills the `ExactSeams.capBelow` field once the family entry
supplies `XCA_WellFormedX`/`XCA_FramedX` (via `layoutFamilyX`). -/
theorem XCA_markerBelowX_closed_admission (exactIds : List String)
    (hwfX : XCA_WellFormedX exactIds) (hfpX : XCA_FramedX exactIds) :
    XCA_MarkerBelowX exactIds :=
  XCA_markerBelowX_holds exactIds (XC_capBandX_holds exactIds)
    (XCA_markerBandBelowX_of_W exactIds (excm_markerBandBelowXW_holds exactIds) hwfX hfpX)

/-- W marker-below closed premise-free: the W caption band is the proved X
band (`XC_capBandX_holds` implies its own W instances pointwise) and the W
marker band is proved (`excm_markerBandBelowXW_holds`); `XCA_markerBelowXW_holds`
composes them. -/
theorem xcb_markerBelowXW_closed (exactIds : List String) :
    XCA_MarkerBelowXW exactIds :=
  XCA_markerBelowXW_holds exactIds (XC_capBandX_holds exactIds)
    (excm_markerBandBelowXW_holds exactIds)

/-- W descendant fallback band closed premise-free: owner-role cases from
`X_FallbackOwnerCasesX_holds` (itself from the premise-free
`X_NonfixedGroupTitleX_holds`) make the band vacuous. This fills the
`ExactSeams.capDescBand` field. -/
theorem xcb_descendantFallbackBandXW_closed (exactIds : List String) :
    X_DescendantFallbackBandXW exactIds :=
  xcb_descendantFallbackBandXW_of_cases exactIds
    (X_FallbackOwnerCasesX_holds exactIds (X_NonfixedGroupTitleX_holds exactIds))

end PipelineImpl
end Layered
end Elegant
