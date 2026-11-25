import Elegant.Kinds.IshikawaRawClearance
import Elegant.Kinds.IshikawaSameRibEnvelope
import Elegant.Kinds.IshikawaSameRibFramesProof
import Elegant.Kinds.IshikawaBoundaryClearance
import Elegant.Kinds.IshikawaBoundaryRouteXProof
import Elegant.Kinds.IshikawaPlaceDrawnBound
import Elegant.IshikawaDeeperOrdIntervalProof
import Elegant.IshikawaDeeperGapOnlyProof
import Elegant.IshikawaDeeperEarlierProof
import Elegant.IshikawaFlattenClausesProof
import Elegant.Kinds.IshikawaValid

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! Assembly of Ishikawa validity from the true leaf residuals.

The raw clearance assembly (`ishikawa_valid_of_deeper`) takes four
residuals; the deeper-earlier one in turn factors through the proved
order interval and the descendant envelope, and the same-rib one
through the frames-based envelope clearance. This module assembles
the deeper-earlier bridge from the corresponding leaves, and
`ishikawa_valid_of_leaves` concludes validity from all true leaves
at once. The boundary and cross-rib branches close with no
hypotheses. -/

/-- Deeper-earlier bridge: the proved order interval plus the
descendant envelope supply the earlier obligation. -/
theorem ishikawaDeeperEarlierRaw_of_leaves (m : Model)
    (hdesc : ∀ (ns : List Elegant.Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
      (hcauseMem : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))) = .ok placed)
      (env : IshikawaEnvFrames ns p
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k)))),
      HardBDeeperDescEnvelope ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace env) :
    IshikawaDeeperEarlierRaw m := by
  intro e cause k hsource hcauseMem ribPlaced hplace henv
  have hord : HardBDeeperOrdInterval e.input.nodes cause k :=
    hardBDeeperOrdInterval' e.input.nodes cause k
  have hgapArg : HardBDeeperDescEnvelope e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource hcauseMem e.spine ribPlaced hplace henv :=
    hdesc e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.raw e.hlayout e.ribs e.hribs cause k hsource hcauseMem e.spine ribPlaced
      hplace henv
  have henvT : HardBDeeperEnvTransport e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource hcauseMem e.spine ribPlaced hplace henv :=
    hardBDeeperEnvTransport'' e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource hcauseMem e.spine ribPlaced hplace henv hgapArg
  have hlink : Tree.link e.input.nodes = true :=
    Elegant.Kinds.IshikawaValid.successful_link e.input.nodes _ e.raw e.hlayout
  exact hardBDeeperEarlierReal e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
    cause k hsource hcauseMem e.spine ribPlaced hplace henv hlink hord henvT

/-- Ishikawa validity from the true leaves: the deeper descendant
envelope, the descendant order interval, the descendant frame gap,
and the cause entry ENV bound. The boundary and cross-rib branches
need no leaf hypotheses. -/
theorem ishikawa_valid_of_leaves (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result)
    (hdesc : ∀ (ns : List Elegant.Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
      (hcauseMem : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))) = .ok placed)
      (env : IshikawaEnvFrames ns p
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k)))),
      HardBDeeperDescEnvelope ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace env)
    (hord : ∀ (ns : List Elegant.Tree.Node) (cause k : Nat),
      DescendantOrdInterval ns cause k)
    (hgap : ∀ (ns : List Elegant.Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
      (hcauseMem : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))) = .ok placed),
      DescendantFrameGap ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace)
    (henv : ∀ (ns : List Elegant.Tree.Node) (p : Params) (raw : Tree.Layout)
      (hrun : layout ns p = .ok raw)
      (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
      (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
      (hcauseMem : cause ∈ children ns 0) (spine : Int) (placed : Rib)
      (hplace : place ns p spine
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))) = .ok placed),
      CauseEntryEnvBound ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace) :
    HardConstraints result.scene.layoutDump := by
  have hdeep := ishikawaDeeperEarlierRaw_of_leaves m hdesc
  have hsame := ishikawaSameRibPieceClearance_frames m hord hgap henv
  have hcross := ishikawaCrossRibPieceClearance''' m
  have hbound := ishikawaBoundaryPieceClearance''' m hwf hlimits
  exact ishikawa_valid_of_deeper m result hwf hlimits h hdeep hsame hcross hbound

end Elegant.Kinds.IshikawaFinal
