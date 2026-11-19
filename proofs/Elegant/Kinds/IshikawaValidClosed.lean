import Elegant.Kinds.IshikawaValidAssembly
import Elegant.Kinds.IshikawaDescFrameGapProof
import Elegant.Kinds.IshikawaDescOrdIntervalProof
import Elegant.Kinds.IshikawaCauseEnvBoundProof
import Elegant.IshikawaDeeperDescEnvelopeProof

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-- Ishikawa validity with all leaf residuals discharged. -/
theorem ishikawa_valid_closed (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  ishikawa_valid_of_leaves m result hwf hlimits h
    (fun ns p raw hrun ribs hg cause k hsource hcauseMem spine placed hplace env =>
      hardBDeeperDescEnvelope ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace env)
    (fun ns cause k => descendantOrdInterval ns cause k)
    (fun ns p raw hrun ribs hg cause k hsource hcauseMem spine placed hplace =>
      descendantFrameGap ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace)
    (fun ns p raw hrun ribs hg cause k hsource hcauseMem spine placed hplace =>
      causeEntryEnvBound ns p raw hrun ribs hg cause k hsource hcauseMem
        spine placed hplace)

end Elegant.Kinds.IshikawaFinal
