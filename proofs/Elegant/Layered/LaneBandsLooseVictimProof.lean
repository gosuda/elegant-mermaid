import Elegant.Layered.LaneBands
import Elegant.Layered.LaneBandsFrameClause
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

 /-! # Loose-band shift helpers plus the refuted lower bound record.

 This module holds only the public pin-axis shift helpers `lvShiftPoint`
 / `lvShiftRect` (used by `LaneBandsLooseLowerProof`, which imports this
 module, and through it by `LaneBandsKeptClearExecutedProof`), plus this
 record of the refutation.

 Verdict on full pin-axis containment of kept loose-band routes: FALSE.
 `wip/Probe/LaneBandsLooseVictimProofProbe.lean` evaluates executed
 layouts: on `mCross` the loose self-loop `e4` has base pin-axis points
 `[22012, 22780, 22780, 22012]` while its loose band covers `[19930, 22012]`
 (`lower=true`, `upper=false`; the overshoot is one routing slot, `768`).
 The same shape recurs on `mLooseBetween`, `mLooseSelf`, `mNested` and
 `mEmptyLane` (e.g. `mLooseSelf e0`: points `[3106, 3874, 3874, 3106]` over
 `[1024, 3106]`). Full containment would need `contentValues` to cover
 routes, but loose content covers boxes only (`inLane boxes id ""` is always
 false), so no strip bound applies to a kept loose route.

 The narrowed lower bound `PinLooseRouteLower` (every kept loose-band route
 point at or above the loose content minimum) is likewise FALSE: witness
 `mWit` in `wip/Probe/PinLooseLowerT_Witness.lean`, recorded in
 `LaneBandsLooseLowerProof` (route dip `8062` below loose minimum `13134`
 while pinned `C6` holds). The true consumer form is the per-pair
 `PinLooseRouteAboveLaneBox` there; the bridge
 `pinLooseRouteLaneVictimClear_of_above` and the closed
 `pinBands_c6_executed_closed` live over it at the end of the tracked
 `LaneBandsKeptClearExecutedProof.lean`, which imports that module. -/

 /-- Pin-axis shift of a point by one band delta (public copy of the tracked
 kept-route shift, shared with `LaneBandsLooseLowerProof`). -/
 def lvShiftPoint (axis : Axis) (delta : Int) (p : Point) : Point :=
   axis.withPoint p (axis.point p + delta)

 /-- Pin-axis shift of a rect by one band delta (public copy of the tracked
 kept-box shift, shared with `LaneBandsLooseLowerProof`). -/
 def lvShiftRect (axis : Axis) (delta : Int) (r : Rect) : Rect :=
   axis.withStart r (axis.start r + delta)


end LaneBands
end Layered
end Elegant
