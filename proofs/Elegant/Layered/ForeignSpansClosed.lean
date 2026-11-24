import Elegant.Layered.ForeignBorderDivergeFramedProof
import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignNonGroupSpansProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem foreignBorderSpansSeparated_closed : ForeignBorderSpansSeparated :=
  foreignBorderSpansSeparated foreignClusterRankSpans' foreignBorderLayerOrder'
    (foreignBorderChainXAligned' foreignBorderDivergeStable_framed)

theorem foreignNonGroupSpansClear_closed : ForeignNonGroupSpansClear :=
  foreignNonGroupSpansClear bracketMarkersAtRank' plainClearOfSideMarker'
    (sideMarkerSpanAligned' (foreignBorderChainXAligned' foreignBorderDivergeStable_framed))

end Elegant.Layered.PipelineImpl
