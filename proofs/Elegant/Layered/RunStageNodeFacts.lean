import Elegant.Layered.RunStagePathFacts
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.FlatC6ScopeBridgeProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Run-phase residual R1: proper declarations follow candidates. -/
theorem properDeclPreserved {inp : Input} {o : Options} {res : FamilyResult} :
    ProperDeclPreserved inp o res := by
  unfold ProperDeclPreserved
  exact properDeclPreservedCore

/-- Run-level cluster-path provenance: every run-proper path entry is a group. -/
theorem runClusterPathGroupMembers
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    RunClusterPathGroupMembers inp o res := by
  unfold RunClusterPathGroupMembers
  exact runClusterPathGroupMembersCore hwf hframed
end PipelineImpl
end Layered
end Elegant
