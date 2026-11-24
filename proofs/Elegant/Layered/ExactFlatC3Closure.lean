import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.ExactRunFrameNestingProof
import Elegant.Layered.ExactParentInComponent
import Elegant.Layered.RecursiveBLiftsA

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- The exact pipeline satisfies the shared `ExactComponentPlacement`
hypothesis: parts are bounded, member frames nest, and parents stay in
the same component. Each conjunct is a separately proved fact. -/
theorem exactComponentPlacement {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} : ExactComponentPlacement exactIds inp o res := by
  intro hwf hframed execution
  refine ⟨?_, ?_, ?_⟩
  · exact exactPartsBounded' execution
  · exact exactMemberInFrame' execution hwf hframed
  · intro comp hcomp key parentKey hkeyLen hkeyIn member hmemberGraph
      childBox hchildBox parentBox hparentBox hparentRef hparentNe
    exact exactParentInComponent execution hwf hframed comp hcomp key parentKey
      hkeyLen hkeyIn member hmemberGraph childBox hchildBox parentBox hparentBox
      hparentRef hparentNe

/-- Clause C3 for `layoutX`, with no placement hypothesis. -/
theorem layoutX_c3' {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) :
    Validator.C3 res.scene.layoutDump :=
  layoutX_c3 h hwf hframed exactComponentPlacement

/-- The exact pipeline discharges the base-parametric flat C3 fact. -/
theorem flatC3B_layoutX (exactIds : List String) : FlatC3B (layoutX exactIds) :=
  fun inp o res hwf hframed hok =>
    layoutX_c3' (exactIds := exactIds) (inp := inp) (o := o) (res := res) hok hwf hframed

end PipelineImpl
end Layered
end Elegant
