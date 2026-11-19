import Elegant.Layered.AttachPipeline
import Elegant.Layered.RegionPipeline

set_option autoImplicit false

/-! The state family entry: exact boxes, concurrent regions and attached notes on one base
layout. The region sets are resolved once against the whole input and re-resolved by id against
every sub-input that a recursion level or a note bundle lays out. -/

namespace Elegant
namespace Layered

/-- The family entry with exact boxes, concurrent regions and attached notes. -/
def layoutFamilyRN (exactIds : List String) (sets : List ModelRegionSet) (inp : Input)
    (o : Options) : Except LayoutFailure FamilyResult :=
  match RegionImpl.graphRegions inp sets with
  | .error e => .error (.geometry e)
  | .ok idSets =>
    layoutFamilyB
      (PipelineImpl.layoutNotes
        (fun ids sub => PipelineImpl.layoutRIds ids (PipelineImpl.reindexRegionSets idSets sub) sub)
        exactIds (inp.boxes.length + 1))
      inp o

end Layered
end Elegant
