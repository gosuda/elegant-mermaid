import Elegant.Layered.NotesRoutePortTransport
import Elegant.Layered.RegionNotesDimensions

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem NotesExecution.region_router_ends
    {idSets : List (String × List String)} {exactIds : List String} {fuel : Nat}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) :
    notesRouterEnds o.profile inp e.atts (notesFrameOf e.contracted o e.margin)
      (notesRectsOf res.scene.boxes)
      (notesLabelsOf e.fragments e.contracted inp)
      (notesTitlesOf e.fragments e.contracted) := by
  have hPath := nriRouterPathExec_of_rects_lookup_nonneg inp o res
    e.contracted e.fragments e.atts e.margin (fun _ _ hLookup => e.region_rects_lookup_nonneg hLookup)
  exact nriRouterEndsExec_of_parts inp o res e.contracted e.fragments e.atts e.margin hPath hwf

end Elegant.Layered.PipelineImpl
