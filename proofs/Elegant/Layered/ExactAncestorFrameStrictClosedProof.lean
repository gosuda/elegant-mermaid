import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.ExecutedExactFallbackStrictProof
import Elegant.Layered.ExactFallbackCaptionFactsProof
import Elegant.Layered.ExactFlatC5SelfRoutes

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem sceneGroupParentX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {child : Box} (hchild : child ∈ res.scene.boxes) (hnonroot : child.parent ≠ "") :
    ∃ parent : Box, res.scene.layoutDump.box? child.parent = some parent ∧
      parent.role = "group" := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hchild
  obtain ⟨source, hsource, _, hparent, _, _⟩ := sceneBox_source_rectX execution hi
  have hsourceNonroot : source.parent ≠ "" := by
    rw [← hparent]
    exact hnonroot
  obtain ⟨parent, hparentMem, hparentId, hparentRole, _⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hsource) hsourceNonroot
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hparentMem
  have hlookup := execution.source_box_lookup_of_box_ids_nodupX (Model.boxIds_nodup hwf) hj
  rw [hparentId, ← hparent] at hlookup
  refine ⟨_, hlookup, ?_⟩
  change parent.role.id = "group"
  exact congrArg BoxRole.id hparentRole

/-- Every group on the executed ancestor walk strictly contains the starting box. -/
theorem X_ancestorFrameStrictW_closed (exactIds : List String) :
    X_AncestorFrameStrictW exactIds := by
  intro inp o res execution hwf hframed frame descendant hframe hdescendant hgroup hancestor
  have hnodup := X_sceneBoxesNodupW_holds exactIds execution hwf hframed
  have hstep := fallbackOwnerStrictStep_executedX execution hwf hframed
  have hframeLookup : res.scene.layoutDump.box? frame.id = some frame :=
    Assembly.keyed_lookup_eq Box.id res.scene.boxes hnodup frame hframe
  have hwalk : ∀ (fuel : Nat) (id : String) (child : Box),
      res.scene.layoutDump.box? id = some child →
      frame.id ∈ LayoutDump.ancestors.go res.scene.layoutDump fuel id →
      frame.rect.StrictInside child.rect := by
    intro fuel
    induction fuel with
    | zero =>
      intro _ _ _ hmem
      change frame.id ∈ ([] : List String) at hmem
      cases hmem
    | succ fuel ih =>
      intro id child hlookup hmem
      have hfind : res.scene.layoutDump.boxes.find? (fun b => b.id == id) = some child := hlookup
      by_cases hroot : child.parent = ""
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hroot, ↓reduceIte] at hmem
        cases hmem
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hroot, ↓reduceIte] at hmem
        have hchild : child ∈ res.scene.boxes := List.mem_of_find?_eq_some hfind
        rcases List.mem_cons.mp hmem with hhead | htail
        · have hparent : res.scene.layoutDump.box? child.parent = some frame := by
            rw [← hhead]
            exact hframeLookup
          exact hstep child hchild hroot frame hparent hgroup
        · obtain ⟨parent, hparent, hrole⟩ := sceneGroupParentX execution hwf hframed hchild hroot
          exact captionStrictInside_trans (ih child.parent parent hparent htail)
            (hstep child hchild hroot parent hparent hrole)
  have hdescendantLookup : res.scene.layoutDump.box? descendant.id = some descendant :=
    Assembly.keyed_lookup_eq Box.id res.scene.boxes hnodup descendant hdescendant
  exact hwalk res.scene.layoutDump.boxes.length descendant.id descendant hdescendantLookup hancestor

end Elegant.Layered.PipelineImpl
