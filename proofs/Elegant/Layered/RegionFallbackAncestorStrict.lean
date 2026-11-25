import Elegant.Layered.RegionFallbackEmptyTransfer
import Elegant.Layered.RegionFlatC3
import Elegant.Layered.RegionParentInComponent
import Elegant.Layered.RegionC5ActiveBoundary
import Elegant.Layered.LabelsClearance

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

/-- Strict parent links of the actually selected, emitted component frames. -/
def R_SelectedDirectFrameStrict (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    R_SelectedDirectFrameRelation execution Rect.StrictInside

/-- The executed region depth walk reduces to one pre-orientation parent link
at a time. No positivity of the child dimensions is needed by this transport. -/
theorem R_ancestorFrameStrictW_of_selected (exactIds : List String)
    (idSets : List (String × List String))
    (hselected : R_SelectedDirectFrameStrict exactIds idSets) :
    R_AncestorFrameStrictW exactIds idSets := by
  intro inp o res execution hwf hfp frame descendant hframe hdescendant _ hancestor
  have hstep := sceneExecutionR_directFrameRelation execution hwf hfp
    (R_parentInComponentR_holds execution hwf hfp)
    (rel := Rect.StrictInside)
    (by
      intro dx dy parent child hrect
      exact strictInside_shiftRect (dx := dx) (dy := dy) hrect)
    (by
      intro direction height parent child hrect
      exact strictInside_orientRect (d := direction) (h := height) hrect)
    (hselected execution hwf hfp)
  have hids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapR, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hids]
    exact Model.boxIds_nodup hwf
  let dump := res.scene.layoutDump
  have hfindFrame : dump.box? frame.id = some frame :=
    Assembly.keyed_lookup_eq Box.id res.scene.boxes hnodup frame hframe
  have hwalk : ∀ (fuel : Nat) (id : String) (child : Box),
      dump.box? id = some child →
      frame.id ∈ LayoutDump.ancestors.go dump fuel id →
      frame.rect.StrictInside child.rect := by
    intro fuel
    induction fuel with
    | zero =>
      intro _ _ _ hmem
      change frame.id ∈ ([] : List String) at hmem
      cases hmem
    | succ fuel ih =>
      intro id child hlookup hmem
      have hfind : dump.boxes.find? (fun b => b.id == id) = some child := hlookup
      by_cases hroot : child.parent = ""
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hroot, ↓reduceIte] at hmem
        cases hmem
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hroot, ↓reduceIte] at hmem
        have hchild := List.mem_of_find?_eq_some hfind
        rcases List.mem_cons.mp hmem with hhead | htail
        · have hparent : dump.box? child.parent = some frame := by
            rw [← hhead]
            exact hfindFrame
          exact hstep child hchild hroot frame hparent
        · cases hparent : dump.box? child.parent with
          | none =>
            cases fuel with
            | zero => cases htail
            | succ fuel =>
              have hn : dump.boxes.find? (fun b => b.id == child.parent) = none := hparent
              simp only [LayoutDump.ancestors.go, LayoutDump.box?, hn] at htail
              cases htail
          | some parent =>
            exact captionStrictInside_trans (ih child.parent parent hparent htail)
              (hstep child hchild hroot parent hparent)
  have hfindDescendant : dump.box? descendant.id = some descendant :=
    Assembly.keyed_lookup_eq Box.id res.scene.boxes hnodup descendant hdescendant
  exact hwalk dump.boxes.length descendant.id descendant hfindDescendant hancestor

/-- Dormant region sets, even nonempty ones, do not change strict ancestry
when all executed components fall back to the exact layout. -/
theorem R_ancestorFrameStrict_of_allComponentsFallback
    {exactIds : List String} {idSets : List (String × List String)} {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hfallback : R_AllComponentsFallbackR execution) :
    ∀ g ob : Box, g ∈ res.scene.boxes → ob ∈ res.scene.boxes →
      g.role = "group" → g.id ∈ res.scene.layoutDump.ancestors ob.id →
      g.rect.StrictInside ob.rect := by
  have hX := (layoutRIds_eq_layoutX_of_allComponentsFallbackR execution hfallback).symm.trans h
  obtain ⟨executionX⟩ := layoutX_sceneExecution hX
  exact X_ancestorFrameStrictW_closed exactIds executionX hwf hfp

end Elegant.Layered.PipelineImpl
