import Elegant.Layered.ExecutedExactFallbackStrictProof
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.ExactStepGeometryProof
import Elegant.Layered.ExpandChildParentFrameProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem closedParentLookup {scene : Scene} (hclosed : SceneParentClosed scene)
    {box : Box} (hbox : box ∈ scene.boxes) (hparent : box.parent ≠ "") :
    ∃ p, scene.layoutDump.box? box.parent = some p := by
  rcases hclosed box hbox with hroot | ⟨parent, hmem, hid⟩
  · exact (hparent hroot).elim
  · cases hlookup : scene.layoutDump.box? box.parent with
    | none =>
      change scene.boxes.find? (fun b => b.id == box.parent) = none at hlookup
      have hfalse := List.find?_eq_none.mp hlookup parent hmem
      simp [hid] at hfalse
    | some p => exact ⟨p, rfl⟩

private theorem mergeStrictStep {inp : Input} {group : ModelBox}
    {parent child res : FamilyResult} {frame : Box} {dx dy : Int}
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun model =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
        (fun box => box.id == model.id)))
    (hfit : ∀ box ∈ child.scene.boxes,
      frame.rect.StrictInside (embedBox group.id dx dy box).rect)
    (hstepParent : ExpandChildParentStrictStep parent)
    (hstepChild : ExpandChildParentStrictStep child)
    (hchildTrans : ∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box))
    (hparentTrans : ∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some box)
    (hclosedParent : SceneParentClosed parent.scene)
    (hclosedChild : SceneParentClosed child.scene) :
    ExpandChildParentStrictStep res := by
  intro box hbox hparent p hp hrole
  rw [hboxes] at hbox
  obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hbox
  rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hchild | hparentMem
  · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hchild
    by_cases hroot : cb.parent = ""
    · have hframeLookup : parent.scene.layoutDump.box? group.id = some frame := hframe
      have hframeId := boxLookupId hframeLookup
      have hself : parent.scene.layoutDump.box? frame.id = some frame := by
        rw [hframeId]; exact hframeLookup
      have hresult := hparentTrans frame hself
      rw [hframeId] at hresult
      have hparentEq : (embedBox group.id dx dy cb).parent = group.id := by
        simp [embedBox, hroot]
      rw [hparentEq] at hp
      have heq : frame = p := Option.some.inj (hresult.symm.trans hp)
      subst p
      exact hfit cb hcb
    · obtain ⟨ancestor, hlookup⟩ := closedParentLookup hclosedChild hcb hroot
      have hid := boxLookupId hlookup
      have hself : child.scene.layoutDump.box? ancestor.id = some ancestor := by
        rw [hid]; exact hlookup
      have hresult := hchildTrans ancestor hself
      rw [hid] at hresult
      have hparentEq : (embedBox group.id dx dy cb).parent = cb.parent := by
        simp [embedBox, hroot]
      rw [hparentEq] at hp
      have heq : embedBox group.id dx dy ancestor = p := Option.some.inj (hresult.symm.trans hp)
      subst p
      exact strictInside_shiftRect (dx := dx) (dy := dy)
        (hstepChild cb hcb hroot ancestor hlookup hrole)
  · obtain ⟨ancestor, hlookup⟩ := closedParentLookup hclosedParent hparentMem hparent
    have hid := boxLookupId hlookup
    have hself : parent.scene.layoutDump.box? ancestor.id = some ancestor := by
      rw [hid]; exact hlookup
    have hresult := hparentTrans ancestor hself
    rw [hid] at hresult
    have heq : ancestor = p := Option.some.inj (hresult.symm.trans hp)
    subst p
    exact hstepParent box hparentMem hparent ancestor hlookup hrole

private theorem exactFlatStrictStep {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hflat : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    ExpandChildParentStrictStep res := by
  obtain ⟨execution⟩ := layoutX_sceneExecution hflat
  exact fallbackOwnerStrictStep_executedX execution hwf hframed

private theorem exactRecursiveStrictStep (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      ExpandChildParentStrictStep res := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hrec hwf hframed
    have hflat : layoutX exactIds inp o = .ok res := hrec
    exact exactFlatStrictStep hflat hwf hframed
  | succ fuel ih =>
    intro inp o res hrec hwf hframed
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) hrec with ⟨_, hflat⟩ |
      ⟨group, P, metric, child, titleLines, parent, hgroup, hP, hmetric, hchild, hwrap,
        hparent, hexpand⟩
    · exact exactFlatStrictStep hflat hwf hframed
    · let titleHeight := (max 1 titleLines.length : Int) * P.lineH
      have hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
          titleLines titleHeight parent child res := ⟨hwf, hgroup, rfl, hchild, hparent, hexpand⟩
      have hparams : ExpandChildCallParams P inp o group titleLines titleHeight :=
        ⟨hP, rfl, metric, hmetric, hwrap⟩
      obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        subInputWellFormedB_layoutX exactIds fuel inp o group P metric titleLines child parent
          hwf hframed hP hmetric hwrap hchild hparent
      have hstepChild := ih (childSubInput inp group) (childSubOptions o group) child
        hchild hwfChild hframedChild
      have hstepParent := ih (parentSubInput inp group P titleLines child) o parent
        hparent hwfParent hframedParent
      obtain ⟨frame, expansionMetric, tl, _, dx, dy, hframe, hmeasured, hwrapped, _, hdx,
        hdy, _, hboxes⟩ := expandChild_sources hexpand
      have htitle : ExpandChildTitleWrapped P inp o group tl :=
        ⟨expansionMetric, hmeasured, hwrapped⟩
      obtain ⟨hfitClosed, hclosedParent, hclosedChild⟩ :=
        exactFitClosed exactIds fuel P inp o group titleLines titleHeight parent child res
          hexpand hctx hparams
      obtain ⟨_, hchildTrans, hparentTrans⟩ := hfitClosed frame tl dx dy hframe hdx hdy htitle
      have hinset := XG_child_boxes_insetB exactIds fuel P inp o group titleLines titleHeight
        parent child res hexpand hframed hctx hparams
      have hcontent := XG_content_fit_strict exactIds fuel P inp o group titleLines titleHeight
        parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy htitle
      exact mergeStrictStep hframe hboxes (fun cb hcb => hcontent cb.rect (hinset cb hcb))
        hstepParent hstepChild hchildTrans hparentTrans hclosedParent hclosedChild

/-- The actual parent scene of an exact expansion has strict group-parent steps. -/
theorem parentStrictStepB_of_recursion (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res) :
    ExpandChildParentStrictStep parent := by
  obtain ⟨hwf, _, _, _, hparent, _⟩ := hctx
  exact exactRecursiveStrictStep exactIds fuel (parentSubInput inp group P titleLines child) o
    parent hparent ((subInputWellFormedC2 inp o group hwf).2 _ _ _)
    (framedParents_selectInput_outside_append inp o group hwf hframed _ child.scene child.itemArea)

end Elegant.Layered.PipelineImpl
