import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.SceneBounds
import Elegant.Layered.FallbackOwnerStrictStepProof
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.RecursiveC6

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Validator

/-!
# Strict-step fact for executed `expandChild` calls

`parentStrictStep` (`ExpandChildParentStrictStep`) is proved outright by
scene-level fuel induction on `layoutRecursive`: flat leaves (fuel zero, or
no expandable group) use `fallbackOwnerStrictStep_executed`; every expansion
transfers the strict steps of the two recursive results through the box
equations, mirroring the C3 half of `expandChild_c1_c3`. Child roots go
through the strict child-canvas fit (`expandChild_content_fit_strict`
composed with `expandChild_child_boxes_inset`); deeper child boxes shift
through `embedBox`; parent boxes transport unchanged. Lookup transport comes
from `layoutRecursive_embedding_assembly_sources` (which needs no
`canvasMargin ≤ clusterPad` premise); parent-closure from
`layoutRecursive_parent_closed_wellFormed`.

`parentFrameStrict` (`ExpandChildParentFrameStrict`) is not settled here.
-/

/-- Strict transfer through `embedBox`: a strict containment between child
scene boxes survives the shift and the root-parent rewrite. -/
private theorem pfs_strictInside_embed {groupId : String} {dx dy : Int}
    {a b : Box} (h : a.rect.StrictInside b.rect) :
    (embedBox groupId dx dy a).rect.StrictInside (embedBox groupId dx dy b).rect := by
  unfold embedBox
  simp only [shiftRect, Rect.StrictInside]
  omega

/-- The strict inset-to-frame transport for every child box, composed from
`expandChild_content_fit_strict` and `expandChild_child_boxes_inset`. -/
private theorem pfs_child_boxes_strictInside_frame
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hP : checkedParams o.profile inp.kind = .ok P)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group tl →
    ∀ cb ∈ child.scene.boxes,
      frame.rect.StrictInside (embedBox group.id dx dy cb).rect := by
  intro frame tl dx dy hframe hdx hdy hwrap cb hcb
  have hmem := expandChild_child_boxes_inset fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hP cb hcb
  have hS := expandChild_content_fit_strict fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
    cb.rect hmem
  have hrect : (embedBox group.id dx dy cb).rect = shiftRect dx dy cb.rect := rfl
  rw [hrect]
  exact hS

/-- The parent sub-input is well-formed. -/
private theorem pfs_parentInput_wellFormed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
  exact (subInputWellFormedC2 inp o group hctx.1).2 _ _ _

/-- The parent sub-input is framed. -/
private theorem pfs_parentInput_framed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    framedParents (parentSubInput inp group P titleLines child) = true := by
  exact framedParents_selectInput_outside_append inp o group hctx.1 hframed
    _ child.scene child.itemArea

/-- `expandChild` preserves the strict step, given the strict steps of both
recursive results, the strict child-box fit, lookup transport, and
parent-closure. Mirrors the C3 half of `expandChild_c1_c3`. -/
private theorem pfs_strictStep_transfer
    {inp : Input} {group : ModelBox} {parent child res : FamilyResult}
    {frame : Box} {dx dy : Int}
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun model =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
        (fun box => box.id == model.id)))
    (hfitStrict : ∀ cb ∈ child.scene.boxes,
      frame.rect.StrictInside (embedBox group.id dx dy cb).rect)
    (hstepParent : ExpandChildParentStrictStep parent)
    (hstepChild : ExpandChildParentStrictStep child)
    (hchildTrans : ∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box))
    (hparentTrans : ∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some box)
    (hclosedChild : SceneParentClosed child.scene)
    (hclosedParent : SceneParentClosed parent.scene) :
    ExpandChildParentStrictStep res := by
  intro b hb hpar p hp hrole
  rw [hboxes] at hb
  obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hb
  have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hfind
  rcases List.mem_append.mp hbItems with hbc | hbp
  · obtain ⟨c, hc, hbEq⟩ := List.mem_map.mp hbc
    by_cases hcRoot : c.parent = ""
    · have hbParent : b.parent = group.id := by
        have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
          rw [← hbEq]; rfl
        rw [hproj]; simp [hcRoot]
      have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
      have hframeSelf : parent.scene.layoutDump.box? frame.id = some frame := by
        rw [hframeId]; exact hframe
      have hresLookup := hparentTrans frame hframeSelf
      rw [hframeId] at hresLookup
      rw [hbParent] at hp
      have hpEq : frame = p := Option.some.inj (hresLookup.symm.trans hp)
      subst hpEq
      rw [← hbEq]
      exact hfitStrict c hc
    · have hbParent : b.parent = c.parent := by
        have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
          rw [← hbEq]; rfl
        rw [hproj]; simp [hcRoot]
      rcases hclosedChild c hc with hcpEmpty | ⟨p', hpmem, hpid⟩
      · exact absurd hcpEmpty hcRoot
      · have hfindNe : child.scene.boxes.find?
            (fun candidate => candidate.id == c.parent) ≠ none := by
          intro hnone
          rw [List.find?_eq_none] at hnone
          exact absurd (hnone p' hpmem) (by simp [hpid])
        cases hfind2 : child.scene.boxes.find?
            (fun candidate => candidate.id == c.parent) with
        | none => exact absurd hfind2 hfindNe
        | some p'' =>
          have hchildLookup : child.scene.layoutDump.box? c.parent = some p'' := hfind2
          have hppid : p''.id = c.parent := by simpa using List.find?_some hfind2
          have hself : child.scene.layoutDump.box? p''.id = some p'' := by
            rw [hppid]; exact hchildLookup
          have htrans := hchildTrans p'' hself
          have hbpId : b.parent = p''.id := hbParent.trans hppid.symm
          rw [hbpId] at hp
          have hpEq : embedBox group.id dx dy p'' = p :=
            Option.some.inj (htrans.symm.trans hp)
          subst hpEq
          have hSI := hstepChild c hc hcRoot p'' hchildLookup hrole
          rw [← hbEq]
          exact pfs_strictInside_embed hSI
  · rcases hclosedParent b hbp with hbEmpty | ⟨p', hpmem, hpid⟩
    · exact absurd hbEmpty hpar
    · have hfindNe : parent.scene.boxes.find?
          (fun candidate => candidate.id == b.parent) ≠ none := by
        intro hnone
        rw [List.find?_eq_none] at hnone
        exact absurd (hnone p' hpmem) (by simp [hpid])
      cases hfind2 : parent.scene.boxes.find?
          (fun candidate => candidate.id == b.parent) with
      | none => exact absurd hfind2 hfindNe
      | some p'' =>
        have hparentLookup : parent.scene.layoutDump.box? b.parent = some p'' := hfind2
        have hppid : p''.id = b.parent := by simpa using List.find?_some hfind2
        have hself : parent.scene.layoutDump.box? p''.id = some p'' := by
          rw [hppid]; exact hparentLookup
        have htrans := hparentTrans p'' hself
        rw [hppid] at htrans
        have hpEq : p'' = p := Option.some.inj (htrans.symm.trans hp)
        subst hpEq
        exact hstepParent b hbp hpar p'' hparentLookup hrole

/-- Every successful recursive layout satisfies the strict step. -/
private theorem pfs_strictStep_of_recursive : ∀ (fuel : Nat) (inp : Input)
    (o : Options) (res : FamilyResult),
    layoutRecursive fuel inp o = .ok res → WellFormed (inputModel inp o) →
    framedParents inp = true → ExpandChildParentStrictStep res := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro inp o res hrec hwf hfp
    cases fuel with
    | zero =>
      have hlay : layout inp o = .ok res := hrec
      obtain ⟨exec⟩ := layout_sceneExecution hlay
      exact fallbackOwnerStrictStep_executed exec hwf hfp
    | succ f =>
      rcases layoutRecursive_succ_sources hrec with ⟨_, hlay⟩ |
        ⟨g', P', met', chi', tls', par', hg', hP', hm', hchild', hwrap', hparent', hexpand'⟩
      · obtain ⟨exec⟩ := layout_sceneExecution hlay
        exact fallbackOwnerStrictStep_executed exec hwf hfp
      · have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
        have hcovered : RoutesCovered inp := inputRoutesCovered hwf
        obtain ⟨P'', met'', chi'', tls'', par'', frame'', _lines'', dx'', dy'',
          hP'', hm'', hchild'', hwrap'', hparent'', hexpand'', hframe'', _hlines'',
          hdx'', hdy'', hchildTransA, hparentTransA, _hroutesA, _hitemsA⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg' hrec
        have hwfPar : WellFormed
            (inputModel (parentSubInput inp g' P'' tls'' chi'') o) :=
          (subInputWellFormedC2 inp o g' hwf).2 _ _ _
        have hfpPar : framedParents (parentSubInput inp g' P'' tls'' chi'') = true :=
          framedParents_selectInput_outside_append inp o g' hwf hfp
            _ chi''.scene chi''.itemArea
        have ihPar := ih f (Nat.lt_succ_self f)
          (parentSubInput inp g' P'' tls'' chi'') o par'' hparent'' hwfPar hfpPar
        have ihChi := ih f (Nat.lt_succ_self f)
          (childSubInput inp g') (childSubOptions o g') chi'' hchild''
          ((subInputWellFormedC2 inp o g' hwf).1)
          ((framedParentsSub inp o g' hwf hfp).1)
        have hclosedPar := layoutRecursive_parent_closed_wellFormed hwfPar f par'' hparent''
        have hclosedChi := layoutRecursive_parent_closed_wellFormed
          ((subInputWellFormedC2 inp o g' hwf).1) f chi'' hchild''
        have hctx'' : ExpandChildCallContext f P'' inp o g' tls'' _ par'' chi'' res :=
          ⟨hwf, hg', rfl, hchild'', hparent'', hexpand''⟩
        have hparams'' : ExpandChildCallParams P'' inp o g' tls'' _ :=
          ⟨hP'', rfl, met'', hm'', hwrap''⟩
        have hwrapT : ExpandChildTitleWrapped P'' inp o g' tls'' :=
          ⟨met'', hm'', hwrap''⟩
        have hfitStrict := pfs_child_boxes_strictInside_frame f P'' inp o g' tls'' _
          par'' chi'' res hexpand'' hfp hctx'' hP'' hparams''
          frame'' tls'' dx'' dy'' hframe'' hdx'' hdy'' hwrapT
        obtain ⟨f0, m0, t0, _ls0, dx0, dy0, hf0, hm0, hw0, _hl0, hdx0, hdy0, _hc0,
          hb0⟩ := expandChild_sources hexpand''
        have hfEq : f0 = frame'' := Option.some.inj (hf0.symm.trans hframe'')
        have hmEq : m0 = met'' := Except.ok.inj (hm0.symm.trans hm'')
        rw [hmEq] at hw0
        have htEq : t0 = tls'' := Except.ok.inj (hw0.symm.trans hwrap'')
        have hdxEq : dx0 = dx'' := by rw [hdx0, hdx'', hfEq, htEq]
        have hdyEq : dy0 = dy'' := by rw [hdy0, hdy'', hfEq, htEq]
        rw [hdxEq, hdyEq] at hb0
        have hchildTrans : ∀ box : Box, chi''.scene.layoutDump.box? box.id = some box →
            res.scene.layoutDump.box? box.id =
              some (embedBox g'.id dx'' dy'' box) := by
          intro box hb
          have h := hchildTransA box hb
          simpa [embedBox] using h
        exact pfs_strictStep_transfer hframe'' hb0 hfitStrict ihPar ihChi
          hchildTrans hparentTransA hclosedChi hclosedPar

/-- `parentStrictStep`: the parent scene of every executed `expandChild`
call satisfies the strict step. -/
theorem parentStrictStep_of_recursion
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildParentStrictStep parent := by
  have _hex := hexpand
  have hctx0 := hctx
  obtain ⟨hwf, _, _, _, hparent, _⟩ := hctx0
  exact pfs_strictStep_of_recursive fuel (parentSubInput inp group P titleLines child) o
    parent hparent (pfs_parentInput_wellFormed hctx) (pfs_parentInput_framed hframed hctx)

end Elegant.Layered.PipelineImpl
