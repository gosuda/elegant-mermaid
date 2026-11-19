import Elegant.Layered.ExactFallbackCaptionFactsProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC3Closure
import Elegant.Layered.PipelineFacts
import Elegant.Layered.LabelsC8b
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact fallback frame facts: ancestor containment core and the two narrow residuals.

Two `ExactSeams` fields (`Kinds/UsecaseValidExact.lean`):
`fbDisj : X_OwnerFrameDisjointX exactIds` (premise-free C8a instance for the
fallback owner frame) and `fbStrict : X_AncestorFrameStrictW exactIds`
(W ancestor-frame strictness).

Probe evidence (`proofs/wip/Probe/ExactFbFrameTProbe.lean`, vector profile,
`layoutX [] inp tOpts`, eight executed exact inputs: nested fitting, nested
no-fix, sibling groups, zero-size nested inner, zero-size outer, empty group,
self-loop route, ill-formed self-parent):

| input | wf | fp | strict | disj | contained | upgrade |
|---|---|---|---|---|---|---|
| fb-nest-fit | true | true | true | true | true | true |
| fb-nest-nofix | true | true | true | true | true | true |
| fb-sib | true | true | true | true | true | true |
| fb-zero-nest | true | true | true | true | true | true |
| fb-zero-outer | true | false | false | true | false | true |
| fb-empty-group | true | true | true | true | true | true |
| fb-self-loop | true | true | true | true | true | true |
| fb-ill-self | false | true | false | true | true | false |

`strict`/`disj` mirror `X_AncestorFrameStrictW` (all ancestor pairs
`StrictInside`) and `X_OwnerFrameDisjointX` (every non-ancestor group frame
disjoint from the fallback owner frame); `contained` mirrors the non-strict
core below; `upgrade` mirrors the `Contained -> StrictInside` implication.
The two bare-false rows are W-vacuous: `fb-zero-outer` has
`framedParents = false`, `fb-ill-self` has `WellFormed = false`.
`X_OwnerFrameDisjointX` is true on every row, ill-formed included.
`XFB_AncestorStrictUpgradeW` is true on every row where the W premises hold
(the one bare-false row, `fb-ill-self`, has `WellFormed = false`).

Proved here:
* `XFB_ancestorContainedW_holds`: the ancestor containment core (non-strict):
  under local `WellFormed`/`framedParents`, every ancestor group frame
  contains the descendant scene box rect. Replay of `layoutX_c3`
  (`ExactFlatFacts.lean`) at one executed `SceneExecutionX` (the layout
  equation is consumed only to extract the execution there; every later step
  goes through execution fields), chained up the dump ancestor walk.
* `X_ancestorFrameStrictW_of_upgrade`: `X_AncestorFrameStrictW` from the core
  plus the upgrade residual below (modus ponens).

Staying open, one public def each:
* `XFB_AncestorStrictUpgradeW`: the strict upgrade given the now-proved
  containment. Needs the strict-step chain (title/margin reservation at
  frame level: `XCA_groupLinkXW_closed` per direct link, transported through
  `xcsp_sceneBox_rect_transport`); true on every probed W row.
* `XFB_OwnerFrameDisjointW`: the W form of `X_OwnerFrameDisjointX` (local
  `WellFormed`/`framedParents` after the execution binder). Needs the C8a
  span replay (`ExactFlatC8a.lean`) restricted to fallback pairs; true on
  every probed row. The consumers (`X_fallbackOwnerFrameClearXW_holds`,
  `X_fallbackCaptionClearBW_closed`) already hold `hwf`/`hfp` and can pass
  them once `ExactSeams.fbDisj` is rewired to this form.
-/

private theorem xfbfr_go_succ_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

private theorem xfbfr_go_none_step {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

private theorem xfbfr_go_root_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

private theorem xfbfr_eq_of_mem_idBox {boxes : List Box} (hnodup : (boxes.map (·.id)).Nodup)
    {a b : Box} (ha : a ∈ boxes) (hb : b ∈ boxes) (h : a.id = b.id) : a = b := by
  induction boxes generalizing a b with
  | nil => cases ha
  | cons c l ih =>
    rcases List.mem_cons.mp ha with rfl | hal
    · rcases List.mem_cons.mp hb with rfl | hbl
      · rfl
      · exact absurd (List.mem_map.mpr ⟨b, hbl, h.symm⟩) (List.nodup_cons.mp hnodup).1
    · rcases List.mem_cons.mp hb with rfl | hbl
      · exact absurd (List.mem_map.mpr ⟨a, hal, h⟩) (List.nodup_cons.mp hnodup).1
      · exact ih (List.nodup_cons.mp hnodup).2 hal hbl h

private theorem xfbfr_box_of_mem {d : LayoutDump} (hnd : (d.boxes.map (·.id)).Nodup)
    {b : Box} (hb : b ∈ d.boxes) : d.box? b.id = some b := by
  have hsome : (d.boxes.find? (fun x => x.id == b.id)).isSome = true :=
    List.find?_isSome.mpr ⟨b, hb, by simp⟩
  cases hfind : d.boxes.find? (fun x => x.id == b.id) with
  | none => simp [hfind] at hsome
  | some bx =>
    have hbxmem : bx ∈ d.boxes := List.mem_of_find?_eq_some hfind
    have hbxp := List.find?_some hfind
    simp only [beq_iff_eq] at hbxp
    have heq : bx = b := xfbfr_eq_of_mem_idBox hnd hbxmem hb hbxp
    rw [heq] at hfind
    exact hfind

private theorem xfbfr_c3_lookup {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {b : Box} (hb : b ∈ res.scene.layoutDump.boxes) (hbparent : b.parent ≠ "")
    {p : Box} (hpLookup : res.scene.layoutDump.box? b.parent = some p) :
    ∃ (bi pj : Nat) (childBox parent pbox : ModelBox),
      inp.boxes[bi]? = some childBox ∧ b.parent = childBox.parent ∧
      parent ∈ inp.boxes ∧ parent.id = childBox.parent ∧
      inp.boxes[pj]? = some parent ∧
      p.id = pbox.id ∧ p.id = b.parent ∧ bi < inp.boxes.length ∧
      pj < inp.boxes.length ∧
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)) ∧
      p.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD pj default)) := by
  simp only [Scene.layoutDump] at hb
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨childBox, hchildBoxMem, -, hbpar, -, hbrect⟩ :=
    sceneBox_source_rectX execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hchildBoxMem).1
  have hparentNe : childBox.parent ≠ "" := by rw [← hbpar]; exact hbparent
  obtain ⟨parent, hparentMem, hpid, -, -⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hchildBoxMem) hparentNe
  obtain ⟨piIdx, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hfind : res.scene.layoutDump.boxes.find? (fun x : Box => x.id == b.parent) =
      some p := hpLookup
  have hpMemDump : p ∈ res.scene.layoutDump.boxes := List.mem_of_find?_eq_some hfind
  have hpId : p.id = b.parent := by
    have hsome := List.find?_some hfind
    simpa only [beq_iff_eq] using hsome
  have hpMem : p ∈ res.scene.boxes := by
    simpa only [Scene.layoutDump] using hpMemDump
  obtain ⟨pj, hpj⟩ := List.mem_iff_getElem?.mp hpMem
  obtain ⟨pbox, hsp, hspid, -, -, hprect⟩ := sceneBox_source_rectX execution hpj
  have hjLen : pj < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsp).1
  have hmapLen2 : piIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[piIdx]? = (inp.boxes.map (·.id))[pj]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hsp]
    simp only [Option.map_some]
    rw [hpid.trans (hbpar.symm.trans (hpId.symm.trans hspid))]
  have hpe : piIdx = pj := (Model.boxIds_nodup hwf).getElem?_inj hmapLen2 |>.mp hid
  have hpiP : inp.boxes[pj]? = some parent := by rw [← hpe]; exact hpi
  exact ⟨bi, pj, childBox, parent, pbox, hchildBoxMem, hbpar, hparentMem, hpid,
    hpiP, hspid, hpId, hbiLen, hjLen, hbrect, hprect⟩

set_option maxHeartbeats 2000000 in
private theorem xfbfr_c3 {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    Validator.C3 res.scene.layoutDump := by
  have hXexec := exactComponentPlacement hwf hframed execution
  have hpackedEq := execution.packed_eq
  unfold packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := bind_ok hpackedEq
  have hcompMap := (actual_components_parts_geometryX (by rfl)
    execution.components_eq).1
  intro b hb hbparent p hpLookup
  obtain ⟨bi, pj, childBox, parent, pbox, hchildBoxMem, hbpar, hparentMem, hpid,
    hpiP, hspid, hpId, hbiLen, hjLen, hbrect, hprect⟩ :=
    xfbfr_c3_lookup execution hwf hframed hb hbparent hpLookup
  have hparentNe : childBox.parent ≠ "" := by rw [← hbpar]; exact hbparent
  obtain ⟨part, posB, k, -, hk, hposB⟩ := key_part_positionX execution hbiLen
  have hkLen := part_packed_box_lenX execution packed hpack hk
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨cand, run, loops, _area, hrun, _hloops, _hpartdef, hlookup⟩ :=
    part_frame_lookupX execution packed hpack hk hbox
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hcompMap]
    exact List.mem_map.mpr ⟨part, List.mem_of_getElem? hk, rfl⟩
  have hgl : bi < execution.graph.nodes.length := sceneExecutionX_graph_len execution hbiLen
  have hmemberGraph : execution.graph.nodes[bi]? = some execution.graph.nodes[bi] :=
    List.getElem?_eq_some_iff.mpr ⟨hgl, rfl⟩
  have hmemberLookup :
      (componentCandidate execution.graph part.1 cand).nodes[posB]? =
        some execution.graph.nodes[bi] :=
    component_node_lookupX hposB hmemberGraph
  have hkeyIn : bi ∈ part.1 := List.mem_of_getElem? hposB
  have hparentIn : pj ∈ part.1 :=
    hXexec.2.2 part.1 hcomp bi pj hbiLen hkeyIn
      _ hmemberGraph _ hchildBoxMem _ hpiP hpid.symm hparentNe
  obtain ⟨parentIndex, hpIdx⟩ := List.getElem?_of_mem hparentIn
  have hcontained :=
    hXexec.2.1 part.1 cand run (candidateOrder cand) hcomp hrun posB bi pj parentIndex
      _ hposB hbiLen hmemberLookup _ hchildBoxMem _ hpiP hpid.symm hparentNe hpIdx
  have hchildRect := hlookup posB bi hposB hbiLen
  have hparentRect := hlookup parentIndex pj hpIdx hjLen
  have hstep1 := contained_shiftRect_imp
    (dx := 0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured loops).minX)
    (dy := -(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured loops).minY)
    hcontained
  have hstep2 := contained_shiftRect_imp
    (dx := packed.boxes[k].x) (dy := packed.boxes[k].y) hstep1
  have hstep3 := contained_orientRect (d := o.direction)
    (h := execution.packedAcc.canvasH) hstep2
  have htransport := contained_shiftRect_imp
    (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin) hstep3
  rw [hprect, hbrect, hchildRect, hparentRect]
  exact htransport

private theorem xfbfr_go_contained {d : LayoutDump} (hC3 : Validator.C3 d)
    (hnd : (d.boxes.map (·.id)).Nodup) (gbox : Box) (hg : gbox ∈ d.boxes) :
    ∀ (n : Nat) (s : String) (cur : Box),
      d.box? s = some cur → cur ∈ d.boxes →
      gbox.id ∈ LayoutDump.ancestors.go d n s →
      gbox.rect.Contained cur.rect := by
  intro n
  induction n with
  | zero =>
    intro s cur _ _ hmem
    have e : LayoutDump.ancestors.go d 0 s = [] := rfl
    rw [e] at hmem
    cases hmem
  | succ n ih =>
    intro s cur hbox hcurmem hmem
    by_cases hpar : cur.parent = ""
    · rw [xfbfr_go_root_step hbox hpar] at hmem
      cases hmem
    · rw [xfbfr_go_succ_step hbox hpar] at hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · have hboxg : d.box? gbox.id = some gbox := xfbfr_box_of_mem hnd hg
        have hcur : d.box? cur.parent = some gbox := by
          rw [← heq]
          exact hboxg
        exact hC3 cur hcurmem hpar gbox hcur
      · cases hlook : d.box? cur.parent with
        | none =>
          have hempty : LayoutDump.ancestors.go d n cur.parent = [] := by
            cases n with
            | zero => rfl
            | succ m => exact xfbfr_go_none_step hlook
          rw [hempty] at htail
          cases htail
        | some parentbox =>
          have hpbmem : parentbox ∈ d.boxes := List.mem_of_find?_eq_some hlook
          have hIH := ih cur.parent parentbox hlook hpbmem htail
          have hstep := hC3 cur hcurmem hpar parentbox hlook
          exact Rect.Contained.trans hIH hstep

private theorem xfbfr_scene_nodup {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) : (res.scene.boxes.map (·.id)).Nodup := by
  have hmap : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapX, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  rw [hmap]
  exact Model.boxIds_nodup hwf

theorem XFB_ancestorContainedW_holds (exactIds : List String) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (_execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      (g ob : Box),
      g ∈ res.scene.boxes → ob ∈ res.scene.boxes →
      g.id ∈ res.scene.layoutDump.ancestors ob.id →
      g.rect.Contained ob.rect := by
  intro inp o res execution hwf hfp g ob hgMem hobMem hanc
  have hC3 := xfbfr_c3 execution hwf hfp
  have hnd : (res.scene.layoutDump.boxes.map (·.id)).Nodup := by
    have h := xfbfr_scene_nodup execution hwf
    simpa only [Scene.layoutDump] using h
  have hmemGo : g.id ∈ LayoutDump.ancestors.go res.scene.layoutDump
      res.scene.layoutDump.boxes.length ob.id := hanc
  have hobmem : ob ∈ res.scene.layoutDump.boxes := by
    simpa only [Scene.layoutDump] using hobMem
  have hgmem : g ∈ res.scene.layoutDump.boxes := by
    simpa only [Scene.layoutDump] using hgMem
  have hboxob : res.scene.layoutDump.box? ob.id = some ob :=
    xfbfr_box_of_mem hnd hobmem
  exact xfbfr_go_contained hC3 hnd g hgmem _ ob.id ob hboxob hobmem hmemGo

/-- W ancestor strictness given the containment core: the strictly narrower
residual for `fbStrict` (`X_AncestorFrameStrictW`). The upgrade itself needs
the strict-step chain; true on every probed W row. -/
def XFB_AncestorStrictUpgradeW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (g ob : Box),
    g ∈ res.scene.boxes → ob ∈ res.scene.boxes →
    g.role = "group" →
    g.id ∈ res.scene.layoutDump.ancestors ob.id →
    g.rect.Contained ob.rect →
    g.rect.StrictInside ob.rect

/-- W fallback-owner frame disjointness: the strictly narrower residual for
`fbDisj` (`X_OwnerFrameDisjointX`), adding the local admission premises. The
full instance needs the C8a span replay; true on every probed row. -/
def XFB_OwnerFrameDisjointW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (ownerIndex : Nat) (obox : ModelBox) (g : Box),
    inp.boxes[ownerIndex]? = some obox →
    (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
    g ∈ res.scene.boxes → g.role = "group" →
    g.id ≠ obox.id →
    g.id ∉ res.scene.layoutDump.ancestors obox.id →
    obox.id ∉ res.scene.layoutDump.ancestors g.id →
    Disjoint g.rect
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect

/-- `X_AncestorFrameStrictW` from the containment core plus the upgrade
residual. -/
theorem X_ancestorFrameStrictW_of_upgrade (exactIds : List String)
    (hUpg : XFB_AncestorStrictUpgradeW exactIds) :
    X_AncestorFrameStrictW exactIds := by
  intro inp o res execution hwf hfp g ob hgMem hobMem hgRole hanc
  exact hUpg execution hwf hfp g ob hgMem hobMem hgRole hanc
    (XFB_ancestorContainedW_holds exactIds execution hwf hfp g ob hgMem hobMem hanc)

end PipelineImpl
end Layered
end Elegant
