import Elegant.Layered.ExactFallbackCaptionClearProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactCaptionFallbackProof
import Elegant.Layered.FallbackCaptionClearProof
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.InputFixedFit
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.LabelsC8b
import Elegant.Layered.PipelineFacts
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact fallback caption facts: proven group-strict and owner-frame facts.

This file proves the two new residuals of
`ExactFallbackCaptionClearProof.lean`:

* `X_fallbackGroupStrictCaption_holds`, from the fixed-size output fit
  (`X_FixedOwnerFitX`, `ExactCaptionFitFactsProof.lean:163`) for fixed owners
  and a new no-title residual for non-fixed groups;
* `X_fallbackOwnerFrameClearXW_holds`, replaying
  `fallbackOwnerFrameClear_executed` (`FallbackOwnerFrameProof.lean:302`)
  over `SceneExecutionX` for the `W` conclusion below.

Well-formedness audit (`proofs/wip/Probe/ExactFallbackCaptionIllTProbe.lean`,
vector profile, `layoutX` on ill-formed inputs that still lay out): three of
the five residuals are false without well-formedness, so they take the `W`
form with local `WellFormed`/`framedParents` premises after the execution
binder. Failing rows:

* `X_SceneBoxesNodupX`: false on two boxes sharing an id (`ill-dup`
  `nodup=false`); the `W` form is proved below from the scene/input id
  transport and input uniqueness;
* `X_AncestorFrameStrictX`: false on a self-parented box, a two-parent cycle,
  and an unframed child (`ill-self`, `ill-cycle`, `ill-unframed`
  `ancstrict=false`); the `W` form stays open (needs the strict-step chain);
* `X_FallbackOwnerNoDescX`: false with an unframed child or a node parent
  (`ill-unframed`, `ill-nodeparent` `nodesc=false`); the `W` form is proved
  below by replaying `owner_not_in_ancestors_of_framed`.

`X_NonfixedGroupTitleX` (non-fixed groups record titles) and the imported
`X_FixedOwnerFitX` do not take well-formedness premises. Fallback caption
containment uses `X_OwnerCaptionContainFallbackFitW` for the current input. The `W`
owner-frame disjointness `XFB_OwnerFrameDisjointW` below is closed by
`XFB_ownerFrameDisjointW_of_chain` (`ExactOwnerFrameDisjointProof.lean`)
from the `c8aChain` seam through the executed flat C8a clause.
-/

/-- A non-fixed group owner always records an installed title: mirror of the
group half of `fallback_owner_cases` (`CaptionFallbackOwnerProof.lean:63`,
via `prepare_group_title_record` and the scene caption selector), stated
without the well-formedness premise so the group-strict proof can apply it.
Single title-presence fact, strictly narrower than any clearance goal. -/
def X_NonfixedGroupTitleX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {k : Nat} {obox : ModelBox},
    inp.boxes[k]? = some obox →
    obox.role = .group →
    inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false →
    ((sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id)).isSome = true

/-- `W` owner-frame disjointness: a group scene box is disjoint from the
fallback owner's scene box at `ownerIndex` once the two ids differ and
neither is a dump ancestor of the other, under the local admission premises
(`WellFormed`, `framedParents`). Moved here from
`ExactFallbackFrameFactsProof.lean` (which imports this module); closed by
`XFB_ownerFrameDisjointW_of_chain`
(`ExactOwnerFrameDisjointProof.lean`). -/
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

/-- `W` ancestor strictness: ancestor groups strictly contain the descendant
frame, under local well-formedness and framed parents. The non-`W` form is
false on self-parented boxes, parent cycles, and unframed children
(`ill-self`, `ill-cycle`, `ill-unframed`); the `W` form stays open (its proof
needs the strict-step chain). -/
def X_AncestorFrameStrictW (exactIds : List String) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (_execution : SceneExecutionX exactIds inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true)
    (g ob : Box),
    g ∈ res.scene.boxes → ob ∈ res.scene.boxes →
    g.role = "group" →
    g.id ∈ res.scene.layoutDump.ancestors ob.id →
    g.rect.StrictInside ob.rect

/-- `W` no-descendants: a fallback owner never appears in any scene ancestor
walk, under local well-formedness and framed parents. The non-`W` form is
false with an unframed child or a node parent (`ill-unframed`,
`ill-nodeparent`); the `W` form is proved below. -/
def X_FallbackOwnerNoDescW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true)
    (ownerIndex : Nat) (obox : ModelBox),
    inp.boxes[ownerIndex]? = some obox →
    (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
    ∀ (g : Box), obox.id ∉ res.scene.layoutDump.ancestors g.id

/-- `W` scene id uniqueness as a pure execution fact, under local
well-formedness. The non-`W` form is false on duplicate input ids
(`ill-dup`); the `W` form is proved below. -/
def X_SceneBoxesNodupW (exactIds : List String) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (_execution : SceneExecutionX exactIds inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true),
    (res.scene.boxes.map (·.id)).Nodup

/-- `W` owner-frame conclusion: the non-`W` `X_FallbackOwnerFrameClearX`
(`ExactFallbackCaptionClearProof.lean`) plus the two local premises its
proof needs. -/
def X_FallbackOwnerFrameClearXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    (ownerIndex : Nat) (obox : ModelBox) (g : Box),
    inp.boxes[ownerIndex]? = some obox →
    (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
    g ∈ res.scene.boxes → g.role = "group" →
    Disjoint g.rect
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect ∨
      g.rect.StrictInside
        ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
          ownerIndex ⟨"", "", default, "", false⟩).rect ∨
      g = (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩

/-- `W` fallback-caption conclusion: the non-`W` `X_FallbackCaptionClearB8`
(`ExactFlatC8b.lean:102`) plus the two local premises its proof needs. -/
def X_FallbackCaptionClearBW (exactIds : List String) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     (_hwf : WellFormed (inputModel inp o))
     (_hfp : framedParents inp = true),
     InputFixedFit inp o →
     ∀ (source : ModelLabel) (index ownerIndex : Nat) (g : Box),
      inp.labels[index]? = some source →
      inp.boxes.findIdx? (fun box : ModelBox =>
        box.id == source.owner && !box.exclusive) = some ownerIndex →
      (sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun t => t.1 == source.owner) = none →
      g ∈ res.scene.boxes → g.role = "group" →
      let l := ownedTextRect execution.params
        ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
          ownerIndex ⟨"", "", default, "", false⟩)
        (execution.lines.getD ownerIndex [])
      Disjoint g.rect l ∨ g.rect.StrictInside l

/-- `xfg_` copy of the `sceneBoxesExpr` bridge (see `xfb_sceneBoxes_eq` in
`ExactFallbackCaptionClearProof.lean`): the exact scene boxes are the
`sceneBoxesExpr` projection. Private lemmas do not resolve across modules. -/
private theorem xfg_sceneBoxes_eq {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    res.scene.boxes =
      sceneBoxesExpr execution.params inp o execution.packedAcc := by
  rw [execution.boxes_eq_mapX]
  rfl

/-- `xfg_` copy of the scene-box transport (see `xfb_box_index_origin` in
`ExactFallbackCaptionClearProof.lean`): the scene box at `index` comes from
the input box at the same index. -/
private theorem xfg_box_index_origin {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {index : Nat} {box : Box}
    (hbox : res.scene.boxes[index]? = some box) :
    ∃ source, inp.boxes[index]? = some source ∧
      box = Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default)))
        source.parent source.exclusive := by
  rw [execution.boxes_eq_mapX] at hbox
  cases hs : inp.boxes[index]? with
  | none => simp [hs] at hbox
  | some source =>
    refine ⟨source, rfl, ?_⟩
    simpa [hs] using hbox.symm

/-- `xfg_` copy of `go_succ_step` (`FallbackOwnerFrameProof.lean`): one
unfolded step of the ancestor walk. -/
private theorem xfg_go_succ_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- `xfg_` copy of `go_none_step` (`FallbackOwnerFrameProof.lean`): the
ancestor walk from a missing id is empty. -/
private theorem xfg_go_none_step {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- `xfg_` copy of `go_root_step` (`FallbackOwnerFrameProof.lean`): the
ancestor walk from a root box is empty. -/
private theorem xfg_go_root_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- `xfg_` copy of `ancestors_mem_ne` (`FallbackOwnerFrameProof.lean`):
members of an ancestor walk are never the empty id. -/
private theorem xfg_ancestors_mem_ne {d : LayoutDump} {x : String}
    {n : Nat} {s : String}
    (hmem : x ∈ LayoutDump.ancestors.go d n s) : x ≠ "" := by
  induction n generalizing s with
  | zero =>
      have e : LayoutDump.ancestors.go d 0 s = [] := rfl
      rw [e] at hmem
      cases hmem
  | succ n ih =>
      cases h : d.box? s with
      | none =>
          rw [xfg_go_none_step h] at hmem
          cases hmem
      | some b =>
          by_cases hpar : b.parent = ""
          · rw [xfg_go_root_step h hpar] at hmem
            cases hmem
          · rw [xfg_go_succ_step h hpar] at hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · rw [heq]
              exact hpar
            · exact ih hmem'

/-- `xfg_` copy of `ancestors_member_parent`
(`FallbackOwnerFrameProof.lean`): ancestor membership yields a scene box
parented at the member id. -/
private theorem xfg_ancestors_member_parent {d : LayoutDump} {x : String}
    {n : Nat} {s : String}
    (hmem : x ∈ LayoutDump.ancestors.go d n s) :
    ∃ c ∈ d.boxes, c.parent = x := by
  induction n generalizing s with
  | zero =>
      have e : LayoutDump.ancestors.go d 0 s = [] := rfl
      rw [e] at hmem
      cases hmem
  | succ n ih =>
      cases h : d.box? s with
      | none =>
          rw [xfg_go_none_step h] at hmem
          cases hmem
      | some b =>
          by_cases hpar : b.parent = ""
          · rw [xfg_go_root_step h hpar] at hmem
            cases hmem
          · rw [xfg_go_succ_step h hpar] at hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · exact ⟨b, List.mem_of_find?_eq_some h, heq.symm⟩
            · exact ih hmem'

/-- `xfg_` copy of `scene_box_source` (`FallbackOwnerFrameProof.lean`): every
scene box comes from the input box at the same index, keeping id, parent,
and role. -/
private theorem xfg_scene_box_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {b : Box} (hb : b ∈ res.scene.boxes) :
    ∃ (idx : Nat) (src : ModelBox), inp.boxes[idx]? = some src ∧
      b.id = src.id ∧ b.parent = src.parent ∧ b.role = src.role.id := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨src, hsrc, hboxeq⟩ := xfg_box_index_origin execution hidx
  refine ⟨idx, src, hsrc, ?_, ?_, ?_⟩ <;> rw [hboxeq]

/-- The exact group-owner strict caption from the fixed-size output fit and
the non-fixed title residual. Replay of the plain `hcapGroup` step
(`FallbackCaptionClearProof.lean:106`): a fixed owner takes its size bound
from the fit premise via `X_FixedOwnerFitX`; a non-fixed owner is impossible
by `X_NonfixedGroupTitleX` against the no-title premise. -/
theorem X_fallbackGroupStrictCaption_holds (exactIds : List String)
    (hfix : X_FixedOwnerFitX exactIds)
    (htitle : X_NonfixedGroupTitleX exactIds) :
    X_FallbackGroupStrictCaption exactIds := by
  intro inp o res execution hfit ownerIndex obox hobox hnone hex hown hgroup
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨obv, hobb⟩ : ∃ box : Box,
      (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = obv := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
    rw [xfg_sceneBoxes_eq execution]
    exact hobb
  obtain ⟨actual, hactual, hboxeq⟩ := xfg_box_index_origin execution hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hroleEq : obv.role = obox.role.id := by rw [hboxeq, hact]
  have hgroupScene : obv.role = "group" := by
    simp only [hroleEq, hgroup, BoxRole.id]
  rw [hgetD]
  by_cases hany : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true
  · have hfit' := hfix execution hfit hboxScene hobox hany hex hown
    rw [hgroup] at hfit'
    simp only [FixedSizeFit] at hfit'
    obtain ⟨hgw, hgh⟩ := hfit'
    have hcp : 0 < execution.params.clusterPad :=
      checkedParams_clusterPad_pos execution.checked
    rw [ownedTextRect_group_eq hgroupScene]
    exact titleRect_strictInside_of_fit hcp hgw hgh
  · have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false :=
      Bool.eq_false_iff.mpr hany
    have hsome := htitle execution hobox hgroup hfalse
    have hnoneSome : ((sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == obox.id)).isSome = false := by
      rw [hnone]
      rfl
    rw [hsome] at hnoneSome
    exact absurd hnoneSome (by decide)

/-- The `W` scene id uniqueness: proved from the scene/input id transport
(`boxes_eq_mapX`, `zipIdx_map_comp`) and input uniqueness
(`Model.boxIds_nodup`). -/
theorem X_sceneBoxesNodupW_holds (exactIds : List String) :
     X_SceneBoxesNodupW exactIds := by
   intro inp o res execution hwf _hfp
   have hmap : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
     rw [execution.boxes_eq_mapX, List.map_map]
     exact zipIdx_map_comp (·.id) inp.boxes 0
   rw [hmap]
   exact Model.boxIds_nodup hwf

/-- The `W` no-descendants fact: replay of `owner_not_in_ancestors_of_framed`
(`FallbackOwnerFrameProof.lean:155`) over `SceneExecutionX`. Any box
parented at the owner forces the owner to be a non-fixed group (via
`framedParents_parent` and input uniqueness), against the fallback cases. -/
theorem X_fallbackOwnerNoDescW_holds (exactIds : List String)
    (hcases : X_FallbackOwnerCasesX exactIds) :
    X_FallbackOwnerNoDescW exactIds := by
  intro inp o res execution hwf hfp ownerIndex obox hobox hnone g hmem
  have hmemGo : obox.id ∈ LayoutDump.ancestors.go res.scene.layoutDump
      res.scene.layoutDump.boxes.length g.id := hmem
  have hneid : obox.id ≠ "" := xfg_ancestors_mem_ne hmemGo
  obtain ⟨c, hcMem, hcPar⟩ := xfg_ancestors_member_parent hmemGo
  obtain ⟨cIdx, cSrc, hsrc, -, hcpar, -⟩ := xfg_scene_box_source execution hcMem
  have hspe : cSrc.parent = obox.id := hcpar.symm.trans hcPar
  have hsrcMem : cSrc ∈ inp.boxes := List.mem_of_getElem? hsrc
  have hne : cSrc.parent ≠ "" := by rw [hspe]; exact hneid
  obtain ⟨par, hparMem, hparId, hparRole, hparNotFixed⟩ :=
    framedParents_parent hfp hsrcMem hne
  have hparIdOb : par.id = obox.id := hparId.trans hspe
  obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp hparMem
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have ha : (inp.boxes.map (·.id))[pIdx]? = some obox.id := by
    simp [List.getElem?_map, hpIdx, hparIdOb]
  have hb : (inp.boxes.map (·.id))[ownerIndex]? = some obox.id := by
    simp [List.getElem?_map, hobox]
  have hlookups : (inp.boxes.map (·.id))[pIdx]? =
      (inp.boxes.map (·.id))[ownerIndex]? := by rw [ha, hb]
  have hbound : pIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hpIdx).1
  have hidxEq : pIdx = ownerIndex :=
    (List.Nodup.getElem?_inj hbound hids).mp hlookups
  have hparOb : par = obox := by
    have hsame : inp.boxes[pIdx]? = inp.boxes[ownerIndex]? := by rw [hidxEq]
    rw [hpIdx, hobox] at hsame
    exact Option.some.inj hsame
  have hfall := hcases execution hwf hobox hnone
  rcases hfall with hnode | hfixed
  · have hgr : obox.role = .group := hparOb ▸ hparRole
    rw [hnode] at hgr
    exact absurd hgr (by decide)
  · have hnf : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false := by
      rw [← hparIdOb]
      exact hparNotFixed
    rw [hfixed] at hnf
    exact absurd hnf (by decide)

/-- The `W` owner-frame fact from the C8a instance, ancestor strictness,
no-descendants, and scene nodup residuals. Replay of
`fallbackOwnerFrameClear_executed` (`FallbackOwnerFrameProof.lean:302`)
over `SceneExecutionX`: the owner itself is identified by index, an ancestor
group strictly contains the owner frame, and every other group is disjoint
by the C8a instance. -/
theorem X_fallbackOwnerFrameClearXW_holds (exactIds : List String)
    (hdisj : XFB_OwnerFrameDisjointW exactIds)
    (hastrict : X_AncestorFrameStrictW exactIds)
    (hnodesc : X_FallbackOwnerNoDescW exactIds)
    (hnodup : X_SceneBoxesNodupW exactIds) :
    X_FallbackOwnerFrameClearXW exactIds := by
  intro inp o res execution hwf hfp ownerIndex obox g hobox hnone hgMem hgRole
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨obv, hobb⟩ : ∃ box : Box,
      (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = obv := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
    rw [xfg_sceneBoxes_eq execution]
    exact hobb
  obtain ⟨actual, hactual, hboxeq⟩ := xfg_box_index_origin execution hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hobId : obv.id = obox.id := by rw [hboxeq, hact]
  have hobMem : obv ∈ res.scene.boxes := List.mem_of_getElem? hboxScene
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hgMem
  rw [hgetD]
  show Disjoint g.rect obv.rect ∨ g.rect.StrictInside obv.rect ∨ g = obv
  by_cases hjEq : j = ownerIndex
  · subst hjEq
    have hgo : g = obv :=
      Option.some.inj (hj.symm.trans hboxScene)
    exact Or.inr (Or.inr hgo)
  · by_cases hanc : g.id ∈ res.scene.layoutDump.ancestors obv.id
    · have hst := hastrict execution hwf hfp g obv hgMem hobMem hgRole hanc
      exact Or.inr (Or.inl hst)
    · by_cases hEqId : g.id = obox.id
      · have hnodup := hnodup execution hwf hfp
        have ha : (res.scene.boxes.map (·.id))[j]? = some obox.id := by
          simp [List.getElem?_map, hj, hEqId]
        have hb : (res.scene.boxes.map (·.id))[ownerIndex]? = some obox.id := by
          simp [List.getElem?_map, hboxScene, hobId]
        have hbound : j < (res.scene.boxes.map (·.id)).length := by
          rw [List.length_map]
          exact (List.getElem?_eq_some_iff.mp hj).1
        have heqIdx : j = ownerIndex :=
          (List.Nodup.getElem?_inj hbound hnodup).mp (ha.trans hb.symm)
        exact absurd heqIdx hjEq
      · have hancOb : g.id ∉ res.scene.layoutDump.ancestors obox.id := by
          rw [← hobId]
          exact hanc
        have hobAbsent := hnodesc execution hwf hfp ownerIndex obox hobox hnone g
        have hd := hdisj execution hwf hfp ownerIndex obox g hobox hnone hgMem
          hgRole hEqId hancOb hobAbsent
        rw [hgetD] at hd
        exact Or.inl hd

/-- The `W` fallback-caption clearance uses `X_OwnerCaptionContainFallbackFitW`
for the current well-formed execution. The proved `W` theorems discharge scene
nodup and no-descendants. Replay of the body of `X_fallbackCaptionClearB8_holds`
(`ExactFallbackCaptionClearProof.lean`) for the `W` conclusion. -/
theorem X_fallbackCaptionClearBW_closed (exactIds : List String)
    (hcontain : X_OwnerCaptionContainFallbackFitW exactIds)
    (hfix : X_FixedOwnerFitX exactIds)
    (htitle : X_NonfixedGroupTitleX exactIds)
    (hdisj : XFB_OwnerFrameDisjointW exactIds)
    (hastrict : X_AncestorFrameStrictW exactIds)
    (hcases : X_FallbackOwnerCasesX exactIds) :
    X_FallbackCaptionClearBW exactIds := by
  intro inp o res execution hwf hfp hfit source index ownerIndex g hsrc hfind
    hnone hgMem hgRole
  have hnodupW : X_SceneBoxesNodupW exactIds :=
    X_sceneBoxesNodupW_holds exactIds
  have hnodescW : X_FallbackOwnerNoDescW exactIds :=
    X_fallbackOwnerNoDescW_holds exactIds hcases
  have hR2 : X_FallbackGroupStrictCaption exactIds :=
    X_fallbackGroupStrictCaption_holds exactIds hfix htitle
  have hR3W : X_FallbackOwnerFrameClearXW exactIds :=
    X_fallbackOwnerFrameClearXW_holds exactIds hdisj hastrict hnodescW hnodupW
  obtain ⟨hlt, hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  obtain ⟨obox, hobox⟩ : ∃ obox, inp.boxes[ownerIndex]? = some obox :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hge : inp.boxes[ownerIndex] = obox :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hobox)
  rw [hge] at hpred
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpred
  obtain ⟨hownId, hex⟩ := hpred
  have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [hownId]
    exact hnone
  have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
    ⟨source, List.mem_of_getElem? hsrc, hownId.symm⟩
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨obv, hobb⟩ : ∃ box : Box,
      (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = obv := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
    rw [xfg_sceneBoxes_eq execution]
    exact hobb
  obtain ⟨actual, hactual, hboxeq⟩ := xfg_box_index_origin execution hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hroleEq : obv.role = obox.role.id := by rw [hboxeq, hact]
  have hcontFull : obv.rect.Contained (ownedTextRect execution.params obv
      (execution.lines.getD ownerIndex [])) := by
    have h := hcontain inp o res execution hwf hfit ownerIndex obox hobox hnone' hex hown
    rw [hgetD] at h
    exact h
  rw [hgetD]
  show Disjoint g.rect (ownedTextRect execution.params obv
      (execution.lines.getD ownerIndex [])) ∨
    g.rect.StrictInside (ownedTextRect execution.params obv
      (execution.lines.getD ownerIndex []))
  have hfr := hR3W execution hwf hfp ownerIndex obox g hobox hnone' hgMem hgRole
  rw [hgetD] at hfr
  rcases hfr with hdisj | hstrictfr | heq
  · exact Or.inl ((Disjoint.comm _ _).mpr
      (disjoint_of_sub_disjoint hcontFull ((Disjoint.comm _ _).mp hdisj)))
  · by_cases hgr : obox.role = .group
    · have hsc :=
        hR2 execution hfit ownerIndex obox hobox hnone' hex hown hgr
      rw [hgetD] at hsc
      have hcont2 : g.rect.Contained obv.rect := by
        unfold Rect.StrictInside at hstrictfr
        unfold Rect.Contained at ⊢
        omega
      exact Or.inr (strictInside_of_contained hsc hcont2)
    · have hgoal : g.rect.StrictInside (ownedTextRect execution.params obv
          (execution.lines.getD ownerIndex [])) := by
          unfold Rect.StrictInside at hstrictfr ⊢
          unfold Rect.Contained at hcontFull
          omega
      exact Or.inr hgoal
  · subst heq
    have hgr : obox.role = .group := by
      rw [hroleEq] at hgRole
      cases h : obox.role with
      | node =>
        rw [h] at hgRole
        simp only [BoxRole.id] at hgRole
        exact absurd hgRole (by decide)
      | group => rfl
    have hsc :=
      hR2 execution hfit ownerIndex obox hobox hnone' hex hown hgr
    rw [hgetD] at hsc
    exact Or.inr hsc

end PipelineImpl
end Layered
end Elegant
