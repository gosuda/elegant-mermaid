import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactCaptionScopeProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactFlatC7Fit
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.InputFixedFit

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact caption scope clearance, well-formed-local (W) form.

`X_CaptionScopeClearanceFitW` is the `X_CaptionScopeClearanceFit`
(`ExactCaptionFallbackProof.lean`) statement with a local
`WellFormed (inputModel inp o)` premise directly after the execution
binder, next to its local `InputFixedFit` premise. No `framedParents`
premise appears: none of the consumed leaves needs it
(`X_OwnerCaptionContainFallbackFitW` and `X_OwnerScopeSamePartClearW`
take only `WellFormed`; the title and descendant branches take no
admission premise at all). `X_captionScopeClearanceFitW_holds` replays
`X_captionScopeClearanceFit_holds` over the W leaves proved in
`ExactCaptionFitFactsProof.lean`. -/

/-- Well-formed-local twin of `X_CaptionScopeClearanceFit`: the same
caption clearance tail with local `WellFormed` and `InputFixedFit`
premises after the execution binder, so family theorems discharge it
per executed input instead of over all inputs. -/
def X_CaptionScopeClearanceFitW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) →
    InputFixedFit inp o →
    ∀ (index ownerIndex : Nat) (source : ModelLabel) (lines : List String) (b : Box),
      inp.labels[index]? = some source →
      execution.measured.find? (fun item => item.index == index) = none →
      inp.boxes.findIdx?
        (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
      b ∈ res.scene.layoutDump.boxes →
      b.exclusive = true →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc
        (X_captionLabel exactIds execution ownerIndex source lines) →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- `xcsw_` copy of the private `XCapScope_findIdx_lookup`
(`ExactCaptionScopeProof.lean`): a `findIdx?` hit exposes the box at that
index and its predicate value. Private lemmas do not resolve across modules. -/
private theorem xcsw_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
    {n : Nat} (h : l.findIdx? p = some n) :
    n < l.length ∧ ∃ a, l[n]? = some a ∧ p a = true := by
  induction l generalizing n with
  | nil =>
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : n = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨Nat.zero_lt_succ _, a, rfl, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmlen, x, hxget, hpx⟩ := ih hmfind
      rw [← hmn]
      exact ⟨Nat.succ_lt_succ hmlen, x, (List.getElem?_cons_succ).trans hxget, hpx⟩

/-- `xcsw_` copy of the private `XCapScope_ownerScope_shiftRect_disjoint`
(`ExactCaptionScopeProof.lean`): `shiftRect` preserves rect disjointness. -/
private theorem xcsw_ownerScope_shiftRect_disjoint {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (shiftRect dx dy a)
      (shiftRect dx dy b) := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect] at h ⊢
  omega

/-- Per-instance replay of `XCapScope_captionDescendantClear_of_same_part`
over the W same-part core: the descendant clearance at one executed input,
threading that input's local core. The lookups need no admission premise. -/
private theorem xcsw_descendantClear_of_samePartW {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hsame : X_CaptionDescendantSamePartClear exactIds)
    {index ownerIndex : Nat} {source : ModelLabel} {lines : List String} {b : Box}
    (hsrc : inp.labels[index]? = some source)
    (hmeas : execution.measured.find? (fun item => item.index == index) = none)
    (hfindIdx : inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex)
    (hmem : b ∈ res.scene.layoutDump.boxes)
    (hex : b.exclusive = true)
    (hscope : b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines))
    (hd : source.owner ∈ res.scene.layoutDump.ancestors b.id) :
    ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect := by
  have hmem0 : b ∈ res.scene.layoutDump.boxes := hmem
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hmem
  obtain ⟨bi, hbi⟩ := hmem
  obtain ⟨sb, hsb, _hbid, _hsbpar, _hsbex, _hbrect⟩ :=
    sceneBox_source_rectX execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨hOILen, _obox, _hobox, _hpobox⟩ := xcsw_findIdx_lookup hfindIdx
  obtain ⟨partO, posO, kO, _hmemO, hkO, hposO⟩ := key_part_positionX execution hOILen
  obtain ⟨partB, posB, kB, _hmemB, hkB, hposB⟩ := key_part_positionX execution hbiLen
  exact hsame inp o res execution index ownerIndex bi source lines b hsrc hmeas
    hfindIdx hmem0 hex hscope hd kO kB posO posB partO partB hbi hkO hkB hposO hposB

/-- Per-instance replay of `XCapScope_ownerScopeExclusiveClear_of_same_part`
over the W same-part core: the non-descendant clearance at one executed
input, threading that input's local `WellFormed` premise into the core.
The cross-part half needs no admission premise. -/
private theorem xcsw_ownerScopeExclusiveClear_of_samePartW (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hsameW : X_OwnerScopeSamePartClearW exactIds)
    (hwf : WellFormed (inputModel inp o))
    {index ownerIndex : Nat} {source : ModelLabel} {lines : List String} {b : Box}
    (hsrc : inp.labels[index]? = some source)
    (hmeas : execution.measured.find? (fun item => item.index == index) = none)
    (hfindIdx : inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex)
    (hmem : b ∈ res.scene.layoutDump.boxes)
    (hex : b.exclusive = true)
    (hscope : b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines))
    (hd : source.owner ∉ res.scene.layoutDump.ancestors b.id)
    (hnone : (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) = none) :
    ¬ b.rect.meetsInterior
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect := by
  have hmem0 : b ∈ res.scene.layoutDump.boxes := hmem
  have hexprEq : (sceneBoxesExpr execution.params inp o execution.packedAcc) =
      res.scene.boxes := by
    rw [execution.boxes_eq_mapX]
    rfl
  have hboxLen : res.scene.boxes.length = inp.boxes.length := by
    rw [execution.boxes_eq_mapX, List.length_map, List.length_zipIdx]
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hmem
  obtain ⟨bi, hbi⟩ := hmem
  obtain ⟨sb, hsb, _hbid, _hsbpar, hsbex, hbrect⟩ :=
    sceneBox_source_rectX execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨hOI, obox, hobox, hpobox⟩ := xcsw_findIdx_lookup hfindIdx
  have hoboxEx : obox.exclusive = false := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
    simpa using hpobox.2
  have hownerLen : ownerIndex < res.scene.boxes.length := by omega
  obtain ⟨ownerBox, hownerGet⟩ : ∃ ob : Box, res.scene.boxes[ownerIndex]? = some ob :=
    ⟨_, List.getElem?_eq_getElem hownerLen⟩
  obtain ⟨_osource, _hos, _hoid, _hopar, _hoex, hownerRect⟩ :=
    sceneBox_source_rectX execution hownerGet
  obtain ⟨partO, posO, kO, _hmemO, hkO, hposO⟩ := key_part_positionX execution hOI
  obtain ⟨partB, posB, kB, _hmemB, hkB, hposB⟩ := key_part_positionX execution hbiLen
  by_cases hksame : kO = kB
  · have hkB' : execution.componentsAcc.parts[kB]? = some partO := hksame ▸ hkO
    have hpartEq : partB = partO := Option.some.inj (hkB.symm.trans hkB')
    rw [hpartEq] at hposB
    have hbine : bi ≠ ownerIndex := by
      intro heq
      have hsbEq : sb = obox := by
        rw [heq] at hsb
        exact Option.some.inj (hsb.symm.trans hobox)
      rw [hsbEq] at hsbex
      rw [hsbex] at hex
      rw [hoboxEx] at hex
      simp at hex
    have hposNe : posO ≠ posB := by
      intro heq
      rw [heq] at hposO
      exact hbine (Option.some.inj (hposB.symm.trans hposO))
    obtain ⟨packed, hpacked, _hfold⟩ := bind_ok execution.packed_eq
    have hKB : kB < packed.boxes.length :=
      part_packed_box_lenX execution packed hpacked hkB'
    obtain ⟨candB, runB, _loopsB, _areaB, hrunB, _hloopsB, _hpartdefB, hlookupB⟩ :=
      part_frame_lookupX execution packed hpacked hkB'
        (List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩)
    have hdisjFrame := hsameW inp o res execution hwf index ownerIndex source lines b
      hsrc hmeas hfindIdx hmem0 hex hscope hd hnone bi kB posO posB partO hbi hkB'
      hposO hposB hposNe candB runB hrunB
    have hdisjFrame' : Disjoint
        (frameRect execution.params
          (componentCandidate execution.graph partO.1 candB) runB posB)
        (frameRect execution.params
          (componentCandidate execution.graph partO.1 candB) runB posO) :=
      (Disjoint.comm _ _).mp hdisjFrame
    have hrectB := hlookupB posB bi hposB hbiLen
    have hrectO := hlookupB posO ownerIndex hposO hOI
    have hdisjPacked : Disjoint (execution.packedAcc.rects.getD bi default)
        (execution.packedAcc.rects.getD ownerIndex default) := by
      rw [hrectB, hrectO]
      exact xcsw_ownerScope_shiftRect_disjoint
        (xcsw_ownerScope_shiftRect_disjoint hdisjFrame')
    have hg : ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩) = ownerBox := by
      rw [hexprEq, List.getD_eq_getElem?_getD, hownerGet]
      rfl
    rw [hg, hownerRect, hbrect]
    exact disjoint_sceneTransport hdisjPacked
  · have hg : ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩) = ownerBox := by
      rw [hexprEq, List.getD_eq_getElem?_getD, hownerGet]
      rfl
    rw [hg]
    exact XCapScope_ownerScopeExclusiveClear_cross_part exactIds execution hOI
      hbiLen hownerRect hbrect hkO hkB hposO hposB hksame

/-- The well-formed-local exact caption scope clearance from the W leaves:
replay of `X_captionScopeClearanceFit_holds` feeding the local `WellFormed`
premise where the old proof used the global fit-only hypothesis. No premise
over all inputs. -/
theorem X_captionScopeClearanceFitW_holds (exactIds : List String)
    (hdesc : X_CaptionDescendantSamePartClear exactIds)
    (hcontainW : X_OwnerCaptionContainFallbackFitW exactIds)
    (hownersW : X_OwnerScopeSamePartClearW exactIds)
    (htitle : X_CaptionTitleBranchClear exactIds)
    (_hborder : X_OwnerResNodeBorderZeroX exactIds) :
    X_CaptionScopeClearanceFitW exactIds := by
  intro inp o res execution hwf hfit index ownerIndex source lines b hsrc hmeas
    hfindIdx hmem hex hscope
  by_cases hd : source.owner ∈ res.scene.layoutDump.ancestors b.id
  · exact xcsw_descendantClear_of_samePartW execution hdesc hsrc hmeas hfindIdx
      hmem hex hscope hd
  · simp only [sceneCaptionRect]
    cases hopt : (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      have hclr := xcsw_ownerScopeExclusiveClear_of_samePartW exactIds execution
        hownersW hwf hsrc hmeas hfindIdx hmem hex hscope hd hopt
      obtain ⟨_, obox, hobox, hpobox⟩ := xcsw_findIdx_lookup hfindIdx
      have heq : obox.id = source.owner := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
        exact hpobox.1
      have hnone : (sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
        rw [heq]
        exact hopt
      have hexcl : obox.exclusive = false := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
        simpa using hpobox.2
      have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
        ⟨source, List.mem_of_getElem? hsrc, heq.symm⟩
      have hc := hcontainW inp o res execution hwf hfit ownerIndex obox hobox hnone
        hexcl hown
      exact fun hmeet =>
        hclr (rect_meetsInterior_comm (contained_meetsInterior_mono hc hmeet))
    | some t =>
      simp only [Option.map_some, Option.getD_some]
      have ht := htitle inp o res execution index ownerIndex source lines b hsrc hmeas
        hfindIdx hmem hex hscope (by rw [hopt]; rfl)
      simp only [sceneCaptionRect] at ht
      rw [hopt] at ht
      simp only [Option.map_some, Option.getD_some] at ht
      exact ht

/-- `xcsw_` copy of the private `xc7f_caption_index_eq_of_id_eq`
(`ExactFlatC7Fit.lean`): two positions of a model label list whose labels
share an id are equal. Private lemmas do not resolve across modules. -/
private theorem xcsw_caption_index_eq_of_id_eq {l : List ModelLabel}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelLabel}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have e1 : (l.map (·.id))[i]? = some a.id := by
    rw [List.getElem?_map, hi, Option.map_some]
  have e2 : (l.map (·.id))[j]? = some a.id := by
    rw [List.getElem?_map, hj, Option.map_some, hid]
  have h3 : i < (l.map (·.id)).length := by simpa using hin
  have h4 : j < (l.map (·.id)).length := by simpa using hjn
  have hv : (l.map (·.id))[i]'h3 = (l.map (·.id))[j]'h4 :=
    Option.some.inj ((List.getElem?_eq_getElem h3).symm.trans (e1.trans (e2.symm.trans
      (List.getElem?_eq_getElem h4))))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j h3 h4 hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i h4 h3 hjt)
    · omega

/-- Fit-conditioned X caption containment over the W scope clearance:
mirror of `xc7f_sceneCaptionBoxContainmentFit` (`ExactFlatC7Fit.lean`)
threading the executed input's `WellFormed` premise into `hclearFitW`. -/
private theorem xcsw_sceneCaptionBoxContainmentFitW {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o)
    (hclearFitW : X_CaptionScopeClearanceFitW exactIds) :
    X_SceneCaptionBoxContainment exactIds inp o res := by
  intro execution l index source hl hsrc hid hmeas howner b hb hex hscope
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨lmodel, lindex⟩ := q
  have hsrcL : inp.labels[lindex]? = some lmodel := List.mem_zipIdx_iff_getElem?.mp hq
  have hlabelNodes := Elegant.Layered.labelIds_nodup hwf
  cases hexcl : inp.boxes.any
      (fun box => box.id == lmodel.owner && box.exclusive) with
  | true =>
    rw [hexcl] at hemitted
    simp only [↓reduceIte] at hemitted
    cases hemitted
  | false =>
    rw [hexcl] at hemitted
    simp only at hemitted
    cases hm : execution.measured.find? (fun item => item.index == lindex) with
    | some measured =>
      rw [hm] at hemitted
      have heq : l = _ := (Option.some.inj hemitted).symm
      have hidEq : lmodel.id = source.id := by
        have h1 : l.id = lmodel.id := by rw [heq]
        exact h1.symm.trans hid
      have hindex : lindex = index :=
        xcsw_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
      rw [hindex] at hm
      rw [hm] at hmeas
      cases hmeas
    | none =>
      rw [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == lmodel.owner && !box.exclusive) with
      | none =>
        rw [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        rw [ho] at hemitted
        have heq : l = _ := (Option.some.inj hemitted).symm
        have hidEq : lmodel.id = source.id := by
          have h1 : l.id = lmodel.id := by rw [heq]
          exact h1.symm.trans hid
        have hindex : lindex = index :=
          xcsw_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
        rw [hindex] at hsrcL
        have hlmodel : lmodel = source := Option.some.inj (hsrcL.symm.trans hsrc)
        have hoS : inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex := by
          rw [← hlmodel]
          exact ho
        have hrect : l.rect = sceneCaptionRect execution.params inp o
            execution.lines execution.packedAcc ownerIndex source.owner := by
          rw [congrArg (fun s : SceneLabel => s.rect) heq]
          unfold sceneCaptionRect
          rw [hlmodel]
          rfl
        have hscope' : b.id ∉ res.scene.layoutDump.labelOwnerAnc
            (X_captionLabel exactIds execution ownerIndex source l.lines) := by
          have hown : (X_captionLabel exactIds execution ownerIndex source l.lines).owner =
              l.toLabel.owner := by
            simp only [X_captionLabel]
            have h2 : l.owner = source.owner := by
              rw [congrArg (fun s : SceneLabel => s.owner) heq]
              rw [hlmodel]
            rw [h2]
          rw [Elegant.Layered.labelOwnerAnc_congr_owner hown]
          exact hscope
        have hclr := hclearFitW inp o res execution hwf hfit index ownerIndex source
          l.lines b hsrc (by rw [hindex] at hm; exact hm) hoS hb hex hscope'
        rw [hrect]
        exact hclr

/-- Flat C7 for the exact pipeline under the W scope premise: replay of
`flatC7B_layoutX_fit` (`ExactFlatC7Fit.lean`) taking
`X_CaptionScopeClearanceFitW` instead of the non-W premise. `FlatC7B` gives
the well-formedness of the input per call, fed to the W premise there. -/
theorem flatC7B_layoutX_fitW (exactIds : List String)
    (hloop : X_RunLocalLoopSeparation exactIds)
    (hcapFitW : X_CaptionScopeClearanceFitW exactIds) :
    FlatC7B (layoutX exactIds) := by
  intro inp o res hwf hfp hfit _hsep _hseam1 _hseam2 h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hrunlocal : X_RunLocalLabelClearance exactIds inp o res :=
    X_runLocalLabelClearance_holds (inp := inp) (o := o) (res := res) hloop
      (x_runLocalForwardSeparation_holds exactIds)
      (x_runLocalReversedSeparation_holds exactIds)
  have hbelong : X_LabelBelongsToRun exactIds inp o res :=
    X_labelBelongsToRun (inp := inp) (o := o) (res := res) hwf x_routeLabelsPlaced_holds
  have hbox : X_ExclusiveBoxInLabelRun exactIds inp o res :=
    X_exclusiveBoxInLabelRun (inp := inp) (o := o) (res := res) hwf hfp
      (x_exclusiveRunNodeDecl_holds exactIds)
      (x_exclusiveKeyOutsideCgPaths_holds exactIds)
  have hbridges : X_RouteLabelDumpBridges exactIds inp o res :=
    X_routeLabelDumpBridges (inp := inp) (o := o) (res := res) hbelong hbox
  have hparts : X_PartsSeparated exactIds inp o res :=
    X_partsSeparated_holds (inp := inp) (o := o) (res := res)
  have hcaps : X_SceneCaptionBoxContainment exactIds inp o res :=
    xcsw_sceneCaptionBoxContainmentFitW (inp := inp) (o := o) (res := res) hwf hfit
      hcapFitW
  exact X_layout_c7 hwf hfp hparts ⟨hrunlocal, hbridges⟩ hcaps h

end PipelineImpl
end Layered
end Elegant
