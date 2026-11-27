import Elegant.Layered.SceneBounds
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.InsetFit
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.PolylineBoxMiss
import Elegant.Layered.ExpandChildTitleBandProof
import Elegant.Layered.CaptionFallbackContainProof

set_option autoImplicit false

/-!
# Child content of an executed `expandChild` lies in the child inset

For every executed expansion call — `expandChild P inp o group titleHeight
parent child = .ok res` — carries the executed-call premises
`ExpandChildCallContext` (`RecursiveCallContext.lean`) and
`framedParents inp = true`.
The margin tie: `layoutRecursive` binds `P ← checkedParams o.profile
inp.kind` before it calls `expandChild`, and the child call runs
`checkedParams (childSubOptions o group).profile (childSubInput inp
group).kind`, which is the same call (`selectInput` keeps `kind`, the
direction update keeps `profile`), so the child's execution margin is
`P.canvasMargin`.  The theorems carry `hP : checkedParams o.profile
inp.kind = .ok P`, which every executed call satisfies by that bind;
`layoutRecursive_checkedParams` records the same fact for any successful
`layoutRecursive`.

Boxes reuse `layoutRecursive_inset` (`InsetFit.lean`), which already lifts
the flat `layout_inset` box bound through the recursion.  Routes are proved
by a parallel induction: the flat branch transports the packed route bounds
through `orient`/`shift` into the inset, and the merge step transports
shifted child points through the executed frame fit
(`layoutRecursive_childInset_fits_frame`) into the parent inset.  Labels
need the same induction.  The group caption rect inside its frame is the
proved `expandChild_title_band` (`ExpandChildTitleBandProof.lean`),
instantiated at each nested expansion the induction encounters; the flat
fallback caption sits inside its owner box by
`ownerCaptionContainFallback_of_fit` (`CaptionFallbackContainProof.lean`)
from `WellFormed` and the `InputFixedFit` premise, threaded to both
sub-inputs at each expansion.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-- A successful `layoutRecursive` ran `checkedParams` on its own
profile/kind: the flat branch exposes it through `layout_sceneExecution`,
the recursive branch binds it before splitting. -/
theorem layoutRecursive_checkedParams (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res →
      ∃ Q : Params, checkedParams o.profile inp.kind = .ok Q := by
  induction fuel with
  | zero =>
    intro inp o res h
    obtain ⟨execution⟩ := layout_sceneExecution h
    exact ⟨execution.params, execution.checked⟩
  | succ fuel ih =>
    intro inp o res h
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨_, P, _, _, _, _, _, hP, _, _, _, _, _⟩
    · obtain ⟨execution⟩ := layout_sceneExecution hlayout
      exact ⟨execution.params, execution.checked⟩
    · exact ⟨P, hP⟩

/-- Packing translation and orientation place a packed point inside the
margin inset of the oriented expanded canvas.  Pure arithmetic over the
direction branches; the packed point only needs the accumulator bounds
`0 ≤ p.x ≤ W`, `0 ≤ p.y ≤ H`. -/
theorem orient_shiftPoint_pointIn_inset (d : Direction) (W H m : Int) (p : Point)
    (hp : 0 ≤ p.x ∧ p.x ≤ W ∧ 0 ≤ p.y ∧ p.y ≤ H) (_hm : 0 ≤ m) :
    PointIn (insetRect (orientCanvas d (W + 2 * m) (H + 2 * m)) m)
      (shiftPoint m m (orientPoint d H p)) := by
  cases d <;> simp only [PointIn, insetRect, shiftPoint, orientPoint,
    orientCanvas] <;> omega

/-- Flat `sceneOf` route points lie in the margin inset of the scene canvas:
the packed route bounds are transported through `orient`/`shift` exactly as
`sceneOf_routes_bounded` transports them into `Size.containsCell`, but the
inset conclusion keeps the non-strict packed bounds. -/
theorem sceneOf_routes_pointIn_inset (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (hacc : AccBounded acc.canvasW acc.canvasH acc) (hm : 0 ≤ P.canvasMargin) :
    ∀ q ∈ (sceneOf P inp o lines acc measured).routes.zipIdx,
      ∀ p ∈ q.1.points,
        PointIn (insetRect (sceneOf P inp o lines acc measured).canvas
          P.canvasMargin) p := by
  intro q hq p hp
  unfold sceneOf at hq ⊢
  dsimp only at hq ⊢
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp hq)
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at heq
  rw [← heq] at hp
  dsimp only at hp
  obtain ⟨origP, horigP, rfl⟩ := List.mem_map.mp hp
  cases hget : acc.routes[q.2]? with
  | none =>
    rw [Array.getD_eq_getD_getElem?, hget] at horigP
    contradiction
  | some pts =>
    rw [Array.getD_eq_getD_getElem?, hget] at horigP
    have hp_bound := hacc.routes_bounded q.2 pts hget origP horigP
    exact orient_shiftPoint_pointIn_inset o.direction acc.canvasW acc.canvasH _
      origP hp_bound hm

/-- Route points of a successful flat `layout` lie in the margin inset of
its canvas, at the params `checkedParams` returned. -/
theorem flat_layout_routes_inset {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) (Q : Params)
    (hQ : checkedParams o.profile inp.kind = .ok Q) :
    ∀ cr ∈ res.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect res.scene.canvas Q.canvasMargin) p := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  have hQeq : Q = execution.params :=
    Except.ok.inj (hQ.symm.trans execution.checked)
  subst hQeq
  intro cr hcr p hp
  rw [execution.scene_eq] at hcr ⊢
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcr
  have hzip : (cr, i) ∈ (sceneOf execution.params inp o execution.lines
      execution.straightAcc execution.measured).routes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hi
  have hm : 0 ≤ execution.params.canvasMargin := by
    have := checkedParams_canvasMargin_ge_one execution.checked
    omega
  have hacc := execution.straightAcc_bounded execution.components_parts_bounded
  exact sceneOf_routes_pointIn_inset execution.params inp o execution.lines
    execution.straightAcc execution.measured hacc hm (cr, i) hzip p hp

/-- Straightening preserves the installed-title captions: titles and canvas height are unchanged. -/
private theorem sceneTitlesExpr_straightAcc {inp : Input} {o : Options} {res : FamilyResult}
    (P : Params) (lines : List (List Measure.Line))
    (execution : SceneExecution inp o res) :
    sceneTitlesExpr P inp o lines execution.straightAcc =
      sceneTitlesExpr P inp o lines execution.packedAcc := by
  unfold sceneTitlesExpr
  rw [execution.straight_titles, execution.straight_canvasH]

/-- Straightening preserves the scene boxes: rects and canvas height are unchanged. -/
private theorem sceneBoxesExpr_straightAcc {inp : Input} {o : Options} {res : FamilyResult}
    (P : Params) (execution : SceneExecution inp o res) :
    sceneBoxesExpr P inp o execution.straightAcc =
      sceneBoxesExpr P inp o execution.packedAcc := by
  unfold sceneBoxesExpr
  rw [(straightenAcc_fields execution.straight_eq).1, execution.straight_canvasH]

/-- Labels of a successful flat `layout` lie in the margin inset of the
canvas.  The three `sceneOf` label families transport separately: measured
labels and installed title captions are margin-shifted packed rectangles
bounded by `AccBounded.labels_bounded`/`titles_bounded` plus the caption
size fit, and the `ownedTextRect` fallback caption sits inside its owner
box (`ownerCaptionContainFallback_of_fit` from `WellFormed` and the
`InputFixedFit` premise), which the box inset already covers. -/
theorem flat_layout_labels_inset {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hfit : InputFixedFit inp o)
    (h : layout inp o = .ok res) (Q : Params)
    (hQ : checkedParams o.profile inp.kind = .ok Q) :
    ∀ cl ∈ res.scene.labels,
      (insetRect res.scene.canvas Q.canvasMargin).Contained cl.rect := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  have _ := hfp
  have hfall := Elegant.Layered.ownerCaptionContainFallback_of_fit (res := res) hwf hfit
  have hQeq : Q = execution.params :=
    Except.ok.inj (hQ.symm.trans execution.checked)
  subst hQeq
  obtain ⟨P', hchecked', _hm', hinset⟩ := layout_inset h
  have hP'eq : P' = execution.params :=
    Except.ok.inj (hchecked'.symm.trans execution.checked)
  subst hP'eq
  rw [execution.scene_eq] at hinset
  have hacc := execution.straightAcc_bounded execution.components_parts_bounded
  have hmargin : 0 ≤ execution.params.canvasMargin := by
    have := checkedParams_canvasMargin_ge_one execution.checked
    omega
  intro cl hcl
  rw [execution.scene_eq] at hcl ⊢
  obtain ⟨q, hqmem, hemitted⟩ := List.mem_filterMap.mp hcl
  cases hexclusive : inp.boxes.any
      (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hexclusive, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == q.2) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      subst cl
      have hrect : let rect := execution.straightAcc.labels.getD measured.index default
          0 ≤ rect.x ∧ rect.x + rect.w ≤ execution.straightAcc.canvasW ∧
          0 ≤ rect.y ∧ rect.y + rect.h ≤ execution.straightAcc.canvasH ∧
          0 ≤ rect.w ∧ 0 ≤ rect.h := by
        cases hget : execution.straightAcc.labels[measured.index]? with
        | none =>
          rw [Array.getD_eq_getD_getElem?, hget]
          change 0 ≤ (0 : Int) ∧ 0 ≤ execution.straightAcc.canvasW ∧
            0 ≤ (0 : Int) ∧ 0 ≤ execution.straightAcc.canvasH ∧
            0 ≤ (0 : Int) ∧ 0 ≤ (0 : Int)
          exact ⟨by omega, hacc.canvas_w_nonneg, by omega, hacc.canvas_h_nonneg,
            by omega, by omega⟩
        | some stored =>
          rw [Array.getD_eq_getD_getElem?, hget]
          exact hacc.labels_bounded measured.index stored hget
      exact orient_shiftRect_inset_containsCellRect o.direction
        execution.straightAcc.canvasW execution.straightAcc.canvasH
        execution.params.canvasMargin _ hrect hmargin
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerIndex =>
        simp only [ho, Option.some.injEq] at hemitted
        subst cl
        show (insetRect (sceneOf execution.params inp o execution.lines
              execution.straightAcc execution.measured).canvas
              execution.params.canvasMargin).Contained
            (sceneCaptionRect execution.params inp o execution.lines
              execution.straightAcc ownerIndex q.1.owner)
        simp only [sceneCaptionRect]
        cases hT : (sceneTitlesExpr execution.params inp o execution.lines
            execution.straightAcc).find? (fun title => title.1 == q.1.owner) with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          obtain ⟨hltB, hmatch, _⟩ :=
            List.findIdx?_eq_some_iff_getElem.mp ho
          have hobox : inp.boxes[ownerIndex]? =
              some (inp.boxes[ownerIndex]'hltB) :=
            List.getElem?_eq_getElem hltB
          have hpred : (((inp.boxes[ownerIndex]'hltB).id == q.1.owner &&
              !(inp.boxes[ownerIndex]'hltB).exclusive) = true) := by
            simpa using hmatch
          cases hid : ((inp.boxes[ownerIndex]'hltB).id == q.1.owner) with
          | false =>
            simp [hid] at hpred
          | true =>
            have hoboxId : (inp.boxes[ownerIndex]'hltB).id = q.1.owner :=
              beq_iff_eq.mp hid
            cases hexb : (inp.boxes[ownerIndex]'hltB).exclusive with
            | true =>
              simp [hid, hexb] at hpred
            | false =>
              have hex : (inp.boxes[ownerIndex]'hltB).exclusive = false := hexb
              have hqget : inp.labels[q.2]? = some q.1 :=
                List.mem_zipIdx_iff_getElem?.mp hqmem
              have hqlabel : q.1 ∈ inp.labels := List.mem_of_getElem? hqget
              have hnone : (sceneTitlesExpr execution.params inp o execution.lines
                  execution.straightAcc).find? (fun title => title.1 ==
                    (inp.boxes[ownerIndex]'hltB).id) = none := by
                rw [hoboxId]
                exact hT
              have hown : ∃ l ∈ inp.labels,
                  l.owner = (inp.boxes[ownerIndex]'hltB).id :=
                ⟨q.1, hqlabel, hoboxId.symm⟩
              have hnoneP : (sceneTitlesExpr execution.params inp o execution.lines
                  execution.packedAcc).find? (fun title => title.1 ==
                    (inp.boxes[ownerIndex]'hltB).id) = none := by
                rw [← sceneTitlesExpr_straightAcc]
                exact hnone
              have hcontain :
                  ((sceneBoxesExpr execution.params inp o
                    execution.straightAcc).getD ownerIndex
                    ⟨"", "", default, "", false⟩).rect.Contained
                    (ownedTextRect execution.params
                      ((sceneBoxesExpr execution.params inp o
                        execution.straightAcc).getD ownerIndex
                        ⟨"", "", default, "", false⟩)
                      (execution.lines.getD ownerIndex [])) := by
                have h := hfall execution ownerIndex _ hobox hnoneP hex hown
                rwa [← sceneBoxesExpr_straightAcc] at h
              have hlt : ownerIndex <
                  (sceneBoxesExpr execution.params inp o
                    execution.straightAcc).length := by
                have hlt' := (List.findIdx?_eq_some_iff_getElem.mp ho).1
                simp only [sceneBoxesExpr, List.length_map, List.length_zipIdx]
                omega
              have hgetD : (sceneBoxesExpr execution.params inp o
                    execution.straightAcc).getD ownerIndex ⟨"", "", default, "", false⟩ =
                  (sceneBoxesExpr execution.params inp o
                    execution.straightAcc)[ownerIndex]'hlt := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
                rfl
              have hmem : (sceneBoxesExpr execution.params inp o
                    execution.straightAcc).getD ownerIndex ⟨"", "", default, "", false⟩ ∈
                  (sceneOf execution.params inp o execution.lines
                    execution.straightAcc execution.measured).boxes := by
                rw [hgetD]
                exact List.getElem_mem _
              have hboxIn := hinset _ hmem
              exact Rect.Contained.trans hboxIn hcontain
        | some title =>
          simp only [Option.map_some, Option.getD_some]
          obtain ⟨stored, hstored, hproduced⟩ :=
            List.mem_filterMap.mp (List.mem_of_find?_eq_some hT)
          obtain ⟨box, _, hproduced⟩ := Option.bind_eq_some_iff.mp hproduced
          have he := Option.some.inj hproduced
          subst title
          let lines := execution.lines.getD stored.1 []
          let width := lines.foldl (fun value line => max value line.width) 0
          let height := (max 1 lines.length : Int) * execution.params.lineH
          let size := match o.direction with
            | .LR | .RL => Size.mk height width
            | .TB | .BT => Size.mk width height
          have hstoredP : stored ∈ execution.packedAcc.titles := by
            rw [← execution.straight_titles]
            exact hstored
          have hfit := execution.packed_title_caption_fit stored hstoredP
          change 0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ stored.2.w ∧
            size.h ≤ stored.2.h at hfit
          have hstoredB := hacc.titles_bounded stored hstored
          have hrect : 0 ≤ stored.2.x ∧ stored.2.x + size.w ≤
              execution.straightAcc.canvasW ∧
              0 ≤ stored.2.y ∧ stored.2.y + size.h ≤
                execution.straightAcc.canvasH ∧
              0 ≤ size.w ∧ 0 ≤ size.h :=
            ⟨hstoredB.1, by omega, hstoredB.2.2.1, by omega, hfit.1, hfit.2.1⟩
          exact orient_shiftRect_inset_containsCellRect o.direction
            execution.straightAcc.canvasW execution.straightAcc.canvasH
            execution.params.canvasMargin { stored.2 with w := size.w, h := size.h }
            hrect hmargin
/-- Labels of a successful `layoutRecursive` lie in the margin inset of the
canvas, by induction on the fuel.  The flat branch is `flat_layout_labels_inset`
from `WellFormed` and the `InputFixedFit` premise; the merge transports shifted child
labels through the executed frame fit into the parent inset, parent labels
verbatim, and group captions through the proved `expandChild_title_band`
plus the parent box inset. -/
theorem layoutRecursive_labels_inset
    (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) →
      framedParents inp = true →
      InputFixedFit inp o →
      layoutRecursive fuel inp o = .ok res →
      ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
        ∀ cl ∈ res.scene.labels,
          (insetRect res.scene.canvas Q.canvasMargin).Contained cl.rect := by
  induction fuel with
  | zero =>
    intro inp o res hwf hframed hfit h Q hQ cl hcl
    exact flat_layout_labels_inset hwf hframed hfit h Q hQ cl hcl
  | succ fuel ih =>
    intro inp o res hwf hframed hfit h Q hQ cl hcl
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp,
        hexpand⟩
    · exact flat_layout_labels_inset hwf hframed hfit hlayout Q hQ cl hcl
    · have hQm : Pm = Q := Except.ok.inj (hPm.symm.trans hQ)
      subst hQm
      obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
      obtain ⟨hframedChild, hframedParentSub⟩ :=
        framedParentsSub inp o group hwf hframed
      have hframedParent : framedParents
          (parentSubInput inp group Pm titleLines child) = true :=
        hframedParentSub _ _ _
      have hQchild : checkedParams (childSubOptions o group).profile
          (childSubInput inp group).kind = .ok Pm := hQ
      have hQparent : checkedParams o.profile
          (parentSubInput inp group Pm titleLines child).kind = .ok Pm := hQ
      have hfitChild : InputFixedFit (childSubInput inp group)
          (childSubOptions o group) := hfit.childSubInput group
      have hcm := layoutRecursive_canvas_margins fuel hc
      have hcw : 2 * Pm.canvasMargin ≤ child.scene.canvas.w := by
        rw [checkedParams_canvasMargin hPm]
        exact hcm.1
      have hch : 2 * Pm.canvasMargin ≤ child.scene.canvas.h := by
        rw [checkedParams_canvasMargin hPm]
        exact hcm.2
      have hfitParent : InputFixedFit
          (parentSubInput inp group Pm titleLines child) o :=
        InputFixedFit.parentSubInput hwf hfit hPm hm ht hcw hch
      have hcIH := ih (childSubInput inp group) (childSubOptions o group) child
        hwfChild hframedChild hfitChild hc Pm hQchild
      have hwfParent : WellFormed
          (inputModel (parentSubInput inp group Pm titleLines child) o) :=
        hparentWF _ _ _
      have hpIH := ih (parentSubInput inp group Pm titleLines child) o parent
        hwfParent hframedParent hfitParent hp Pm hQparent
      obtain ⟨frame, metricS, ftl, _linesS, fdx, fdy, hframe, hmS, htlS, _hlS,
        hdxS, hdyS, hcanvasS, _hboxesS⟩ := expandChild_sources hexpand
      have hmetricSeq : metric = metricS :=
        Except.ok.inj (hm.symm.trans hmS)
      subst hmetricSeq
      have htlSeq : titleLines = ftl :=
        Except.ok.inj (ht.symm.trans htlS)
      subst htlSeq
      have hwrapS : ExpandChildTitleWrapped Pm inp o group titleLines :=
        ⟨metric, hm, ht⟩
      have hlabelsEq := expandChild_labels_eq_wrapped hexpand frame titleLines
        fdx fdy hframe hdxS hdyS hwrapS
      have hfitFrame : frame.rect.Contained
          (shiftRect fdx fdy (insetRect child.scene.canvas Pm.canvasMargin)) :=
        layoutRecursive_childInset_fits_frame hwf h hg hPm hm hc ht rfl hp
          frame fdx fdy hframe hdxS hdyS
      have hparentInset := layoutRecursive_inset fuel subInputWellFormedC2
        (parentSubInput inp group Pm titleLines child) o parent hwfParent hp Pm
        hQparent
      rw [hlabelsEq] at hcl
      obtain ⟨model, _hmodel, hbind⟩ := List.mem_filterMap.mp hcl
      cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
          { label with rect := shiftRect fdx fdy label.rect }) ++
        parent.scene.labels).find? (fun label : SceneLabel =>
          label.id == model.id)) with
      | none => rw [hfind] at hbind; simp at hbind
      | some label =>
        rw [hfind, Option.bind_some] at hbind
        have hclEq := Option.some.inj hbind
        by_cases hown : (model.owner == group.id) = true
        · rw [hown] at hclEq
          simp only [reduceIte] at hclEq
          have hframeMem : frame ∈ parent.scene.boxes :=
            List.mem_of_find?_eq_some hframe
          have hparams : ExpandChildCallParams Pm inp o group titleLines
              ((max 1 titleLines.length : Int) * Pm.lineH) :=
            ⟨hPm, rfl, hwrapS⟩
          have hctxNested : ExpandChildCallContext fuel Pm inp o group titleLines
              ((max 1 titleLines.length : Int) * Pm.lineH) parent child res :=
            ⟨hwf, hg, rfl, hc, hp, hexpand⟩
          have hband := expandChild_title_band fuel Pm inp o group titleLines
            ((max 1 titleLines.length : Int) * Pm.lineH) parent child res
            hexpand hframed hctxNested hparams
            frame titleLines fdx fdy hframe hdxS hdyS hwrapS
          have hcapFrame : frame.rect.Contained
              (groupTitleRect group Pm titleLines
                ((max 1 titleLines.length : Int) * Pm.lineH) frame) :=
            hband.1
          have hframeIn : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
              frame.rect := hparentInset.2 frame hframeMem
          rw [hcanvasS, ← hclEq]
          exact Rect.Contained.trans hframeIn hcapFrame
        · have hcondF : (model.owner == group.id) = false := by
            cases hb : (model.owner == group.id) with
            | false => rfl
            | true => exact absurd hb hown
          rw [hcondF] at hclEq
          simp only [Bool.false_eq_true, reduceIte] at hclEq
          have hlabelMem : label ∈ (child.scene.labels.map
              (fun l => { l with rect := shiftRect fdx fdy l.rect })) ++
              parent.scene.labels := List.mem_of_find?_eq_some hfind
          rcases List.mem_append.mp hlabelMem with hcm | hpm
          · obtain ⟨cl', hcl'mem, hcl'Eq⟩ := List.mem_map.mp hcm
            have hclIH : (insetRect child.scene.canvas Pm.canvasMargin).Contained
                cl'.rect := hcIH cl' hcl'mem
            have hshiftC : (shiftRect fdx fdy
                (insetRect child.scene.canvas Pm.canvasMargin)).Contained
                (shiftRect fdx fdy cl'.rect) :=
              (contained_shiftRect fdx fdy).mpr hclIH
            have hframeMem : frame ∈ parent.scene.boxes :=
              List.mem_of_find?_eq_some hframe
            have hframeIn : (insetRect parent.scene.canvas
                Pm.canvasMargin).Contained frame.rect :=
              hparentInset.2 frame hframeMem
            have hclRect : cl.rect = shiftRect fdx fdy cl'.rect := by
              rw [← hclEq, ← hcl'Eq]
            rw [hcanvasS, hclRect]
            exact Rect.Contained.trans hframeIn
              (Rect.Contained.trans hfitFrame hshiftC)
          · have hclRect : cl.rect = label.rect := by rw [← hclEq]
            rw [hcanvasS, hclRect]
            exact hpIH label hpm

/-- Route points of a successful `layoutRecursive` lie in the margin inset
of the canvas, by the same induction.  The flat branch transports the
packed accumulator route bounds through `orient`/`shift`; the merge shifts
child points into the frame and keeps parent points verbatim. -/
theorem layoutRecursive_routes_inset (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) →
      layoutRecursive fuel inp o = .ok res →
      ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
        ∀ cr ∈ res.scene.routes, ∀ p ∈ cr.points,
          PointIn (insetRect res.scene.canvas Q.canvasMargin) p := by
  induction fuel with
  | zero =>
    intro inp o res _hwf h Q hQ cr hcr p hp
    exact flat_layout_routes_inset h Q hQ cr hcr p hp
  | succ fuel ih =>
    intro inp o res hwf h Q hQ cr hcr p hp
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp',
        hexpand⟩
    · exact flat_layout_routes_inset hlayout Q hQ cr hcr p hp
    · have hQm : Pm = Q := Except.ok.inj (hPm.symm.trans hQ)
      subst hQm
      obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
      have hQchild : checkedParams (childSubOptions o group).profile
          (childSubInput inp group).kind = .ok Pm := hQ
      have hQparent : checkedParams o.profile
          (parentSubInput inp group Pm titleLines child).kind = .ok Pm := hQ
      have hcIH := ih (childSubInput inp group) (childSubOptions o group) child
        hwfChild hc Pm hQchild
      have hwfParent : WellFormed
          (inputModel (parentSubInput inp group Pm titleLines child) o) :=
        hparentWF _ _ _
      have hpIH := ih (parentSubInput inp group Pm titleLines child) o parent
        hwfParent hp' Pm hQparent
      obtain ⟨frame, metricS, ftl, _linesS, fdx, fdy, hframe, hmS, htlS, _hlS,
        hdxS, hdyS, hcanvasS, _hboxesS⟩ := expandChild_sources hexpand
      have hmetricSeq : metric = metricS :=
        Except.ok.inj (hm.symm.trans hmS)
      subst hmetricSeq
      have htlSeq : titleLines = ftl :=
        Except.ok.inj (ht.symm.trans htlS)
      subst htlSeq
      have hroutesEq := expandChild_routes_eq hexpand frame metric titleLines
        fdx fdy hframe hm ht hdxS hdyS
      have hfitFrame : frame.rect.Contained
          (shiftRect fdx fdy (insetRect child.scene.canvas Pm.canvasMargin)) :=
        layoutRecursive_childInset_fits_frame hwf h hg hPm hm hc ht rfl hp'
          frame fdx fdy hframe hdxS hdyS
      have hparentInset := layoutRecursive_inset fuel subInputWellFormedC2
        (parentSubInput inp group Pm titleLines child) o parent hwfParent hp' Pm
        hQparent
      rw [hroutesEq] at hcr
      obtain ⟨model, _hmodel, hbind⟩ := List.mem_filterMap.mp hcr
      cases hfind : (((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint fdx fdy) }) ++
        parent.scene.routes).find? (fun (route : Route) => route.id == model.id)) with
      | none => rw [hfind] at hbind; simp at hbind
      | some route =>
        rw [hfind] at hbind
        have hrEq : route = cr := Option.some.inj hbind
        have hrouteMem : route ∈ (child.scene.routes.map
            (fun r => { r with points := r.points.map (shiftPoint fdx fdy) })) ++
            parent.scene.routes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hrouteMem with hcm | hpm
        · obtain ⟨cr', hcr'mem, hcr'Eq⟩ := List.mem_map.mp hcm
          rw [← hrEq, ← hcr'Eq] at hp
          change p ∈ cr'.points.map (shiftPoint fdx fdy) at hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          have hqIH : PointIn (insetRect child.scene.canvas
              Pm.canvasMargin) q := hcIH cr' hcr'mem q hq
          have h1 : PointIn (shiftRect fdx fdy
              (insetRect child.scene.canvas Pm.canvasMargin))
              (shiftPoint fdx fdy q) := pointIn_shift hqIH
          have h2 : (shiftRect fdx fdy
              (insetRect child.scene.canvas Pm.canvasMargin)).Contained
              ⟨(shiftPoint fdx fdy q).x, (shiftPoint fdx fdy q).y, 0, 0⟩ :=
            (pointIn_contained).mp h1
          have h3 : frame.rect.Contained ⟨(shiftPoint fdx fdy q).x,
              (shiftPoint fdx fdy q).y, 0, 0⟩ :=
            Rect.Contained.trans hfitFrame h2
          have hframeMem : frame ∈ parent.scene.boxes :=
            List.mem_of_find?_eq_some hframe
          have h4 : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
              frame.rect := hparentInset.2 frame hframeMem
          have h5 : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
              ⟨(shiftPoint fdx fdy q).x, (shiftPoint fdx fdy q).y, 0, 0⟩ :=
            Rect.Contained.trans h4 h3
          rw [hcanvasS]
          exact (pointIn_contained).mpr h5
        · rw [← hrEq] at hp
          rw [hcanvasS]
          exact hpIH route hpm p hp

/-- Child boxes of an executed `expandChild` lie in the margin inset of the
child canvas: the flat `layout_inset` box bound lifted through the child
sub-input's `layoutRecursive` success. -/
theorem expandChild_child_boxes_inset
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hP : checkedParams o.profile inp.kind = .ok P) :
    ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect := by
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, _hparent, _hexpand'⟩ := hctx
  have hwfChild : WellFormed
      (inputModel (childSubInput inp group) (childSubOptions o group)) :=
    (subInputWellFormedC2 inp o group hwf).1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hinset := layoutRecursive_inset fuel subInputWellFormedC2
    (childSubInput inp group) (childSubOptions o group) child hwfChild hchild P
    hQchild
  exact hinset.2

/-- Child labels of an executed `expandChild` lie in the margin inset of the
child canvas, from the `InputFixedFit` premise threaded to the child sub-input. -/
theorem expandChild_child_labels_inset
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hfit : InputFixedFit inp o)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hP : checkedParams o.profile inp.kind = .ok P) :
    ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect := by
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, _hparent, _hexpand'⟩ := hctx
  have hwfChild : WellFormed
      (inputModel (childSubInput inp group) (childSubOptions o group)) :=
    (subInputWellFormedC2 inp o group hwf).1
  have hframedChild : framedParents (childSubInput inp group) = true :=
    (framedParentsSub inp o group hwf hframed).1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hfitChild : InputFixedFit (childSubInput inp group)
      (childSubOptions o group) := hfit.childSubInput group
  exact layoutRecursive_labels_inset fuel
    (childSubInput inp group) (childSubOptions o group) child hwfChild
    hframedChild hfitChild hchild P hQchild

/-- Child route points of an executed `expandChild` lie in the margin inset
of the child canvas. -/
theorem expandChild_child_routes_inset
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hP : checkedParams o.profile inp.kind = .ok P) :
    ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect child.scene.canvas P.canvasMargin) p := by
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, _hparent, _hexpand'⟩ := hctx
  have hwfChild : WellFormed
      (inputModel (childSubInput inp group) (childSubOptions o group)) :=
    (subInputWellFormedC2 inp o group hwf).1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  exact layoutRecursive_routes_inset fuel
    (childSubInput inp group) (childSubOptions o group) child hwfChild hchild P
    hQchild

end Elegant.Layered.PipelineImpl
