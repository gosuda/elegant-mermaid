import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.LabelsClearance
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.PipelineFacts
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C8b: `FlatC8bB (layoutX exactIds)`.

Replays `layout_c8b` over `SceneExecutionX`. The plain clause (`LabelsC8b.lean`)
takes the packed-coordinate clearance `LabelFramePackedClear` (route-label and
installed-title rects against every group frame) and the scene-level fallback
branch `FallbackCaptionClear` (the `ownedTextRect` caption against every group
frame). The plain discharge (`layoutFamily_valid_of_seams` in
`FamilyAssembly.lean`) builds that pair with `frameLabels_executed` from the
component-local geometric cores (`ExecutedPartFrameCores`, a named open seam)
and the owner-frame residual (`FallbackOwnerFrameClear`, proved outright via
`fallbackOwnerFrameClear_executed` from `flatC8a_executed` and the strict step,
bottoming out in the open seam `ForeignBorderChainXAligned`).

Over `layoutX` the packed transport (`PackedPartTransportBounded`) and the
fallback owner analysis (`fallback_owner_cases`, `fixed_owner_fit`,
`ownerCaptionContainFallback_of_fit`) have no exact port and their replays are
long, so each plain run-level fact below is stated as its own exact mirror
`X_...B8` hypothesis, one per plain fact. The packed-clear conclusion itself is
reproved here from the cores and transport mirrors (a verbatim replay of
`labelFramePackedClear_of_bounded`, which needs only generic shelf geometry);
the fallback-clear conclusion is taken as a mirror hypothesis; the final
assembly is a verbatim replay of `layout_c8b` with the exact scene bridges
(`boxes_eq_mapX`, `components_rects_size`). -/

/-- X core residual: mirror of `ExecutedPartFrameCores` over `SceneExecutionX`.
Plain counterpart: the named open seam `LayeredSeams.executedPartFrameCores`. -/
def X_ExecutedPartFrameCoresB8 (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

/-- X transport residual: mirror of `PackedPartTransportBounded` over
`SceneExecutionX` (same clause order and shape, with the rect clause guarded by
`k < packedAcc.rects.size` as in the plain repaired transport).
Plain counterpart: `packedTransportBounded_of_residuals`, proved outright over
the plain pipeline; the exact replay is long (exact shelf existence, exact title
and rect-value sources), so it stays a hypothesis. -/
def X_PackedPartTransportBoundedB8 (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (∀ (k : Nat), k < execution.packedAcc.rects.size → ∀ (r : Rect),
        execution.packedAcc.rects.getD k default = r →
        ∃ (pk : Nat) (part : List Nat × Part) (pos : Nat) (r0 box : Rect),
          execution.componentsAcc.parts[pk]? = some part ∧ part.1[pos]? = some k ∧
          part.2.rects[pos]? = some r0 ∧
          packed.boxes[pk]? = some box ∧
          r = shiftRect box.x box.y r0 ∧
          box.Contained r) ∧
      (∀ (index : Nat) (r : Rect), execution.packedAcc.labels.getD index default = r →
        (∃ (pl : Nat) (part : List Nat × Part) (r0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧
          (index, r0) ∈ part.2.labels ∧
          packed.boxes[pl]? = some box ∧
          r = shiftRect box.x box.y r0 ∧
          box.Contained r) ∨
        r = default) ∧
      (∀ (key : Nat) (stored : Rect), (key, stored) ∈ execution.packedAcc.titles →
        ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧ part.1[i]? = some key ∧
          (i, stored0) ∈ part.2.titles ∧
          packed.boxes[pl]? = some box ∧
          stored = shiftRect box.x box.y stored0 ∧
          box.Contained
            (shiftRect box.x box.y
              { stored0 with
                w := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).w
                h := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).h })) ∧
      (∀ (k : Nat) (r : Rect), execution.packedAcc.rects.getD k default = r → 0 ≤ r.x)

/-- X fallback residual: mirror of `FallbackCaptionClear` over `SceneExecutionX`
(same body, with the fixed-size fit premise it is proved from).
Plain counterpart: `fallbackCaptionClear_of_fit`, proved outright over the plain
pipeline from `FallbackOwnerFrameClear`; the exact replay is long (exact
fallback-owner cases, exact fixed-owner fit, exact owner-caption containment),
so it stays a hypothesis. -/
def X_FallbackCaptionClearB8 (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
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

/-- The caption resize commutes with the shelf translation (copy of the private
`caption_shift_comm` in `FrameLabelsProof.lean`). -/
private theorem b8_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl

/-- Two positions of a box list whose boxes share an id are equal (copy of the
private `index_eq_of_id_eq` in `LabelsC8b.lean`). -/
private theorem b8_index_eq_of_id_eq {l : List ModelBox}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelBox}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hil : i < (l.map (·.id)).length := by rw [List.length_map]; exact hin
  have hjl : j < (l.map (·.id)).length := by rw [List.length_map]; exact hjn
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have hv : (l.map (·.id))[i] = (l.map (·.id))[j] := by
    have e1 : (l.map (·.id))[i]? = some ((l.map (·.id))[i]) :=
      List.getElem?_eq_getElem hil
    have e2 : (l.map (·.id))[j]? = some ((l.map (·.id))[j]) :=
      List.getElem?_eq_getElem hjl
    exact Option.some.inj (e1.symm.trans (hget.trans e2))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j hil hjl hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i hjl hil hjt)
    · omega

/-- The packing fold preserves the rect array size (copy of the private
`X_packFold_rects_size` in `ExactFitClosure.lean`). -/
private theorem b8_packFold_rects_sizeX
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Exact packed rect array size (copy of the private `X_packed_rects_size` in
`ExactFitClosure.lean`). -/
private theorem b8_packedAcc_rects_sizeX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [b8_packFold_rects_sizeX]
  exact execution.components_rects_size

set_option maxHeartbeats 800000 in
/-- The packed-coordinate C8b core over the exact execution: the X component
cores plus the X transport give `LabelFramePackedClear`. Replay of
`labelFramePackedClear_of_bounded` in `FrameLabelsProof.lean`; every step is
generic shelf geometry once the transport supplies the part correspondence. -/
private theorem b8_labelFramePackedClear_of_bounded {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hcores : X_ExecutedPartFrameCoresB8 exactIds)
    (htransport : X_PackedPartTransportBoundedB8 exactIds) :
    LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc := by
  obtain ⟨packed, hpack, hrects, hlabels, htitles, hnonneg⟩ := htransport execution
  refine ⟨?_, ?_⟩
  · intro index k gBox hbox hrole
    dsimp only
    have hksize : k < execution.packedAcc.rects.size := by
      rw [b8_packedAcc_rects_sizeX execution]
      exact (List.getElem?_eq_some_iff.mp hbox).1
    obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
      hrects k hksize (execution.packedAcc.rects.getD k default) rfl
    rw [hreq] at hboxk
    rcases hlabels index (execution.packedAcc.labels.getD index default) rfl with
      ⟨pl, partl, r0l, bl, hpartl, hmeml, hbl, hreql, hboxl⟩ | hdef
    · rw [hreql] at hboxl
      by_cases hpk : pk = pl
      · subst hpk
        obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
        obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
        obtain ⟨hcore, -⟩ := (hcores execution) partk (List.mem_of_getElem? hpartk)
        have hclr := hcore index r0l posk k gBox r0 hmeml hkeyk hbox hrole hr0
        rw [hreq, hreql]
        rcases hclr with h | h
        · exact Or.inl (disjoint_shiftRect h)
        · exact Or.inr (strictInside_shiftRect h)
      · have hpkL : pk < execution.componentsAcc.parts.length :=
          (List.getElem?_eq_some_iff.mp hpartk).1
        have hplL : pl < execution.componentsAcc.parts.length :=
          (List.getElem?_eq_some_iff.mp hpartl).1
        have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
          rw [Pack.pack_count hpack, List.length_map]
        have hpkBox : pk < packed.boxes.length := by omega
        have hplBox : pl < packed.boxes.length := by omega
        have hd : Disjoint bk bl := by
          have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
            Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
          have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
          have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
          rw [hbk', hbl'] at hd0
          exact hd0
        rw [hreq, hreql]
        exact Or.inl (disjoint_of_contained_disjoint hboxk hboxl hd)
    · rw [hreq, hdef]
      exact Or.inl (disjoint_default_of_nonneg (by
        rw [← hreq]
        exact hnonneg k (execution.packedAcc.rects.getD k default) rfl))
  · intro key stored htitle k gBox hbox hrole
    dsimp only
    have hksize : k < execution.packedAcc.rects.size := by
      rw [b8_packedAcc_rects_sizeX execution]
      exact (List.getElem?_eq_some_iff.mp hbox).1
    obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
      hrects k hksize (execution.packedAcc.rects.getD k default) rfl
    rw [hreq] at hboxk
    obtain ⟨pl, partl, i, stored0, bl, hpartl, hkeyi, hmeml, hbl, hstored, hboxCap⟩ :=
      htitles key stored htitle
    by_cases hpk : pk = pl
    · subst hpk
      obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
      obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
      obtain ⟨-, hcore⟩ := (hcores execution) partk (List.mem_of_getElem? hpartk)
      have hgetD : partk.1.getD i 0 = key := by
        simp only [List.getD, hkeyi, Option.getD_some]
      have hclr := hcore i stored0 posk k gBox r0 hmeml hkeyk hbox hrole hr0
      simp only [hgetD] at hclr
      rw [hreq, hstored, b8_caption_shift_comm]
      rcases hclr with h | h
      · exact Or.inl (disjoint_shiftRect h)
      · exact Or.inr (strictInside_shiftRect h)
    · have hpkL : pk < execution.componentsAcc.parts.length :=
        (List.getElem?_eq_some_iff.mp hpartk).1
      have hplL : pl < execution.componentsAcc.parts.length :=
        (List.getElem?_eq_some_iff.mp hpartl).1
      have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
        rw [Pack.pack_count hpack, List.length_map]
      have hpkBox : pk < packed.boxes.length := by omega
      have hplBox : pl < packed.boxes.length := by omega
      have hd : Disjoint bk bl := by
        have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
          Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
        have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
        have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
        rw [hbk', hbl'] at hd0
        exact hd0
      rw [hreq, hstored, b8_caption_shift_comm]
      exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)

set_option maxHeartbeats 1000000 in
/-- Clause 8, condition 2 of the layout validator for a successful exact
`layoutX` under the well-formed input model and the X label/frame clearance
facts. Replay of `layout_c8b` in `LabelsC8b.lean` over `SceneExecutionX`, with
`boxes_eq_mapX` for the scene-box lookup and the copied id-equality lemma. -/
private theorem b8_layout_c8b {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hpack : LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc)
    (hfall : X_FallbackCaptionClearB8 exactIds)
    (hfit : InputFixedFit inp o)
    (hwf : WellFormed (inputModel inp o)) :
    Validator.C8b res.scene.layoutDump := by
  have hfallApp := hfall execution hfit
  obtain ⟨hpackLabels, hpackTitles⟩ := hpack
  have hlabBridge : (sceneOf execution.params inp o execution.lines
      execution.straightAcc execution.measured).labels =
      (sceneOf execution.params inp o execution.lines execution.packedAcc
        execution.measured).labels :=
    (sceneOf_straightenAcc execution.params inp o execution.lines
      execution.packedAcc execution.straightAcc execution.measured
      execution.straight_eq).2.2
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  intro g hgMem hgRole l hlMem
  simp only [Scene.layoutDump] at hgMem hlMem
  obtain ⟨sl, hsl, hlEq⟩ := List.mem_map.mp hlMem
  rw [execution.scene_eq, hlabBridge] at hsl
  obtain ⟨qL, hqL, hemitted⟩ := List.mem_filterMap.mp hsl
  obtain ⟨source, indexL⟩ := qL
  have hsrcL : inp.labels[indexL]? = some source :=
    List.mem_zipIdx_iff_getElem?.mp hqL
  have hslRect : l.rect = sl.rect := by rw [← hlEq]
  rw [execution.boxes_eq_mapX] at hgMem
  obtain ⟨q, hq, hgeq⟩ := List.mem_map.mp hgMem
  obtain ⟨hgBox, hKey⟩ := q
  dsimp only [Prod.fst, Prod.snd] at hgeq hq
  have hk : inp.boxes[hKey]? = some hgBox := List.mem_zipIdx_iff_getElem?.mp hq
  have hgRole0 : g.role = hgBox.role.id := by
    rw [← hgeq]
  have hgroupRole : hgBox.role = BoxRole.group := by
    have hgid : hgBox.role.id = "group" := hgRole0.symm.trans hgRole
    cases hrole : hgBox.role with
    | node =>
      rw [hrole] at hgid
      simp only [BoxRole.id] at hgid
      exact absurd hgid (by decide)
    | group => rfl
  have hgRect : g.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin (orientRect o.direction
        execution.packedAcc.canvasH (execution.packedAcc.rects.getD hKey default)) := by
    rw [← hgeq]
  cases hexcl : inp.boxes.any (fun box : ModelBox =>
      box.id == source.owner && box.exclusive) with
  | true =>
    simp only [hexcl, ↓reduceIte] at hemitted
    cases hemitted
  | false =>
    simp only [hexcl] at hemitted
    cases hm : execution.measured.find?
        (fun item : MeasuredLabel => item.index == indexL) with
    | some measured =>
      have hpm := List.find?_some hm
      have hmIdx : measured.index = indexL := by simpa using hpm
      have hrel := hpackLabels indexL hKey hgBox hk hgroupRole
      simp only [hm] at hemitted
      have hlrect : sl.rect = shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            (execution.packedAcc.labels.getD indexL default)) := by
        have heq' := Option.some.inj hemitted
        have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
        dsimp only at hrr
        rw [hrr, hmIdx]
      rw [hslRect, hgRect, hlrect]
      cases hrel with
      | inl h => exact Or.inl (disjoint_sceneTransport h)
      | inr h => exact Or.inr (strictInside_sceneTransport h)
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box : ModelBox =>
          box.id == source.owner && !box.exclusive) with
      | none =>
        simp only [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        simp only [ho] at hemitted
        obtain ⟨hb, hownerPred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
        have hobGet : inp.boxes[ownerIndex]? = some inp.boxes[ownerIndex] :=
          List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
        have hownerId : inp.boxes[ownerIndex].id = source.owner := by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hownerPred
          exact hownerPred.1
        have heq := hemitted
        have hselD : (sceneTitlesExpr execution.params inp o execution.lines
            execution.packedAcc).find? (fun t => t.1 == source.owner) = none ∨
            ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := by
          cases h : (sceneTitlesExpr execution.params inp o execution.lines
              execution.packedAcc).find? (fun t => t.1 == source.owner) with
          | none => exact Or.inl rfl
          | some t => exact Or.inr ⟨t, rfl⟩
        cases hselD with
        | inl hsel =>
          have hgMemScene : g ∈ res.scene.boxes := by
            rw [execution.boxes_eq_mapX]
            exact hgMem
          have hlrect : sl.rect = ownedTextRect execution.params
              ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                ownerIndex ⟨"", "", default, "", false⟩)
              (execution.lines.getD ownerIndex []) := by
            have heq' := Option.some.inj heq
            have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
            dsimp only at hrr
            rw [hrr]
            show (Option.map (fun x => x.snd)
                ((sceneTitlesExpr execution.params inp o execution.lines
                  execution.packedAcc).find? (fun t => t.1 == source.owner))).getD
                (ownedTextRect execution.params
                  ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                    ownerIndex ⟨"", "", default, "", false⟩)
                  (execution.lines.getD ownerIndex [])) =
              ownedTextRect execution.params
                ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                  ownerIndex ⟨"", "", default, "", false⟩)
                (execution.lines.getD ownerIndex [])
            rw [hsel]
            rfl
          rw [hslRect, hlrect]
          exact hfallApp source indexL ownerIndex g hsrcL ho hsel hgMemScene hgRole
        | inr hts =>
          have hts' : ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := hts
          obtain ⟨tsel, hsel⟩ := hts'
          have hselMem := List.mem_of_find?_eq_some hsel
          obtain ⟨stored, hstoredMem, hfeq⟩ := List.mem_filterMap.mp hselMem
          cases hbx : inp.boxes[stored.1]? with
          | none => simp only [hbx] at hfeq; cases hfeq
          | some box0 =>
            simp only [hbx] at hfeq
            have hpair := Option.some.inj hfeq
            have htid : box0.id = tsel.1 := congrArg Prod.fst hpair
            have htrect : shiftRect execution.params.canvasMargin
                execution.params.canvasMargin (orientRect o.direction
                  execution.packedAcc.canvasH
                  { stored.2 with
                    w := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).w
                    h := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).h }) = tsel.2 :=
              congrArg Prod.snd hpair
            have hselKey : tsel.1 = source.owner := by
              simpa using List.find?_some hsel
            have hid' : box0.id = inp.boxes[ownerIndex].id :=
              htid.trans (hselKey.trans hownerId.symm)
            have hkeyEq : stored.1 = ownerIndex :=
              b8_index_eq_of_id_eq hidsNodup hbx hobGet hid'
            have hrel := hpackTitles stored.1 stored.2 hstoredMem hKey hgBox hk hgroupRole
            have hlrect : sl.rect = shiftRect execution.params.canvasMargin
                execution.params.canvasMargin (orientRect o.direction
                  execution.packedAcc.canvasH
                  { stored.2 with
                    w := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).w
                    h := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).h }) := by
              have heq' := Option.some.inj heq
              have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
              dsimp only at hrr
              rw [hrr]
              show (Option.map (fun x => x.snd)
                  ((sceneTitlesExpr execution.params inp o execution.lines
                    execution.packedAcc).find? (fun t => t.1 == source.owner))).getD
                  (ownedTextRect execution.params
                    ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                      ownerIndex ⟨"", "", default, "", false⟩)
                    (execution.lines.getD ownerIndex [])) =
                shiftRect execution.params.canvasMargin
                  execution.params.canvasMargin (orientRect o.direction
                    execution.packedAcc.canvasH
                    { stored.2 with
                      w := (titleCaptionSize execution.params o
                        (execution.lines.getD stored.1 [])).w
                      h := (titleCaptionSize execution.params o
                        (execution.lines.getD stored.1 [])).h })
              rw [hsel]
              show tsel.2 = _
              rw [← htrect]
            rw [hslRect, hgRect, hlrect]
            cases hrel with
            | inl h => exact Or.inl (disjoint_sceneTransport h)
            | inr h => exact Or.inr (strictInside_sceneTransport h)

/-- Flat C8b for the exact pipeline: every successful `layoutX` keeps every
group frame disjoint from every scene label or strictly containing it, modulo
the X core, transport, and fallback residuals. -/
theorem flatC8bB_layoutX (exactIds : List String)
    (hcores : X_ExecutedPartFrameCoresB8 exactIds)
    (htransport : X_PackedPartTransportBoundedB8 exactIds)
    (hfall : X_FallbackCaptionClearB8 exactIds) :
    FlatC8bB (layoutX exactIds) := by
  intro inp o res hwf _hfp hfit h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hpack := b8_labelFramePackedClear_of_bounded execution hcores htransport
  exact b8_layout_c8b execution hpack hfall hfit hwf

end PipelineImpl
end Layered
end Elegant
