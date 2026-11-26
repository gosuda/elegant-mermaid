import Elegant.Layered.ExactFlatC8b

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C8b, W form (`flatC8bB_layoutX_W`, Packet 5).

Replay of `flatC8bB_layoutX` (`ExactFlatC8b.lean:469`) over W-form premises:
local `WellFormed (inputModel inp o)` and `framedParents inp = true` appear
directly after the execution binder in each hypothesis, and `FlatC8bB` hands
those very premises to the proof (`hwf`/`hfp` threaded at application).
Transport `X_PackedPartTransportBoundedB8` is unchanged (pure per-run
geometry). The cores hypothesis body below is identical to the W cores def
proved alongside Packet 3, and the fallback hypothesis body is identical to
the W fallback def proved with the fallback facts; both are stated inline so
this module imports only tracked code while staying definitionally
compatible with those defs. No premise here quantifies over all inputs or
executions with an admission conclusion. -/

/-- W copy of the private `b8_caption_shift_comm` (`ExactFlatC8b.lean:121`):
the caption resize commutes with the shelf translation. -/
private theorem w8b_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl

/-- W copy of the private `b8_index_eq_of_id_eq` (`ExactFlatC8b.lean:127`):
two positions of a box list whose boxes share an id are equal. -/
private theorem w8b_index_eq_of_id_eq {l : List ModelBox}
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

/-- W copy of the private `b8_packFold_rects_sizeX` (`ExactFlatC8b.lean:153`):
the packing fold preserves the rect array size. -/
private theorem w8b_packFold_rects_sizeX
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- W copy of the private `b8_packedAcc_rects_sizeX` (`ExactFlatC8b.lean:164`):
the exact packed rect array has one entry per input box. -/
private theorem w8b_packedAcc_rects_sizeX {exactIds : List String} {inp : Input}
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
  rw [w8b_packFold_rects_sizeX]
  exact execution.components_rects_size

set_option maxHeartbeats 800000 in
/-- W packed-coordinate C8b core: the per-execution component cores plus the
X transport give `LabelFramePackedClear`. Replay of `b8_labelFramePackedClear_of_bounded`
(`ExactFlatC8b.lean:186`); the cores arrive as the W instance at this
execution (applied by the caller from `hcoresW execution hwf hfp`). -/
private theorem w8b_labelFramePackedClear_of_boundedW {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : X_PackedPartTransportBoundedB8 exactIds) :
    LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc := by
  obtain ⟨packed, hpack, hrects, hlabels, htitles, hnonneg⟩ := htransport execution
  refine ⟨?_, ?_⟩
  · intro index k gBox hbox hrole
    dsimp only
    have hksize : k < execution.packedAcc.rects.size := by
      rw [w8b_packedAcc_rects_sizeX execution]
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
        obtain ⟨hcore, -⟩ := hcore partk (List.mem_of_getElem? hpartk)
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
      rw [w8b_packedAcc_rects_sizeX execution]
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
      obtain ⟨-, hcore⟩ := hcore partk (List.mem_of_getElem? hpartk)
      have hgetD : partk.1.getD i 0 = key := by
        simp only [List.getD, hkeyi, Option.getD_some]
      have hclr := hcore i stored0 posk k gBox r0 hmeml hkeyk hbox hrole hr0
      simp only [hgetD] at hclr
      rw [hreq, hstored, w8b_caption_shift_comm]
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
      rw [hreq, hstored, w8b_caption_shift_comm]
      exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)

set_option maxHeartbeats 1000000 in
/-- W clause 8, condition 2: replay of `b8_layout_c8b` (`ExactFlatC8b.lean:283`)
over the W fallback instance at this execution (applied by the caller from
`hfallW execution hwf hfp hfit`). -/
private theorem w8b_layout_c8bW {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hpack : LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc)
    (hfallApp : ∀ (source : ModelLabel) (index ownerIndex : Nat) (g : Box),
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
      Disjoint g.rect l ∨ g.rect.StrictInside l)
    (hwf : WellFormed (inputModel inp o)) :
    Validator.C8b res.scene.layoutDump := by
  obtain ⟨hpackLabels, hpackTitles⟩ := hpack
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hlabBridge : (sceneOf execution.params inp o execution.lines
      execution.straightAcc execution.measured).labels =
      (sceneOf execution.params inp o execution.lines execution.packedAcc
        execution.measured).labels :=
    (sceneOf_straightenAcc execution.params inp o execution.lines
      execution.packedAcc execution.straightAcc execution.measured
      execution.straight_eq).2.2
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
              w8b_index_eq_of_id_eq hidsNodup hbx hobGet hid'
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

/-- Flat C8b for the exact pipeline, W form: every successful `layoutX` keeps
every group frame disjoint from every scene label or strictly containing it,
from W-form cores, unchanged transport, and W-form fallback. The cores body
matches the W cores def proved alongside Packet 3 and the fallback body
matches the W fallback def proved with the fallback facts; `FlatC8bB` supplies
`hwf`/`hfp`/`hfit` per input and they are threaded into the W premises. -/
theorem flatC8bB_layoutX_W (exactIds : List String)
    (hcoresW : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
      ∀ part ∈ execution.componentsAcc.parts,
        PartRouteLabelFrameClear inp part ∧
        PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : X_PackedPartTransportBoundedB8 exactIds)
    (hfallW : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
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
        Disjoint g.rect l ∨ g.rect.StrictInside l) :
    FlatC8bB (layoutX exactIds) := by
  intro inp o res hwf hfp hfit h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hpack :=
    w8b_labelFramePackedClear_of_boundedW execution (hcoresW execution hwf hfp)
      htransport
  exact w8b_layout_c8bW execution hpack (hfallW execution hwf hfp hfit) hwf

end PipelineImpl
end Layered
end Elegant
