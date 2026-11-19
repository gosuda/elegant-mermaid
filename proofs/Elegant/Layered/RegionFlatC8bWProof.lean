import Elegant.Layered.RegionFlatC8b
import Elegant.Layered.RegionPartFrameCores
import Elegant.Layered.RegionFallbackCaption
import Elegant.Layered.RegionPartSizing

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! Region flat C8b, W form (`flatC8bB_layoutRIds_W`).

Replay of `flatC8bB_layoutX_W` (`ExactFlatC8bWProof.lean`) over `SceneExecutionR`:
local `WellFormed (inputModel inp o)` / `framedParents inp = true` appear after
the execution binder in the cores and fallback hypotheses, and `FlatC8bB` hands
those very premises to the proof (`hwf`/`hfp` threaded at application).
Transport (`R_PackedPartTransportBoundedB8`) is closed from the chosen-run
residual `R_PartSizingRResidual` (NOT the deleted false universal
`R_PartSizingR`: see `RegionPartSizing.lean` junk-node witness) via
`R_packedPartTransportBounded_closed` (`RegionFlatC8b.lean`), which replays
`r8b_packedPartTransportBounded_holds` with the bounded conjunct supplied by
`exactComponentPlacementR_bounded_of_residual` (`R_partSizingR_chosenFacts`
closes dims/titles/slot on chosen runs; coverage/envelope come from the
residual). Caption-fit `R_ExactTitleCaptionFitB8` is unchanged: it carries no
admission hypotheses.

Proved: `flatC8bB_layoutRIds_W` from W premises only.
Open: `hcoresW` (via `R_executedPartFrameCoresW_holds`), `hfallW` (via
`R_fallbackCaptionClearB8W_closed` from its six premises), `hres`
(`R_PartSizingRResidual`), `hcap`. `hcap` is clean (quantifies only over
executed parts and their actual titles; proved outright by
`R_exactTitleCaptionFitB8_holds`); `hcoresW` is clean (`PartRouteLabelFrameClear`
and `PartCaptionFrameClear` quantify only over elements actually carried in
`part.2.labels` / `part.2.titles`, with no arbitrary `(cg, run)` binders).
Probe evidence: `#eval`s below (flat, nested, self-loop, zero-size, empty,
ill-formed duplicate); non-vacuous cores/fallback mirrors live in
`RegionFlatC8b.lean` (`r8bProbeC8bB`) and `RegionFallbackCaption.lean`
(`rfbFallbackB`, `rfbOk` on six rows).

Matching `RegionSeams` shape (not edited here): `partFrameCores` becomes
`∀ sub, R_ExecutedPartFrameCoresB8W exactIds (reindexRegionSets idSets sub)`;
`fallbackCaption` becomes `∀ sub, R_FallbackCaptionClearBW exactIds
(reindexRegionSets idSets sub)`; `titleCaptionFit` stays
`∀ sub, R_ExactTitleCaptionFitB8 exactIds (reindexRegionSets idSets sub)`
(no admission content, hence no W form). -/

/-- Shared options for the W-probes (vector profile, top-to-bottom). -/
private def r8wOpts : Options := { profile := .vector, direction := .TB }

/-- Flat group with a fallback label owned by node `a`. -/
private def r8wFlat : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "a", parent := "G", exclusive := false }]
    routes := []
    texts := ["G", "a"]
    edges := []
    labels := [{ id := "L1", owner := "a", text := "hi" }] }

/-- Nested groups with a fallback label owned by the innermost node. -/
private def r8wNest : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "H", parent := "G", exclusive := false },
      { id := "h", parent := "H", exclusive := false }]
    routes := []
    texts := ["G", "H", "h"]
    edges := []
    labels := [{ id := "L1", owner := "h", text := "deep" }] }
/-- Self-loop route with a fallback label on the looping node. -/
private def r8wSelf : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "a", parent := "G", exclusive := false }]
    routes := [{ id := "e0", fromId := "a", toId := "a" }]
    texts := ["G", "a"]
    edges := [.plain]
    labels := [{ id := "L1", owner := "a", text := "loop" }] }

/-- Zero-size fixed box owning a fallback label. -/
private def r8wZero : Input :=
  { kind := "state"
    boxes := [{ id := "Z", parent := "", exclusive := false }]
    routes := []
    texts := ["Z"]
    edges := []
    fixedSizes := [("Z", { w := 0, h := 0 })]
    labels := [{ id := "L1", owner := "Z", text := "zero" }] }

/-- Empty group: no labels, vacuous fallback. -/
private def r8wEmpty : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false }]
    routes := []
    texts := ["G"]
    edges := [] }

/-- Ill-formed row: duplicate box id `A`. -/
private def r8wDup : Input :=
  { kind := "state"
    boxes := [{ id := "G", role := .group, parent := "", exclusive := false },
      { id := "A", parent := "G", exclusive := false },
      { id := "A", parent := "", exclusive := false }]
    routes := []
    texts := ["G", "A", "A"]
    edges := []
    labels := [{ id := "L1", owner := "A", text := "dup" }] }

/-- Layout success mirror. -/
private def r8wOk (inp : Input) : Bool :=
  match layoutRIds [] [] inp r8wOpts with
  | .ok _ => true
  | .error _ => false

#eval r8wOk r8wFlat
#eval r8wOk r8wNest
#eval r8wOk r8wSelf
#eval r8wOk r8wZero
#eval r8wOk r8wEmpty
#eval r8wOk r8wDup
/-! ## Small pack helpers (prefixed copies of the `rpc_` twins in
`RegionPartFrameCores.lean`). -/

/-- The packing fold preserves the rect array size (copy of
`rpc_packFold_rects_size`). -/
private theorem r8w_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Region packed rect array size (copy of `rpc_packedAcc_rects_sizeR`). -/
private theorem r8w_packedAcc_rects_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
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
  rw [r8w_packFold_rects_size]
  exact execution.components_rects_sizeR

/-- Caption shift commutes with the title-size overwrite (copy of
`rpc_caption_shift_comm`). -/
private theorem r8w_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl

/-- Box-index equality from id equality under nodup (copy of
`rpc_index_eq_of_id_eq`). -/
private theorem r8w_index_eq_of_id_eq {l : List ModelBox}
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
/-- W packed-label clearance: copy of `rpc_labelsClear_of_boundedW`. The cores
arrive as the W instance at this execution (applied by the caller from
`hcoresW execution hwf hfp`). -/
private theorem r8w_labelsClear_of_boundedW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets)
    (index k : Nat) (gBox : ModelBox) (hbox : inp.boxes[k]? = some gBox)
    (hrole : gBox.role = BoxRole.group) :
    let g := execution.packedAcc.rects.getD k default
    let l := execution.packedAcc.labels.getD index default
    Disjoint g l ∨ g.StrictInside l := by
  obtain ⟨packed, hpack, hrects, hlabels, _htitles, hnonneg⟩ :=
    htransport execution
  dsimp only
  have hksize : k < execution.packedAcc.rects.size := by
    rw [r8w_packedAcc_rects_sizeR execution]
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
/-- W packed-title clearance: copy of `rpc_titlesClear_of_boundedW`. -/
private theorem r8w_titlesClear_of_boundedW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets)
    (key : Nat) (stored : Rect) (htitle : (key, stored) ∈ execution.packedAcc.titles)
    (k : Nat) (gBox : ModelBox) (hbox : inp.boxes[k]? = some gBox)
    (hrole : gBox.role = BoxRole.group) :
    let g := execution.packedAcc.rects.getD k default
    let caption : Rect :=
      { stored with
        w := (titleCaptionSize execution.params o
        (execution.lines.getD key [])).w
        h := (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h }
    Disjoint g caption ∨ g.StrictInside caption := by
  obtain ⟨packed, hpack, hrects, _hlabels, htitles, _hnonneg⟩ :=
    htransport execution
  dsimp only
  have hksize : k < execution.packedAcc.rects.size := by
    rw [r8w_packedAcc_rects_sizeR execution]
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
    rw [hreq, hstored, r8w_caption_shift_comm]
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
    rw [hreq, hstored, r8w_caption_shift_comm]
    exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)

/-- W packed-coordinate C8b core: copy of `rpc_labelFramePackedClear_of_boundedW`. -/
private theorem r8w_labelFramePackedClear_of_boundedW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets) :
    LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc := by
  refine ⟨?_, ?_⟩
  · intro index k gBox hbox hrole
    exact r8w_labelsClear_of_boundedW execution hcore htransport index k gBox
      hbox hrole
  · intro key stored htitle k gBox hbox hrole
    exact r8w_titlesClear_of_boundedW execution hcore htransport key stored
      htitle k gBox hbox hrole

set_option maxHeartbeats 1000000 in
/-- W clause 8, condition 2 for a successful region `layoutRIds`: copy of
`rpc_layout_c8bW` over the per-execution packed clearance and the W fallback
instance at this execution (applied by the caller from
`hfallW execution hwf hfp hfit`). -/
private theorem r8w_layout_c8bW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
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
  intro g hgMem hgRole l hlMem
  simp only [Scene.layoutDump] at hgMem hlMem
  obtain ⟨sl, hsl, hlEq⟩ := List.mem_map.mp hlMem
  rw [execution.scene_eq] at hsl
  obtain ⟨qL, hqL, hemitted⟩ := List.mem_filterMap.mp hsl
  obtain ⟨source, indexL⟩ := qL
  have hsrcL : inp.labels[indexL]? = some source :=
    List.mem_zipIdx_iff_getElem?.mp hqL
  have hslRect : l.rect = sl.rect := by rw [← hlEq]
  rw [execution.boxes_eq_mapR] at hgMem
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
            rw [execution.scene_eq]
            exact List.mem_map.mpr ⟨(hgBox, hKey), hq, hgeq⟩
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
              r8w_index_eq_of_id_eq hidsNodup hbx hobGet hid'
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
/-- Flat C8b for the region pipeline, W form: every successful `layoutRIds` keeps
every group frame disjoint from every scene label or strictly containing it,
from W-form cores, residual-closed transport, and the W-form fallback. The W cores
and W fallback bodies match `R_ExecutedPartFrameCoresB8W` (proved alongside packet 3
via `R_executedPartFrameCoresW_holds`) and `R_FallbackCaptionClearBW` (proved via
`R_fallbackCaptionClearB8W_closed`); `FlatC8bB` supplies `hwf`/`hfp`/`hfit` per
input and they are threaded into the W premises. Transport is closed from the
chosen-run residual `R_PartSizingRResidual` (NOT the false `R_PartSizingR`) plus
the caption-fit residual. -/
theorem flatC8bB_layoutRIds_W (exactIds : List String)
    (idSets : List (String × List String))
    (hcoresW : R_ExecutedPartFrameCoresB8W exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (PipelineImpl.layoutRIds exactIds idSets) := by
  intro inp o res hwf hfp hfit h
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hpack :=
    r8w_labelFramePackedClear_of_boundedW execution (hcoresW execution hwf hfp)
      (R_packedPartTransportBounded_closed exactIds idSets hres hcap)
  exact r8w_layout_c8bW execution hpack (hfallW execution hwf hfp hfit) hwf

end PipelineImpl
end Layered
end Elegant
