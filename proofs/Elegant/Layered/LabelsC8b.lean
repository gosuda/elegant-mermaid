import Elegant.Layered.SceneBounds
import Elegant.Layered.LabelsClearance
import ElegantGeometry.Validator

set_option autoImplicit false

/-! # Flat layered C8b (group frame vs label)

`layout_c8b` lifts `Validator.C8b` — every group frame of the dump is disjoint
from every scene label or strictly contains it — from a successful flat
 `PipelineImpl.layout`.  The proof dispatches the label families that
 `PipelineImpl.sceneOf` emits (measured route labels, installed title captions,
 and the scene-level `ownedTextRect` fallback captions) and transports the
 packed-coordinate relations through the common margin/orientation projection.

The geometric content lives in two executed facts:

 * `LabelFramePackedClear` — the packed-coordinate core over the actual
   `Acc.labels` route-label rects and `Acc.titles` caption rects that
   `placeComponent` and `packAcc` produce (`placedLabels`, `componentTitles`,
   `Labels.textRectAt`, `Loops.placement`, `RouteImpl.reversedLabelRect`,
   `frameRect` group frames, `Pack.pack` shelf disjointness).
* `FallbackCaptionClear` — the caption produced by the `ownedTextRect`
  fallback branch of `sceneOf` (`titleRect`, `nodeSize` insets,
  `group_caption_output_rank_fit`, the border-proxy width lane).

Both are named real facts about executed definitions, not restatements of
`C8b` at the scene level. -/

namespace Elegant.Layered

namespace PipelineImpl

/-- The measured caption size that `sceneOf` substitutes into a stored title
rect. -/
def titleCaptionSize (P : Params) (o : Options)
    (textLines : List Measure.Line) : Size :=
  let width := textLines.foldl (fun value line => max value line.width) 0
  let height := (max 1 textLines.length : Int) * P.lineH
  match o.direction with
  | .LR | .RL => Size.mk height width
  | .TB | .BT => Size.mk width height

/-- The scene boxes that `sceneOf` builds from the packed accumulator. -/
def sceneBoxesExpr (P : Params) (inp : Input) (o : Options) (packed : Acc) :
    List Box :=
  inp.boxes.zipIdx.map fun q =>
    Box.mk q.1.id q.1.role.id
      (shiftRect P.canvasMargin P.canvasMargin
        (orientRect o.direction packed.canvasH (packed.rects.getD q.2 default)))
      q.1.parent q.1.exclusive

/-- The installed-title captions that `sceneOf` derives from `packed.titles`. -/
def sceneTitlesExpr (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (packed : Acc) :
    List (String × Rect) :=
  packed.titles.filterMap fun stored => do
    let box ← inp.boxes[stored.1]?
    let size := titleCaptionSize P o (lines.getD stored.1 [])
    pure (box.id, shiftRect P.canvasMargin P.canvasMargin
      (orientRect o.direction packed.canvasH
        { stored.2 with w := size.w, h := size.h }))

 /-- Packed-coordinate core of the label/frame clearance: over the actual
 `packed.labels` route-label rects (placed by `placedLabels`) and the
 substituted `packed.titles` caption rects (placed by `componentTitles`),
 against the packed rect of every group-role box (the `frameRect` span
 carried through `packAcc`).  The `ownedTextRect` fallback captions are
 covered at scene level by `FallbackCaptionClear` instead: the packed-frame
 fallback clause was false in vector LR/RL (it evaluates `ownedTextRect`
 before `orientRect`) and is redundant for `layout_c8b`.  This is the
 fact that the coordinate phases establish — cluster-pad insets of
`crossCoordsClusterWith`, the top/bottom marker ranks of `Compound.markNodes`
behind `frameRect`'s vertical span, `Labels.textRectAt`/`Loops.placement`/
`RouteImpl.reversedLabelRect` label placement, and `Pack.pack` shelf
disjointness across components. -/
def LabelFramePackedClear (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (packed : Acc) : Prop :=
  (∀ index : Nat,
      ∀ (k : Nat) (gBox : ModelBox), inp.boxes[k]? = some gBox →
        gBox.role = BoxRole.group →
        let g := packed.rects.getD k default
        let l := packed.labels.getD index default
        Disjoint g l ∨ g.StrictInside l) ∧
    (∀ key : Nat, ∀ stored : Rect, (key, stored) ∈ packed.titles →
      ∀ (k : Nat) (gBox : ModelBox), inp.boxes[k]? = some gBox →
        gBox.role = BoxRole.group →
        let g := packed.rects.getD k default
        let caption : Rect :=
          { stored with
            w := (titleCaptionSize P o (lines.getD key [])).w
            h := (titleCaptionSize P o (lines.getD key [])).h }
        Disjoint g caption ∨ g.StrictInside caption)

/-- The fallback-branch caption clearance: for a scene label emitted by the
`ownedTextRect` fallback of `sceneOf` (owner is a non-exclusive box absent
from the installed titles) against every group-role scene box.  This is the
scene-level branch fact; it is established by the `titleRect`/`nodeSize`
insets (`clusterPad`, `nodePadY`, `nodeBorder`), the caption sizing
reservations (`group_caption_output_rank_fit`,
`component_group_caption_rank_fit`), the border-proxy width lane
(`GroupWidthFacts`, `proxyWidths`), member containment
(`ParentContainmentFacts`), and cross-shelf `Pack.pack` disjointness. -/
def FallbackCaptionClear {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∀ (source : ModelLabel) (index ownerIndex : Nat) (g : Box),
    inp.labels[index]? = some source →
    inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) =
      some ownerIndex →
    (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun t => t.1 == source.owner) = none →
    g ∈ res.scene.boxes → g.role = "group" →
    let l := ownedTextRect execution.params
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩)
      (execution.lines.getD ownerIndex [])
    Disjoint g.rect l ∨ g.rect.StrictInside l

/-! ### Transport helpers -/

/-- The scene transport used by `sceneOf`: margin shift after orientation. -/
theorem not_meetsInterior_sceneTransport {a b : Rect} {m h : Int}
    {d : Direction} (hclr : ¬ a.meetsInterior b) :
    ¬ (shiftRect m m (orientRect d h a)).meetsInterior
      (shiftRect m m (orientRect d h b)) :=
  not_meetsInterior_shiftRect (not_meetsInterior_orientRect hclr)

/-- `Disjoint` survives the scene transport. -/
theorem disjoint_sceneTransport {a b : Rect} {m h : Int} {d : Direction}
    (hd : Disjoint a b) :
    Disjoint (shiftRect m m (orientRect d h a))
      (shiftRect m m (orientRect d h b)) :=
  not_meetsInterior_sceneTransport hd

/-- `StrictInside` survives the scene transport. -/
theorem strictInside_sceneTransport {g l : Rect} {m h : Int} {d : Direction}
    (hclr : g.StrictInside l) :
    (shiftRect m m (orientRect d h g)).StrictInside
      (shiftRect m m (orientRect d h l)) :=
  strictInside_shiftRect (strictInside_orientRect hclr)

/-- Two positions of a box list whose boxes share an id are equal. -/
private theorem index_eq_of_id_eq {l : List ModelBox}
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

/-! ### The flat C8b clause -/

set_option maxHeartbeats 1000000 in
/-- Clause 8, condition 2 of the layout validator for a successful flat
`PipelineImpl.layout` under the well-formed input model and the executed
label/frame clearance facts. -/
theorem layout_c8b {inp : Input} {o : Options} {res : FamilyResult}
    (h : PipelineImpl.layout inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hclear : ∀ (execution : SceneExecution inp o res),
      LabelFramePackedClear execution.params inp o execution.lines
        execution.packedAcc ∧ FallbackCaptionClear execution) :
    Validator.C8b res.scene.layoutDump := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  obtain ⟨hpack, hfall⟩ := hclear execution
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
  rw [execution.boxes_eq_map] at hgMem
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
      obtain ⟨h1, _⟩ := hpack
      have hpm := List.find?_some hm
      have hmIdx : measured.index = indexL := by simpa using hpm
      have hrel := h1 indexL hKey hgBox hk hgroupRole
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
        obtain ⟨hb, hownerPred, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
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
          exact hfall source indexL ownerIndex g hsrcL ho hsel hgMemScene hgRole
        | inr hts =>
          have hts' : ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := hts
          obtain ⟨tsel, hsel⟩ := hts'
          obtain ⟨_, h2⟩ := hpack
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
              index_eq_of_id_eq hidsNodup hbx hobGet hid'
            have hrel := h2 stored.1 stored.2 hstoredMem hKey hgBox hk hgroupRole
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

end PipelineImpl

end Elegant.Layered
