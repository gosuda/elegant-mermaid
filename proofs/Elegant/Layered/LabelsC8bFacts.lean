import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsClearance
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Pack
import ElegantGeometry.Validator

set_option autoImplicit false

/-! # Executed C8b seams: label/frame clearance and fallback captions

`PipelineImpl.LabelFramePackedClear` and `PipelineImpl.FallbackCaptionClear`
(`Layered/LabelsC8b.lean`) are the two executed facts that lift `Validator.C8b`
to the flat layered pipeline.  This file proves both from named executed facts.

## Decomposition of `LabelFramePackedClear`

The definition quantifies over the packed arrays `packedAcc.rects`,
`packedAcc.labels`, and `packedAcc.titles`.  `placePart`/`packAcc` write those
arrays from the per-component `Part` values, translating each part by its
`Pack.pack` shelf origin; `Disjoint` and `Rect.StrictInside` are translation
invariant.  The clearance of a part's own frames against its own route labels,
installed captions, and `ownedTextRect` fallbacks is therefore the
component-local geometric core, and the cross-shelf case follows from
`Pack.pack_boxes_disjoint`.

The component-local cores are the geometry named by the C8b header: the
cluster-pad insets of `crossCoordsClusterWith`, the top/bottom marker ranks of
`Compound.markNodes` behind `frameRect`'s vertical span,
`Labels.textRectAt`/`Loops.placement`/`RouteImpl.reversedLabelRect` route-label
placement with `Labels.stackRects_contained`, and the caption reservations
(`componentRun_group_reservation`, `componentRun_group_frame_height_ge`,
`SceneExecution.component_group_caption_rank_fit`).  They are stated over the
`Part` values `placePart` stores, not over the packed arrays, so they are not
restatements of the packed conclusion.

`FallbackCaptionClear` is scene-level: it compares `ownedTextRect` of the
assembled scene boxes against the assembled group boxes, with no pack
transport.  Its named core drops the label-emission side conditions. -/

namespace Elegant.Layered

namespace PipelineImpl

/-! ### Rectangle helpers -/

/-- A rectangle contained in one of two disjoint rectangles is disjoint from a
rectangle contained in the other. -/
theorem disjoint_of_contained_disjoint {a b c d : Rect}
    (ha : c.Contained a) (hb : d.Contained b) (hd : Disjoint c d) :
    Disjoint a b := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  omega

/-- The default rectangle does not meet the interior of a rectangle with a
non-negative origin. -/
theorem disjoint_default_of_nonneg {r : Rect} (hx : 0 ≤ r.x) : Disjoint r default := by
  have hd : (default : Rect) = ⟨0, 0, 0, 0⟩ := rfl
  rw [hd]
  unfold Disjoint Rect.meetsInterior
  dsimp only
  omega

/-- An array index beyond the array size reads as the default value. -/
theorem array_getD_of_size_le {α : Type} [Inhabited α] {a : Array α} {i : Nat}
    (h : a.size ≤ i) : a.getD i default = default := by
  unfold Array.getD
  split
  · rename_i hlt
    omega
  · rfl

/-- `ownedTextRect` is translation equivariant: shifting the owning box shifts
the emitted text rectangle. -/
theorem ownedTextRect_shiftRect (P : Params) (id role parent : String) (excl : Bool)
    (rect : Rect) (lines : List Measure.Line) (dx dy : Int) :
    ownedTextRect P ⟨id, role, shiftRect dx dy rect, parent, excl⟩ lines =
      shiftRect dx dy (ownedTextRect P ⟨id, role, rect, parent, excl⟩ lines) := by
  unfold ownedTextRect titleRect shiftRect
  dsimp only
  split <;> simp only [Rect.mk.injEq] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ac_rfl

/-- The checked parameters are the base table plus the kind overrides; every
field outside `nodeGap`, `rankGap`, `wrapWidth`, and `canvasMargin` is the
family default literal. -/
theorem checkedParams_source {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) :
    P = Params.forKind profile kind
      ⟨LayoutConst.node_pad_x.get profile, LayoutConst.node_pad_y.get profile,
       LayoutConst.node_border.get profile, LayoutConst.line_h.get profile,
       LayoutConst.node_min_w.get profile, LayoutConst.node_min_h.get profile,
       LayoutConst.port_gap.get profile, LayoutConst.node_gap.get profile,
       LayoutConst.rank_gap.get profile, LayoutConst.slot.get profile,
       LayoutConst.corner_radius.get profile, LayoutConst.cluster_pad.get profile,
       LayoutConst.cluster_border_w.get profile, 0, 0⟩ := by
  unfold checkedParams at h
  cases hp : paramsOf profile kind with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some Q =>
    rw [hp] at h
    dsimp only at h
    by_cases hv : Q.Valid
    · simp only [hv, ↓reduceIte] at h
      have hQP : Q = P := Except.ok.inj h
      subst hQP
      unfold paramsOf at hp
      rw [baseParams] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      rw [hp]
    · simp only [hv, ↓reduceIte] at h
      exact absurd h (by simp)

/-- The measured cluster padding is positive in every profile, so a caption
inside a frame keeps a strict inset on the axes `titleRect` pads. -/
theorem checkedParams_clusterPad_pos {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 < P.clusterPad := by
  rw [checkedParams_source h]
  change 0 < LayoutConst.cluster_pad.get profile
  cases profile <;> decide

/-- The line height is positive in every profile, so a caption with at least one
measured line has positive height. -/
theorem checkedParams_lineH_pos {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 < P.lineH := by
  rw [checkedParams_source h]
  change 0 < LayoutConst.line_h.get profile
  cases profile <;> decide

/-! ### Component-local geometric cores -/

/-- Route-label core: inside one executed component `Part`, the placed rect of
every measured route label (`placedLabels`, carried in `Part.labels`) either
misses the frame of every group box of the same component or lies strictly
inside it. -/
def PartRouteLabelFrameClear (inp : Input) (part : List Nat × Part) : Prop :=
  ∀ (index : Nat) (rect : Rect) (pos key : Nat) (src : ModelBox) (g : Rect),
    (index, rect) ∈ part.2.labels →
    part.1[pos]? = some key →
    inp.boxes[key]? = some src →
    src.role = BoxRole.group →
    part.2.rects[pos]? = some g →
    Disjoint g rect ∨ g.StrictInside rect

/-- Caption core: inside one executed component `Part`, the installed title
caption (`componentTitles`, carried in `Part.titles`) resized to the measured
text size (`titleCaptionSize`, as `sceneOf` substitutes it) either misses the
frame of every group box of the same component or lies strictly inside it. -/
def PartCaptionFrameClear (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (part : List Nat × Part) : Prop :=
  ∀ (i : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (g : Rect),
    (i, stored) ∈ part.2.titles →
    part.1[pos]? = some key →
    inp.boxes[key]? = some src →
    src.role = BoxRole.group →
    part.2.rects[pos]? = some g →
    let capKey := part.1.getD i 0
    let size := titleCaptionSize P o (lines.getD capKey [])
    Disjoint g { stored with w := size.w, h := size.h } ∨
      g.StrictInside { stored with w := size.w, h := size.h }

/-- Fallback-caption core: inside one executed component `Part`, the
`ownedTextRect` caption of every model box position either misses the frame of
every group box of the same component or lies strictly inside it. -/
def PartOwnedTextFrameClear (P : Params) (inp : Input)
    (lines : List (List Measure.Line)) (part : List Nat × Part) : Prop :=
  ∀ (pos oi : Nat) (r0 : Rect) (oiSrc src : ModelBox) (j gKey : Nat) (g : Rect),
    part.1[pos]? = some oi →
    part.2.rects[pos]? = some r0 →
    inp.boxes[oi]? = some oiSrc →
    part.1[j]? = some gKey →
    inp.boxes[gKey]? = some src →
    src.role = BoxRole.group →
    part.2.rects[j]? = some g →
    let boxOwner : Box := ⟨"", oiSrc.role.id, r0, "", false⟩
    Disjoint g (ownedTextRect P boxOwner (lines.getD oi [])) ∨
      g.StrictInside (ownedTextRect P boxOwner (lines.getD oi []))

/-- The three component-local cores hold for every executed part.  `placePart`
stores exactly these `Part` values in `componentsAcc.parts`, so this is a fact
about the executed layout, not about the packed arrays. -/
def ExecutedPartFrameCores {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∀ part ∈ execution.componentsAcc.parts,
    PartRouteLabelFrameClear inp part ∧
    PartCaptionFrameClear execution.params inp o execution.lines part ∧
    PartOwnedTextFrameClear execution.params inp execution.lines part

/-! ### Packed-accumulator transport -/

 /-- Packed transport: the packed accumulator is the union of the executed parts
 shifted by their `Pack.pack` shelf origins.  Every packed box rectangle, route
 label, and title comes from one part position under that shift; a part's frames,
 labels, and resized captions stay inside its shelf box; packed frames have
 non-negative origins.  (`ownedTextRect` fallback captions are covered at scene
 level by `FallbackCaptionClear`, not by this transport.)  This is the structural
 half of `placePart`/`packAcc` in `Pipeline.lean`, stated over the executed values. -/
def PackedPartTransport {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∃ packed : Pack.State,
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
    (∀ (k : Nat) (r : Rect), execution.packedAcc.rects.getD k default = r →
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

/-- The caption resize commutes with the shelf translation. -/
private theorem caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl

/-! ### `LabelFramePackedClear` -/

set_option maxHeartbeats 800000 in
/-- The packed-coordinate C8b core of a successful flat `PipelineImpl.layout`:
the executed component-local geometric cores plus the packed shelf transport
give `LabelFramePackedClear` over the actual accumulator arrays. -/
theorem labelFramePackedClear {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (hcores : ExecutedPartFrameCores execution)
    (htransport : PackedPartTransport execution) :
    LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc := by
  obtain ⟨packed, hpack, hrects, hlabels, htitles, hnonneg⟩ := htransport
  refine ⟨?_, ?_⟩
  · intro index k gBox hbox hrole
    dsimp only
    obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
      hrects k (execution.packedAcc.rects.getD k default) rfl
    rw [hreq] at hboxk
    rcases hlabels index (execution.packedAcc.labels.getD index default) rfl with
      ⟨pl, partl, r0l, bl, hpartl, hmeml, hbl, hreql, hboxl⟩ | hdef
    · rw [hreql] at hboxl
      by_cases hpk : pk = pl
      · subst hpk
        obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
        obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
        obtain ⟨hcore, -, -⟩ := hcores partk (List.mem_of_getElem? hpartk)
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
    obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
      hrects k (execution.packedAcc.rects.getD k default) rfl
    rw [hreq] at hboxk
    obtain ⟨pl, partl, i, stored0, bl, hpartl, hkeyi, hmeml, hbl, hstored, hboxCap⟩ :=
      htitles key stored htitle
    by_cases hpk : pk = pl
    · subst hpk
      obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
      obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
      obtain ⟨-, hcore, -⟩ := hcores partk (List.mem_of_getElem? hpartk)
      have hgetD : partk.1.getD i 0 = key := by
        simp only [List.getD, hkeyi, Option.getD_some]
      have hclr := hcore i stored0 posk k gBox r0 hmeml hkeyk hbox hrole hr0
      simp only [hgetD] at hclr
      rw [hreq, hstored, caption_shift_comm]
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
      rw [hreq, hstored, caption_shift_comm]
      exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)

/-! ### `FallbackCaptionClear` -/

/-- Scene-level caption core: every `ownedTextRect` caption of an assembled
scene box either misses every group scene box or lies strictly inside it.  It
is stronger than `FallbackCaptionClear`, whose quantifier carries the label
emission side conditions (label presence, owner lookup, absent installed
title) that the core does not need. -/
def SceneOwnedTextFrameCore {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Prop :=
  ∀ (ownerIndex : Nat) (g : Box), g ∈ res.scene.boxes → g.role = "group" →
    let l := ownedTextRect execution.params
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩)
      (execution.lines.getD ownerIndex [])
    Disjoint g.rect l ∨ g.rect.StrictInside l

/-- The fallback-caption branch of the scene C8b clause, from the scene-level
caption core. -/
theorem fallbackCaptionClear {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (hcore : SceneOwnedTextFrameCore execution) :
    FallbackCaptionClear execution := by
  intro source index ownerIndex g _ _ _ hgMem hgRole
  exact hcore ownerIndex g hgMem hgRole

end PipelineImpl

end Elegant.Layered
