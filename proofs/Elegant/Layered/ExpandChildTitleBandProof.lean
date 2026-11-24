import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78
import Elegant.Layered.InsetFit
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildCanvasFitProof

set_option autoImplicit false

/-!
# Title-band facts of the recursive `expandChild` step

For every executed `expandChild` call the recursion performs, the group
caption rect (`groupTitleRect`, the `childTitleRect` at the located frame)
lies strictly inside the frame, and it misses the shifted child *inset* canvas: the
canvas with the margin border removed (`insetRect`), which is exactly the
region the expansion offsets line back up with the frame reservation.

The whole-canvas disjointness does not hold: the shifted child canvas
carries its margin border, which overlaps the title band by `P.canvasMargin`
on the title side in every direction (above/below for `TB`/`BT`, left/right
for `LR`/`RL`). Two closed `decide` witnesses below satisfy the frame-size
bounds and the exact shift equations yet meet the title rect, so the
universal whole-canvas claim is false. The proved form is the inset version,
which still yields every shifted child box and label: those lie in the
shifted inset by the child inset invariant (`layoutRecursive_inset`),
turned into per-primitive clearance by `titleBand_clear_of_insetDisjoint`.

No residuals remain. The call parameters come from `ExpandChildCallParams`
(checked params, the executed title-height equation, the wrapped group
title); the frame reservation is the public `expandChild_frame_size_bounds`
of the canvas-fit worker; the child canvas margin cover is proved below by
fuel induction over `layoutRecursive`, whose child call runs with the same
profile and kind (hence definitionally the same checked params) because
`childSubOptions` keeps the profile and `childSubInput` keeps the kind.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-- Canvas of a flat `layout` result covers the margin border on every side:
the scene canvas is the oriented packed extents plus twice the margin. -/
private theorem layout_canvas_ge_margins {inp : Input} {o : Options}
    {res : FamilyResult} (h : layout inp o = .ok res) (Q : Params)
    (hQ : checkedParams o.profile inp.kind = .ok Q) :
    0 ≤ res.scene.canvas.w - 2 * Q.canvasMargin ∧
      0 ≤ res.scene.canvas.h - 2 * Q.canvasMargin := by
  have exec := Classical.choice (layout_sceneExecution h)
  have hacc := exec.packedAcc_bounded exec.components_parts_bounded
  obtain ⟨hcwA, hchA, _, _, _, _⟩ := hacc
  have hQm : exec.params = Q := Except.ok.inj (exec.checked.symm.trans hQ)
  subst hQm
  have hcan : (sceneOf exec.params inp o exec.lines exec.packedAcc
      exec.measured).canvas =
      orientCanvas o.direction
        (exec.packedAcc.canvasW + 2 * exec.params.canvasMargin)
        (exec.packedAcc.canvasH + 2 * exec.params.canvasMargin) := rfl
  rw [exec.scene_eq, hcan]
  unfold orientCanvas
  generalize o.direction = d
  cases d <;> dsimp only <;> omega

/-- Canvas of a successful recursion covers the margin border on every side,
for the checked params of the call's own profile and kind. The flat case is
the lemma above; the expansion case keeps the parent canvas
(`expandChild_sources`), so the induction hypothesis on the parent success
transports through the result canvas equation. No well-formedness is needed:
the canvas form holds for every successful execution. -/
private theorem layoutRecursive_canvas_ge_margins (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res → ∀ Q : Params,
      checkedParams o.profile inp.kind = .ok Q →
      0 ≤ res.scene.canvas.w - 2 * Q.canvasMargin ∧
        0 ≤ res.scene.canvas.h - 2 * Q.canvasMargin := by
  induction fuel with
  | zero =>
    intro inp o res h Q hQ
    exact layout_canvas_ge_margins h Q hQ
  | succ fuel ih =>
    intro inp o res h Q hQ
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨_, Pm, _, _, _, parent, _, hPm, _, _, _, hp, hexpand⟩
    · exact layout_canvas_ge_margins hlayout Q hQ
    · have hQPm : Q = Pm := Except.ok.inj (hQ.symm.trans hPm)
      rw [hQPm]
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcanvas, _⟩ :=
        expandChild_sources hexpand
      have hcanv : res.scene.canvas = parent.scene.canvas := hcanvas
      obtain ⟨hpw, hph⟩ := ih _ _ _ hp Pm hPm
      rw [hcanv]
      exact ⟨hpw, hph⟩

/-- A `foldl max` starting at `0` is nonnegative, whatever the line widths. -/
private theorem titleWidth_nonneg (ls : List Measure.Line) :
    0 ≤ ls.foldl (fun width line => max width line.width) 0 := by
  suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
      0 ≤ ls.foldl (fun width line => max width line.width) acc by
    exact key ls 0 (by omega)
  intro ls acc hac
  induction ls generalizing acc with
  | nil => simpa using hac
  | cons line ls ih =>
    simp only [List.foldl_cons]
    exact ih _ (Int.le_trans hac (Int.le_max_left _ _))

/-- Pure geometry behind the containment conclusion: the title rect lies in
any frame whose width and height dominate the `childFrameSize` reservation,
given a nonnegative pad and nonnegative inset content. -/
private theorem titleRect_contained_aux {direction : String}
    {pad tw th conw conh fx fy fw fh : Int}
    (hpad : 0 ≤ pad)
    (hconw : 0 ≤ conw) (hconh : 0 ≤ conh)
    (hfw : (childFrameSize direction pad tw th ⟨conw, conh⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th ⟨conw, conh⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).Contained
      (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩) := by
  have htw : tw + 2 * pad ≤ fw := by
    unfold childFrameSize at hfw
    split at hfw <;> dsimp only at hfw <;> omega
  have hth : th + 2 * pad ≤ fh := by
    unfold childFrameSize at hfh
    split at hfh <;> dsimp only at hfh <;> omega

  unfold childTitleRect
  split <;> unfold Rect.Contained <;> dsimp only <;>
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] <;> omega

/-- Pure geometry behind the clearance conclusion: the title rect misses the
shifted child inset. On the `LR`/`TB` sides the inset starts exactly where
the title ends (the margin cancels); on the `RL`/`BT` sides the gap comes
from the frame reservation. -/
private theorem titleInset_disjoint_aux {direction : String}
    {pad tw th margin cw ch fx fy fw fh dx dy : Int}
    (htw : 0 ≤ tw) (hth : 0 ≤ th)
    (hfw : (childFrameSize direction pad tw th
      ⟨cw - 2 * margin, ch - 2 * margin⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th
      ⟨cw - 2 * margin, ch - 2 * margin⟩).h ≤ fh)
    (hdx : dx = fx + (childInset direction pad tw th).x - margin)
    (hdy : dy = fy + (childInset direction pad tw th).y - margin) :
    Disjoint (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩)
      (shiftRect dx dy (insetRect ⟨cw, ch⟩ margin)) := by
  have hdir : direction = "LR" ∨ direction = "RL" ∨ direction = "BT" ∨
      (direction ≠ "LR" ∧ direction ≠ "RL" ∧ direction ≠ "BT") := by
    by_cases h1 : direction = "LR"
    · exact Or.inl h1
    · by_cases h2 : direction = "RL"
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : direction = "BT"
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
  rcases hdir with hLR | hRL | hBT | ⟨hnLR, hnRL, hnBT⟩
  · rw [hLR] at hfw hfh hdx hdy ⊢
    simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · rw [hRL] at hfw hfh hdx hdy ⊢
    simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · rw [hBT] at hfw hfh hdx hdy ⊢
    have eW : (childFrameSize "BT" pad tw th
        ⟨cw - 2 * margin, ch - 2 * margin⟩).w
        = max (cw - 2 * margin) tw + 2 * pad := rfl
    have eH : (childFrameSize "BT" pad tw th
        ⟨cw - 2 * margin, ch - 2 * margin⟩).h
        = ch - 2 * margin + th + 2 * pad := rfl
    rw [eW] at hfw
    rw [eH] at hfh
    simp only [childTitleRect, childInset, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega

/-- Per-expansion title-band facts for an executed call: the caption rect is
inside the located frame, and it misses the shifted child inset canvas
(the corrected form of whole-canvas disjointness, which is false by the
witnesses below). The executed-call premises pin the context; the parameters
come from `ExpandChildCallParams`, the frame reservation from the public
`expandChild_frame_size_bounds`, and the child canvas margin cover from
`layoutRecursive_canvas_ge_margins` applied to the child success in `hctx`.
No residuals remain. -/
theorem expandChild_title_band
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    frame.rect.Contained (groupTitleRect group P titleLines' titleHeight frame) ∧
    Disjoint (groupTitleRect group P titleLines' titleHeight frame)
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
  intro frame titleLines' dx dy hfind hdx hdy hwrap
  have hP := hparams.1
  have hheightEq := hparams.2.1
  have hpad : 0 ≤ P.clusterPad := checkedParams_clusterPad_nonneg hP
  have hth : 0 ≤ titleHeight := by
    rw [hheightEq]
    exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  have hchild := hctx.2.2.2.1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  obtain ⟨hconw, hconh⟩ :=
    layoutRecursive_canvas_ge_margins fuel _ _ _ hchild P hQchild
  obtain ⟨hfw, hfh⟩ := expandChild_frame_size_bounds fuel P inp o group
    titleLines titleHeight parent child res hexpand hframed hctx hparams
    frame titleLines' hfind hwrap
  have htw := titleWidth_nonneg titleLines'
  refine ⟨?_, ?_⟩
  · unfold groupTitleRect
    exact titleRect_contained_aux hpad hconw hconh hfw hfh
  · unfold groupTitleRect
    exact titleInset_disjoint_aux htw hth hfw hfh hdx hdy

/-- Pure geometry behind the strict caption containment: the title rect lies
strictly inside any frame whose width and height dominate the
`childFrameSize` reservation, given a positive pad and nonnegative inset
content.  The centering-axis strictness needs two inset units of slack, which
the doubled pad supplies; the title-axis strictness is the pad itself. -/
private theorem titleRect_strictInside_aux {direction : String}
    {pad tw th conw conh fx fy fw fh : Int}
    (hpad : 0 < pad)
    (hconw : 0 ≤ conw) (hconh : 0 ≤ conh)
    (hfw : (childFrameSize direction pad tw th ⟨conw, conh⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th ⟨conw, conh⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).StrictInside
      (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩) := by
  have hW : tw + 2 * pad ≤ fw := by
    unfold childFrameSize at hfw
    split at hfw <;> dsimp only at hfw <;> omega
  have hH : th + 2 * pad ≤ fh := by
    unfold childFrameSize at hfh
    split at hfh <;> dsimp only at hfh <;> omega
  unfold childTitleRect
  split <;> unfold Rect.StrictInside <;> dsimp only <;>
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] <;> omega

/-- The caption rect of an executed `expandChild` lies strictly inside the
located group frame.  The frame reservation
(`expandChild_frame_size_bounds`), the positive cluster pad, and the child
canvas margin cover (`layoutRecursive_canvas_ge_margins`) supply the strict
auxiliary above. -/
theorem frame_strictInside_caption
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    frame.rect.StrictInside
      (groupTitleRectC8 group P titleLines' titleHeight frame) := by
  intro frame titleLines' _dx _dy hframe _hdx _hdy hwrap'
  obtain ⟨hw, hh⟩ := expandChild_frame_size_bounds fuel P inp o group titleLines
    titleHeight parent child res _hexpand _hframed hctx hparams frame titleLines'
    hframe hwrap'
  obtain ⟨hP, _hheightEq, _hwrapCtx⟩ := hparams
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  obtain ⟨_hwf, _hgroup, _hpboxes, hchild, _hparent, _hexpand'⟩ := hctx
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  obtain ⟨hconw, hconh⟩ :=
    layoutRecursive_canvas_ge_margins fuel _ _ _ hchild P hQchild
  exact titleRect_strictInside_aux hpad hconw hconh hw hh

/-- Witness: whole-canvas disjointness is false with the title above the
content (`TB`). The frame-size bounds and the exact shift equations hold
(minimal fitting frame, `pad = margin = 1`), yet the title rect meets the
shifted child canvas along the margin strip. -/
example : (childFrameSize "TB" 1 10 1 ⟨6 - 2 * 1, 6 - 2 * 1⟩).w ≤ 12 ∧
    (childFrameSize "TB" 1 10 1 ⟨6 - 2 * 1, 6 - 2 * 1⟩).h ≤ 7 ∧
    (0 : Int) = 0 + (childInset "TB" 1 10 1).x - 1 ∧
    (1 : Int) = 0 + (childInset "TB" 1 10 1).y - 1 ∧
    (childTitleRect "TB" 1 10 1 ⟨0, 0, 12, 7⟩).meetsInterior
      (shiftRect 0 1 (⟨0, 0, 6, 6⟩ : Rect)) := by
  decide

/-- Witness: whole-canvas disjointness is false with the title beside the
content (`LR`). Same shape as the `TB` witness at a minimal fitting frame. -/
example : (childFrameSize "LR" 1 10 1 ⟨6 - 2 * 1, 6 - 2 * 1⟩).w ≤ 16 ∧
    (childFrameSize "LR" 1 10 1 ⟨6 - 2 * 1, 6 - 2 * 1⟩).h ≤ 6 ∧
    (10 : Int) = 0 + (childInset "LR" 1 10 1).x - 1 ∧
    (0 : Int) = 0 + (childInset "LR" 1 10 1).y - 1 ∧
    (childTitleRect "LR" 1 10 1 ⟨0, 0, 16, 6⟩).meetsInterior
      (shiftRect 10 0 (⟨0, 0, 6, 6⟩ : Rect)) := by
  decide

/-- Per-primitive clearance from the inset band fact: every shifted child
box and every shifted child label misses the title rect, because each lies
in the shifted inset. The child inset hypotheses come from
`layoutRecursive_inset` (boxes) and the label inset at the lift site. -/
theorem titleBand_clear_of_insetDisjoint {title inset : Rect} {dx dy : Int}
    {boxes : List Box} {labels : List SceneLabel}
    (hband : Disjoint title (shiftRect dx dy inset))
    (hb : ∀ b ∈ boxes, inset.Contained b.rect)
    (hl : ∀ l ∈ labels, inset.Contained l.rect) :
    (∀ b ∈ boxes, Disjoint title (shiftRect dx dy b.rect)) ∧
      ∀ l ∈ labels, Disjoint title (shiftRect dx dy l.rect) := by
  refine ⟨?_, ?_⟩
  · intro b hmem
    have hshift := (contained_shiftRect dx dy).mpr (hb b hmem)
    exact (Disjoint.comm _ _).mp
      (disjoint_contained_left hshift ((Disjoint.comm _ _).mp hband))
  · intro l hmem
    have hshift := (contained_shiftRect dx dy).mpr (hl l hmem)
    exact (Disjoint.comm _ _).mp
      (disjoint_contained_left hshift ((Disjoint.comm _ _).mp hband))

end Elegant.Layered.PipelineImpl
