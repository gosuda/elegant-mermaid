import Elegant.GridArchitectureRouteClearanceFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Kinds.Architecture

open Polyline
open Elegant
open Elegant.Grid.Architecture
open Elegant.Grid.Architecture.ClearanceAux

/-! ### Clause 7 for the architecture adapter

`Grid.Architecture.placeLabels` only emits an edge label when `labelClear` accepts it, and
`labelClear` rejects every overlap with a placed node box; the fallback branch spills the
label strictly right of the content bounds, and every node box ends at the content bound.
Exclusive dump boxes are exactly the node boxes (`modelWellFormed` forbids exclusive
groups) and their rectangles are the translated versions of `geometry.boxes`.  Hence an
edge label never meets the interior of an exclusive box, which is clause 7. -/

/-- Canvas margin is non-negative for both profiles. -/
theorem canvas_margin_nonnegative (profile : Profile) :
    0 ≤ LayoutConst.canvas_margin.get profile := by
  cases profile <;> decide

/-- One `getD` either returns the default or an element of the list. -/
theorem getD_default_or_mem {α : Type} {xs : List α} {i : Nat} {d : α} :
    xs.getD i d = d ∨ ∃ x ∈ xs, x = xs.getD i d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : xs[i]? with
  | none => exact Or.inl rfl
  | some x =>
    refine Or.inr ⟨x, List.mem_of_getElem? h, ?_⟩
    simp only [Option.getD_some]

/-- A dump label's rectangle is either the zero rectangle or the translation of one
`placeLabels` output rectangle. -/
theorem dump_label_rect_origin {labels : List ModelLabel} {routes : List ModelRoute}
    {edgeRects : List Rect} {edgeLines : List (List Measure.Line)}
    {dump : List SceneLabel}
    (h : labels.mapM (fun (l : ModelLabel) => do
      let some i := routes.findIdx? (fun r => r.id == l.owner) | throw LayoutError.domain
      pure ({
        id := l.id
        owner := l.owner
        text := l.text
        rect := edgeRects.getD i ⟨0, 0, 0, 0⟩
        lines := (edgeLines.getD i []).map
          (fun line => String.ofList line.text) } : SceneLabel)) =
        (Except.ok dump : Except LayoutError (List SceneLabel)))
    {lab : SceneLabel} (hmem : lab ∈ dump) :
    lab.rect = (⟨0, 0, 0, 0⟩ : Rect) ∨
      ∃ rawRect ∈ edgeRects, rawRect = lab.rect := by
  obtain ⟨ml, _, hf⟩ := mapM_output_origin h hmem
  split at hf
  · dsimp only [pure, Except.pure] at hf
    cases hf
    dsimp only
    exact getD_default_or_mem
  · dsimp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure,
      Bind.bind, Except.bind] at hf
    cases hf

/-- An exclusive dump box's rectangle is either the zero rectangle or the translation of
one `geometry.boxes` entry. -/
theorem dump_box_rect_origin {boxes frames : List Rect} {groups nodes : List ModelBox}
    {source : List ModelBox} {dump : List Box}
    (h : source.mapM (fun (b : ModelBox) => do
      let r ← if b.role == .group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure ({
        id := b.id
        role := b.role.id
        parent := b.parent
        exclusive := b.exclusive
        rect := r } : Box)) = (Except.ok dump : Except LayoutError (List Box)))
    (hrole : ∀ b ∈ source, (b.role != .group || !b.exclusive) = true)
    {bx : Box} (hmem : bx ∈ dump) (hexclusive : bx.exclusive = true) :
    bx.rect = (⟨0, 0, 0, 0⟩ : Rect) ∨
      ∃ rawRect ∈ boxes, rawRect = bx.rect := by
  obtain ⟨mb, hmb, hf⟩ := mapM_output_origin h hmem
  have hsafe := hrole mb hmb
  split at hf
  · rename_i hgroup
    split at hf
    · dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hf
      cases hf
      have hne : (mb.role != .group) = false := by
        cases hr : mb.role <;> simp [hr] at hgroup ⊢
      have hfalse : mb.exclusive = false := by
        have hthis := hsafe
        rw [hne] at hthis
        simpa using hthis
      have htrue : mb.exclusive = true := hexclusive
      rw [hfalse] at htrue
      cases htrue
    · dsimp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure,
        Bind.bind, Except.bind] at hf
      cases hf
  · rename_i hnotgroup
    split at hf
    · dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hf
      cases hf
      dsimp only
      exact getD_default_or_mem
    · dsimp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure,
        Bind.bind, Except.bind] at hf
      cases hf

/-- The zero rectangle never meets the interior of a rectangle on its right. -/
theorem meetsInterior_zero_right (r : Rect) :
    ¬ r.meetsInterior (⟨0, 0, 0, 0⟩ : Rect) := by
  intro h
  exact zeroRect_no_meetsInterior r ((Rect.meetsInterior_comm r _).mp h)

/-- The zero span translates to the zero rectangle. -/
theorem translateRect_zero (dx dy : Int) :
    Grid.Architecture.translateRect dx dy (⟨0, 0, 0, 0⟩ : Span) =
      .ok (⟨0, 0, 0, 0⟩ : Rect) := by
  unfold Grid.Architecture.translateRect
  rfl

/-- Clause 7: an edge label never meets the interior of an exclusive box. -/
theorem architecture_c7 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    _root_.Validator.C7 result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := public_layout_dump m result h
  rw [dump]
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Elegant.Kinds.Architecture.build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  have hrole : ∀ b ∈ m.boxes, (b.role != .group || !b.exclusive) = true := by
    have hmw : modelWellFormed m = true := hwf
    simp only [modelWellFormed, Bool.and_eq_true] at hmw
    exact List.all_eq_true.mp hmw.2
  have hboxEq : scene.layoutDump.boxes = dumpBoxes := by
    rw [hscene]
    rfl
  have hlabelEq : scene.layoutDump.labels = dumpLabels.map (fun s => s.toLabel) := by
    rw [hscene]
    rfl
  intro l hl b hb hexclusive _
  rw [hlabelEq] at hl
  rw [hboxEq] at hb
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hl
  rcases dump_box_rect_origin hdumpBoxes hrole hb hexclusive with hbz | ⟨bs, hbsmem, hbsEq⟩
  · intro hmeet
    rw [hbz] at hmeet
    exact meetsInterior_zero_right sl.toLabel.rect hmeet
  · rcases dump_label_rect_origin hdumpLabels hsl with hlz | ⟨rawRect, hrawMem, hrawEq⟩
    · intro hmeet
      rw [hlz] at hmeet
      exact zeroRect_no_meetsInterior b.rect hmeet
    · obtain ⟨raw, hrawMem, hrawTrans⟩ :=
        mapM_output_origin hedgeRects hrawMem
      rw [hrawEq] at hrawTrans
      obtain ⟨gbs, hgbsMem, hgbsTrans⟩ :=
        mapM_output_origin hboxes hbsmem
      rw [hbsEq] at hgbsTrans
      rw [hrawLabels] at hrawMem
      rcases placeLabels_output_safe p margin geometry rawRoutes sizes bounds0 raw hrawMem with
        hzero | hclear | hspill
      · intro hmeet
        have htrans0 : Grid.Architecture.translateRect dx dy raw =
            .ok (⟨0, 0, 0, 0⟩ : Rect) := by
          rw [hzero]
          exact translateRect_zero dx dy
        have hlzero : sl.toLabel.rect = (⟨0, 0, 0, 0⟩ : Rect) :=
          Except.ok.inj (hrawTrans.symm.trans htrans0)
        rw [hlzero] at hmeet
        exact zeroRect_no_meetsInterior b.rect hmeet
      · exact translateRect_no_meetInterior
          dx dy raw gbs sl.toLabel.rect b.rect hrawTrans hgbsTrans
          (any_eq_false_iff.mp hclear gbs hgbsMem)
      · have hordered : gbs.x0 ≤ gbs.x1 ∧ gbs.y0 ≤ gbs.y1 :=
          translateRect_source_ordered dx dy gbs b.rect hgbsTrans
        have hmemAll : gbs ∈ geometry.boxes ++ geometry.labels ++ geometry.frames ++
            geometry.titles ++ geometry.badges :=
          List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ hgbsMem)))
        have hcontains := normalized_content_contains_shape geometry rawRoutes gbs hmemAll hordered
        have hbounds0' : bounds0 = (if content geometry rawRoutes = emptySpan then
            (⟨0, 0, 0, 0⟩ : Span) else content geometry rawRoutes) := by
          rw [hbounds0, hrawBounds]
        have hle : gbs.x1 ≤ bounds0.x1 := by
          rw [hbounds0']
          exact hcontains.2.1
        have hmargin0 : 0 ≤ margin := by
          rw [hmargin]
          exact canvas_margin_nonnegative profile
        have hsep : gbs.x1 ≤ (bounds0.inflate margin).x1 + margin := by
          have hinf : (bounds0.inflate margin).x1 = bounds0.x1 + margin := rfl
          omega
        exact translateRect_no_meetInterior_of_xseparated
          dx dy raw gbs sl.toLabel.rect b.rect ((bounds0.inflate margin).x1 + margin)
          hrawTrans hgbsTrans hsep hspill


end Elegant.Kinds.Architecture
