import Elegant.GridArchitectureCellContracts
import Elegant.GridArchitectureRouteClearanceFacts
import Elegant.GridArchitectureClauses
import Elegant.GridArchitectureValidity
import Elegant.Kinds.ArchitectureStructural
import Elegant.Kinds.ArchitectureC2
import Elegant.Kinds.ArchitectureC3
import Elegant.Kinds.ArchitectureC6
import Elegant.Kinds.ArchitectureValid

set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Elegant.Kinds.Architecture

open Elegant
open Elegant.Grid.Architecture
open Elegant.Grid.Architecture.ClearanceAux

/-! ### Clause 8 for the architecture adapter

`Validator.C8a` asks that every group frame be disjoint from every foreign box;
`Validator.C8b` asks that every group frame be disjoint from every label or strictly
contain it. Group frames are translated `geometry.frames` spans, node boxes are
translated `geometry.boxes` spans, and edge labels are translated `placeLabels`
spans. Translation preserves span disjointness and strict insideness, and
`labelClear` forces every edge label to avoid every frame or sit strictly inside
it (spills land strictly to the right of all frames). -/

/-- A translated group frame clears a translated edge label whenever the raw
spans do: disjoint raw spans stay disjoint, and a raw label strictly inside
its frame stays strictly inside the translated frame. A point-sized raw label
translates to the zero rectangle, which is disjoint from every nonneg
rectangle, so that case clears through `Disjoint`. -/
private theorem c8_frame_label_clear (dx dy : Int) (frame raw : Span)
    (rf rl : Rect)
    (hf : translateRect dx dy frame = .ok rf)
    (hl : translateRect dx dy raw = .ok rl)
    (h : raw.overlaps frame = false ∨ raw.strictlyInside frame = true) :
    Disjoint rf rl ∨ rf.StrictInside rl := by
  rcases h with hover | hinside
  · exact Or.inl ((Disjoint.comm _ _).mp
      (translateRect_disjoint_of_spans dx dy raw frame rl rf hl hf hover))
  · by_cases hdeg : raw.x0 = raw.x1 ∧ raw.y0 = raw.y1
    · have hnn_f := translateRect_nonneg dx dy frame rf hf
      have hzero : rl = (⟨0, 0, 0, 0⟩ : Rect) := by
        unfold translateRect at hl
        simp only [hdeg, ↓reduceIte] at hl
        exact (Except.ok.inj hl).symm
      subst hzero
      exact Or.inl ((Rect.disjoint_comm rf _).mpr (zeroRect_disjoint_left rf hnn_f))
    · have hord_i := translateRect_source_ordered dx dy raw rl hl
      unfold Span.strictlyInside at hinside
      rw [decide_eq_true_eq] at hinside
      have hne_o : frame.x0 ≠ frame.x1 ∨ frame.y0 ≠ frame.y1 := by
        by_cases hx : frame.x0 = frame.x1
        · right; omega
        · exact Or.inl hx
      have hne_i : raw.x0 ≠ raw.x1 ∨ raw.y0 ≠ raw.y1 := by
        by_cases hx : raw.x0 = raw.x1
        · right
          intro hy
          exact hdeg ⟨hx, hy⟩
        · exact Or.inl hx
      obtain ⟨ox, oy, ow, oh⟩ := translateRect_nonempty_shape dx dy frame rf hne_o hf
      obtain ⟨ix, iy, iw, ih⟩ := translateRect_nonempty_shape dx dy raw rl hne_i hl
      refine Or.inr ?_
      simp only [Rect.StrictInside, ox, oy, ow, oh, ix, iy, iw, ih]
      omega

/-- Span containment is transitive. -/
private theorem c8_span_contains_trans (outer middle inner : Span)
    (first : outer.contains middle) (second : middle.contains inner) :
    outer.contains inner := by
  unfold Span.contains at first second ⊢
  omega

private theorem c8_getD_append_singleton (xs : List Span) (r : Span) :
    (xs ++ [r]).getD xs.length default = r := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  simp

/-- One `labelStep` either emits the zero rect, or emits a rect that avoids every
frame or sits strictly inside it, or emits a rect starting at `spillX`. -/
private theorem c8_labelStep_last_cases (p : GeometryParams) (margin : Int)
    (g : Geometry) (routes : List (List Point)) (spillX : Int) (state : LabelState)
    (q : Size × Nat) :
    (labelStep p margin g routes spillX state q).output.getD state.output.length default = (⟨0, 0, 0, 0⟩ : Span) ∨
      (∀ f ∈ g.frames, ((labelStep p margin g routes spillX state q).output.getD state.output.length default).overlaps f = false ∨
        ((labelStep p margin g routes spillX state q).output.getD state.output.length default).strictlyInside f = true) ∨
      spillX ≤ ((labelStep p margin g routes spillX state q).output.getD state.output.length default).x0 := by
  unfold labelStep
  dsimp only
  split
  · rw [c8_getD_append_singleton]
    exact Or.inl rfl
  · split
    · rename_i r hr
      have hclear : labelClear p g routes state r = true := List.find?_some hr
      unfold labelClear at hclear
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_append,
        Bool.or_eq_false_iff] at hclear
      have hframes : (g.frames.all fun frame => !r.overlaps frame || r.strictlyInside frame) = true :=
        hclear.1.1.2
      refine Or.inr (Or.inl ?_)
      rw [c8_getD_append_singleton]
      intro f hf2
      rw [List.all_eq_true] at hframes
      have hthis := hframes f hf2
      rw [Bool.or_eq_true] at hthis
      rcases hthis with h1 | h2
      · rw [Bool.not_eq_true'] at h1
        exact Or.inl h1
      · exact Or.inr h2
    · refine Or.inr (Or.inr ?_)
      rw [c8_getD_append_singleton]
      simp only [sized]
      omega

/-- Every `placeLabels` output is the zero rect, frame-safe, or spilled past the
content bounds. -/
private theorem c8_placeLabels_frames_safe (p : GeometryParams) (margin : Int)
    (g : Geometry) (routes : List (List Point)) (sizes : List Size) (bounds : Span) :
    ∀ raw ∈ placeLabels p margin g routes sizes bounds,
      raw = (⟨0, 0, 0, 0⟩ : Span) ∨
        (∀ f ∈ g.frames, raw.overlaps f = false ∨ raw.strictlyInside f = true) ∨
        bounds.x1 + 2 * margin ≤ raw.x0 := by
  have key : ∀ (qs : List (Size × Nat)) (state : LabelState),
      (∀ r ∈ state.output,
          r = (⟨0, 0, 0, 0⟩ : Span) ∨
            (∀ f ∈ g.frames, r.overlaps f = false ∨ r.strictlyInside f = true) ∨
            (bounds.inflate margin).x1 + margin ≤ r.x0) →
      ∀ r ∈ (qs.foldl (labelStep p margin g routes ((bounds.inflate margin).x1 + margin)) state).output,
        r = (⟨0, 0, 0, 0⟩ : Span) ∨
          (∀ f ∈ g.frames, r.overlaps f = false ∨ r.strictlyInside f = true) ∨
          (bounds.inflate margin).x1 + margin ≤ r.x0 := by
    intro qs
    induction qs with
    | nil => intro state hI r hr; exact hI r (by simpa only [List.foldl_nil] using hr)
    | cons q rest ih =>
        intro state hI r hr
        simp only [List.foldl_cons] at hr
        refine ih _ ?_ r hr
        intro r' hr'
        have happ := labelStep_appended p margin g routes ((bounds.inflate margin).x1 + margin) state q
        rw [happ] at hr'
        simp only [List.mem_append, List.mem_singleton] at hr'
        rcases hr' with hold | hnew
        · exact hI r' hold
        · rw [hnew]
          exact c8_labelStep_last_cases p margin g routes ((bounds.inflate margin).x1 + margin) state q
  intro raw hmem
  rw [placeLabels_eq] at hmem
  have hspill : (bounds.inflate margin).x1 + margin = bounds.x1 + 2 * margin := by
    have hx1 : (bounds.inflate margin).x1 = bounds.x1 + margin := rfl
    omega
  have hmem' := key sizes.zipIdx ⟨bounds.inflate margin, [], [], (bounds.inflate margin).y0 + margin⟩
    (by intro r hr; exact absurd hr (by simp)) raw hmem
  rcases hmem' with h0 | hsafe | hsp
  · exact Or.inl h0
  · exact Or.inr (Or.inl hsafe)
  · exact Or.inr (Or.inr (by omega))
/-- Pointwise form of `mapM` for `getD` lookup: the `i`-th output is the image
of the `i`-th input. This packages `mapM_pointwise` through `getD` so callers
never write explicit `getElem` proofs. -/
private theorem c8_mapM_getD {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (a : α) (b : β) (hi : i < xs.length) :
    f (xs.getD i a) = .ok (ys.getD i b) := by
  have hj : i < ys.length := by
    have hlen := (Elegant.Grid.mapM_ok_pairs _ _ h).1
    omega
  have hpt := mapM_pointwise h i hi hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] at hpt ⊢
  exact hpt

/-- Clause 8b: every group frame is disjoint from every edge label or strictly
contains it. A dump group box records a translated `geometry.frames` span and a
dump label records a translated `placeLabels` span; `placeLabels` forces each
label to avoid every frame or sit strictly inside it, with spills landing
strictly to the right of all frames. Translation preserves both conclusions. -/
theorem architecture_c8b (m : Model) (result : Layered.FamilyResult)
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    _root_.Validator.C8b result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := public_layout_dump m result h
  rw [dump]
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  have hboxEq : scene.layoutDump.boxes = dumpBoxes := by rw [hscene]; rfl
  have hlabEq : scene.layoutDump.labels = dumpLabels.map (·.toLabel) := by
    rw [hscene]; rfl
  have groupLen : groupInput.length = groups.length := by
    have hgl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have htit := (Elegant.Grid.mapM_ok_pairs _ _ htitles).1
    have hzl : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    rw [htit] at hzl
    simp only [Nat.min_self] at hzl
    exact (hgl.symm.trans hzl).trans htit.symm
  have hg_eq : input.groups = groupInput := by rw [hinput]
  have hresLen : resolved.frames.length = input.groups.length := by
    rw [hresolved, hplaced]
    exact (resolveHierarchy_storage_lengths input params frameParams _).2
  have hgeomFrames : geometry.frames = resolved.frames := by
    rw [hgeometry]
    rfl
  have hframesLenEq : frames.length = geometry.frames.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hframes).1.symm
  have hrawLen : rawLabels.length = sizes.length := by
    rw [hrawLabels]
    exact placeLabels_length p margin geometry rawRoutes sizes bounds0
  have hsizesLen : sizes.length = m.routes.length := by
    have h1 := (Elegant.Grid.mapM_ok_pairs _ _ hedgeLines).1
    have h2 : edgeTexts.length = m.routes.length := by
      rw [hedgeTexts]
      simp
    rw [hsizes, List.length_map]
    omega
  have hedgeLen : rawLabels.length = edgeRects.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hedgeRects).1
  have hmar : 0 ≤ margin := by rw [hmargin]; cases profile <;> decide
  have hsafe := c8_placeLabels_frames_safe p margin geometry rawRoutes sizes bounds0
  intro g hg hroleG l hl
  rw [hboxEq] at hg
  rw [hlabEq] at hl
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hl
  obtain ⟨mb, _hmb, hdec⟩ := mapM_output_origin hdumpBoxes hg
  simp only at hdec
  by_cases hrole : (mb.role == BoxRole.group) = true
  · simp only [hrole, ↓reduceIte] at hdec
    cases hfind : groups.findIdx? (fun q => q.id == mb.id) with
    | none =>
        simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw,
          throwThe, MonadExceptOf.throw] at hdec
        cases hdec
    | some gi =>
        simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
        have hgiGroups : gi < groups.length :=
          (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
        have hgiInput : gi < input.groups.length := by
          rw [hg_eq, groupLen]; exact hgiGroups
        have hgiRes : gi < resolved.frames.length := by
          rw [hresLen]; exact hgiInput
        have hgiGeom : gi < geometry.frames.length := by
          rw [hgeomFrames]; exact hgiRes
        have hgiFrames : gi < frames.length := by
          rw [hframesLenEq]; exact hgiGeom
        have hfmem : geometry.frames.getD gi default ∈ geometry.frames := by
          simpa only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hgiGeom, Option.getD_some] using
            List.getElem_mem hgiGeom
        have htrans_f : translateRect dx dy (geometry.frames.getD gi default) =
            .ok (frames.getD gi ⟨0, 0, 0, 0⟩) :=
          c8_mapM_getD hframes gi _ _ hgiGeom
        obtain ⟨ml, _hml, hdecL⟩ := mapM_output_origin hdumpLabels hsl
        cases hfi : m.routes.findIdx? (fun r => r.id == ml.owner) with
        | none =>
            simp only [hfi, throw, throwThe, MonadExceptOf.throw] at hdecL
            cases hdecL
        | some ri =>
            simp only [hfi, pure, Except.pure] at hdecL
            cases hdecL
            have hriRoutes : ri < m.routes.length :=
              (List.findIdx?_eq_some_iff_findIdx_eq.mp hfi).1
            have hriRaw : ri < rawLabels.length := by
              rw [hrawLen, hsizesLen]; exact hriRoutes
            have hriEdge : ri < edgeRects.length := by
              rw [← hedgeLen]; exact hriRaw
            have htrans_l : translateRect dx dy (rawLabels.getD ri default) =
                .ok (edgeRects.getD ri ⟨0, 0, 0, 0⟩) :=
              c8_mapM_getD hedgeRects ri _ _ hriRaw
            have hrlmem : rawLabels.getD ri default ∈
                placeLabels p margin geometry rawRoutes sizes bounds0 := by
              rw [← hrawLabels]
              simpa only [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hriRaw, Option.getD_some] using
                List.getElem_mem hriRaw
            have hmemAll : geometry.frames.getD gi default ∈ geometry.boxes ++
                geometry.labels ++ geometry.frames ++ geometry.titles ++
                geometry.badges := by
              refine List.mem_append.mpr (Or.inl ?_)
              refine List.mem_append.mpr (Or.inl ?_)
              refine List.mem_append.mpr (Or.inr ?_)
              exact hfmem
            have hord_f : (geometry.frames.getD gi default).x0 ≤
                (geometry.frames.getD gi default).x1 ∧
                (geometry.frames.getD gi default).y0 ≤
                  (geometry.frames.getD gi default).y1 :=
              translateRect_source_ordered dx dy _ _ htrans_f
            have hbounds0c : bounds0.contains (geometry.frames.getD gi default) := by
              have hnorm := normalized_content_contains_shape geometry rawRoutes
                (geometry.frames.getD gi default) hmemAll hord_f
              rw [← hrawBounds, ← hbounds0] at hnorm
              exact hnorm
            rcases hsafe (rawLabels.getD ri default) hrlmem with h0 | hfr | hsp
            · have hzero_l : edgeRects.getD ri ⟨0, 0, 0, 0⟩ = (⟨0, 0, 0, 0⟩ : Rect) := by
                have hzero : translateRect dx dy (⟨0, 0, 0, 0⟩ : Span) = .ok (⟨0, 0, 0, 0⟩ : Rect) := by
                  unfold translateRect
                  simp
                have hrr := h0
                rw [hrr] at htrans_l
                exact (Except.ok.inj (hzero.symm.trans htrans_l)).symm
              have hnn_f := translateRect_nonneg dx dy _ _ htrans_f
              show Disjoint (frames.getD gi ⟨0, 0, 0, 0⟩) (edgeRects.getD ri ⟨0, 0, 0, 0⟩) ∨
                (frames.getD gi ⟨0, 0, 0, 0⟩).StrictInside (edgeRects.getD ri ⟨0, 0, 0, 0⟩)
              rw [hzero_l]
              exact Or.inl ((Rect.disjoint_comm _ _).mp
                (zeroRect_disjoint_left _ hnn_f))
            · have hclear := c8_frame_label_clear dx dy _ _ _ _ htrans_f htrans_l
                (hfr _ hfmem)
              show Disjoint (frames.getD gi ⟨0, 0, 0, 0⟩) (edgeRects.getD ri ⟨0, 0, 0, 0⟩) ∨
                (frames.getD gi ⟨0, 0, 0, 0⟩).StrictInside (edgeRects.getD ri ⟨0, 0, 0, 0⟩)
              exact hclear
            · have hfx : (geometry.frames.getD gi default).x1 ≤
                  (rawLabels.getD ri default).x0 := by
                unfold Span.contains at hbounds0c
                omega
              have hno : ¬ (edgeRects.getD ri ⟨0, 0, 0, 0⟩).meetsInterior
                  (frames.getD gi ⟨0, 0, 0, 0⟩) := by
                refine translateRect_no_meetInterior_of_xseparated dx dy _ _ _ _
                  _ htrans_l htrans_f hfx (Int.le_refl _)
              show Disjoint (frames.getD gi ⟨0, 0, 0, 0⟩) (edgeRects.getD ri ⟨0, 0, 0, 0⟩) ∨
                (frames.getD gi ⟨0, 0, 0, 0⟩).StrictInside (edgeRects.getD ri ⟨0, 0, 0, 0⟩)
              exact Or.inl ((Disjoint.comm _ _).mp hno)
  · have hgroupF : (mb.role == BoxRole.group) = false := by simp [hrole]
    simp only [hgroupF, ↓reduceIte] at hdec
    cases hfind : nodes.findIdx? (fun q => q.id == mb.id) with
    | none =>
        simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw,
          throwThe, MonadExceptOf.throw] at hdec
        cases hdec
    | some ni =>
        simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
        cases hmb : mb.role <;> simp_all [BoxRole.id]

/-- Architecture validity modulo C8a: C2, C3, C6, and C8b are proved from a
successful layout; C8a remains the single hypothesis. The missing geometric
fact is a bridge from dump-box ancestor strings (`LayoutDump.ancestors`
follows `parent` strings via `box?`) to the group-index hierarchy
(`virtualParents` / `groupChain` / `ParentPath` over `input.groups`): no
lemma yet shows that translated dump rects of ancestor-unrelated boxes are
disjoint by lifting sibling-span separation
(`executed_sibling_final_spans_separated`, `hierarchy_final_cells_unique`)
through ancestor-frame containment (`resolved_group_contains_node_tile`,
`resolved_group_contains_child_frame`) to `Validator.C8a`. -/
theorem architecture_valid (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : layout m = .ok result)
    (hC8a : _root_.Validator.C8a result.scene.layoutDump) :
    _root_.HardConstraints result.scene.layoutDump :=
  architecture_valid_of_clauses hwf hlimits h
    (architecture_c2 m result hwf hlimits h)
    (architecture_c3 m result hwf hlimits h)
    (architecture_c6 m result hwf hlimits h)
    hC8a
    (architecture_c8b m result hwf hlimits h)

end Elegant.Kinds.Architecture
