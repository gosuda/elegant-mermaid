import Elegant.Kinds.ArchitectureC6

/-!
# Clause 2 (exclusive box separation) for the architecture adapter

`Validator.C2` constrains two dump boxes that are both exclusive and share the same
parent. `modelWellFormed` forbids exclusive group boxes, so every exclusive dump box is
a node box. Two node boxes sit in the pitch tiles of their resolved cells; those cells
are pairwise distinct (`hierarchy_final_cells_unique`), each node box lies inside its
own tile with gutter clearance on the sides (`nodeTileFits`, `RouteClearance.BoxBounds`),
and distinct tiles share no interior, so the translated dump rectangles are disjoint.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace Elegant.Kinds.Architecture

open Elegant
open Elegant.Grid.Architecture
open Elegant.Grid.Architecture.ClearanceAux

local instance : Inhabited Elegant.ModelBox := ⟨{ id := "" }⟩

/-- The computed pitch never drops below the base pitch on either axis. -/
private theorem pitch_x_lower (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    p.pitchX ≤ (Grid.Architecture.pitch p nodes edgeLabels).x := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

private theorem pitch_y_lower (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    p.pitchY ≤ (Grid.Architecture.pitch p nodes edgeLabels).y := by
  simp only [Grid.Architecture.pitch]
  omega

/-- The computed pitch's top inset is never negative. -/
private theorem pitch_top_nonneg (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    0 ≤ (Grid.Architecture.pitch p nodes edgeLabels).top := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

/-- `configInt` only returns integers that passed the nonnegative config guard. -/
private theorem configInt_value_nonneg (m : Model) (key : String) (v : Int)
    (h : configInt m key = some v) : 0 ≤ v := by
  unfold configInt at h
  cases hsrc : m.options.config.find? (fun q => q.1 == key) with
  | none => rw [hsrc] at h; cases h
  | some pair =>
      obtain ⟨k, cv⟩ := pair
      cases cv with
      | string s => rw [hsrc] at h; cases h
      | boolean b => rw [hsrc] at h; cases h
      | integer val =>
          rw [hsrc] at h
          change (if 0 ≤ val ∧ val ≤ I32_MAX then some val else none) = some v at h
          by_cases valid : 0 ≤ val ∧ val ≤ I32_MAX
          · rw [ite_eq_left valid] at h
            have same := Option.some.inj h
            rw [← same]
            exact valid.1
          · rw [ite_eq_right valid] at h
            cases h

/-- A successful `parentIndex` lookup admits only the root or an in-range group
index. -/
private theorem parentIndex_ok_admitted {groups : List ModelBox} {id : String}
    {p : Int} (h : parentIndex groups id = .ok p) :
    p = -1 ∨ ∃ i, i < groups.length ∧ p = Int.ofNat i := by
  unfold parentIndex at h
  by_cases he : id.isEmpty = true
  · simp only [he, ↓reduceIte, Except.ok.injEq] at h
    exact Or.inl h.symm
  · simp only [he] at h
    cases hf : groups.findIdx? (fun b => b.id == id) with
    | none => rw [hf] at h; simp at h
    | some i =>
        rw [hf] at h
        simp at h
        have hi : i < groups.length :=
          (List.findIdx?_eq_some_iff_findIdx_eq.mp hf).1
        exact Or.inr ⟨i, hi, h.symm⟩

/-- The head of a duplicate-free list differs from every tail element. -/
private theorem nodup_head_ne {α : Type} (x : α) (rest : List α)
    (hnd : (x :: rest).Nodup) (k : Nat) (hk : k < rest.length) :
    x ≠ rest.get ⟨k, hk⟩ :=
  fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ List.get_mem _ _)

/-- Distinct indices of a duplicate-free list hold distinct values. -/
private theorem nodup_getElem_ne {α : Type} {xs : List α} (hnd : xs.Nodup) :
    ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) (_hij : i < j),
      xs.get ⟨i, hi⟩ ≠ xs.get ⟨j, hj⟩ := by
  intro i j hi hj _hij
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x rest ih =>
      cases j with
      | zero => omega
      | succ l =>
          cases i with
          | zero => exact nodup_head_ne x rest hnd l (by simpa using hj)
          | succ k =>
              exact ih (List.nodup_cons.mp hnd).2 k l (by simpa using hi)
                (by simpa using hj) (by omega)

/-- `mapM` point lookup: the `i`-th output is the image of the `i`-th input. -/
private theorem mapM_at {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ hy : i < ys.length, f xs[i] = .ok ys[i] := by
  obtain ⟨hlen, hpairs⟩ := Elegant.Grid.mapM_ok_pairs xs ys h
  have hy : i < ys.length := by omega
  exact ⟨hy, hpairs xs[i] ys[i] (by
    apply List.mem_iff_getElem.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_zip]
      omega
    · simp only [List.getElem_zip])⟩

/-- Two distinct cells differ in some coordinate. -/
private theorem cell_xy_ne (u v : Grid.Architecture.Cell) (h : u ≠ v) :
    u.x ≠ v.x ∨ u.y ≠ v.y := by
  by_cases hx : u.x = v.x
  · refine Or.inr fun hy => h ?_
    cases u <;> cases v <;> simp_all
  · exact Or.inl hx

/-- A tile-fitting node's dump rectangle stays inside its own pitch tile with gutter
clearance on the sides, which is exactly `RouteClearance.BoxBounds`. -/
private theorem node_box_bounds (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch) (nodeInput : List Grid.Architecture.Node)
    (groupInput : List Grid.Architecture.Group) (resolved : Grid.Architecture.Resolved)
    (n : Nat) (hn : n < nodeInput.length)
    (pxpos : 0 < pitch.x) (pypos : 0 < pitch.y) (g0 : 0 ≤ p.gutter)
    (_pth : 0 ≤ p.thickness)
    (fits : nodeTileFits p pitch (nodeInput.getD n default) = true)
    (jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2)
    (ptop : 0 ≤ pitch.top) :
    RouteClearance.BoxBounds pitch.x pitch.y p.gutter
      (RouteClearance.spanRect
        ((Grid.Architecture.geometry p pitch nodeInput groupInput resolved).boxes.getD n default))
      (resolved.nodes.getD n default).x (resolved.nodes.getD n default).y := by
  have icon := Grid.Architecture.geometry_icon_at p pitch nodeInput groupInput resolved n hn
  have hbox := Grid.Architecture.geometry_box_at p pitch nodeInput groupInput resolved n hn
  rw [icon] at hbox
  simp only [Grid.Architecture.sized] at hbox
  unfold nodeTileFits at fits
  have hright : (resolved.nodes.getD n default).x * pitch.x + pitch.x =
      ((resolved.nodes.getD n default).x + 1) * pitch.x := by
    rw [Int.add_mul, Int.one_mul]
  have hrightY : (resolved.nodes.getD n default).y * pitch.y + pitch.y =
      ((resolved.nodes.getD n default).y + 1) * pitch.y := by
    rw [Int.add_mul, Int.one_mul]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
  obtain ⟨fits1, fits2⟩ := fits
  have hdecomp := Int.mul_fdiv_add_fmod (pitch.x - (nodeInput.getD n default).icon.w) 2
  have hmodnn := Int.fmod_nonneg_of_pos (pitch.x - (nodeInput.getD n default).icon.w)
    (show (0 : Int) < 2 by decide)
  have hmodlt := Int.fmod_lt_of_pos (pitch.x - (nodeInput.getD n default).icon.w)
    (show (0 : Int) < 2 by decide)
  rw [hbox]
  simp only [RouteClearance.spanRect]
  by_cases hj : (nodeInput.getD n default).junction = true
  · have hjq := jq hj
    simp only [hj, ↓reduceIte] at fits2 ⊢
    refine ⟨pxpos, pypos, g0, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · simp only [hj, Bool.false_eq_true, ↓reduceIte] at fits2 ⊢
    refine ⟨pxpos, pypos, g0, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

/-- Node rectangles fitted into distinct pitch tiles stay disjoint under a common
translation: boxes in different columns are separated by the street between their
tiles, and boxes in different rows occupy disjoint row bands. -/
private theorem translated_node_boxes_disjoint (dx dy px py g : Int)
    (s1 s2 : Grid.Architecture.Span) (r1 r2 : Rect) (c1 c2 : Grid.Architecture.Cell)
    (h1 : Grid.Architecture.translateRect dx dy s1 = .ok r1)
    (h2 : Grid.Architecture.translateRect dx dy s2 = .ok r2)
    (b1 : RouteClearance.BoxBounds px py g (RouteClearance.spanRect s1) c1.x c1.y)
    (b2 : RouteClearance.BoxBounds px py g (RouteClearance.spanRect s2) c2.x c2.y)
    (hne : c1 ≠ c2) : Disjoint r1 r2 := by
  unfold Disjoint Rect.meetsInterior
  rcases Grid.Architecture.translateRect_shape dx dy s1 r1 h1 with deg1 | shape1
  · rw [deg1.2.2]
    exact zeroRect_no_meetsInterior r2
  · rcases Grid.Architecture.translateRect_shape dx dy s2 r2 h2 with deg2 | shape2
    · rw [deg2.2.2]
      intro hmi
      exact zeroRect_no_meetsInterior r1 ((Rect.meetsInterior_comm _ _).mp hmi)
    · obtain ⟨x1e, y1e, w1e, h1e⟩ := shape1
      obtain ⟨x2e, y2e, w2e, h2e⟩ := shape2
      obtain ⟨px1, py1, gn1, x0ge1, x1le1, y0ge1, y1le1⟩ := b1
      obtain ⟨px2, py2, gn2, x0ge2, x1le2, y0ge2, y1le2⟩ := b2
      simp only [RouteClearance.spanRect] at x0ge1 x1le1 y0ge1 y1le1 x0ge2 x1le2 y0ge2 y1le2

      rcases cell_xy_ne c1 c2 hne with hxx | hyy
      · -- Different columns: the street between the tiles separates the x-intervals.
        by_cases hlt : c1.x < c2.x
        · have hA : (c1.x + 1) * px ≤ c2.x * px :=
            Int.mul_le_mul_of_nonneg_right (by omega : (c1.x + 1) ≤ c2.x)
              (by omega : (0 : Int) ≤ px)
          rw [x1e, y1e, w1e, h1e, x2e, y2e, w2e, h2e]
          omega
        · have hA : (c2.x + 1) * px ≤ c1.x * px :=
            Int.mul_le_mul_of_nonneg_right (by omega : (c2.x + 1) ≤ c1.x)
              (by omega : (0 : Int) ≤ px)
          rw [x1e, y1e, w1e, h1e, x2e, y2e, w2e, h2e]
          omega
      · -- Different rows: the street between the tiles separates the y-intervals.
        by_cases hlt : c1.y < c2.y
        · have hB : (c1.y + 1) * py ≤ c2.y * py :=
            Int.mul_le_mul_of_nonneg_right (by omega : (c1.y + 1) ≤ c2.y)
              (by omega : (0 : Int) ≤ py)
          rw [x1e, y1e, w1e, h1e, x2e, y2e, w2e, h2e]
          omega
        · have hB : (c2.y + 1) * py ≤ c1.y * py :=
            Int.mul_le_mul_of_nonneg_right (by omega : (c2.y + 1) ≤ c1.y)
              (by omega : (0 : Int) ≤ py)
          rw [x1e, y1e, w1e, h1e, x2e, y2e, w2e, h2e]
          omega
/-- Clause 2: exclusive dump boxes sharing a parent are disjoint. `modelWellFormed`
forbids exclusive group boxes, so both boxes of a constrained pair are node boxes;
their resolved cells are distinct, and their tile-fitted rectangles cannot share an
interior once translated into the dump. -/
theorem architecture_c2 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    _root_.Validator.C2 result.scene.layoutDump := by
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
  have hrole : ∀ b ∈ m.boxes, (b.role != .group || !b.exclusive) = true := by
    have hmw : modelWellFormed m = true := hwf
    simp only [modelWellFormed, Bool.and_eq_true] at hmw
    exact List.all_eq_true.mp hmw.2
  have hboxEq : scene.layoutDump.boxes = dumpBoxes := by rw [hscene]; rfl
  have hnodeLen : nodeInput.length = nodes.length := by
    have hc := (Elegant.Grid.mapM_ok_pairs _ _ hcaptions).1
    have hn := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    simp only [List.length_zip] at hn
    omega
  have hpxBase : 0 < LayoutConst.architecture_pitch_x.get profile := by
    cases profile <;> decide
  have hpyBase : 0 < LayoutConst.architecture_pitch_y.get profile := by
    cases profile <;> decide
  have hpPitchX : p.pitchX = LayoutConst.architecture_pitch_x.get profile := by rw [hp]
  have hpPitchY : p.pitchY = LayoutConst.architecture_pitch_y.get profile := by rw [hp]
  have hpxpos : 0 < pitch.x := by
    rw [hpitch]
    have hx := pitch_x_lower p nodeInput sizes
    rw [hpPitchX] at hx
    have hbase : 0 < p.pitchX := by rw [hpPitchX]; exact hpxBase
    omega
  have hpypos : 0 < pitch.y := by
    rw [hpitch]
    have hy := pitch_y_lower p nodeInput sizes
    rw [hpPitchY] at hy
    have hbase : 0 < p.pitchY := by rw [hpPitchY]; exact hpyBase
    omega
  have hptop : 0 ≤ pitch.top := by
    rw [hpitch]
    exact pitch_top_nonneg p nodeInput sizes
  have hgut : 0 ≤ p.gutter := by
    rw [hp]
    show 0 ≤ (if cell then (1 : Int) else 0)
    split <;> omega
  have hpth : 0 ≤ p.thickness := by
    rw [hp]
    show 0 ≤ thickness
    rw [hthickness]
    cases profile <;> decide
  have hp_eq : p = archParams m := by
    rw [hp]
    simp only [archParams, archIconWidth, archIconHeight,
      GeometryParams.mk.injEq]
    rw [← hprofile, ← hcell]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | rfl
        | exact hiw
        | exact hih
        | exact hlh
        | exact hinset
        | exact hthickness
  have hpitch_eq : pitch = archPitch m nodeInput edgeLines := by
    rw [hpitch, hsizes]
    simp only [archPitch, archLineHeight]
    rw [← hp_eq, ← hprofile, ← hlh]
  rw [← hp_eq, ← hpitch_eq] at hguard
  have hfits : ∀ n, n < nodeInput.length →
      nodeTileFits p pitch (nodeInput.getD n default) = true := by
    intro n hn
    have hmem : nodeInput.getD n default ∈ nodeInput := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
        Option.getD_some] using List.getElem_mem hn
    by_cases hfit : nodeTileFits p pitch (nodeInput.getD n default) = true
    · exact hfit
    · have hfalse : nodeTileFits p pitch (nodeInput.getD n default) = false :=
        Bool.eq_false_iff.mpr hfit
      have hany : nodeInput.any (fun n => !(nodeTileFits p pitch n)) = true :=
        List.any_eq_true.mpr ⟨nodeInput.getD n default, hmem, by rw [hfalse]; decide⟩
      exact absurd hany hguard
  have hjsle : LayoutConst.architecture_junction_size.get profile ≤
      LayoutConst.architecture_pitch_y.get profile := by
    cases profile <;> decide
  have hpy' : p.pitchY ≤ pitch.y := by
    have h := pitch_y_lower p nodeInput sizes
    rw [← hpitch] at h
    exact h
  have node_decode : ∀ n, n < nodeInput.length →
      ((nodeInput.getD n default).junction = true →
        (nodeInput.getD n default).icon.h =
          LayoutConst.architecture_junction_size.get profile) ∧
      ((nodeInput.getD n default).parent = -1 ∨
        ∃ i, i < groups.length ∧
          (nodeInput.getD n default).parent = Int.ofNat i) := by
    intro n hn
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    have hxs : n < (nodes.zip captions).length := by rw [hnl]; exact hn
    have hzip : (nodes.zip captions).length =
        min nodes.length captions.length := by simp only [List.length_zip]
    have hnn : n < nodes.length := by omega
    have hnc : n < captions.length := by omega
    have hdec := mapM_pointwise hnodeInput n hxs hn
    simp only [List.getElem_zip] at hdec
    cases hp : parentIndex groups nodes[n].parent with
    | error err =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hget : nodeInput.getD n default = nodeInput[n] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
            Option.getD_some]
        refine ⟨?_, ?_⟩
        · intro hj
          rw [hget, ← hdec] at hj ⊢
          dsimp only at hj ⊢
          simp only [hj, ↓reduceIte]
        · rw [hget, ← hdec]
          dsimp only
          exact parentIndex_ok_admitted hp
  have groupLen : groupInput.length = groups.length := by
    have hgl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have htit := (Elegant.Grid.mapM_ok_pairs _ _ htitles).1
    have hzl : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    rw [htit] at hzl
    simp only [Nat.min_self] at hzl
    exact (hgl.symm.trans hzl).trans htit.symm
  have group_decode : ∀ g, g < groupInput.length →
      (groupInput.getD g default).parent = -1 ∨
        ∃ i, i < groups.length ∧
          (groupInput.getD g default).parent = Int.ofNat i := by
    intro g hg
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have hxs : g < (groups.zip titles).length := by rw [hnl]; exact hg
    have hzip : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    have hgg : g < groups.length := by omega
    have hgt : g < titles.length := by omega
    have hdec := mapM_pointwise hgroupInput g hxs hg
    simp only [List.getElem_zip] at hdec
    cases hp : parentIndex groups groups[g].parent with
    | error err =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hget : groupInput.getD g default = groupInput[g] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
            Option.getD_some]
        rw [hget, ← hdec]
        dsimp only
        exact parentIndex_ok_admitted hp
  have hg_eq : input.groups = groupInput := by rw [hinput]
  have hpar : input.parents = nodeInput.map (·.parent) := by rw [hinput]
  have ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k := by
    rw [hinput]
    intro k hk
    change (groupInput.getD k default).parent < Int.ofNat k
    apply Classical.byContradiction
    intro notEarlier
    have indexed : (groupInput.getD k default, k) ∈ groupInput.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some]
    have hany : groupInput.zipIdx.any
        (fun q => decide (q.1.parent ≥ Int.ofNat q.2)) = true := by
      apply List.any_eq_true.mpr
      refine ⟨(groupInput.getD k default, k), indexed, ?_⟩
      simp only [decide_eq_true_eq]
      omega
    exact absurd hany hgroupOrder
  have groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent := by
    intro g hg
    have hg' : g < groupInput.length := by rw [← hg_eq]; exact hg
    rw [hg_eq]
    rcases group_decode g hg' with h | ⟨i, hi, heq⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, by rw [groupLen]; exact hi, heq⟩
  have hpad : 0 ≤ padding := by
    rw [hpadding]
    let value : Option Int :=
      match m.options.config.find? (fun q => q.1 == "padding") with
      | some (_, .integer v) =>
        if 0 ≤ v ∧ v ≤ I32_MAX then some v else none
      | _ => none
    change 0 ≤ (match value with
      | some px => if cell then Int.fdiv (2 * px + 20) 40 else px * 64
      | none => LayoutConst.architecture_padding.get profile)
    cases actual : value with
    | none =>
        change 0 ≤ LayoutConst.architecture_padding.get profile
        cases profile <;> decide
    | some px =>
        have hcfg : configInt m "padding" = some px := actual
        have hpx0 : 0 ≤ px := configInt_value_nonneg m "padding" px hcfg
        change 0 ≤ (if cell then Int.fdiv (2 * px + 20) 40 else px * 64)
        cases cell with
        | false =>
            change 0 ≤ px * 64
            exact Int.mul_nonneg hpx0 (by decide)
        | true =>
            change 0 ≤ Int.fdiv (2 * px + 20) 40
            rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
            exact Int.ediv_nonneg (by omega) (by decide)
  have hfpad : 0 ≤ frameParams.padding := by rw [hframeParams]; exact hpad
  have hfline : 0 ≤ frameParams.lineHeight := by
    rw [hframeParams]
    have hlh0 : 0 ≤ lh := by rw [hlh]; cases profile <;> decide
    exact hlh0
  have hpX : 0 < params.pitchX := by rw [hparams]; exact hpxpos
  have hpY : 0 < params.pitchY := by rw [hparams]; exact hpypos
  have parents_adm : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
    intro parent hmem
    rw [hpar] at hmem
    obtain ⟨a, ha, hfa⟩ := List.mem_map.mp hmem
    obtain ⟨k, hk, hka⟩ := List.mem_iff_getElem.mp ha
    have hkp : nodeInput[k].parent = parent := by
      have h1 := congrArg (fun x : Grid.Architecture.Node => x.parent) hka
      exact h1.trans hfa
    have hkd : nodeInput.getD k default = nodeInput[k] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some]
    obtain ⟨hjc, hE⟩ := node_decode k hk
    rw [hkd] at hE
    rcases hE with h | ⟨i, hi, heq⟩
    · left
      rw [hkp] at h
      exact h
    · right
      refine ⟨i, ?_, ?_⟩
      · rw [hg_eq, groupLen]; exact hi
      · rw [hkp] at heq
        exact heq
  have hnodup : resolved.nodes.Nodup := by
    have huniq := CellContracts.hierarchy_final_cells_unique input params
      frameParams (LayoutConst.architecture_bfs_cap.get profile).toNat
      ordered groupParents parents_adm hpX hpY hfpad hfline
    rw [← hplaced, ← hresolved] at huniq
    exact huniq
  have hresLen : nodeInput.length ≤ resolved.nodes.length := by
    have hlen := (resolveHierarchy_storage_lengths input params frameParams
      (LayoutConst.architecture_bfs_cap.get profile).toNat).1
    rw [← hplaced, ← hresolved] at hlen
    have hparLen : input.parents.length = nodeInput.length := by
      rw [hpar, List.length_map]
    have hge : input.parents.length ≤ (virtualParents input).length := by
      simp only [virtualParents, List.length_append, List.length_map]
      omega
    rw [hlen, ← hparLen]
    exact hge
  have hjqAt : ∀ n, n < nodeInput.length →
      (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2 := by
    intro n hn hj
    obtain ⟨hjc, _⟩ := node_decode n hn
    have hij : (nodeInput.getD n default).icon.h =
        LayoutConst.architecture_junction_size.get profile := hjc hj
    have hdiff : 0 ≤ pitch.y - (nodeInput.getD n default).icon.h := by
      rw [hij]
      omega
    exact Int.fdiv_nonneg hdiff (by decide)
  have hboxBoundsAt : ∀ n, n < nodeInput.length →
      RouteClearance.BoxBounds pitch.x pitch.y p.gutter
        (RouteClearance.spanRect (geometry.boxes.getD n default))
        (resolved.nodes.getD n default).x (resolved.nodes.getD n default).y := by
    intro n hn
    have h := node_box_bounds p pitch nodeInput groupInput resolved n hn
      hpxpos hpypos hgut hpth
      (hfits n hn) (hjqAt n hn) hptop
    rw [← hgeometry] at h
    exact h
  have hgeomsLen : geometry.boxes.length = nodes.length := by
    rw [hgeometry]
    simp only [Grid.Architecture.geometry, List.length_map, List.length_zipIdx]
    exact hnodeLen
  have hboxesLen : geometry.boxes.length = boxes.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hboxes).1
  intro b hb c hc _hid hexclb hexclc _hparent
  rw [hboxEq] at hb hc
  obtain ⟨mb, hmb, hrecb⟩ := mapM_output_origin hdumpBoxes hb
  obtain ⟨mc, hmc, hrecc⟩ := mapM_output_origin hdumpBoxes hc
  simp only at hrecb hrecc
  have hbNode : ∃ f, f < nodes.length ∧ (nodes.getD f default).id = mb.id ∧
      b.id = mb.id ∧ b.rect = boxes.getD f ⟨0, 0, 0, 0⟩ := by
    by_cases hgroup : (mb.role == BoxRole.group) = true
    · exfalso
      simp only [hgroup, ↓reduceIte] at hrecb
      cases hfound : groups.findIdx? (fun q => q.id == mb.id) with
      | none =>
          simp only [hfound, pure, Except.pure, Bind.bind, Except.bind, throw,
            throwThe, MonadExceptOf.throw] at hrecb
          cases hrecb
      | some i =>
          simp only [hfound, pure, Except.pure, Bind.bind, Except.bind] at hrecb
          cases hrecb
          have hne : (mb.role != BoxRole.group) = false := by
            cases hrole2 : mb.role <;> simp_all
          have hfalse : mb.exclusive = false := by
            have hsafe := hrole mb hmb
            rw [hne] at hsafe
            simpa using hsafe
          have htrue : mb.exclusive = true := hexclb
          rw [hfalse] at htrue
          cases htrue
    · have hgroupF : (mb.role == BoxRole.group) = false := by simp [hgroup]
      simp only [hgroupF, ↓reduceIte] at hrecb
      cases hfind : nodes.findIdx? (fun q => q.id == mb.id) with
      | none =>
          simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw,
            throwThe, MonadExceptOf.throw] at hrecb
          cases hrecb
      | some f =>
          simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at hrecb
          cases hrecb
          have hfLen : f < nodes.length :=
            (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
          have hfId : (nodes.getD f default).id = mb.id := by
            have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
            have hg : nodes.getD f default = nodes[f] := by
              simp only [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hfLen, Option.getD_some]
            rw [hg]
            simpa using hbeq
          exact ⟨f, hfLen, hfId, rfl, rfl⟩
  have hcNode : ∃ g, g < nodes.length ∧ (nodes.getD g default).id = mc.id ∧
      c.id = mc.id ∧ c.rect = boxes.getD g ⟨0, 0, 0, 0⟩ := by
    by_cases hgroup : (mc.role == BoxRole.group) = true
    · exfalso
      simp only [hgroup, ↓reduceIte] at hrecc
      cases hfound : groups.findIdx? (fun q => q.id == mc.id) with
      | none =>
          simp only [hfound, pure, Except.pure, Bind.bind, Except.bind, throw,
            throwThe, MonadExceptOf.throw] at hrecc
          cases hrecc
      | some i =>
          simp only [hfound, pure, Except.pure, Bind.bind, Except.bind] at hrecc
          cases hrecc
          have hne : (mc.role != BoxRole.group) = false := by
            cases hrole2 : mc.role <;> simp_all
          have hfalse : mc.exclusive = false := by
            have hsafe := hrole mc hmc
            rw [hne] at hsafe
            simpa using hsafe
          have htrue : mc.exclusive = true := hexclc
          rw [hfalse] at htrue
          cases htrue
    · have hgroupF : (mc.role == BoxRole.group) = false := by simp [hgroup]
      simp only [hgroupF, ↓reduceIte] at hrecc
      cases hfind : nodes.findIdx? (fun q => q.id == mc.id) with
      | none =>
          simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw,
            throwThe, MonadExceptOf.throw] at hrecc
          cases hrecc
      | some g =>
          simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at hrecc
          cases hrecc
          have hgLen : g < nodes.length :=
            (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
          have hgId : (nodes.getD g default).id = mc.id := by
            have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
            have hg : nodes.getD g default = nodes[g] := by
              simp only [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hgLen, Option.getD_some]
            rw [hg]
            simpa using hbeq
          exact ⟨g, hgLen, hgId, rfl, rfl⟩
  obtain ⟨f, hfLen, hfGetD, hfbId, hfbRect⟩ := hbNode
  obtain ⟨g, hgLen, hgGetD, hgcId, hgRect⟩ := hcNode
  have hfId : nodes[f].id = mb.id := by
    have hg : nodes.getD f default = nodes[f] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfLen,
        Option.getD_some]
    rw [← hg]
    exact hfGetD
  have hgId : nodes[g].id = mc.id := by
    have hg : nodes.getD g default = nodes[g] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgLen,
        Option.getD_some]
    rw [← hg]
    exact hgGetD
  have hfInput : f < nodeInput.length := by omega
  have hgInput : g < nodeInput.length := by omega
  have hfg : f ≠ g := by
    intro heq
    subst heq
    apply _hid
    rw [hfbId, hgcId, ← hfId, ← hgId]

  have hfn : f < resolved.nodes.length := by omega
  have hgn : g < resolved.nodes.length := by omega
  have hcellsNe : resolved.nodes.getD f default ≠ resolved.nodes.getD g default := by
    intro heq
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfn, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgn, Option.getD_some] at heq
    rcases Nat.lt_or_gt_of_ne hfg with hlt | hlt
    · exact nodup_getElem_ne hnodup f g hfn hgn hlt heq
    · exact nodup_getElem_ne hnodup g f hgn hfn hlt heq.symm
  have hfGeom : f < geometry.boxes.length := by omega
  have hgGeom : g < geometry.boxes.length := by omega
  obtain ⟨hboxesLf, hboxAtf⟩ := mapM_at hboxes f hfGeom
  obtain ⟨hboxesLg, hboxAtg⟩ := mapM_at hboxes g hgGeom
  have hspanDf : geometry.boxes.getD f default = geometry.boxes[f] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfGeom,
      Option.getD_some]
  have hboxGetDf : boxes.getD f ⟨0, 0, 0, 0⟩ = boxes[f] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hboxesLf,
      Option.getD_some]
  have hspanDg : geometry.boxes.getD g default = geometry.boxes[g] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgGeom,
      Option.getD_some]
  have hboxGetDg : boxes.getD g ⟨0, 0, 0, 0⟩ = boxes[g] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hboxesLg,
      Option.getD_some]
  have hrectTransf : Grid.Architecture.translateRect dx dy
      (geometry.boxes.getD f default) = .ok (boxes.getD f ⟨0, 0, 0, 0⟩) := by
    rw [hspanDf, hboxGetDf]
    exact hboxAtf
  have hrectTransg : Grid.Architecture.translateRect dx dy
      (geometry.boxes.getD g default) = .ok (boxes.getD g ⟨0, 0, 0, 0⟩) := by
    rw [hspanDg, hboxGetDg]
    exact hboxAtg
  have hdis := translated_node_boxes_disjoint dx dy pitch.x pitch.y p.gutter
    (geometry.boxes.getD f default) (geometry.boxes.getD g default)
    (boxes.getD f ⟨0, 0, 0, 0⟩) (boxes.getD g ⟨0, 0, 0, 0⟩)
    (resolved.nodes.getD f default) (resolved.nodes.getD g default)
    hrectTransf hrectTransg (hboxBoundsAt f hfInput) (hboxBoundsAt g hgInput)
    hcellsNe
  rw [hfbRect, hgRect]
  exact hdis
end Elegant.Kinds.Architecture
