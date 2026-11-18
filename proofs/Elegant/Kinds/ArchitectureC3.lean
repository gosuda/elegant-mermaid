import Elegant.GridArchitectureCellContracts
import Elegant.GridArchitectureRouteClearanceFacts
import Elegant.Kinds.ArchitectureStructural

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Elegant
open Elegant.Grid.Architecture
open Elegant.Grid.Architecture.ClearanceAux
local instance : Inhabited Elegant.ModelBox := ⟨{ id := "" }⟩

namespace Elegant.Kinds.Architecture

/-! ### Clause 3 for the architecture adapter

Clause 3 asks that every dump box whose `parent` field is nonempty lies inside the
rectangle of the dump box that field names. The executed build gives this directly: a
node's resolved cell sits inside its parent group's frame
(`CellContracts.node_ancestor_frames_contain_tile`), its measured box stays inside its
pitch tile (`nodeTileFits` admission), and a child group's frame sits inside its parent
group's frame (`CellContracts.resolved_group_contains_child_frame`). The dump rectangles
are translations of those spans, and translation preserves containment. -/

/-- `mapM` point lookup: the `i`-th output is the image of the `i`-th input. -/
private theorem c3_mapM_at {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (hi : i < xs.length) :
    ∃ hy : i < ys.length, f xs[i] = .ok ys[i] := by
  have hy : i < ys.length := by
    have hlen := (Elegant.Grid.mapM_ok_pairs xs ys h).1
    omega
  exact ⟨hy, mapM_pointwise h i hi hy⟩

/-- Point lookup in an indexed map. -/
private theorem c3_zipIdx_map_getD {α β : Type} (items : List α) (f : α × Nat → β)
    (i : Nat) (a : α) (b : β) (bound : i < items.length) :
    (items.zipIdx.map f).getD i b = f (items.getD i a, i) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem bound, Option.map_some, Option.getD_some, Nat.zero_add]

/-- A group's own unit closes its ancestor chain whenever the chain has fuel. -/
private theorem c3_groupChain_self (groups : List Grid.Architecture.Group) :
    ∀ (fuel : Nat) (k : Nat), 0 < fuel →
      (⟨-1, Int.ofNat k⟩ : Grid.Architecture.Unit) ∈
        Grid.Architecture.groupChain groups fuel (Int.ofNat k) := by
  intro fuel
  cases fuel with
  | zero => intro k hk; omega
  | succ rest =>
    intro k _
    have hnn : ¬(Int.ofNat k < 0) := Int.not_lt.mpr (Int.natCast_nonneg k)
    rw [Grid.Architecture.groupChain, ite_eq_right hnn, Int.ofNat_eq_natCast,
      Int.toNat_natCast, List.mem_append]
    exact Or.inr (List.mem_singleton.mpr rfl)

/-- Span containment is transitive. -/
private theorem c3_span_contains_trans (outer middle inner : Grid.Architecture.Span)
    (first : outer.contains middle) (second : middle.contains inner) :
    outer.contains inner := by
  unfold Grid.Architecture.Span.contains at first second ⊢
  omega

/-- Translating both spans by the same offset preserves containment. Degenerate spans
translate to the zero rectangle instead, so both spans must be non-degenerate. -/
private theorem c3_translate_contained (dx dy : Int)
    (outer inner : Grid.Architecture.Span) (ro ri : Rect)
    (ho : Grid.Architecture.translateRect dx dy outer = .ok ro)
    (hi : Grid.Architecture.translateRect dx dy inner = .ok ri)
    (hout : ¬(outer.x0 = outer.x1 ∧ outer.y0 = outer.y1))
    (hin : ¬(inner.x0 = inner.x1 ∧ inner.y0 = inner.y1))
    (hcon : outer.contains inner) : ro.Contained ri := by
  rcases Grid.Architecture.translateRect_shape dx dy outer ro ho with deg | shapeo
  · exact absurd ⟨deg.1, deg.2.1⟩ hout
  · rcases Grid.Architecture.translateRect_shape dx dy inner ri hi with deg | shapei
    · exact absurd ⟨deg.1, deg.2.1⟩ hin
    · obtain ⟨ox, oy, ow, oh⟩ := shapeo
      obtain ⟨ix, iy, iw, ih⟩ := shapei
      simp only [Grid.Architecture.Span.contains] at hcon
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- Every resolved group frame spans a positive horizontal extent: it is a translate of
a placed relative frame, which contains its anchor tile. -/
private theorem c3_frame_x0_lt_x1 (input : Grid.Architecture.Input)
    (p : Grid.Architecture.Params) (fp : Grid.Architecture.FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (k : Nat) (hk : k < input.groups.length) :
    ((Grid.Architecture.resolveHierarchy input p
        (Grid.Architecture.placeHierarchy input p fp fuel)).frames.getD k default).x0 <
      ((Grid.Architecture.resolveHierarchy input p
        (Grid.Architecture.placeHierarchy input p fp fuel)).frames.getD k default).x1 := by
  obtain ⟨origins, -, -, framesEq, -⟩ :=
    Grid.Architecture.resolveHierarchy_execution input p
      (Grid.Architecture.placeHierarchy input p fp fuel) ordered
  have framesLen :
      ((Grid.Architecture.resolveHierarchy input p
        (Grid.Architecture.placeHierarchy input p fp fuel)).frames).length =
        input.groups.length :=
    (Grid.Architecture.resolveHierarchy_storage_lengths input p fp fuel).2
  have relLen :
      ((Grid.Architecture.placeHierarchy input p fp fuel).relative).length =
        input.groups.length :=
    (Grid.Architecture.placeHierarchy_storage_lengths input p fp fuel).2.2
  have anchor := Grid.Architecture.placeHierarchy_frame_anchors input p fp fuel
    ordered px py padding line k hk
  have lookup :
      ((Grid.Architecture.resolveHierarchy input p
        (Grid.Architecture.placeHierarchy input p fp fuel)).frames.getD k default) =
      (((Grid.Architecture.placeHierarchy input p fp fuel).relative.getD k default).shift
        ((origins.getD k default).x * p.pitchX)
        ((origins.getD k default).y * p.pitchY)) := by
    rw [framesEq]
    exact c3_zipIdx_map_getD _ _ k default default (by rw [relLen]; exact hk)
  rw [lookup]
  simp only [Grid.Architecture.ContainsAnchor] at anchor
  simp only [Grid.Architecture.Span.shift]
  omega

/-- The node box's vertical extent stays inside its pitch tile, from the
`nodeTileFits` admission guard. -/
private theorem c3_node_box_y_inside_tile (p : GeometryParams) (pitch : Pitch)
    (nodeInput : List Node) (groupInput : List Grid.Architecture.Group) (resolved : Resolved)
    (n : Nat) (hn : n < nodeInput.length)
    (fits : nodeTileFits p pitch (nodeInput.getD n default) = true)
    (jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2)
    (ptop : 0 ≤ pitch.top) (hgutter : 0 ≤ p.gutter) :
    (resolved.nodes.getD n default).y * pitch.y ≤
      ((geometry p pitch nodeInput groupInput resolved).boxes.getD n default).y0 ∧
    ((geometry p pitch nodeInput groupInput resolved).boxes.getD n default).y1 ≤
      ((resolved.nodes.getD n default).y + 1) * pitch.y := by
  have hbox := geometry_box_at p pitch nodeInput groupInput resolved n hn
  have hicon := geometry_icon_at p pitch nodeInput groupInput resolved n hn
  rw [hicon] at hbox
  simp only [sized] at hbox
  have hrightY : (resolved.nodes.getD n default).y * pitch.y + pitch.y =
      ((resolved.nodes.getD n default).y + 1) * pitch.y := by
    rw [Int.add_mul, Int.one_mul]
  unfold nodeTileFits at fits
  simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
  obtain ⟨-, fits2⟩ := fits
  rw [hbox]
  by_cases hj : (nodeInput.getD n default).junction = true
  · have hjq := jq hj
    simp only [hj, ↓reduceIte] at fits2 ⊢
    exact ⟨by omega, by omega⟩
  · simp only [hj, Bool.false_eq_true, ↓reduceIte] at fits2 ⊢
    exact ⟨by omega, by omega⟩

/-- A tile-fitting node's geometry box stays inside its own pitch tile. -/
private theorem c3_node_box_inside_tile (p : GeometryParams) (pitchv : Pitch)
    (sizes : List Size) (nodeInput : List Node)
    (groupInput : List Grid.Architecture.Group) (resolved : Resolved)
    (n : Nat) (hn : n < nodeInput.length)
    (hpitchEq : pitchv = Grid.Architecture.pitch p nodeInput sizes)
    (sourceWidth : (nodeInput.getD n default).icon.w ≤
      max p.pitchX (p.iconW + p.gutter))
    (fits : nodeTileFits p pitchv (nodeInput.getD n default) = true)
    (jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitchv.y - (nodeInput.getD n default).icon.h) 2)
    (ptop : 0 ≤ pitchv.top) (hgutter : 0 ≤ p.gutter) :
    ((⟨0, 0, pitchv.x, pitchv.y⟩ : Span).shift
      ((resolved.nodes.getD n default).x * pitchv.x)
      ((resolved.nodes.getD n default).y * pitchv.y)).contains
      ((geometry p pitchv nodeInput groupInput resolved).boxes.getD n default) := by
  have hhor := geometry_box_horizontal_inside_native_tile p nodeInput sizes groupInput
    resolved n hn sourceWidth
  rw [← hpitchEq] at hhor
  dsimp only at hhor
  obtain ⟨hx0, hx1⟩ := hhor
  have hvert := c3_node_box_y_inside_tile p pitchv nodeInput groupInput resolved n hn
    fits jq ptop hgutter
  obtain ⟨hy0, hy1⟩ := hvert
  have hrightX : (resolved.nodes.getD n default).x * pitchv.x + pitchv.x =
      ((resolved.nodes.getD n default).x + 1) * pitchv.x := by
    rw [Int.add_mul, Int.one_mul]
  have hrightY : (resolved.nodes.getD n default).y * pitchv.y + pitchv.y =
      ((resolved.nodes.getD n default).y + 1) * pitchv.y := by
    rw [Int.add_mul, Int.one_mul]
  simp only [Grid.Architecture.Span.contains, Grid.Architecture.Span.shift]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A node's geometry box spans a positive horizontal extent because its icon width is
positive. -/
private theorem c3_node_box_x0_lt_x1 (p : GeometryParams) (pitchv : Pitch)
    (nodeInput : List Node) (groupInput : List Grid.Architecture.Group)
    (resolved : Resolved) (n : Nat) (hn : n < nodeInput.length)
    (hw : 0 < (nodeInput.getD n default).icon.w) :
    ((geometry p pitchv nodeInput groupInput resolved).boxes.getD n default).x0 <
      ((geometry p pitchv nodeInput groupInput resolved).boxes.getD n default).x1 := by
  have hbox := geometry_box_at p pitchv nodeInput groupInput resolved n hn
  have hicon := geometry_icon_at p pitchv nodeInput groupInput resolved n hn
  rw [hicon] at hbox
  simp only [sized] at hbox
  rw [hbox]
  dsimp only
  omega

/-- The computed pitch never drops below the base pitch on either axis. -/
private theorem c3_pitch_x_lower (p : GeometryParams)
    (nodes : List Node) (edgeLabels : List Size) :
    p.pitchX ≤ (pitch p nodes edgeLabels).x := by
  simp only [pitch]
  split <;> omega

private theorem c3_pitch_y_lower (p : GeometryParams)
    (nodes : List Node) (edgeLabels : List Size) :
    p.pitchY ≤ (pitch p nodes edgeLabels).y := by
  simp only [pitch]
  omega

/-- The computed pitch's top inset is never negative. -/
private theorem c3_pitch_top_nonneg (p : GeometryParams)
    (nodes : List Node) (edgeLabels : List Size) :
    0 ≤ (pitch p nodes edgeLabels).top := by
  simp only [pitch]
  split <;> omega

/-- A decoded configuration integer is nonnegative. -/
private theorem c3_configInt_value_nonneg (m : Model) (key : String) (v : Int)
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

/-- Clause 3: every dump box whose `parent` field is nonempty lies inside the rectangle
of the dump box that field names. A node's parent is a group: the executed node decode
resolves it through `parentIndex`, the group frame contains the node's pitch tile, and
the tile contains the node's measured box. A group's parent is a group as well, and the
parent frame contains the child frame. Dump rectangles translate those spans, and
translation preserves containment. -/
theorem architecture_c3 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    _root_.Validator.C3 result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := Grid.Architecture.public_layout_dump m result h
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
    have hx := c3_pitch_x_lower p nodeInput sizes
    rw [hpPitchX] at hx
    have hbase : 0 < p.pitchX := by rw [hpPitchX]; exact hpxBase
    omega
  have hpypos : 0 < pitch.y := by
    rw [hpitch]
    have hy := c3_pitch_y_lower p nodeInput sizes
    rw [hpPitchY] at hy
    have hbase : 0 < p.pitchY := by rw [hpPitchY]; exact hpyBase
    omega
  have hptop : 0 ≤ pitch.top := by
    rw [hpitch]
    exact c3_pitch_top_nonneg p nodeInput sizes
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
  have hlh0 : 0 ≤ lh := by rw [hlh]; cases profile <;> decide
  have hiw0 : 0 < iw := by
    rw [hiw]
    cases hcfg : configInt m "iconSize" with
    | none =>
        show 0 < LayoutConst.architecture_icon_width.get profile
        cases profile <;> decide
    | some px =>
        have hpx0 : 0 ≤ px := c3_configInt_value_nonneg m "iconSize" px hcfg
        show 0 < (if px > 0 then
          (if cell then max 1 (Int.fdiv (14*px+80) 160) else px*64)
          else LayoutConst.architecture_icon_width.get profile)
        split
        · rename_i hpx
          split
          · exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1)
              (Int.le_max_left _ _)
          · exact Int.mul_pos hpx (by decide)
        · cases profile <;> decide
  have hjs0 : 0 < LayoutConst.architecture_junction_size.get profile := by
    cases profile <;> decide
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
  have groupLen : groupInput.length = groups.length := by
    have hgl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have htit := (Elegant.Grid.mapM_ok_pairs _ _ htitles).1
    have hzl : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    rw [htit] at hzl
    simp only [Nat.min_self] at hzl
    exact (hgl.symm.trans hzl).trans htit.symm
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
        have hpx0 : 0 ≤ px := c3_configInt_value_nonneg m "padding" px hcfg
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
    show 0 ≤ lh
    exact hlh0
  have hpX : 0 < params.pitchX := by rw [hparams]; exact hpxpos
  have hpY : 0 < params.pitchY := by rw [hparams]; exact hpypos
  have hg_eq : input.groups = groupInput := by rw [hinput]
  have hparEq : input.parents = nodeInput.map (·.parent) := by rw [hinput]
  have hparLen : input.parents.length = nodeInput.length := by
    rw [hparEq, List.length_map]
  have hframesLen : resolved.frames.length = input.groups.length := by
    rw [hresolved, hplaced]
    exact (Grid.Architecture.resolveHierarchy_storage_lengths input params frameParams
      (LayoutConst.architecture_bfs_cap.get profile).toNat).2
  have hgeomFrames : geometry.frames = resolved.frames := by rw [hgeometry]; rfl
  have hgeomBoxesLen : geometry.boxes.length = nodeInput.length := by
    rw [hgeometry]
    simp only [Grid.Architecture.geometry, List.length_map, List.length_zipIdx,
      hnodeLen]
  have framesTrans : ∀ i, i < input.groups.length →
      Grid.Architecture.translateRect dx dy (resolved.frames.getD i default) =
        .ok (frames.getD i ⟨0, 0, 0, 0⟩) := by
    intro i hi
    have hiG : i < geometry.frames.length := by rw [hgeomFrames, hframesLen]; exact hi
    obtain ⟨hy, hpt⟩ := c3_mapM_at hframes i hiG
    have hsrcD : geometry.frames.getD i default = geometry.frames[i]'hiG := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiG,
        Option.getD_some]
    have houtD : frames.getD i ⟨0, 0, 0, 0⟩ = frames[i]'hy := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy,
        Option.getD_some]
    rw [← hgeomFrames, hsrcD, houtD]
    exact hpt
  have boxesTrans : ∀ f, f < nodeInput.length →
      Grid.Architecture.translateRect dx dy (geometry.boxes.getD f default) =
        .ok (boxes.getD f ⟨0, 0, 0, 0⟩) := by
    intro f hf
    have hfG : f < geometry.boxes.length := by rw [hgeomBoxesLen]; exact hf
    obtain ⟨hy, hpt⟩ := c3_mapM_at hboxes f hfG
    have hsrcD : geometry.boxes.getD f default = geometry.boxes[f]'hfG := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfG,
        Option.getD_some]
    have houtD : boxes.getD f ⟨0, 0, 0, 0⟩ = boxes[f]'hy := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy,
        Option.getD_some]
    rw [hsrcD, houtD]
    exact hpt
  have node_decode : ∀ f, f < nodeInput.length →
      ((nodeInput.getD f default).icon.w =
          if (nodeInput.getD f default).junction then
            LayoutConst.architecture_junction_size.get profile else iw) ∧
      ((nodeInput.getD f default).junction = true →
        (nodeInput.getD f default).icon.h =
          LayoutConst.architecture_junction_size.get profile) ∧
      ((nodeInput.getD f default).parent = -1 ∧ (nodes.getD f default).parent = "" ∨
        ∃ i, i < groups.length ∧ (nodeInput.getD f default).parent = Int.ofNat i ∧
          groups.findIdx? (fun q => q.id == (nodes.getD f default).parent) = some i) := by
    intro f hf
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    have hxs : f < (nodes.zip captions).length := by rw [hnl]; exact hf
    have hzip : (nodes.zip captions).length =
        min nodes.length captions.length := by simp only [List.length_zip]
    have hnn : f < nodes.length := by omega
    have hnc : f < captions.length := by omega
    have hdec := mapM_pointwise hnodeInput f hxs hf
    simp only [List.getElem_zip] at hdec
    have hnd : nodes.getD f default = nodes[f]'hnn := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnn,
        Option.getD_some]
    have hget : nodeInput.getD f default = nodeInput[f]'hf := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf,
        Option.getD_some]
    cases hp : parentIndex groups (nodes[f]'hnn).parent with
    | error err =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        rw [← hnd] at hp
        refine ⟨?_, ?_, ?_⟩
        · rw [hget, ← hdec]
        · intro hj
          rw [hget, ← hdec] at hj ⊢
          dsimp only at hj ⊢
          simp only [hj, ↓reduceIte]
        · by_cases hempty : (nodes.getD f default).parent = ""
          · left
            have hminus : parentIndex groups (nodes.getD f default).parent =
                .ok (-1) := by rw [hempty]; simp [parentIndex]
            rw [hp] at hminus
            have hval : parent = -1 := Except.ok.inj hminus
            exact ⟨by rw [hget, ← hdec, hval], hempty⟩
          · right
            obtain ⟨i, hi, heq, hfind⟩ := decoded_parent_index hp hempty
            exact ⟨i, hi, by rw [hget, ← hdec, heq], hfind⟩
  have group_decode : ∀ c, c < groupInput.length →
      ((groupInput.getD c default).parent = -1 ∧ (groups.getD c default).parent = "" ∨
        ∃ i, i < groups.length ∧ (groupInput.getD c default).parent = Int.ofNat i ∧
          groups.findIdx? (fun q => q.id == (groups.getD c default).parent) = some i) := by
    intro c hc
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have hxs : c < (groups.zip titles).length := by rw [hnl]; exact hc
    have hzip : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    have hgg : c < groups.length := by omega
    have hgt : c < titles.length := by omega
    have hdec := mapM_pointwise hgroupInput c hxs hc
    simp only [List.getElem_zip] at hdec
    have hgd : groups.getD c default = groups[c]'hgg := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgg,
        Option.getD_some]
    have hgetG : groupInput.getD c default = groupInput[c]'hc := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc,
        Option.getD_some]
    cases hp : parentIndex groups (groups[c]'hgg).parent with
    | error err =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hp] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        rw [← hgd] at hp
        by_cases hempty : (groups.getD c default).parent = ""
        · left
          have hminus : parentIndex groups (groups.getD c default).parent =
              .ok (-1) := by rw [hempty]; simp [parentIndex]
          rw [hp] at hminus
          have hval : parent = -1 := Except.ok.inj hminus
          exact ⟨by rw [hgetG, ← hdec, hval], hempty⟩
        · right
          obtain ⟨i, hi, heq, hfind⟩ := decoded_parent_index hp hempty
          exact ⟨i, hi, by rw [hgetG, ← hdec, heq], hfind⟩
  have ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k := by
    intro k hk
    have hgk : k < groupInput.length := by rw [← hg_eq]; exact hk
    rw [hg_eq]
    apply Classical.byContradiction
    intro notEarlier
    have indexed : (groupInput.getD k default, k) ∈ groupInput.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgk, Option.getD_some]
    have hany : groupInput.zipIdx.any
        (fun q => decide (q.1.parent ≥ Int.ofNat q.2)) = true := by
      apply List.any_eq_true.mpr
      refine ⟨(groupInput.getD k default, k), indexed, ?_⟩
      simp only [decide_eq_true_eq]
      omega
    exact absurd hany hgroupOrder
  have parents_adm : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
    intro parent hmem
    rw [hparEq] at hmem
    obtain ⟨k, hkl, hka⟩ := List.mem_map.mp hmem
    obtain ⟨f, hf, hfeq⟩ := List.mem_iff_getElem.mp hkl
    have hkd : nodeInput.getD f default = nodeInput[f]'hf := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf,
        Option.getD_some]
    obtain ⟨-, -, hinfo⟩ := node_decode f hf
    have hkpar : (nodeInput.getD f default).parent = parent := by
      rw [hkd, hfeq]
      exact hka
    rcases hinfo with ⟨hval, -⟩ | ⟨g, hg, heq, -⟩
    · exact Or.inl (hkpar.symm.trans hval)
    · exact Or.inr ⟨g, by rw [hg_eq, groupLen]; exact hg, hkpar.symm.trans heq⟩
  have hjqAt : ∀ n, n < nodeInput.length →
      (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2 := by
    intro n hn hj
    obtain ⟨-, hjh, -⟩ := node_decode n hn
    have hij : (nodeInput.getD n default).icon.h =
        LayoutConst.architecture_junction_size.get profile := hjh hj
    have hpy' : p.pitchY ≤ pitch.y := by
      have h := c3_pitch_y_lower p nodeInput sizes
      rw [← hpitch] at h
      exact h
    have hjsle : LayoutConst.architecture_junction_size.get profile ≤
        LayoutConst.architecture_pitch_y.get profile := by
      cases profile <;> decide
    rw [hij]
    exact Int.fdiv_nonneg (by omega) (by decide)
  have hpXeq : params.pitchX = pitch.x := by rw [hparams]
  have hpYeq : params.pitchY = pitch.y := by rw [hparams]
  intro b hb hne parent hlook
  rw [hboxEq] at hb
  have hboxFind : dumpBoxes.find? (fun x => x.id == b.parent) = some parent := by
    rw [← hboxEq]
    exact hlook
  have parentRectOf : ∀ (pidx : Nat) (hlt : pidx < groups.length)
      (hfind : groups.findIdx? (fun q => q.id == b.parent) = some pidx),
      parent.rect = frames.getD pidx ⟨0, 0, 0, 0⟩ := by
    intro pidx hlt hfind
    have pmem : parent ∈ dumpBoxes := List.mem_of_find?_eq_some hboxFind
    have pid : (fun x => x.id == b.parent) parent = true :=
      List.find?_some (p := fun x => x.id == b.parent) (a := parent) hboxFind
    have hpid : parent.id = b.parent := LawfulBEq.eq_of_beq pid
    obtain ⟨mbp, hmbp, hrecp⟩ := mapM_output_origin hdumpBoxes pmem
    simp only at hrecp
    have hbeq : (groups.getD pidx default).id = b.parent := by
      have hbeq2 := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
      have hgetP : groups.getD pidx default = groups[pidx]'hlt := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
          Option.getD_some]
      rw [hgetP]
      simpa using hbeq2
    by_cases hpgroup : (mbp.role == BoxRole.group) = true
    · simp only [hpgroup, ↓reduceIte] at hrecp
      cases hfound2 : groups.findIdx? (fun g => g.id == mbp.id) with
      | none =>
          simp only [hfound2, Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at hrecp
          cases hrecp
      | some i2 =>
          simp only [hfound2, pure, Except.pure, Bind.bind, Except.bind] at hrecp
          cases hrecp
          dsimp only at hpid
          rw [hpid] at hfound2
          have hsame : i2 = pidx := Option.some.inj (hfound2.symm.trans hfind)
          subst hsame
          rfl
    · exfalso
      have hpgroupF : (mbp.role == BoxRole.group) = false := by simp [hpgroup]
      simp only [hpgroupF] at hrecp
      cases hfound2 : nodes.findIdx? (fun g => g.id == mbp.id) with
      | none =>
          simp only [hfound2, pure, Except.pure, Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at hrecp
          cases hrecp
      | some f2 =>
          simp only [hfound2, pure, Except.pure, Bind.bind, Except.bind] at hrecp
          cases hrecp
          dsimp only at hpid
          have hmemG : groups.getD pidx default ∈ groups := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
              Option.getD_some]
            exact List.getElem_mem hlt
          have hmemB : groups.getD pidx default ∈ m.boxes := by
            have hmem : groups.getD pidx default ∈
                m.boxes.filter (fun b => b.role == BoxRole.group) := by
              rw [← hgroups]; exact hmemG
            exact (List.mem_filter.mp hmem).1
          have hmbpGroup : mbp = groups.getD pidx default :=
            box_eq_of_id_eq hwf hmbp hmemB (by rw [hpid]; exact hbeq.symm)
          have hroleG : ((groups.getD pidx default).role == BoxRole.group) = true := by
            have hmem : groups.getD pidx default ∈
                m.boxes.filter (fun b => b.role == BoxRole.group) := by
              rw [← hgroups]; exact hmemG
            simpa using (List.mem_filter.mp hmem).2
          rw [hmbpGroup, hroleG] at hpgroup
          exact absurd rfl hpgroup
  obtain ⟨mb, hmb, hrec⟩ := mapM_output_origin hdumpBoxes hb
  by_cases hgroup : (mb.role == BoxRole.group) = true
  · simp only [hgroup, ↓reduceIte] at hrec
    cases hfound : groups.findIdx? (fun g => g.id == mb.id) with
    | none =>
        simp only [hfound, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hrec
        cases hrec
    | some cIdx =>
        simp only [hfound, pure, Except.pure, Bind.bind, Except.bind] at hrec
        cases hrec
        dsimp only at hne ⊢
        dsimp only at parentRectOf
        have hcLen : cIdx < groups.length :=
          (List.findIdx?_eq_some_iff_findIdx_eq.mp hfound).1
        have hmbGroup : groups.getD cIdx default = mb := by
          have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfound).2.1
          have hmemG : groups.getD cIdx default ∈ groups := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcLen,
              Option.getD_some]
            exact List.getElem_mem hcLen
          have hmemB : groups.getD cIdx default ∈ m.boxes := by
            have hmem : groups.getD cIdx default ∈
                m.boxes.filter (fun b => b.role == BoxRole.group) := by
              rw [← hgroups]; exact hmemG
            exact (List.mem_filter.mp hmem).1
          have hget : groups.getD cIdx default = groups[cIdx]'hcLen := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcLen,
              Option.getD_some]
          refine box_eq_of_id_eq hwf hmemB hmb ?_
          rw [hget]
          simpa using hbeq
        have hcInput : cIdx < input.groups.length := by rw [hg_eq]; omega
        have hinfo := group_decode cIdx (by rw [← hg_eq]; exact hcInput)
        rw [hmbGroup] at hinfo
        rcases hinfo with ⟨-, hempty⟩ | ⟨i, hi, heq, hfind⟩
        · exact absurd hempty hne
        · have hiInput : i < input.groups.length := by rw [hg_eq]; omega
          have howner : (input.groups.getD cIdx default).parent = Int.ofNat i := by
            rw [hg_eq]
            exact heq
          have hinside := Grid.Architecture.CellContracts.resolved_group_contains_child_frame
            input params frameParams (LayoutConst.architecture_bfs_cap.get profile).toNat
            ordered hpX hpY hfpad hfline cIdx i hcInput hiInput howner
          dsimp only at hinside
          rw [← hplaced, ← hresolved] at hinside
          have hchildNDlt := c3_frame_x0_lt_x1 input params frameParams
            (LayoutConst.architecture_bfs_cap.get profile).toNat ordered hpX hpY hfpad
            hfline cIdx hcInput
          rw [← hplaced, ← hresolved] at hchildNDlt
          have hchildND : ¬((resolved.frames.getD cIdx default).x0 =
              (resolved.frames.getD cIdx default).x1 ∧
            (resolved.frames.getD cIdx default).y0 =
              (resolved.frames.getD cIdx default).y1) := by
            intro hpair
            obtain ⟨h1, h2⟩ := hpair
            omega
          have hparentND : ¬((resolved.frames.getD i default).x0 =
              (resolved.frames.getD i default).x1 ∧
            (resolved.frames.getD i default).y0 =
              (resolved.frames.getD i default).y1) := by
            have hcopy := hinside
            simp only [Grid.Architecture.Span.contains] at hcopy
            intro hpair
            obtain ⟨h1, h2⟩ := hpair
            omega
          have hparentRect := parentRectOf i hi hfind
          rw [hparentRect]
          exact c3_translate_contained dx dy (resolved.frames.getD i default)
            (resolved.frames.getD cIdx default) (frames.getD i ⟨0, 0, 0, 0⟩)
            (frames.getD cIdx ⟨0, 0, 0, 0⟩) (framesTrans i hiInput)
            (framesTrans cIdx hcInput) hparentND hchildND hinside
  · have hgroupF : (mb.role == BoxRole.group) = false := by simp [hgroup]
    simp only [hgroupF] at hrec
    cases hfound : nodes.findIdx? (fun g => g.id == mb.id) with
    | none =>
        simp only [hfound, pure, Except.pure, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hrec
        cases hrec
    | some f =>
        simp only [hfound, pure, Except.pure, Bind.bind, Except.bind] at hrec
        cases hrec
        dsimp only at hne ⊢
        dsimp only at parentRectOf
        have hfLen : f < nodes.length :=
          (List.findIdx?_eq_some_iff_findIdx_eq.mp hfound).1
        have hfInput : f < nodeInput.length := by omega
        obtain ⟨hwEq, -, hinfo⟩ := node_decode f hfInput
        have hmbNode : nodes.getD f default = mb := by
          have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfound).2.1
          have hmemN : nodes.getD f default ∈ nodes := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfLen,
              Option.getD_some]
            exact List.getElem_mem hfLen
          have hmemB : nodes.getD f default ∈ m.boxes := by
            have hmem : nodes.getD f default ∈
                m.boxes.filter (fun b => b.role != BoxRole.group) := by
              rw [← hnodes]; exact hmemN
            exact (List.mem_filter.mp hmem).1
          have hget : nodes.getD f default = nodes[f]'hfLen := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfLen,
              Option.getD_some]
          refine box_eq_of_id_eq hwf hmemB hmb ?_
          rw [hget]
          simpa using hbeq
        rw [hmbNode] at hinfo
        rcases hinfo with ⟨-, hempty⟩ | ⟨i, hi, heq, hfind⟩
        · exact absurd hempty hne
        · have hiInput : i < input.groups.length := by rw [hg_eq]; omega
          have hlen' : f < (nodeInput.map (·.parent)).length := by
            simp only [List.length_map]; exact hfInput
          have hvirt : (Grid.Architecture.virtualParents input).getD f (-1) =
              (nodeInput.getD f default).parent := by
            have hstep1 : (Grid.Architecture.virtualParents input).getD f (-1) =
                (nodeInput.map (·.parent)).getD f (-1) := by
              unfold Grid.Architecture.virtualParents
              rw [hparEq]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen']
            rw [hstep1]
            have hstep2 : (nodeInput.map (·.parent)).getD f (-1) =
                (nodeInput.getD f default).parent := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getElem?_eq_getElem hfInput, Option.map_some, Option.getD_some]
            exact hstep2
          have hfVirt : f < (Grid.Architecture.virtualParents input).length := by
            have h1 : (Grid.Architecture.virtualParents input).length =
                input.parents.length +
                  ((List.range input.groups.length).filter fun (g : Nat) =>
                    !input.parents.contains (Int.ofNat g) &&
                      !input.groups.any (fun entry => entry.parent == Int.ofNat g)).length := by
              simp only [Grid.Architecture.virtualParents, List.length_append,
                List.length_map]
            rw [h1, hparLen]
            omega
          have hchain := Grid.Architecture.CellContracts.node_ancestor_frames_contain_tile
            input params frameParams (LayoutConst.architecture_bfs_cap.get profile).toNat
            ordered hpX hpY hfpad hfline parents_adm f hfVirt
          dsimp only at hchain
          rw [hvirt, heq] at hchain
          have hmemChain := c3_groupChain_self input.groups input.groups.length i
            (by omega)
          obtain ⟨-, hframeTile⟩ :=
            hchain (⟨-1, Int.ofNat i⟩ : Grid.Architecture.Unit) hmemChain
          simp only [Int.ofNat_eq_natCast, Int.toNat_natCast] at hframeTile
          rw [← hplaced, ← hresolved, hpXeq, hpYeq] at hframeTile
          have hw : 0 < (nodeInput.getD f default).icon.w := by
            rw [hwEq]
            by_cases hj : (nodeInput.getD f default).junction = true
            · rw [ite_eq_left hj]; exact hjs0
            · rw [ite_eq_right hj]; exact hiw0
          have hsourceW : (nodeInput.getD f default).icon.w ≤
              max p.pitchX (p.iconW + p.gutter) := by
            have hpw : p.iconW = iw := by rw [hp]
            have hjx : LayoutConst.architecture_junction_size.get profile ≤
                LayoutConst.architecture_pitch_x.get profile := by
              cases profile <;> decide
            rw [hwEq]
            by_cases hj : (nodeInput.getD f default).junction = true
            · rw [ite_eq_left hj, hpPitchX]
              omega
            · rw [ite_eq_right hj]
              omega
          have htileBox := c3_node_box_inside_tile p pitch sizes nodeInput groupInput
            resolved f hfInput hpitch hsourceW (hfits f hfInput) (hjqAt f hfInput) hptop
            hgut
          rw [← hgeometry] at htileBox
          have hcon : (resolved.frames.getD i default).contains
              (geometry.boxes.getD f default) :=
            c3_span_contains_trans _ _ _ hframeTile htileBox
          have hboxND : ¬((geometry.boxes.getD f default).x0 =
              (geometry.boxes.getD f default).x1 ∧
            (geometry.boxes.getD f default).y0 = (geometry.boxes.getD f default).y1) := by
            have hlt := c3_node_box_x0_lt_x1 p pitch nodeInput groupInput resolved f
              hfInput hw
            rw [← hgeometry] at hlt
            intro hpair
            obtain ⟨h1, h2⟩ := hpair
            omega
          have hframeND : ¬((resolved.frames.getD i default).x0 =
              (resolved.frames.getD i default).x1 ∧
            (resolved.frames.getD i default).y0 =
              (resolved.frames.getD i default).y1) := by
            have hcopy := hcon
            simp only [Grid.Architecture.Span.contains] at hcopy
            have hlt := c3_node_box_x0_lt_x1 p pitch nodeInput groupInput resolved f
              hfInput hw
            rw [← hgeometry] at hlt
            intro hpair
            obtain ⟨h1, h2⟩ := hpair
            omega
          have hparentRect := parentRectOf i hi hfind
          rw [hparentRect]
          exact c3_translate_contained dx dy (resolved.frames.getD i default)
            (geometry.boxes.getD f default) (frames.getD i ⟨0, 0, 0, 0⟩)
            (boxes.getD f ⟨0, 0, 0, 0⟩) (framesTrans i hiInput) (boxesTrans f hfInput)
            hframeND hboxND hcon

end Elegant.Kinds.Architecture
