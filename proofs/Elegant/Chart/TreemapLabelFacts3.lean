import Elegant.Chart.TreemapFacts
import Elegant.Chart.TreemapLabelFacts
import Elegant.Chart.TreemapLabelFacts2
import Elegant.Chart.TreemapAdapter
import Elegant.Kinds.Treemap
import ElegantGeometry.Validator

/-! Label-rectangle geometry for the treemap adapter.

First milestone: the rectangles written by `placeLeaf` are contained in the
node's tile. `leaf_body_rects_contained` is the pure geometry over the run
values; `leaf_place_side_conditions` derives the numeric side conditions from a
successful, changing `placeLeaf` call. -/

namespace Elegant.Treemap.LabelFacts3

open Elegant.Treemap
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.CanvasC1

private theorem bind_ok' {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `(p == .cell) = true` means `p = .cell`. -/
private theorem beq_cell_true {p : Profile} (h : (p == .cell) = true) : p = .cell := by
  cases p <;> simp_all

/-- `Int.fdiv` by 2 of a non-negative value is non-negative. -/
private theorem fdiv_two_nonneg {d : Int} (hd : 0 ≤ d) : 0 ≤ Int.fdiv d 2 :=
  Int.fdiv_nonneg hd (by decide)

/-- `2 * (d / 2) ≤ d` for non-negative `d` (floor division). -/
private theorem two_fdiv_le {d : Int} (hd : 0 ≤ d) : 2 * Int.fdiv d 2 ≤ d := by
  have h := Int.fdiv_mul_add_fmod d 2
  have hm : 0 ≤ Int.fmod d 2 := Int.fmod_nonneg hd (by decide)
  omega

/-- Non-negative constants of `denseConstants`: pad and spacing are non-negative
in both profiles and both density classes. -/
private theorem dense_pad_nonneg (m : Model) (nodes : List Node) :
    0 ≤ (denseConstants m nodes).pad := by
  unfold denseConstants leafConstants
  split <;> cases m.profile <;> decide

private theorem dense_spacing_nonneg (m : Model) (nodes : List Node) :
    0 ≤ (denseConstants m nodes).spacing := by
  unfold denseConstants leafConstants
  split <;> cases m.profile <;> decide

/-- In the cell profile the dense leaf constants have `minDisplay = 1`. -/
private theorem dense_minDisplay_cell (m : Model) (nodes : List Node)
    (hp : m.profile = .cell) : (denseConstants m nodes).minDisplay = 1 := by
  unfold denseConstants leafConstants
  split <;> rw [hp] <;> decide

/-- Containment from scalar bounds: the four side inequalities determine
`Rect.Contained` (the projections of the literal reduce to the components). -/
private theorem rect_contained_of_bounds {r : Rect} {x y w h : Int}
    (hx : r.x ≤ x) (hx2 : x + w ≤ r.x + r.w) (hy : r.y ≤ y) (hy2 : y + h ≤ r.y + r.h) :
    Rect.Contained r ⟨x, y, w, h⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hx
  · exact hx2
  · exact hy
  · exact hy2

/-- Scalar version for a literal outer rectangle. -/
private theorem rect_contained_of_bounds4 {rx ry rw rh x y w h : Int}
    (hx : rx ≤ x) (hx2 : x + w ≤ rx + rw) (hy : ry ≤ y) (hy2 : y + h ≤ ry + rh) :
    Rect.Contained ⟨rx, ry, rw, rh⟩ ⟨x, y, w, h⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hx
  · exact hx2
  · exact hy
  · exact hy2

/-- The pure geometry of a leaf write: given the run values pinned by the
`LeafWriteRun` equations and the placer's two guards, the written name and
value rectangles are contained in the node's tile. -/
theorem leaf_body_rects_contained (m : Model) (nodes : List Node) (n : Node)
    (before : List PlacedLabel) (j : Nat) (ns : Int) (shown : String) (nw vw : Int)
    (lh pair rows top : Int) (room showValue : Bool)
    (hfit : fit (m.profile == .cell) (((before[j]?).map (·.source.text)).getD "")
        ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad) .label ns =
      .ok (some (shown, nw)))
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (hpair : pair = 2 * lh + (denseConstants m nodes).spacing)
    (hroom : room = decide (pair ≤ (if (m.profile == .cell) then
      (tileRect n.rect).h - 2 * (denseConstants m nodes).pad else (tileRect n.rect).h)))
    (hsvdef : showValue =
      ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
        room && decide (vw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad)))
    (hrows : rows = if showValue then pair else lh)
    (htop : top = if (m.profile == .cell) then
      (tileRect n.rect).y + (denseConstants m nodes).pad +
        Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad - rows) 2
      else (tileRect n.rect).y + Int.fdiv ((tileRect n.rect).h - rows) 2)
    (hmin : ¬((tileRect n.rect).w - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay ∨
      (tileRect n.rect).h - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay))
    (hvec : (m.profile == .cell) = false → 1280 ≤ (tileRect n.rect).h) :
    Rect.Contained (tileRect n.rect)
      ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
        Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
        top, nw, lh⟩ ∧
    (showValue = true →
      Rect.Contained (tileRect n.rect)
        ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
          Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw) 2,
          top + lh + (denseConstants m nodes).spacing, vw, lh⟩) := by
  have hpad : 0 ≤ (denseConstants m nodes).pad := dense_pad_nonneg m nodes
  have hsp : 0 ≤ (denseConstants m nodes).spacing := dense_spacing_nonneg m nodes
  have hnww : nw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
    fit_width_le_avail (m.profile == .cell) _ _ _ _ _ _ hfit
  have hdx : 0 ≤ Int.fdiv ((tileRect n.rect).w -
      2 * (denseConstants m nodes).pad - nw) 2 :=
    fdiv_two_nonneg (by omega)
  have hdx2 : 2 * Int.fdiv ((tileRect n.rect).w -
      2 * (denseConstants m nodes).pad - nw) 2 ≤
      (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw :=
    two_fdiv_le (by omega)
  by_cases hcp : (m.profile == .cell) = true
  · -- Cell profile
    have hlh1 : lh = 1 := by rw [hlh]; simp only [hcp, ↓reduceIte]
    have hminD : (denseConstants m nodes).minDisplay = 1 :=
      dense_minDisplay_cell m nodes (beq_cell_true hcp)
    rw [hminD] at hmin
    by_cases hsv : showValue = true
    · have h1 : ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
          room && decide (vw ≤ (tileRect n.rect).w -
            2 * (denseConstants m nodes).pad)) = true := by
        rw [hsvdef] at hsv; exact hsv
      simp only [hlh, htop, hrows, hsv, hcp, ↓reduceIte] at *
      rw [Bool.and_eq_true] at h1
      rw [Bool.and_eq_true] at h1
      have hroomT : room = true := h1.1.2
      have hple : pair ≤ (tileRect n.rect).h - 2 * (denseConstants m nodes).pad := by
        have hd : decide (pair ≤ (tileRect n.rect).h - 2 * (denseConstants m nodes).pad) =
            true := by
          rw [← hroom]; exact hroomT
        exact of_decide_eq_true hd
      have hvwle : vw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
        of_decide_eq_true h1.2
      have hdxv : 0 ≤ Int.fdiv ((tileRect n.rect).w -
          2 * (denseConstants m nodes).pad - vw) 2 :=
        fdiv_two_nonneg (by omega)
      have hdxv2 : 2 * Int.fdiv ((tileRect n.rect).w -
          2 * (denseConstants m nodes).pad - vw) 2 ≤
          (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw :=
        two_fdiv_le (by omega)
      have hfty : 0 ≤ Int.fdiv ((tileRect n.rect).h -
          2 * (denseConstants m nodes).pad - pair) 2 :=
        fdiv_two_nonneg (by omega)
      have hfty2 : 2 * Int.fdiv ((tileRect n.rect).h -
          2 * (denseConstants m nodes).pad - pair) 2 ≤
          (tileRect n.rect).h - 2 * (denseConstants m nodes).pad - pair :=
        two_fdiv_le (by omega)
      refine ⟨rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega), ?_⟩
      · intro _
        exact rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega)
    · simp at hsv
      simp only [hlh, htop, hrows, hsv, hcp, Bool.false_eq_true, ↓reduceIte] at *
      have hfty : 0 ≤ Int.fdiv ((tileRect n.rect).h -
          2 * (denseConstants m nodes).pad - 1) 2 :=
        fdiv_two_nonneg (by omega)
      have hfty2 : 2 * Int.fdiv ((tileRect n.rect).h -
          2 * (denseConstants m nodes).pad - 1) 2 ≤
          (tileRect n.rect).h - 2 * (denseConstants m nodes).pad - 1 :=
        two_fdiv_le (by omega)
      refine ⟨rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega), ?_⟩
      · intro hsv'
        exact absurd hsv' (by decide)
  · -- Vector profile
    have hcpf : (m.profile == .cell) = false := by
      cases h3 : m.profile with
      | vector => rfl
      | cell =>
        rw [h3] at hcp
        exact absurd rfl hcp
    have hlh1280 : lh = 1280 := by
      rw [hlh]; simp only [hcpf, Bool.false_eq_true, ↓reduceIte]
    have hrh : 1280 ≤ (tileRect n.rect).h := hvec hcpf
    by_cases hsv : showValue = true
    · have h1 : ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
          room && decide (vw ≤ (tileRect n.rect).w -
            2 * (denseConstants m nodes).pad)) = true := by
        rw [hsvdef] at hsv; exact hsv
      simp only [hlh, htop, hrows, hsv, hcpf, Bool.false_eq_true, ↓reduceIte] at *
      rw [Bool.and_eq_true] at h1
      rw [Bool.and_eq_true] at h1
      have hroomT : room = true := h1.1.2
      have hple : pair ≤ (tileRect n.rect).h := by
        have hd : decide (pair ≤ (tileRect n.rect).h) = true := by
          rw [← hroom]; exact hroomT
        exact of_decide_eq_true hd
      have hvwle : vw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
        of_decide_eq_true h1.2
      have hdxv : 0 ≤ Int.fdiv ((tileRect n.rect).w -
          2 * (denseConstants m nodes).pad - vw) 2 :=
        fdiv_two_nonneg (by omega)
      have hdxv2 : 2 * Int.fdiv ((tileRect n.rect).w -
          2 * (denseConstants m nodes).pad - vw) 2 ≤
          (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw :=
        two_fdiv_le (by omega)
      have hfty : 0 ≤ Int.fdiv ((tileRect n.rect).h - pair) 2 :=
        fdiv_two_nonneg (by omega)
      have hfty2 : 2 * Int.fdiv ((tileRect n.rect).h - pair) 2 ≤
          (tileRect n.rect).h - pair :=
        two_fdiv_le (by omega)
      refine ⟨rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega), ?_⟩
      · intro _
        exact rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega)
    · simp at hsv
      simp only [hlh, htop, hrows, hsv, hcpf, Bool.false_eq_true, ↓reduceIte] at *
      have hfty : 0 ≤ Int.fdiv ((tileRect n.rect).h - 1280) 2 :=
        fdiv_two_nonneg (by omega)
      have hfty2 : 2 * Int.fdiv ((tileRect n.rect).h - 1280) 2 ≤
          (tileRect n.rect).h - 1280 :=
        two_fdiv_le (by omega)
      refine ⟨rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega), ?_⟩
      · intro hsv'
        exact absurd hsv' (by decide)

/-- The pure geometry of the title placement: the written title rectangle is
contained in the title band `⟨0, 0, c.width, c.titleBand⟩` of the canvas.
`t` is the title text, `shown` the fitted text and `w` the fitted width. -/
theorem title_rect_in_band (m : Model) (t shown : String) (w : Int)
    (h : fit (m.profile == .cell) t (constants m).width .title 16 =
      .ok (some (shown, w))) :
    Rect.Contained
      ⟨0, 0, (constants m).width, (constants m).titleBand⟩
      ⟨Int.fdiv ((constants m).width - w) 2,
        Int.fdiv ((constants m).titleBand -
          (if (m.profile == .cell) then 1 else 1536)) 2,
        w, if (m.profile == .cell) then 1 else 1536⟩ := by
  have hw : w ≤ (constants m).width := fit_width_le_avail _ _ _ _ _ _ _ h
  have hb : (if (m.profile == .cell) then 1 else 1536) ≤ (constants m).titleBand := by
    unfold constants
    cases m.profile <;> simp [LayoutConst.treemap_title_band, LayoutConst.Pair.get]
  refine rect_contained_of_bounds4 ?_ ?_ ?_ ?_
  all_goals
    have hgw : 0 ≤ (constants m).width - w := by omega
    have hgb : 0 ≤ (constants m).titleBand -
      (if (m.profile == .cell) then 1 else 1536) := by omega
    have hx : 0 ≤ Int.fdiv ((constants m).width - w) 2 := fdiv_two_nonneg hgw
    have hx2 : 2 * Int.fdiv ((constants m).width - w) 2 ≤ (constants m).width - w :=
      two_fdiv_le hgw
    have hy : 0 ≤ Int.fdiv ((constants m).titleBand -
      (if (m.profile == .cell) then 1 else 1536)) 2 := fdiv_two_nonneg hgb
    have hy2 : 2 * Int.fdiv ((constants m).titleBand -
      (if (m.profile == .cell) then 1 else 1536)) 2 ≤
      (constants m).titleBand - (if (m.profile == .cell) then 1 else 1536) :=
      two_fdiv_le hgb
    omega

/-- The two numeric side conditions of `leaf_body_rects_contained`, derived
from a successful, changing `placeLeaf` call: the display guard and the
vector height guard. -/
theorem leaf_place_side_conditions (m : Model) (nodes : List Node) (n : Node)
    (before after : List PlacedLabel)
    (h : placeLeaf m (denseConstants m nodes) n before = .ok after)
    (hne : after ≠ before) :
    ¬((tileRect n.rect).w - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay ∨
      (tileRect n.rect).h - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay) ∧
    ((m.profile == .cell) = false → 1280 ≤ (tileRect n.rect).h) := by
  refine ⟨?_, ?_⟩
  · intro hd
    exact hne (Except.ok.inj
      (h.symm.trans (placeLeaf_skip_display m (denseConstants m nodes) n before hd)))
  · intro hcpf
    have hrun := changed_leaf_write_run m (denseConstants m nodes) n before after h hne
    unfold LeafWriteRun at hrun
    obtain ⟨j, ns, shown, nw, vw, middle, hj, hns, hfit, hrest⟩ := hrun
    obtain ⟨_, _, _⟩ := hrest
    have hdisp : ¬((tileRect n.rect).w - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay ∨
      (tileRect n.rect).h - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay) := by
      intro hd
      exact hne (Except.ok.inj
        (h.symm.trans (placeLeaf_skip_display m (denseConstants m nodes) n before hd)))
    obtain ⟨_, hcases⟩ :=
      placeLeaf_vector_fit_cases m (denseConstants m nodes) n before after j hcpf hj
        hdisp h
    rcases hcases with ⟨_, heq⟩ | ⟨_, _, _, hcases2⟩
    · exact absurd heq hne
    · rcases hcases2 with ⟨_, heq⟩ | ⟨_, _, hle, _, _⟩
      · exact absurd heq hne
      · omega

/-- Scalar strict-containment from the four strict side bounds. -/
private theorem strict_inside_of_bounds {o i : Rect}
    (hx : o.x < i.x) (hx2 : i.x + i.w < o.x + o.w)
    (hy : o.y < i.y) (hy2 : i.y + i.h < o.y + o.h) :
    Rect.StrictInside o i := ⟨hx, hx2, hy, hy2⟩

/-- Scalar strict-containment for a literal inner rectangle. -/
private theorem strict_inside_of_bounds4 {o : Rect} {x y w h : Int}
    (hx : o.x < x) (hx2 : x + w < o.x + o.w) (hy : o.y < y) (hy2 : y + h < o.y + o.h) :
    Rect.StrictInside o ⟨x, y, w, h⟩ := ⟨hx, hx2, hy, hy2⟩

/-- A zero-size rectangle meets no interior. -/
private theorem meetsInterior_zero_left (r : Rect) : ¬ Rect.meetsInterior ⟨0, 0, 0, 0⟩ r := by
  unfold Rect.meetsInterior
  dsimp only
  omega

/-- A zero-size rectangle meets no interior (right variant). -/
private theorem meetsInterior_zero_right (r : Rect) : ¬ Rect.meetsInterior r ⟨0, 0, 0, 0⟩ := by
  unfold Rect.meetsInterior
  dsimp only
  omega

/-- Containment transports disjointness from the container to the contained. -/
private theorem disjoint_of_contained {l o b : Rect}
    (hlo : Rect.Contained o l) (hd : Disjoint o b) : Disjoint l b := by
  unfold Rect.Contained at hlo
  intro hm
  exact hd ⟨by omega, by omega⟩

/-- Strict ancestor containment composes with containment of the label in the
descendant tile. -/
private theorem strict_inside_of_contained {g o l : Rect}
    (hgo : Rect.StrictInside g o) (hlo : Rect.Contained o l) : Rect.StrictInside g l := by
  unfold Rect.Contained at hlo
  exact strict_inside_of_bounds4 (by omega) (by omega) (by omega) (by omega)

/-- `Int.fdiv d 2 ≥ 1` when `2 ≤ d`. -/
private theorem fdiv_two_ge_one {d : Int} (hd : 2 ≤ d) : 1 ≤ Int.fdiv d 2 := by
  have h1 : Int.fdiv d 2 * 2 + Int.fmod d 2 = d := Int.fdiv_mul_add_fmod d 2
  have h2 : 0 ≤ Int.fmod d 2 := Int.fmod_nonneg_of_pos d (by decide)
  have h3 : Int.fmod d 2 < 2 := Int.fmod_lt_of_pos d (by decide)
  omega

/-- The treemap header constants at the cell profile. -/
private theorem hborder_cell : LayoutConst.treemap_header_border.get .cell = 1 := rfl
private theorem hni_cell : LayoutConst.treemap_header_label_inset.get .cell = 2 := rfl
private theorem hvi_cell : LayoutConst.treemap_header_value_inset.get .cell = 2 := rfl
private theorem hgap_cell : LayoutConst.treemap_header_gap.get .cell = 1 := rfl

/-- The treemap header constants at the vector profile. -/
private theorem hborder_vector : LayoutConst.treemap_header_border.get .vector = 0 := rfl
private theorem hni_vector : LayoutConst.treemap_header_label_inset.get .vector = 384 := rfl
private theorem hvi_vector : LayoutConst.treemap_header_value_inset.get .vector = 640 := rfl
private theorem hgap_vector : LayoutConst.treemap_header_gap.get .vector = 640 := rfl

/-- The header band offset `top` at the cell profile. -/
private theorem htop_cell (c : Consts) (hch : c.header = 2) :
    LayoutConst.treemap_header_border.get .cell +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get .cell - 1) 2 = 1 := by
  rw [hch]
  decide

/-- The header band offset `top` at the vector profile. -/
private theorem htop_vector (c : Consts) (hch : c.header = 1600) :
    LayoutConst.treemap_header_border.get .vector +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get .vector - 1280) 2 = 160 := by
  rw [hch]
  decide

private theorem constants_header_cell (m : Model) (hp : m.profile = .cell) :
    (constants m).header = 2 := by
  unfold constants
  rw [hp]
  simp only [LayoutConst.treemap_section_header, LayoutConst.Pair.get]

private theorem constants_header_vector (m : Model) (hp : m.profile = .vector) :
    (constants m).header = 1600 := by
  unfold constants
  rw [hp]
  simp only [LayoutConst.treemap_section_header, LayoutConst.Pair.get]

private theorem dense_pad_pos (m : Model) (nodes : List Node) :
    0 < (denseConstants m nodes).pad := by
  unfold denseConstants leafConstants
  split <;> cases m.profile <;> decide

private theorem dense_spacing_cell (m : Model) (nodes : List Node)
    (hp : m.profile = .cell) : (denseConstants m nodes).spacing = 0 := by
  unfold denseConstants leafConstants
  split <;> rw [hp] <;> decide

private theorem dense_minDisplay_vector (m : Model) (nodes : List Node)
    (hp : m.profile = .vector) : 1 ≤ (denseConstants m nodes).minDisplay := by
  unfold denseConstants leafConstants
  split <;> rw [hp] <;> decide

/-- The pure geometry of a header write: given the run values pinned by the
`HeaderWriteRun` equations, the height guard, and a successful name fit, the
written name rectangle is contained in the node's tile, and so is the written
value rectangle when the value is shown. -/
theorem header_body_rects_contained (m : Model) (c : Consts) (n : Node)
    (text shown : String) (ns w vw lh top ni vi reserve avail : Int) (showValue : Bool)
    (hfit : fit (m.profile == .cell) text avail .label ns = .ok (some (shown, w)))
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (hni : ni = LayoutConst.treemap_header_label_inset.get m.profile)
    (hvi : vi = LayoutConst.treemap_header_value_inset.get m.profile)
    (hch : c.header = if (m.profile == .cell) then 2 else 1600)
    (htop : top = LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2)
    (hhgt : ¬((tileRect n.rect).h ≤ LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2 + lh))
    (havail : avail = if showValue then (tileRect n.rect).w - ni - reserve
      else (tileRect n.rect).w - 2 * ni)
    (hsvT : showValue = true)
    (hreserve : reserve = vi + vw + LayoutConst.treemap_header_gap.get m.profile)
    (hvwle : vw + vi + ni ≤ (tileRect n.rect).w)
    (hvw0 : 0 ≤ vw) :
    Rect.Contained (tileRect n.rect)
      ⟨(tileRect n.rect).x + ni, (tileRect n.rect).y + top, w, lh⟩ ∧
    Rect.Contained (tileRect n.rect)
      ⟨(tileRect n.rect).x + (tileRect n.rect).w - vi - vw, (tileRect n.rect).y + top, vw, lh⟩ := by
  have hw : w ≤ avail := fit_width_le_avail (m.profile == .cell) _ _ _ _ _ _ hfit
  rw [hsvT] at havail
  simp only [↓reduceIte] at havail
  by_cases hcp : (m.profile == .cell) = true
  · have mp : m.profile = .cell := beq_cell_true hcp
    have hlh1 : lh = 1 := by rw [hlh]; simp only [hcp, ↓reduceIte]
    have hch2 : c.header = 2 := by rw [hch]; simp only [hcp, ↓reduceIte]
    have hf0 : Int.fdiv ((2:Int) - 1 - 1) 2 = 0 := by decide
    have hni2 : ni = 2 := by rw [hni, mp, hni_cell]
    have hvi2 : vi = 2 := by rw [hvi, mp, hvi_cell]
    have hgap1 : LayoutConst.treemap_header_gap.get m.profile = 1 := by
      rw [mp, hgap_cell]
    rw [hni2] at havail hvwle ⊢
    rw [hvi2] at hreserve hvwle ⊢
    rw [hgap1] at hreserve
    rw [hreserve] at havail
    have htop1 : top = 1 := by
      rw [htop, hlh1, hch2, mp, hborder_cell, hf0]; omega
    have hhgt2 : ¬((tileRect n.rect).h ≤ 2) := by
      intro hc
      apply hhgt
      rw [hlh1, hch2, mp, hborder_cell, hf0]
      omega
    rw [htop1, hlh1] at *
    exact ⟨rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega),
      rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega)⟩
  · have hcpf : (m.profile == .cell) = false := by
      cases h3 : m.profile with
      | vector => rfl
      | cell =>
        rw [h3] at hcp
        exact absurd rfl hcp
    have mv : m.profile = .vector := by
      cases h4 : m.profile with
      | vector => rfl
      | cell =>
        rw [h4] at hcpf
        simp at hcpf
    have hlh1280 : lh = 1280 := by
      rw [hlh]; simp only [hcpf, Bool.false_eq_true, ↓reduceIte]
    have hch1600 : c.header = 1600 := by
      rw [hch]; simp only [hcpf, Bool.false_eq_true, ↓reduceIte]
    have hf160 : Int.fdiv ((1600:Int) - 0 - 1280) 2 = 160 := by decide
    have hni384 : ni = 384 := by rw [hni, mv, hni_vector]
    have hvi640 : vi = 640 := by rw [hvi, mv, hvi_vector]
    have hgap640 : LayoutConst.treemap_header_gap.get m.profile = 640 := by
      rw [mv, hgap_vector]
    rw [hni384] at havail hvwle ⊢
    rw [hvi640] at hreserve hvwle ⊢
    rw [hgap640] at hreserve
    rw [hreserve] at havail
    have htop160 : top = 160 := by
      rw [htop, hlh1280, hch1600, mv, hborder_vector, hf160]; omega
    have hhgt1440 : ¬((tileRect n.rect).h ≤ 1440) := by
      intro hc
      apply hhgt
      rw [hlh1280, hch1600, mv, hborder_vector, hf160]
      omega
    rw [htop160, hlh1280] at *
    exact ⟨rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega),
      rect_contained_of_bounds (by omega) (by omega) (by omega) (by omega)⟩

/-- The strict version of the header-write geometry: the written name rectangle
keeps a positive distance from every side of the node's tile, and so does the
written value rectangle when the value is shown. -/
theorem header_body_rects_strict (m : Model) (c : Consts) (n : Node)
    (text shown : String) (ns w vw lh top ni vi reserve avail : Int) (showValue : Bool)
    (hfit : fit (m.profile == .cell) text avail .label ns = .ok (some (shown, w)))
    (hlh : lh = if (m.profile == .cell) then 1 else 1280)
    (hni : ni = LayoutConst.treemap_header_label_inset.get m.profile)
    (hvi : vi = LayoutConst.treemap_header_value_inset.get m.profile)
    (hch : c.header = if (m.profile == .cell) then 2 else 1600)
    (htop : top = LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2)
    (hhgt : ¬((tileRect n.rect).h ≤ LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile - lh) 2 + lh))
    (havail : avail = if showValue then (tileRect n.rect).w - ni - reserve
      else (tileRect n.rect).w - 2 * ni)
    (hreserve : reserve = vi + vw + LayoutConst.treemap_header_gap.get m.profile)
    (hvwle : vw + vi + ni ≤ (tileRect n.rect).w)
    (hvw0 : 0 ≤ vw) :
    Rect.StrictInside (tileRect n.rect)
      ⟨(tileRect n.rect).x + ni, (tileRect n.rect).y + top, w, lh⟩ ∧
    (showValue = true →
      Rect.StrictInside (tileRect n.rect)
        ⟨(tileRect n.rect).x + (tileRect n.rect).w - vi - vw,
          (tileRect n.rect).y + top, vw, lh⟩) := by
  have hw : w ≤ avail := fit_width_le_avail (m.profile == .cell) _ _ _ _ _ _ hfit
  by_cases hcp : (m.profile == .cell) = true
  · have mp : m.profile = .cell := beq_cell_true hcp
    have hlh1 : lh = 1 := by rw [hlh]; simp only [hcp, ↓reduceIte]
    have hch2 : c.header = 2 := by rw [hch]; simp only [hcp, ↓reduceIte]
    have hf0 : Int.fdiv ((2:Int) - 1 - 1) 2 = 0 := by decide
    have hni2 : ni = 2 := by rw [hni, mp, hni_cell]
    have hvi2 : vi = 2 := by rw [hvi, mp, hvi_cell]
    have hgap1 : LayoutConst.treemap_header_gap.get m.profile = 1 := by
      rw [mp, hgap_cell]
    rw [hni2] at havail hvwle ⊢
    rw [hvi2] at hreserve hvwle ⊢
    rw [hgap1] at hreserve
    have htop1 : top = 1 := by
      rw [htop, hlh1, hch2, mp, hborder_cell, hf0]; omega
    have hhgt2 : ¬((tileRect n.rect).h ≤ 2) := by
      intro hc
      apply hhgt
      rw [hlh1, hch2, mp, hborder_cell, hf0]
      omega
    rw [htop1, hlh1] at *
    refine ⟨strict_inside_of_bounds4 (by omega) (by omega) (by omega) (by omega), ?_⟩
    intro hsvT
    rw [hsvT] at havail
    simp only [↓reduceIte] at havail
    rw [hreserve] at havail
    exact strict_inside_of_bounds4 (by omega) (by omega) (by omega) (by omega)
  · have hcpf : (m.profile == .cell) = false := by
      cases h3 : m.profile with
      | vector => rfl
      | cell =>
        rw [h3] at hcp
        exact absurd rfl hcp
    have mv : m.profile = .vector := by
      cases h4 : m.profile with
      | vector => rfl
      | cell =>
        rw [h4] at hcpf
        simp at hcpf
    have hlh1280 : lh = 1280 := by
      rw [hlh]; simp only [hcpf, Bool.false_eq_true, ↓reduceIte]
    have hch1600 : c.header = 1600 := by
      rw [hch]; simp only [hcpf, Bool.false_eq_true, ↓reduceIte]
    have hf160 : Int.fdiv ((1600:Int) - 0 - 1280) 2 = 160 := by decide
    have hni384 : ni = 384 := by rw [hni, mv, hni_vector]
    have hvi640 : vi = 640 := by rw [hvi, mv, hvi_vector]
    have hgap640 : LayoutConst.treemap_header_gap.get m.profile = 640 := by
      rw [mv, hgap_vector]
    rw [hni384] at havail hvwle ⊢
    rw [hvi640] at hreserve hvwle ⊢
    rw [hgap640] at hreserve
    have htop160 : top = 160 := by
      rw [htop, hlh1280, hch1600, mv, hborder_vector, hf160]; omega
    have hhgt1440 : ¬((tileRect n.rect).h ≤ 1440) := by
      intro hc
      apply hhgt
      rw [hlh1280, hch1600, mv, hborder_vector, hf160]
      omega
    rw [htop160, hlh1280] at *
    refine ⟨strict_inside_of_bounds4 (by omega) (by omega) (by omega) (by omega), ?_⟩
    intro hsvT
    rw [hsvT] at havail
    simp only [↓reduceIte] at havail
    rw [hreserve] at havail
    exact strict_inside_of_bounds4 (by omega) (by omega) (by omega) (by omega)


/-- `findIdx?` on equal source lists agrees. -/
private theorem findIdx?_sources (a b : List PlacedLabel) (id : String)
    (h : sources a = sources b) :
    a.findIdx? (fun l => l.source.id == id) = b.findIdx? (fun l => l.source.id == id) := by
  have e1 : (sources a).findIdx? (fun x : ModelLabel => x.id == id) =
      a.findIdx? (fun l => l.source.id == id) := List.findIdx?_map
  have e2 : (sources b).findIdx? (fun x : ModelLabel => x.id == id) =
      b.findIdx? (fun l => l.source.id == id) := List.findIdx?_map
  rw [← e1, ← e2]
  exact congrArg (fun l : List ModelLabel => l.findIdx? (fun x => x.id == id)) h

/-- Lookup and text extraction on equal source lists agree. -/
private theorem text_sources (a b : List PlacedLabel) (j : Nat)
    (h : sources a = sources b) :
    ((a[j]?).map (·.source.text)).getD "" =
      ((b[j]?).map (·.source.text)).getD "" := by
  have hj := congrArg (fun l : List ModelLabel => l[j]?) h
  simp only [sources, List.getElem?_map] at hj
  cases ha : a[j]? with
  | none =>
    rw [ha] at hj
    simp only [Option.map_none] at hj
    cases hb : b[j]? with
    | none => rfl
    | some lb =>
      rw [hb, Option.map_some] at hj
      exact absurd hj (by simp)
  | some la =>
    rw [ha] at hj
    simp only [Option.map_some] at hj
    cases hb : b[j]? with
    | none =>
      rw [hb, Option.map_none] at hj
      exact absurd hj (by simp)
    | some lb =>
      rw [hb, Option.map_some] at hj
      have hsrc : la.source = lb.source := Option.some.inj hj
      rw [Option.map_some, Option.map_some, hsrc]

/-- The indexed text lookup after a `findIdx?` on equal source lists agrees. -/
private theorem lookupText_sources (a b : List PlacedLabel) (id : String)
    (h : sources a = sources b) :
    (((a.findIdx? (fun l => l.source.id == id)).bind fun k => a[k]?).map
      (·.source.text)).getD "" =
      (((b.findIdx? (fun l => l.source.id == id)).bind fun k => b[k]?).map
        (·.source.text)).getD "" := by
  have hf := findIdx?_sources a b id h
  rw [hf]
  cases b.findIdx? (fun l => l.source.id == id) with
  | none => rfl
  | some k =>
    rw [Option.bind_some, Option.bind_some]
    exact text_sources a b k h

/-- A box whose id occurs in a dump's ancestor list has a box carrying it as
parent. -/
private theorem exists_box_parent_of_mem_ancestors (d : LayoutDump) :
    ∀ (fuel : Nat) (s x : String), x ∈ LayoutDump.ancestors.go d fuel s →
      ∃ c ∈ d.boxes, c.parent = x := by
  intro fuel
  induction fuel with
  | zero => intro s x hx; cases hx
  | succ fuel ih =>
    intro s x hx
    have hgo : LayoutDump.ancestors.go d (fuel + 1) s =
        match d.box? s with
        | none => []
        | some b => if b.parent = "" then []
                    else b.parent :: LayoutDump.ancestors.go d fuel b.parent := rfl
    rw [hgo] at hx
    cases hs : d.box? s with
    | none => rw [hs] at hx; cases hx
    | some b =>
      rw [hs] at hx
      simp only at hx
      split at hx
      · cases hx
      · rename_i hpar
        rcases List.mem_cons.mp hx with heq | hx
        · refine ⟨b, ?_, heq.symm⟩
          unfold LayoutDump.box? at hs
          exact List.mem_of_find?_eq_some hs
        · exact ih b.parent x hx


/-- The leaf-group flush guard holds on the tiled node list of a successful
layout. -/
theorem layout_guard_holds (m : Model) (scene : Scene)
    (h : Elegant.Treemap.layout m = .ok scene) :
    ∃ nodes, tileNodes (constants m) (seededNodes m) = .ok nodes ∧
      leafGroupLabelVerticalStrict m nodes = true := by
  unfold Elegant.Treemap.layout at h
  dsimp only at h
  obtain ⟨nodes, hn, h⟩ := bind_ok' h
  split at h
  · cases h
  · rename_i hg
    refine ⟨nodes, hn, ?_⟩
    cases hb : leafGroupLabelVerticalStrict m nodes with
    | true => rfl
    | false =>
      exfalso
      rw [hb] at hg
      simp at hg

/-- A `findIdx?` hit carries its element and predicate. -/
private theorem findIdx?_eq_some_lookup {α : Type} {l : List α} (p : α → Bool)
    (j : Nat) (h : l.findIdx? p = some j) :
    ∃ x : α, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none =>
          rw [hv] at h
          simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

/-- A changing `placeLeaf` write on a childless group node places a label whose
rectangle is strictly inside the node's tile: the cell profile insets through
`pad`, and the vector profile is kept off the tile's top and bottom edges by
the leaf-group flush guard. -/
theorem leaf_group_write_strict_rects
    (m : Model) (nodes : List Node) (n : Node) (before after : List PlacedLabel)
    (i : Nat)
    (hguard : leafGroupLabelVerticalStrict m nodes = true)
    (hmem : n ∈ nodes)
    (hid : (n.source.id == "root") = false)
    (hgroup : n.source.role = .group)
    (hleaf : (children nodes n.source.id).isEmpty = true)
    (hs : sources before = sources (initialLabels m))
    (h : placeLeaf m (denseConstants m nodes) n before = .ok after)
    (hne : after ≠ before)
    (hchange : after[i]? ≠ before[i]?) :
    (∃ l : PlacedLabel, after[i]? = some l ∧ l.source.id = n.source.id ++ ".name" ∧
        Rect.StrictInside (tileRect n.rect) l.rect) ∨
    (∃ l : PlacedLabel, after[i]? = some l ∧ l.source.id = n.source.id ++ ".value" ∧
        Rect.StrictInside (tileRect n.rect) l.rect) := by
  have hpad : 0 < (denseConstants m nodes).pad := dense_pad_pos m nodes
  have hsp : 0 ≤ (denseConstants m nodes).spacing := dense_spacing_nonneg m nodes
  have hcopy := h
  unfold placeLeaf at h
  simp only [labelIndex_eq_findIdx, sourceText_eq_lookup] at h
  cases hj : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
  | none =>
    rw [hj] at h
    simp only [pure, Except.pure] at h
    exact absurd (Except.ok.inj h.symm) hne
  | some j =>
    obtain ⟨nl, hnl, hpnl⟩ :=
      findIdx?_eq_some_lookup (α := PlacedLabel)
        (fun l => l.source.id == n.source.id ++ ".name") j hj
    have hidnl : nl.source.id = n.source.id ++ ".name" := beq_iff_eq.mp hpnl
    rw [hj] at h
    by_cases hd : ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay ∨
      (tileRect n.rect).h - 2 * (denseConstants m nodes).pad <
        (denseConstants m nodes).minDisplay)
    · simp only [Bool.or_eq_true, decide_eq_true_eq, hd, ↓reduceIte,
        pure, Except.pure] at h
      exact absurd (Except.ok.inj h.symm) hne
    · simp only [Bool.or_eq_true, decide_eq_true_eq, hd, ↓reduceIte,
        pure, Except.pure] at h
      by_cases hcell : (m.profile == .cell) = true
      · -- cell profile: ns = 0, lh = 1
        rw [hcell] at h
        simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true] at h
        obtain ⟨ns, hns, h⟩ := bind_ok' h
        simp only [Except.ok.injEq] at hns
        subst hns
        obtain ⟨fitted, hf, h⟩ := bind_ok' h
        cases fitted with
        | none =>
          simp only at h
          exact absurd (Except.ok.inj h.symm) hne
        | some pp =>
          obtain ⟨shown, nw⟩ := pp
          simp only [] at h
          have hnwa : nw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
            fit_width_le_avail true _ _ _ _ _ _ hf
          have hm1 : (denseConstants m nodes).minDisplay = 1 :=
            dense_minDisplay_cell m nodes (beq_cell_true hcell)
          rw [hm1] at hd
          have hawge : (tileRect n.rect).w - 2 * (denseConstants m nodes).pad ≥ 1 := by omega
          have hahge : (tileRect n.rect).h - 2 * (denseConstants m nodes).pad ≥ 1 := by omega
          have hfx1 : 0 ≤ Int.fdiv ((tileRect n.rect).w -
              2 * (denseConstants m nodes).pad - nw) 2 := fdiv_two_nonneg (by omega)
          have hfx2 : 2 * Int.fdiv ((tileRect n.rect).w -
              2 * (denseConstants m nodes).pad - nw) 2 ≤
              (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw :=
            two_fdiv_le (by omega)
          have hnamestrict : ∀ yco : Int, (tileRect n.rect).y < yco →
              yco + 1 < (tileRect n.rect).y + (tileRect n.rect).h →
              Rect.StrictInside (tileRect n.rect)
                ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                  yco, nw, 1⟩ := by
            intro yco hy1 hy2
            exact strict_inside_of_bounds4
              (show (tileRect n.rect).x < (tileRect n.rect).x +
                (denseConstants m nodes).pad +
                Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2 from by
                  have h := hfx1; have h := hpad; omega)
              (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2 + nw <
                (tileRect n.rect).x + (tileRect n.rect).w from by
                  have h := hfx1; have h := hfx2; have h := hnwa; omega)
              hy1 hy2
          have hvalstrict : ∀ w yco : Int,
              w ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad →
              (tileRect n.rect).y < yco →
              yco + 1 < (tileRect n.rect).y + (tileRect n.rect).h →
              Rect.StrictInside (tileRect n.rect)
                ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - w) 2,
                  yco, w, 1⟩ := by
            intro w yco hw hy1 hy2
            have hfx1 : 0 ≤ Int.fdiv ((tileRect n.rect).w -
                2 * (denseConstants m nodes).pad - w) 2 := fdiv_two_nonneg (by omega)
            have hfx2 : 2 * Int.fdiv ((tileRect n.rect).w -
                2 * (denseConstants m nodes).pad - w) 2 ≤
                (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - w :=
              two_fdiv_le (by omega)
            exact strict_inside_of_bounds4
              (show (tileRect n.rect).x < (tileRect n.rect).x +
                (denseConstants m nodes).pad +
                Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - w) 2 from by
                  have h := hfx1; have h := hpad; omega)
              (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - w) 2 + w <
                (tileRect n.rect).x + (tileRect n.rect).w from by
                  have h := hfx1; have h := hfx2; have h := hw; omega)
              hy1 hy2
          -- navigation over the room / showValue / value-match structure
          have hvallookup : ∀ k : Nat,
              before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") = some k →
              ∃ vl : PlacedLabel, before[k]? = some vl ∧
                vl.source.id = n.source.id ++ ".value" := by
            intro k hk
            obtain ⟨vl, hvl, hvid⟩ := findIdx?_eq_some_lookup (α := PlacedLabel)
              (fun l => l.source.id == n.source.id ++ ".value") k hk
            exact ⟨vl, hvl, beq_iff_eq.mp hvid⟩
          have hnamefinish :
              (before.modify j (fun l => putLabel l shown
                ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                  (tileRect n.rect).y + (denseConstants m nodes).pad +
                    Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad - 1) 2,
                  nw, 1⟩ 0)) = after →
              (∃ l : PlacedLabel, after[i]? = some l ∧
                  l.source.id = n.source.id ++ ".name" ∧
                  Rect.StrictInside (tileRect n.rect) l.rect) ∨
              (∃ l : PlacedLabel, after[i]? = some l ∧
                  l.source.id = n.source.id ++ ".value" ∧
                  Rect.StrictInside (tileRect n.rect) l.rect) := by
            intro hh
            by_cases hij : j = i
            · subst hij
              refine Or.inl ⟨putLabel nl shown
                ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                  (tileRect n.rect).y + (denseConstants m nodes).pad +
                    Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad - 1) 2,
                  nw, 1⟩ 0, ?_, hidnl, ?_⟩
              · rw [← hh, modified_label_at_index, hnl]
                simp only [Option.map_some, ite_true]
              · have hft1 : 0 ≤ Int.fdiv ((tileRect n.rect).h -
                  2 * (denseConstants m nodes).pad - 1) 2 := fdiv_two_nonneg (by omega)
                have hft2 : 2 * Int.fdiv ((tileRect n.rect).h -
                    2 * (denseConstants m nodes).pad - 1) 2 ≤
                    (tileRect n.rect).h - 2 * (denseConstants m nodes).pad - 1 :=
                  two_fdiv_le (by omega)
                have ht1 : (tileRect n.rect).y < (tileRect n.rect).y +
                    (denseConstants m nodes).pad +
                    Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad - 1) 2 := by
                  have h := hpad; have h := hft1; omega
                have ht2 : (tileRect n.rect).y + (denseConstants m nodes).pad +
                    Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad - 1) 2 + 1 <
                    (tileRect n.rect).y + (tileRect n.rect).h := by
                  have h := hft1; have h := hft2; have h := hpad; have h := hahge; omega
                exact hnamestrict _ ht1 ht2
            · exfalso
              rw [← hh] at hchange
              rw [modified_label_at_index] at hchange
              cases hbi : before[i]? with
              | none => rw [hbi, Option.map_none] at hchange; exact hchange rfl
              | some _ =>
                rw [hbi] at hchange
                simp only [Option.map_some, ite_eq_right hij] at hchange
                exact hchange rfl
          cases hval : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
          | none =>
            rw [hval] at h
            simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              bind, Except.bind, Except.ok.injEq] at h
            exact hnamefinish h
          | some k =>
            rw [hval] at h
            split at h
            · rename_i hroom
              obtain ⟨vw, -, h⟩ := bind_ok' h
              have hpairle : 2 * 1 + (denseConstants m nodes).spacing ≤
                  (tileRect n.rect).h - 2 * (denseConstants m nodes).pad := by
                rw [Bool.and_eq_true] at hroom
                exact of_decide_eq_true hroom.2
              have hft1 : 0 ≤ Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                  (2 * 1 + (denseConstants m nodes).spacing)) 2 := fdiv_two_nonneg (by omega)
              have hft2 : 2 * Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                  (2 * 1 + (denseConstants m nodes).spacing)) 2 ≤
                  (tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                    (2 * 1 + (denseConstants m nodes).spacing) :=
                two_fdiv_le (by omega)
              have htname : (tileRect n.rect).y < (tileRect n.rect).y +
                  (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                    (2 * 1 + (denseConstants m nodes).spacing)) 2 := by
                have h := hpad; have h := hft1; omega
              have htname2 : (tileRect n.rect).y + (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                    (2 * 1 + (denseConstants m nodes).spacing)) 2 + 1 <
                  (tileRect n.rect).y + (tileRect n.rect).h := by
                have h := hft1; have h := hft2; have h := hpad; have h := hsp;
                  have h := hpairle; have h := hahge; omega
              split at h
              · rename_i hvwle
                have hvwle' : vw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad := by
                  rw [Bool.and_eq_true] at hvwle
                  exact of_decide_eq_true hvwle.2
                obtain ⟨vl, hvl, hvid⟩ := hvallookup k hval
                dsimp only at h
                simp only [Except.ok.injEq] at h
                by_cases hij : j = i
                · subst hij
                  have hkj : ¬ (k = j) := by
                    intro he
                    rw [he, hnl, Option.some.injEq] at hvl
                    exact absurd ((String.append_right_inj n.source.id).mp
                      (show n.source.id ++ ".value" = n.source.id ++ ".name" by
                        rw [← hvid, ← hidnl, ← hvl])) (by decide)
                  refine Or.inl ⟨putLabel nl shown
                    ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                      Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                      (tileRect n.rect).y + (denseConstants m nodes).pad +
                        Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                          (2 * 1 + (denseConstants m nodes).spacing)) 2, nw, 1⟩ 0,
                    ?_, hidnl, ?_⟩
                  · rw [← h, modified_label_at_index, modified_label_at_index, hnl]
                    simp only [Option.map_some, ite_eq_right hkj, ite_true]
                  · exact hnamestrict _ htname htname2
                · by_cases hik : k = i
                  · subst hik
                    refine Or.inr ⟨putLabel vl vl.source.text
                      ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                        Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw) 2,
                        (tileRect n.rect).y + (denseConstants m nodes).pad +
                          Int.fdiv ((tileRect n.rect).h - 2 * (denseConstants m nodes).pad -
                            (2 * 1 + (denseConstants m nodes).spacing)) 2 + 1 +
                          (denseConstants m nodes).spacing, vw, 1⟩ 0, ?_, hvid, ?_⟩
                    · have hjk : ¬(j = k) := hij
                      rw [← h, modified_label_at_index, modified_label_at_index, hvl]
                      simp only [Option.map_some, ite_eq_right hjk, ite_true]
                    · refine hvalstrict vw _ hvwle' ?_ ?_
                      · have h := hpad; have h := hsp; have h := hft1; omega
                      · have h := hft1; have h := hft2; have h := hpad; have h := hsp;
                          have h := hpairle; have h := hahge; omega
                  · exfalso
                    rw [← h] at hchange
                    rw [modified_label_at_index, modified_label_at_index] at hchange
                    cases hbi : before[i]? with
                    | none => rw [hbi, Option.map_none] at hchange; exact hchange rfl
                    | some _ =>
                      rw [hbi] at hchange
                      simp only [Option.map_some, ite_eq_right hik, ite_eq_right hij] at hchange
                      exact hchange rfl
              · simp only [Except.ok.injEq] at h
                exact hnamefinish h
            · rename_i hroomf
              simp only [hroomf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind,
                Except.bind, Except.ok.injEq] at h
              exact hnamefinish h
      · -- vector profile: navigate the run and pull the vertical slack from the
        -- leaf-group flush guard
        have hcpf : (m.profile == .cell) = false := by
          cases h5 : m.profile with
          | vector => rfl
          | cell => simp_all
        rw [hcpf] at h
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and] at h
        obtain ⟨ns, hns, h⟩ := bind_ok' h
        obtain ⟨fitted, hfit, h⟩ := bind_ok' h
        cases fitted with
        | none =>
          simp only at h
          exact absurd (Except.ok.inj h.symm) hne
        | some pp =>
          obtain ⟨shown, nw⟩ := pp
          simp only [] at h
          have hnwa : nw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
            fit_width_le_avail false _ _ _ _ _ _ hfit
          -- reduce `cell`/`lh` in `h`; the height `if` needs a derived guard,
          -- since `decide` of an atom cannot `reduceIte`: prove it false from
          -- the guard's skip-display consequence (output unchanged vs `hne`)
          have hshort'' : decide (1280 > (tileRect n.rect).h) = false := by
            by_cases hcon : decide (1280 > (tileRect n.rect).h) = true
            · rw [hcon] at h
              simp only [↓reduceIte] at h
              exact (hne (Except.ok.inj h).symm).elim
            · simpa using hcon
          simp only [hshort'', Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · rename_i hcond
            -- hcond : value.isSome && room = true (the inner if condition)
            -- h is now `(width ... >>= fun vw => ...) = .ok after` or similar
            obtain ⟨vw, hvw, h⟩ := bind_ok' h
            -- continue with the rest...
            -- align the constant forms on the equations used against the guard
            simp only [denseConstants] at hns hfit hvw hd
            -- extract the per-node guard conclusion
            unfold leafGroupLabelVerticalStrict at hguard
            rw [hcpf] at hguard
            simp only [Bool.false_eq_true, ↓reduceIte, labelIndex_eq_findIdx] at hguard
            have hnode := List.all_eq_true.mp hguard n hmem
            have hgr : (BoxRole.group != BoxRole.group) = false := by simp
            simp only [hid, hgroup, hgr, hleaf, Bool.not_true] at hnode
            have hf3 : decide (1280 > (tileRect n.rect).h) = false := hshort''
            simp only [hf3, Bool.false_or] at hnode
            -- transfer the guard's lookups to `before`
            have hji : (initialLabels m).findIdx? (fun l => l.source.id == n.source.id ++ ".name")
                = some j := (findIdx?_sources before (initialLabels m) _ hs).symm.trans hj
            simp only [hji] at hnode
            rw [sourceText_eq_lookup] at hnode
            dsimp only [Option.bind_some] at hnode
            have htx := text_sources (initialLabels m) before j hs.symm
            simp only [htx] at hnode
            simp only [Option.bind_some] at hns hfit hvw
            simp only [hns] at hnode
            simp only [hfit] at hnode
            simp only [sourceText_eq_lookup] at hnode
            have hlt := lookupText_sources (initialLabels m) before (n.source.id ++ ".value") hs.symm
            have hvi : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
                = (initialLabels m).findIdx? (fun l => l.source.id == n.source.id ++ ".value") :=
              findIdx?_sources before (initialLabels m) _ hs
            simp only [hlt] at hnode
            simp only [← hvi] at hnode
            simp only [hvw] at hnode
            have hcond2 : ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
                decide (2 * 1280 + (leafConstants m.profile
                    ((nodes.countP (fun n => n.source.id != "root" &&
                        (children nodes n.source.id).isEmpty)) >
                      (LayoutConst.treemap_dense_leaves.get m.profile).toNat)).spacing ≤
                  (tileRect n.rect).h)) = true := hcond
            simp only [hcond2, Bool.true_and, ↓reduceIte] at hnode
            -- hnode : decide(aw<min) || decide(ah<min) || false ||
            --   decide (2 ≤ r.h - if ((room && decide (vw ≤ aw)) = true) then 2*1280+spacing else 1280)
            split at hnode
            · rename_i hSvT
              have hpair : 2 ≤ (tileRect n.rect).h -
                  (2 * 1280 + (denseConstants m nodes).spacing) := by
                simp only [Bool.or_assoc, Bool.or_eq_true] at hnode
                rcases hnode with h | h | h | h
                · exact absurd (of_decide_eq_true h) (fun hc => hd (Or.inl hc))
                · exact absurd (of_decide_eq_true h) (fun hc => hd (Or.inr hc))
                · simp at h
                · exact of_decide_eq_true h
              have hvwle : vw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
                of_decide_eq_true hSvT
              split at h
              · -- value written too
                rename_i _
                cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
                | none =>
                  simp only [hv] at h
                  simp only [Except.ok.injEq] at h
                  -- only the name label was written
                  by_cases hij : j = i
                  · subst hij
                    refine Or.inl ⟨putLabel nl shown
                      ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                        Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                        (tileRect n.rect).y +
                          Int.fdiv ((tileRect n.rect).h -
                            (2 * 1280 + (denseConstants m nodes).spacing)) 2,
                        nw, 1280⟩ ns, ?_, hidnl, ?_⟩
                    · rw [← h, modified_label_at_index, hnl]
                      simp only [Option.map_some, ite_true]
                    · exact strict_inside_of_bounds4
                        (show (tileRect n.rect).x < (tileRect n.rect).x +
                          (denseConstants m nodes).pad +
                          Int.fdiv ((tileRect n.rect).w -
                            2 * (denseConstants m nodes).pad - nw) 2 from by
                            have := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                            have := hpad
                            omega)
                        (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                          Int.fdiv ((tileRect n.rect).w -
                            2 * (denseConstants m nodes).pad - nw) 2 + nw <
                          (tileRect n.rect).x + (tileRect n.rect).w from by
                            have h1 := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                            have h2 := two_fdiv_le (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                            have := hpad
                            have := fit_width_le_avail false _ _ _ _ _ _ hfit
                            omega)
                        (show (tileRect n.rect).y < (tileRect n.rect).y +
                          Int.fdiv ((tileRect n.rect).h -
                            (2 * 1280 + (denseConstants m nodes).spacing)) 2 from by
                            have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                            omega)
                        (show (tileRect n.rect).y +
                          Int.fdiv ((tileRect n.rect).h -
                            (2 * 1280 + (denseConstants m nodes).spacing)) 2 + 1280 <
                          (tileRect n.rect).y + (tileRect n.rect).h from by
                            have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                            have h2 := two_fdiv_le (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                            have := hpad
                            have := hsp
                            omega)
                  · exfalso
                    rw [← h] at hchange
                    rw [modified_label_at_index] at hchange
                    cases hbi : before[i]? with
                    | none => rw [hbi, Option.map_none] at hchange; exact hchange rfl
                    | some _ =>
                      rw [hbi] at hchange
                      simp only [Option.map_some, ite_eq_right hij] at hchange
                      exact hchange rfl
                | some k =>
                  simp only [hv] at h
                  simp only [Except.ok.injEq] at h
                  obtain ⟨vl, hvl, hvid⟩ :=
                    findIdx?_eq_some_lookup (α := PlacedLabel)
                      (fun l => l.source.id == n.source.id ++ ".value") k hv
                  have hvid' : vl.source.id = n.source.id ++ ".value" := beq_iff_eq.mp hvid
                  have hkj : ¬ (k = j) := by
                    intro he
                    rw [he, hnl, Option.some.injEq] at hvl
                    exact absurd ((String.append_right_inj n.source.id).mp
                      (show n.source.id ++ ".value" = n.source.id ++ ".name" by
                        rw [← hvid', ← hidnl, ← hvl])) (by decide)
                  by_cases hij : j = i
                  · subst hij
                    refine Or.inl ⟨putLabel nl shown
                      ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                        Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                        (tileRect n.rect).y +
                          Int.fdiv ((tileRect n.rect).h -
                            (2 * 1280 + (denseConstants m nodes).spacing)) 2,
                        nw, 1280⟩ ns, ?_, hidnl, ?_⟩
                    · rw [← h, modified_label_at_index, modified_label_at_index, hnl]
                      simp only [Option.map_some, ite_eq_right hkj, ite_true]
                    · exact strict_inside_of_bounds4
                        (show (tileRect n.rect).x < (tileRect n.rect).x +
                          (denseConstants m nodes).pad +
                          Int.fdiv ((tileRect n.rect).w -
                            2 * (denseConstants m nodes).pad - nw) 2 from by
                            have := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega); have := hpad; omega)
                        (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                          Int.fdiv ((tileRect n.rect).w -
                            2 * (denseConstants m nodes).pad - nw) 2 + nw <
                          (tileRect n.rect).x + (tileRect n.rect).w from by
                            have h1 := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                            have h2 := two_fdiv_le (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                            have := hpad
                            have := fit_width_le_avail false _ _ _ _ _ _ hfit
                            omega)
                        (show (tileRect n.rect).y < (tileRect n.rect).y +
                          Int.fdiv ((tileRect n.rect).h -
                            (2 * 1280 + (denseConstants m nodes).spacing)) 2 from by
                            have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                            omega)
                        (show (tileRect n.rect).y +
                          Int.fdiv ((tileRect n.rect).h -
                            (2 * 1280 + (denseConstants m nodes).spacing)) 2 + 1280 <
                          (tileRect n.rect).y + (tileRect n.rect).h from by
                            have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                            have h2 := two_fdiv_le (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                            have := hpad
                            have := hsp
                            omega)
                  · by_cases hik : k = i
                    · subst hik
                      refine Or.inr ⟨putLabel vl vl.source.text
                        ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                          Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw) 2,
                          (tileRect n.rect).y +
                            Int.fdiv ((tileRect n.rect).h -
                              (2 * 1280 + (denseConstants m nodes).spacing)) 2 + 1280 +
                            (denseConstants m nodes).spacing, vw, 1280⟩
                        (max ((denseConstants m nodes).valueMin.fdiv 64)
                          (min ((denseConstants m nodes).valueSize.fdiv 64)
                            (roundDiv (ns * LayoutConst.treemap_value_scale_percent.get m.profile)
                              100))), ?_, hvid', ?_⟩
                      · rw [← h, modified_label_at_index, modified_label_at_index, hvl]
                        simp only [Option.map_some, ite_eq_right hij, ite_true]
                      · exact strict_inside_of_bounds4
                          (show (tileRect n.rect).x < (tileRect n.rect).x +
                            (denseConstants m nodes).pad +
                            Int.fdiv ((tileRect n.rect).w -
                              2 * (denseConstants m nodes).pad - vw) 2 from by
                              have := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw) (by omega); have := hpad; omega)
                          (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                            Int.fdiv ((tileRect n.rect).w -
                              2 * (denseConstants m nodes).pad - vw) 2 + vw <
                            (tileRect n.rect).x + (tileRect n.rect).w from by
                              have h1 := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw) (by omega)
                              have h2 := two_fdiv_le (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - vw) (by omega)
                              have := hpad
                              have := hvwle
                              omega)
                          (show (tileRect n.rect).y < (tileRect n.rect).y +
                            Int.fdiv ((tileRect n.rect).h -
                              (2 * 1280 + (denseConstants m nodes).spacing)) 2 + 1280 +
                            (denseConstants m nodes).spacing from by
                              have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                              have := hpad
                              have := hsp
                              omega)
                          (show (tileRect n.rect).y +
                            Int.fdiv ((tileRect n.rect).h -
                              (2 * 1280 + (denseConstants m nodes).spacing)) 2 + 1280 +
                            (denseConstants m nodes).spacing + 1280 <
                            (tileRect n.rect).y + (tileRect n.rect).h from by
                              have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                              have h2 := two_fdiv_le (d := (tileRect n.rect).h - (2 * 1280 + (denseConstants m nodes).spacing)) (by omega)
                              have := hpad
                              have := hsp
                              omega)
                    · exfalso
                      rw [← h] at hchange
                      rw [modified_label_at_index, modified_label_at_index] at hchange
                      cases hbi : before[i]? with
                      | none => rw [hbi, Option.map_none] at hchange; exact hchange rfl
                      | some _ =>
                        rw [hbi] at hchange
                        simp only [Option.map_some, ite_eq_right hik, ite_eq_right hij] at hchange
                        exact hchange rfl
              · rename_i hSvT2
                exfalso
                exact hSvT2 (Bool.and_eq_true_iff.mpr ⟨hcond, hSvT⟩)
            · rename_i hSvF
              have hb : 2 ≤ (tileRect n.rect).h - 1280 := by
                simp only [Bool.or_assoc, Bool.or_eq_true] at hnode
                rcases hnode with h | h | h | h
                · exact absurd (of_decide_eq_true h) (fun hc => hd (Or.inl hc))
                · exact absurd (of_decide_eq_true h) (fun hc => hd (Or.inr hc))
                · simp at h
                · exact of_decide_eq_true h
              split at h
              · rename_i hSvT2
                exfalso
                rw [hcond] at hSvT2
                exact hSvF (Bool.and_eq_true_iff.mp hSvT2).2
              · -- only the name label was written
                simp only [Except.ok.injEq] at h
                by_cases hij : j = i
                · subst hij
                  refine Or.inl ⟨putLabel nl shown
                    ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                      Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                      (tileRect n.rect).y +
                        Int.fdiv ((tileRect n.rect).h - 1280) 2,
                      nw, 1280⟩ ns, ?_, hidnl, ?_⟩
                  · rw [← h, modified_label_at_index, hnl]
                    simp only [Option.map_some, ite_true]
                  · exact strict_inside_of_bounds4
                      (show (tileRect n.rect).x < (tileRect n.rect).x +
                        (denseConstants m nodes).pad +
                        Int.fdiv ((tileRect n.rect).w -
                          2 * (denseConstants m nodes).pad - nw) 2 from by
                          have := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega); have := hpad; omega)
                      (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                        Int.fdiv ((tileRect n.rect).w -
                          2 * (denseConstants m nodes).pad - nw) 2 + nw <
                        (tileRect n.rect).x + (tileRect n.rect).w from by
                          have h1 := fdiv_two_nonneg (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                          have h2 := two_fdiv_le (d := (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) (by omega)
                          have := hpad
                          have := fit_width_le_avail false _ _ _ _ _ _ hfit
                          omega)
                      (show (tileRect n.rect).y < (tileRect n.rect).y +
                        Int.fdiv ((tileRect n.rect).h - 1280) 2 from by
                          have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - 1280) (by omega)
                          omega)
                      (show (tileRect n.rect).y +
                        Int.fdiv ((tileRect n.rect).h - 1280) 2 + 1280 <
                        (tileRect n.rect).y + (tileRect n.rect).h from by
                          have h1 := fdiv_two_ge_one (d := (tileRect n.rect).h - 1280) (by omega)
                          have h2 := two_fdiv_le (d := (tileRect n.rect).h - 1280) (by omega)
                          have := hpad
                          omega)
                · exfalso
                  rw [← h] at hchange
                  rw [modified_label_at_index] at hchange
                  cases hbi : before[i]? with
                  | none => rw [hbi, Option.map_none] at hchange; exact hchange rfl
                  | some _ =>
                    rw [hbi] at hchange
                    simp only [Option.map_some, ite_eq_right hij] at hchange
                    exact hchange rfl
          · -- `value.isSome && room` is false: `vw` is bound through `pure 0`,
            -- so `showValue` collapses to `false` and only the name label is written
            rename_i hcond
            have hx : ((before.findIdx? (fun l => l.source.id ==
                    n.source.id ++ ".value")).isSome &&
                  decide (2 * 1280 + (denseConstants m nodes).spacing ≤
                    (tileRect n.rect).h)) = false :=
              Bool.of_not_eq_true hcond
            have hxl :
                ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
                    decide (2 * 1280 + (leafConstants m.profile
                        ((nodes.countP (fun n => n.source.id != "root" &&
                            (children nodes n.source.id).isEmpty)) >
                          (LayoutConst.treemap_dense_leaves.get m.profile).toNat)).spacing ≤
                      (tileRect n.rect).h)) = false := hx
            -- per-node guard conclusion, independent of the `vw` computation
            unfold leafGroupLabelVerticalStrict at hguard
            rw [hcpf] at hguard
            simp only [Bool.false_eq_true, ↓reduceIte, labelIndex_eq_findIdx] at hguard
            have hnode := List.all_eq_true.mp hguard n hmem
            have hgr : (BoxRole.group != BoxRole.group) = false := by simp
            simp only [hid, hgroup, hgr, hleaf, Bool.not_true] at hnode
            have hf3 : decide (1280 > (tileRect n.rect).h) = false := hshort''
            simp only [hf3, Bool.false_or] at hnode
            have hji : (initialLabels m).findIdx? (fun l => l.source.id == n.source.id ++ ".name")
                = some j := (findIdx?_sources before (initialLabels m) _ hs).symm.trans hj
            simp only [hji] at hnode
            rw [sourceText_eq_lookup] at hnode
            dsimp only [Option.bind_some] at hnode
            have htx := text_sources (initialLabels m) before j hs.symm
            simp only [htx] at hnode
            simp only [denseConstants, Option.bind_some] at hns hfit
            simp only [hns] at hnode
            simp only [hfit] at hnode
            simp only [sourceText_eq_lookup] at hnode
            have hlt := lookupText_sources (initialLabels m) before (n.source.id ++ ".value") hs.symm
            have hvi : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
                = (initialLabels m).findIdx? (fun l => l.source.id == n.source.id ++ ".value") :=
              findIdx?_sources before (initialLabels m) _ hs
            simp only [hlt] at hnode
            simp only [← hvi] at hnode
            simp only [hxl, Bool.false_and] at hnode
            have h2le : 2 ≤ (tileRect n.rect).h - 1280 := by
              simp only [Bool.or_assoc, Bool.or_eq_true] at hnode
              rcases hnode with h | h | h | h
              · exact absurd (of_decide_eq_true h) (fun hc => hd (Or.inl hc))
              · exact absurd (of_decide_eq_true h) (fun hc => hd (Or.inr hc))
              · simp at h
              · exact of_decide_eq_true h
            -- `h`: `vw` is `0`, and the second `showValue` if takes its else branch
            obtain ⟨vw, hvw, h⟩ := bind_ok' h
            simp only [Except.ok.injEq] at hvw
            subst hvw
            simp only [hx, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              Except.ok.injEq] at h
            by_cases hij : j = i
            · subst hij
              refine Or.inl ⟨putLabel nl shown
                ⟨(tileRect n.rect).x + (denseConstants m nodes).pad +
                  Int.fdiv ((tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw) 2,
                  (tileRect n.rect).y +
                    Int.fdiv ((tileRect n.rect).h - 1280) 2,
                  nw, 1280⟩ ns, ?_, hidnl, ?_⟩
              · rw [← h, modified_label_at_index, hnl]
                simp only [Option.map_some, ite_true]
              · have hnwa : nw ≤ (tileRect n.rect).w - 2 * (denseConstants m nodes).pad :=
                  fit_width_le_avail false _ _ _ _ _ _ hfit
                have hfx1 : 0 ≤ Int.fdiv ((tileRect n.rect).w -
                    2 * (denseConstants m nodes).pad - nw) 2 := fdiv_two_nonneg (by omega)
                have hfx2 : 2 * Int.fdiv ((tileRect n.rect).w -
                    2 * (denseConstants m nodes).pad - nw) 2 ≤
                    (tileRect n.rect).w - 2 * (denseConstants m nodes).pad - nw :=
                  two_fdiv_le (by omega)
                have hft1 : 1 ≤ Int.fdiv ((tileRect n.rect).h - 1280) 2 :=
                  fdiv_two_ge_one h2le
                have hft2 : 2 * Int.fdiv ((tileRect n.rect).h - 1280) 2 ≤
                    (tileRect n.rect).h - 1280 :=
                  two_fdiv_le (by have h := h2le; omega)
                exact strict_inside_of_bounds4
                  (show (tileRect n.rect).x < (tileRect n.rect).x +
                    (denseConstants m nodes).pad +
                    Int.fdiv ((tileRect n.rect).w -
                      2 * (denseConstants m nodes).pad - nw) 2 from by
                      have h := hfx1; have h := hpad; omega)
                  (show (tileRect n.rect).x + (denseConstants m nodes).pad +
                    Int.fdiv ((tileRect n.rect).w -
                      2 * (denseConstants m nodes).pad - nw) 2 + nw <
                    (tileRect n.rect).x + (tileRect n.rect).w from by
                      have h := hfx1; have h := hfx2; have h := hnwa; have h := hpad; omega)
                  (show (tileRect n.rect).y < (tileRect n.rect).y +
                    Int.fdiv ((tileRect n.rect).h - 1280) 2 from by
                      have h := hft1; omega)
                  (show (tileRect n.rect).y +
                    Int.fdiv ((tileRect n.rect).h - 1280) 2 + 1280 <
                    (tileRect n.rect).y + (tileRect n.rect).h from by
                      have h := hft1; have h := hft2; omega)
            · exfalso
              rw [← h] at hchange
              rw [modified_label_at_index] at hchange
              cases hbi : before[i]? with
              | none => rw [hbi, Option.map_none] at hchange; exact hchange rfl
              | some _ =>
                rw [hbi] at hchange
                simp only [Option.map_some, ite_eq_right hij] at hchange
                exact hchange rfl
end Elegant.Treemap.LabelFacts3
