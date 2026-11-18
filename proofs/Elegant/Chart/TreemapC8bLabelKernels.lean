import Elegant.Chart.TreemapC8bKernelFacts

namespace Elegant.Treemap.C8b

open Elegant.Treemap.C8a
open Elegant.Treemap.CanvasC1
open Elegant.Treemap.Clearance
open Elegant.Treemap.TileForest
open Elegant.Treemap.Containment
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.LabelFacts3

/-!
### The status of `internal_label_header_band`

`placeHeader` (`TreemapAdapter.lean:218-231`) skips the `.name` write when the
fit fails (`match ← fit ... with | none => pure labels`) and skips the whole
call when the tile is too low (`if r.h ≤ top + lh then pure labels`).  An
internal node whose header step hits either branch leaves its owned `.name`
label at the initial zero rectangle through a successful layout.  For such a
label the strict-containment conjunct of `internal_label_header_band` is
false, because a zero rectangle cannot sit strictly inside a tile whose x
coordinate is nonnegative.  The model below realizes the skip branch, and
`placeHeader_skip_concrete` verifies the skip by kernel computation
(`placeHeader` crosses only `fit`/`width`/`findIdx`, all reducible; the full
pipeline is not, because `List.mergeSort` inside `dependencyOrder` is
well-founded and stays as an `Acc.rec` spine under kernel reduction).
-/

/-- Witness model: `x` is an internal node (parent of `y`) whose `.name` label
is owned by `x`.  All region values are zero, so the tiled `x` tile is the
inset of the single zero-value cell, which `placeCells_zero_shape` makes
degenerate; either skip branch of `placeHeader` then fires. -/
def headerSkipModel : Model := {
  kind := "treemap",
  profile := .vector,
  boxes := [
    { id := "root", role := .group, parent := "", exclusive := false },
    { id := "x", role := .group, parent := "root", exclusive := false },
    { id := "y", role := .node, parent := "x", exclusive := false }],
  routes := [],
  labels := [
    { id := "x.name", owner := "x", text := "xname" },
    { id := "y.name", owner := "y", text := "y" }],
  regionSets := [{ parent := 0, regions := [0, 0] }] }

theorem headerSkipModel_wellFormed : WellFormed headerSkipModel := by decide

theorem headerSkipModel_withinLimits : WithinLimits headerSkipModel := by decide

/-- The internal node of the witness, carrying the degenerate zero tile that
the zero-value tiling produces for it. -/
def headerSkipNode : Node := {
  source := { id := "x", role := .group, parent := "root", exclusive := false },
  value := 0 }

/-- Executed evidence of the skip branch: `placeHeader` on the internal node
with a zero-height tile returns its labels unchanged, so the `.name` label
owned by `x` keeps the zero rectangle. -/
theorem placeHeader_skip_concrete :
    placeHeader headerSkipModel (constants headerSkipModel) headerSkipNode
      (initialLabels headerSkipModel) = .ok (initialLabels headerSkipModel) := by
  rfl

/-- Refutation kernel: whenever an internal node's owned label is untouched
(the zero rectangle that `placeHeader`'s skip branches leave behind), the
conclusion of `internal_label_header_band` fails, since strict containment of
the zero rectangle would force a negative tile x coordinate. -/
theorem internal_label_header_band_refutes_untouched {m : Model}
    (n : Node) (l : Label) (hzero : l.rect = ⟨0, 0, 0, 0⟩)
    (hx : 0 ≤ (tileRect n.rect).x) :
    ¬ (l.rect.y + l.rect.h ≤ (tileRect n.rect).y +
          (constants m).header + (constants m).padY ∧
        Rect.StrictInside (tileRect n.rect) l.rect) := by
  intro hboth
  have hlt := hboth.2.1
  unfold Rect.StrictInside at hlt
  rw [hzero] at hlt
  dsimp only at hlt
  omega

/-- A checked text width is never negative. -/
private theorem width_nonneg' {cell : Bool} {text : String} {role : Measure.Role}
    {size x : Int} (h : width cell text role size = .ok x) : 0 ≤ x := by
  unfold width at h
  obtain ⟨metric, _, hw⟩ := CanvasC1.except_bind_ok h
  exact Measure.textWidth_nonneg hw

/-- A nonpositive-height tile always skips its header write when the profile's
band bottom is nonnegative. -/
theorem placeHeader_skip_of_nonpos_height (m : Model) (c : Consts) (n : Node)
    (before : List PlacedLabel)
    (hh : (tileRect n.rect).h ≤ 0)
    (htop : 0 ≤ LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280)) :
    placeHeader m c n before = .ok before :=
  placeHeader_skip_height m c n before (by omega)

/-- The witness model's vector header band bottom is nonnegative. -/
theorem headerSkipModel_band_bottom_nonneg :
    0 ≤ LayoutConst.treemap_header_border.get headerSkipModel.profile +
        Int.fdiv ((constants headerSkipModel).header -
          LayoutConst.treemap_header_border.get headerSkipModel.profile - 1280) 2 +
        1280 := by decide
/-- The written header band bottom stays within the reserved body band:
`top + lh ≤ header + padY` in both profiles. -/
theorem treemap_header_bottom_within_band (m : Model) :
    LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv (LayoutConst.treemap_section_header.get m.profile -
        LayoutConst.treemap_header_border.get m.profile -
        (if m.profile == .cell then 1 else 1280)) 2 +
      (if m.profile == .cell then 1 else 1280) ≤
    LayoutConst.treemap_section_header.get m.profile +
      LayoutConst.treemap_section_padding_y.get m.profile := by
  cases m.profile <;> decide

/-- The same bound in `constants` form, for consumers of the band conjunct. -/
theorem treemap_band_bottom_ge (m : Model) :
    LayoutConst.treemap_header_border.get m.profile +
      Int.fdiv ((constants m).header -
        LayoutConst.treemap_header_border.get m.profile -
        (if m.profile == .cell then 1 else 1280)) 2 +
      (if m.profile == .cell then 1 else 1280) ≤
    (constants m).header + (constants m).padY :=
  treemap_header_bottom_within_band m

/-- Named residual gap for the two label kernels: when an internal node's
header step changes only its `.value` label (the `.name` fit returned
`none`, so `header_body_rects_strict` does not apply), the changed label is
still strictly inside the node's tile or keeps the zero rectangle. Every
other write shape is covered by `header_body_rects_strict`,
`leaf_group_write_strict_rects`, and `leaf_body_rects_contained`. -/
def header_value_only_write_strict (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel) : Prop :=
  HeaderWriteRun m c n before after →
    (before.findIdx? (fun l => l.source.id == n.source.id ++ ".name")).isNone = true →
    ∀ i : Nat, after[i]? ≠ before[i]? →
      ∃ l : PlacedLabel, after[i]? = some l ∧
        l.source.id = n.source.id ++ ".value" ∧
        (Rect.StrictInside (tileRect n.rect) l.rect ∨ l.rect = ⟨0, 0, 0, 0⟩)
end Elegant.Treemap.C8b
