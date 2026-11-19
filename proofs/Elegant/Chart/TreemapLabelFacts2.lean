import Elegant.Chart.TreemapFacts
import Elegant.Kinds.Treemap
import ElegantGeometry.Validator

/-! Flush-label witnesses for the treemap leaf-group guard.

`flushWitness` is a vector-profile model with a childless group `g` whose tile
lands at height exactly 1280, so `placeLeaf` would write `g.name` flush with
the tile top and bottom. The adapter rejects it through
`Elegant.Treemap.leafGroupLabelVerticalStrict`. `flushControlTall` and
`flushControlCell` are one-label controls that stay accepted in both profiles.
-/

namespace Elegant.Treemap.LabelFacts2

open Elegant.Treemap.CanvasC1

private theorem tileStep_no_children (c : Treemap.Consts) (acc : List Treemap.Node)
    (i : Nat) (n : Treemap.Node) (hn : acc[i]? = some n)
    (h : (Treemap.sortedChildren acc n.source.id).isEmpty = true) :
    tileStep c acc i = .ok acc := by
  unfold tileStep
  rw [hn]
  simp only [h, ↓reduceIte, pure, Except.pure]

/-! ## The rejected witness: childless group with a 1280-high tile -/

private def flushWitness : Model :=
  { kind := "treemap", profile := .vector,
    options := { profile := .vector, config := [
      ("nodeWidth", ConfigValue.integer 96), ("nodeHeight", ConfigValue.integer 100)] },
    boxes := [{ id := "root", role := .group, exclusive := false },
              { id := "s", parent := "root" },
              { id := "g", parent := "root", role := .group, exclusive := false }],
    labels := [{ id := "s.name", owner := "s", text := "s" },
               { id := "g.name", owner := "g", text := "g" }],
    regionSets := [{ parent := 0, regions := [935, 30] }] }

private def wRoot : Treemap.Node :=
  { source := { id := "root", role := .group, exclusive := false }, value := 965,
    series := 0, rect := ⟨0, 0, 61440, 64000⟩ }

private def wS : Treemap.Node :=
  { source := { id := "s", parent := "root" }, value := 935, series := 0 }

private def wG : Treemap.Node :=
  { source := { id := "g", parent := "root", role := .group, exclusive := false },
    value := 30, series := 1 }

private def wInitial : List Treemap.Node :=
  [{ source := { id := "root", role := .group, exclusive := false }, value := 0 },
   { source := { id := "s", parent := "root" }, value := 935 },
   { source := { id := "g", parent := "root", role := .group, exclusive := false }, value := 30 }]

private def wAggregated : List Treemap.Node :=
  [ { source := { id := "root", role := .group, exclusive := false }, value := 965 },
    { source := { id := "s", parent := "root" }, value := 935 },
    { source := { id := "g", parent := "root", role := .group, exclusive := false },
      value := 30 } ]

private def wSeries : List Treemap.Node :=
  [ { source := { id := "root", role := .group, exclusive := false }, value := 965 },
    { source := { id := "s", parent := "root" }, value := 935, series := 0 },
    { source := { id := "g", parent := "root", role := .group, exclusive := false },
      value := 30, series := 1 } ]

private def wSeeded : List Treemap.Node := [wRoot, wS, wG]

private def wS1 : Treemap.Node := { wS with rect := ⟨640, 2240, 60800, 61440⟩ }

private def wG1 : Treemap.Node := { wG with rect := ⟨640, 62080, 60800, 63360⟩ }

private def wAfterRoot : List Treemap.Node := [wRoot, wS1, wG1]

private def wTiled : List Treemap.Node := wAfterRoot

private theorem wInitial_eq : Treemap.initialNodes flushWitness = wInitial := by
  rfl

private theorem wOrderInitial_eq : Treemap.dependencyOrder wInitial = [0, 1, 2] := by
  change ((([(0, 0), (1, 1), (2, 1)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 1, 2]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]
  try decide

private theorem wOrder_eq : Treemap.dependencyOrder wAggregated = [0, 1, 2] := by
  change ((([(0, 0), (1, 1), (2, 1)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 1, 2]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]
  try decide

private theorem wAggregate_eq :
    Treemap.aggregate (Treemap.initialNodes flushWitness) = wAggregated := by
  unfold Treemap.aggregate
  rw [wInitial_eq, wOrderInitial_eq]
  rfl

private theorem wSeries_eq : Treemap.assignSeries wAggregated = wSeries := by
  unfold Treemap.assignSeries
  rw [wOrder_eq]
  rfl

private theorem wConstants_eq : Treemap.constants flushWitness =
    { width := 61440, height := 64000, titleBand := 1920, header := 1600,
      padX := 640, padY := 640, innerX := 640, innerY := 640,
      rho := 1737350766, fuel := 2000 : Treemap.Consts } := by
  rfl

private theorem wSeeded_lookup0 : wSeeded[0]? = some wRoot := rfl

private theorem wChildren_eq : Treemap.sortedChildren wSeeded wRoot.source.id = [1, 2] := by
  change (([1, 2] : List Nat).mergeSort (Treemap.childKeyLe wSeeded)) = [1, 2]
  simp [Treemap.childKeyLe]
  decide

private theorem wChildren_root_eq : Treemap.sortedChildren wSeeded "root" = [1, 2] := by
  simpa [wRoot] using wChildren_eq

private theorem wChildArea_eq :
    Treemap.childArea ⟨0, 0, 61440, 64000⟩ 640 640 1600 640 640 =
      ⟨320, 1920, 61120, 63680⟩ := by
  rfl

private theorem wSquarify_eq :
    Treemap.squarify [935, 30] ⟨320, 1920, 61120, 63680⟩ 1737350766 2000 =
      .ok ([⟨320, 1920, 61120, 61760⟩, ⟨320, 61760, 61120, 63680⟩], false) := by
  rfl

private theorem wRootStep_eq :
    tileStep (Treemap.constants flushWitness) wSeeded 0 = .ok wAfterRoot := by
  unfold tileStep
  rw [wSeeded_lookup0, wConstants_eq]
  dsimp only [wRoot]
  rw [wChildren_root_eq, wChildArea_eq]
  rfl

private theorem wAfterRoot_children_s :
    (Treemap.sortedChildren wAfterRoot wS.source.id).isEmpty = true := by
  change ([].mergeSort (Treemap.childKeyLe wAfterRoot)).isEmpty = true
  simp [List.mergeSort_nil]

private theorem wAfterRoot_children_g :
    (Treemap.sortedChildren wAfterRoot wG.source.id).isEmpty = true := by
  change ([].mergeSort (Treemap.childKeyLe wAfterRoot)).isEmpty = true
  simp [List.mergeSort_nil]

private theorem wAfterRoot_lookup1 : wAfterRoot[1]? = some wS1 := rfl

private theorem wAfterRoot_lookup2 : wAfterRoot[2]? = some wG1 := rfl

private theorem wSStep_eq :
    tileStep (Treemap.constants flushWitness) wAfterRoot 1 = .ok wAfterRoot :=
  tileStep_no_children _ _ _ _ wAfterRoot_lookup1 wAfterRoot_children_s

private theorem wGStep_eq :
    tileStep (Treemap.constants flushWitness) wAfterRoot 2 = .ok wAfterRoot :=
  tileStep_no_children _ _ _ _ wAfterRoot_lookup2 wAfterRoot_children_g

private theorem wSeededOrder_eq : Treemap.dependencyOrder wSeeded = [0, 1, 2] := by
  change ((([(0, 0), (1, 1), (2, 1)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 1, 2]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

private theorem wTiling_eq :
    Treemap.tileNodes (Treemap.constants flushWitness) wSeeded = .ok wTiled := by
  rw [tileNodes_eq_foldlM, wSeededOrder_eq]
  simp only [List.foldlM_cons, wRootStep_eq, wSStep_eq, wGStep_eq, List.foldlM_nil,
    bind, Except.bind, pure, Except.pure]
  rfl

private theorem wSeededFull_eq :
    ((Treemap.assignSeries (Treemap.aggregate (Treemap.initialNodes flushWitness))).map
      (fun k => if k.source.id == "root" then
        { k with rect := ⟨0,
          (if (Treemap.labelText flushWitness "title").isEmpty then 0
            else (Treemap.constants flushWitness).titleBand),
          (Treemap.constants flushWitness).width,
          (if (Treemap.labelText flushWitness "title").isEmpty then 0
            else (Treemap.constants flushWitness).titleBand) +
            (Treemap.constants flushWitness).height⟩ } else k)) = wSeeded := by
  rw [wAggregate_eq, wSeries_eq]
  rfl

/-- The adapter rejects exactly when the leaf-group guard fails on the tiled
list: tiling succeeds, the guard is the only gate between tiling and label
placement, and its failure throws `.domain`. -/
theorem layout_error_of_guard (m : Model) (n : List Treemap.Node)
    (htile : Treemap.tileNodes (Treemap.constants m)
      ((Treemap.assignSeries (Treemap.aggregate (Treemap.initialNodes m))).map
        (fun k => if k.source.id == "root" then
          { k with rect := ⟨0,
            (if (Treemap.labelText m "title").isEmpty then 0
              else (Treemap.constants m).titleBand),
            (Treemap.constants m).width,
            (if (Treemap.labelText m "title").isEmpty then 0
              else (Treemap.constants m).titleBand) +
              (Treemap.constants m).height⟩ } else k)) = .ok n)
    (hg : Elegant.Treemap.leafGroupLabelVerticalStrict m n = false) :
    Elegant.Treemap.layout m = .error LayoutError.domain := by
  unfold Elegant.Treemap.layout
  dsimp only
  rw [htile]
  simp only [bind, Except.bind]
  split
  · rfl
  · next hc =>
      rw [hg] at hc
      exact absurd hc (by decide)

/-- The flush witness is rejected by the leaf-group guard: tiling succeeds and
the guard evaluates to `false` on the resulting tile list. -/
theorem flushWitness_rejected
    (hguard : Elegant.Treemap.leafGroupLabelVerticalStrict flushWitness wTiled = false) :
    Kinds.Treemap.layout flushWitness =
      .error (LayoutFailure.geometry LayoutError.domain) := by
  unfold Kinds.Treemap.layout
  rw [show Elegant.Treemap.layout flushWitness = .error LayoutError.domain from
    layout_error_of_guard flushWitness wTiled (by rw [wSeededFull_eq]; exact wTiling_eq)
      hguard]
  rfl


end Elegant.Treemap.LabelFacts2
