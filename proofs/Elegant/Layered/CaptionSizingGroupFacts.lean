import Elegant.Layered.CaptionSizingFacts

/-!
# Caption sizing group facts

The per-index nonfixed-group clause of `CaptionInputs` (the `2 * clusterPad`
width bound and the `clusterPad + caption block height` bound on the shifted,
oriented packed rect) from executed layout facts.

Executed facts used (all previously compiled):

* `PipelineImpl.SceneExecution.group_caption_packed_rank_fit`: the executed
  caption block plus `clusterPad` fits the rank-axis extent of the packed
  group rect. Discharges the height clause for `TB`/`BT` outright.
* `PipelineImpl.packAcc_rect_minimum_dimensions_of_coverage` with
  `parts_coverage`: a per-index minimum size covered by the executed part
  rects survives packing.

The width clause is NOT derivable from the executed facts alone. A group
frame's width is exactly the horizontal span of its border rectangles
(`frameRect_group_width_eq_horizontal_span`); no `2 * clusterPad` term is
added on this path (`childFrameSize` adds one only for fixed-child groups).
`frameRect_group_empty_borders_counterexample` exhibits the shape: with no
borders the frame width is `0 < 2 * clusterPad` for positive `clusterPad` -
the narrow-title group with no members, whose frame collapses to the title
bracket. `componentRun_group_title_bracket` brackets the title with border
nodes but yields only `frame.w ≥ title width`, which does not cover
`2 * clusterPad ≤ frame.w` for a narrow title.

The two honest premises below state the missing executed facts at the level
where they are missing:

* `CaptionGroupFrameWidthFloor`: the pre-packing, pre-orientation part frame
  of every nonfixed group entry carries the direction-matched allowance -
  `2 * clusterPad` in `TB`/`BT` (the width clause) and `clusterPad` plus the
  caption block in `LR`/`RL` (the rank-space width that orientation maps to
  the output height).
* `CaptionGroupTitleWidthFloor`: the measured (wrapped) caption block of a
  nonfixed group is at least `clusterPad` wide; combined with the executed
  rank-axis fit this yields the `LR`/`RL` width clause.
-/

namespace Elegant.Layered

variable {inp : Input} {o : Options} {res : FamilyResult}

/-- The shifted, oriented executed rect that `sceneBoxesExpr` produces for box
index `i`. -/
def captionGroupRect (o : Options) (execution : PipelineImpl.SceneExecution inp o res)
    (i : Nat) :=
  PipelineImpl.shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
      (execution.packedAcc.rects.getD i default))

/-- Executed fact (part level, before packing and orientation): the frame
rect of every nonfixed group entry carries the direction-matched caption
allowance in its border-span width. This is the border-bracket width fact
that `componentRun_group_title_bracket` does not yet provide; it fails for
the narrow-title, memberless group shape of
`frameRect_group_empty_borders_counterexample`. -/
def CaptionGroupFrameWidthFloor (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (part : List Nat × PipelineImpl.Part),
    part ∈ execution.componentsAcc.parts →
    ∀ (j k : Nat) (source : ModelBox),
      part.1[j]? = some k →
        inp.boxes[k]? = some source →
          source.role = .group →
            inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false →
              ∀ frame : Rect, part.2.rects[j]? = some frame →
                (match o.direction with
                  | .LR | .RL =>
                    execution.params.clusterPad +
                      (max 1 (execution.lines.getD k []).length : Int) *
                        execution.params.lineH
                  | .TB | .BT => 2 * execution.params.clusterPad) ≤ frame.w

/-- Measured-title fact: the wrapped caption block of every nonfixed group
box is at least `clusterPad` wide. -/
def CaptionGroupTitleWidthFloor (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (k : Nat) (source : ModelBox),
    inp.boxes[k]? = some source →
      source.role = .group →
        inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false →
          execution.params.clusterPad ≤
            (execution.lines.getD k []).foldl (fun width line => max width line.width) 0

/-- A width floor covered by the executed part rects of one box index
survives packing: the packed rect of that index is at least the floor. The
transport is the `packAcc` minimum-dimension coverage lemma; entries of
other indices only need nonnegative dimensions from
`components_parts_bounded`. -/
private theorem packed_rect_width_of_part_floor
    (execution : PipelineImpl.SceneExecution inp o res)
    (i : Nat) (source : ModelBox)
    (hidx : inp.boxes[i]? = some source)
    (floorW : Int)
    (hpartFloor : ∀ part : List Nat × PipelineImpl.Part,
      part ∈ execution.componentsAcc.parts →
      ∀ j : Nat, part.1[j]? = some i →
        ∀ frame : Rect, part.2.rects[j]? = some frame → floorW ≤ frame.w) :
    floorW ≤ (execution.packedAcc.rects.getD i default).w := by
  obtain ⟨rect, hrectPacked⟩ := execution.packed_rect_exists
    ((List.getElem?_eq_some_iff.mp hidx).1)
  let minimum : Nat → Size := fun k => ⟨if k = i then floorW else 0, 0⟩
  have hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h := by
    intro part hmem entry hentry
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hentry
    simp only [List.length_zip] at hj
    have hjl : j < part.1.length := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    have hjr : j < part.2.rects.length := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hpair : (part.1[j], part.2.rects[j]) = entry := by
      simpa only [List.getElem_zip] using heq
    have hkey : part.1[j]? = some entry.1 := by
      rw [List.getElem?_eq_getElem hjl, ← hpair]
    have hrectj : part.2.rects[j]? = some entry.2 := by
      rw [List.getElem?_eq_getElem hjr, ← hpair]
    have hb := execution.components_parts_bounded part hmem
    have hn := hb.2.2.1 entry.2 (List.of_mem_zip hentry).2
    refine ⟨?_, by simpa only [minimum, ↓reduceIte] using hn.2.2.2.2.2⟩
    by_cases he : entry.1 = i
    · have hfl := hpartFloor part hmem j (by rw [hkey, he]) entry.2 hrectj
      simpa only [minimum, he, ↓reduceIte] using hfl
    · simpa only [minimum, he, ↓reduceIte] using hn.2.2.2.2.1
  have hcovered := PipelineImpl.packAcc_rect_minimum_dimensions_of_coverage minimum
    execution.packed_eq
    (fun k r hr => Or.inr (execution.parts_coverage k r hr)) hparts i rect hrectPacked
  have hget : execution.packedAcc.rects.getD i default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrectPacked
    simpa [Array.getD, hi] using heq
  simpa only [minimum, ↓reduceIte, hget] using hcovered.1

/-- The per-index nonfixed-group clause of `CaptionInputs`, from the executed
caption fit, the `packAcc` coverage transport, and the two named premises.
The height clause for `TB`/`BT` needs no premise. -/
theorem caption_group_clause_of_executed
    (hfloor : CaptionGroupFrameWidthFloor inp o res)
    (htitle : CaptionGroupTitleWidthFloor inp o res)
    (execution : PipelineImpl.SceneExecution inp o res)
    (i : Nat) (source : ModelBox)
    (hidx : inp.boxes[i]? = some source) (hrole : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    2 * execution.params.clusterPad ≤ (captionGroupRect o execution i).w ∧
      execution.params.clusterPad +
          (max 1 (execution.lines.getD i []).length : Int) *
            execution.params.lineH ≤
        (captionGroupRect o execution i).h := by
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold PipelineImpl.boxLines at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (PipelineImpl.mapM_getElem? _ _ _ hl).1
      _ = inp.boxes.length := List.length_zipIdx
  obtain ⟨rect, hrectPacked⟩ := execution.packed_rect_exists
    ((List.getElem?_eq_some_iff.mp hidx).1)
  have hget : execution.packedAcc.rects.getD i default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrectPacked
    simpa [Array.getD, hi] using heq
  obtain ⟨nodes, edges, titles, hprepared, hlength, -⟩ :=
    PipelineImpl.measuredGraph_prepared_source execution.graph_eq
  have hinodes : i < nodes.length := by
    rw [hlength, hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hidx).1
  have hpreparedSource :
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)[i]? = some source := by
    simp [List.getElem?_map, hidx, hfixed]
  have hrecord := Compound.prepare_group_title_record
    (inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hinodes hpreparedSource hrole
  rw [← hprepared] at hrecord
  have hfitPacked := execution.group_caption_packed_rank_fit hrecord rfl hidx
  unfold captionGroupRect
  cases hd : o.direction
  case TB =>
    simp only [hd] at hfitPacked
    obtain ⟨rect', hrect', hfit⟩ := hfitPacked
    have hreq : rect' = rect := Option.some.inj (hrect'.symm.trans hrectPacked)
    subst hreq
    have hcovered := packed_rect_width_of_part_floor execution i source hidx
      (2 * execution.params.clusterPad)
      (fun part hmem j hj frame hframe => by
        have hfl := hfloor execution part hmem j i source hj hidx hrole hfixed frame hframe
        simp only [hd] at hfl
        exact hfl)
    refine ⟨?_, ?_⟩
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      exact hcovered
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      rw [hget]
      omega
  case BT =>
    simp only [hd] at hfitPacked
    obtain ⟨rect', hrect', hfit⟩ := hfitPacked
    have hreq : rect' = rect := Option.some.inj (hrect'.symm.trans hrectPacked)
    subst hreq
    have hcovered := packed_rect_width_of_part_floor execution i source hidx
      (2 * execution.params.clusterPad)
      (fun part hmem j hj frame hframe => by
        have hfl := hfloor execution part hmem j i source hj hidx hrole hfixed frame hframe
        simp only [hd] at hfl
        exact hfl)
    refine ⟨?_, ?_⟩
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      exact hcovered
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      rw [hget]
      omega
  case LR =>
    simp only [hd] at hfitPacked
    obtain ⟨rect', hrect', hfit⟩ := hfitPacked
    have hreq : rect' = rect := Option.some.inj (hrect'.symm.trans hrectPacked)
    subst hreq
    have hwidth := htitle execution i source hidx hrole hfixed
    have hcovered := packed_rect_width_of_part_floor execution i source hidx
      (execution.params.clusterPad +
        (max 1 (execution.lines.getD i []).length : Int) *
          execution.params.lineH)
      (fun part hmem j hj frame hframe => by
        have hfl := hfloor execution part hmem j i source hj hidx hrole hfixed frame hframe
        simp only [hd] at hfl
        exact hfl)
    refine ⟨?_, ?_⟩
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      rw [hget]
      omega
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      exact hcovered
  case RL =>
    simp only [hd] at hfitPacked
    obtain ⟨rect', hrect', hfit⟩ := hfitPacked
    have hreq : rect' = rect := Option.some.inj (hrect'.symm.trans hrectPacked)
    subst hreq
    have hwidth := htitle execution i source hidx hrole hfixed
    have hcovered := packed_rect_width_of_part_floor execution i source hidx
      (execution.params.clusterPad +
        (max 1 (execution.lines.getD i []).length : Int) *
          execution.params.lineH)
      (fun part hmem j hj frame hframe => by
        have hfl := hfloor execution part hmem j i source hj hidx hrole hfixed frame hframe
        simp only [hd] at hfl
        exact hfl)
    refine ⟨?_, ?_⟩
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      rw [hget]
      omega
    · simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect]
      exact hcovered

/-- `CaptionInputs` follows from the caption input contract, the part-level
group frame width floor, and the measured-title width floor. -/
theorem captionInputs_of_group_facts
    (hcap : ∃ captions : String → String, PipelineImpl.CaptionInputs captions inp o)
    (hfloor : CaptionGroupFrameWidthFloor inp o res)
    (htitle : CaptionGroupTitleWidthFloor inp o res) :
    CaptionInputs inp o res := by
  intro execution
  obtain ⟨captions, hcap⟩ := hcap
  exact ⟨captions, hcap, fun i source hidx hrole hfixed =>
    caption_group_clause_of_executed hfloor htitle execution i source hidx hrole hfixed⟩
