import Elegant.Layered.BottomClearanceBracket
import Elegant.Layered.BottomClearanceInside
import Elegant.Layered.RecursiveC6
import Elegant.Layered.CoordGraph
import Elegant.Layered.BottomSeamsStructural
import Elegant.Layered.BracketInsideStructuralFacts

set_option autoImplicit false

/-!
# The flat frame-clearance seam, for every executed component run

`FrameClearanceSeam` (`RecursiveC6`, line 39) asks that every successful
component run of the flat layout keep `FrameClearance run.proper run.layers
run.xs`.  `componentRun_frame_clearance` (`BottomClearanceBracket`, line 442)
derives that clause from the inside-rank bracket closure
`BracketInsideRankBelowBottom` plus the executed measured-graph equation and
the box-count equation.

This module does two things:

* `BracketInsideForAll` restates the closure as a single named seam over the
  actual `SceneExecution` of a successful layout: for every executed component
  and every candidate index, the closure of that component's graph holds.
  The measured-graph equation and the box-count equation are the
  `SceneExecution.graph_eq` and `SceneExecution.lines_eq` fields, so they are
  facts of the successful execution, not caller assumptions.
* `frameClearanceSeam_of_bracket` discharges `FrameClearanceSeam` from that
  seam by `componentRun_frame_clearance`.
* `BracketInsidePremises` bundles the named premises
  `bracket_inside_rank_below_bottom` still takes, and
  `frameClearanceSeam_holds` instantiates the producer so the seam itself is
  discharged, leaving only those premises.

The closure is a genuine seam, not a consequence of `WellFormed` alone: the
executed witness `flowchart TD; subgraph g1; a --> m; end; g1 --> z;
n0 --> n1; n1 --> z` has a non-member node overlapping a bottom proxy span at
its own rank, so the same-rank premise of the def is not removable.  The
producer of the closure is `BottomClearanceInside.lean`'s
`bracket_inside_rank_below_bottom`.
-/

namespace Elegant.Layered.PipelineImpl

/-- `boxLines` produces one line block per input box; this is the
`SceneExecution.lines.length = inp.boxes.length` fact that the frame-clearance
derivation consumes. -/
private theorem executionLines_length {m : Measure.Metric} {target : Int}
    {inp : Input} {lines : List (List Measure.Line)}
    (h : boxLines m target inp = .ok lines) : lines.length = inp.boxes.length := by
  unfold boxLines at h
  have hlen := (mapM_getElem? _ _ _ h).1
  have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
  omega

/-- The inside-rank bracket closure, for every executed component of a
successful flat layout.  `execution.graph_eq` and `execution.lines_eq` supply
the two equations `BracketInsideRankBelowBottom` takes; `hcomp` is the
membership of the executed component. -/
def BracketInsideForAll (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (hcomp : comp ∈ components execution.graph),
    BracketInsideRankBelowBottom execution.graph_eq
      (executionLines_length execution.lines_eq) hcomp candidate

/-- The flat frame-clearance seam follows from the inside-rank bracket closure
by `componentRun_frame_clearance`, run by run over the executed components. -/
theorem frameClearanceSeam_of_bracket {inp : Input} {o : Options} {res : FamilyResult}
    (hInside : BracketInsideForAll inp o res) : FrameClearanceSeam inp o res := by
  intro execution comp candidate run orderOptions hcomp hrun
  exact componentRun_frame_clearance execution.graph_eq
    (executionLines_length execution.lines_eq) hcomp
    (hInside execution comp candidate hcomp) hrun

/-- The named OPEN premises `bracket_inside_rank_below_bottom` still takes,
bundled per executed layout: three graph-level clauses about executed runs and
the per-run inside-prefix hypothesis.  None of them restates frame clearance;
each is a statement about dummies, cluster paths, or ranks of an executed
component run.  The other three clauses are proved: `sideTitleHeightZero` and
`nonDummyBorderPlain` (`BracketInsideStructuralFacts.lean`) and `sidePathEq`
(`BottomSeamsStructural.lean`). -/
def BracketInsidePremises (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ execution : SceneExecution inp o res,
    plainMemberRankLtProxy execution.params execution.graph ∧
    dummyInsideSameRankFalse execution.params execution.graph ∧
    titleCopySpanClearStrict execution.params execution.graph ∧
    ∀ (comp : List Nat) (_hcomp : comp ∈ components execution.graph) (candidate : Nat)
      (run : Run) (labels : List MeasuredLabel) (orderOptions : OrderOptions),
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) labels orderOptions = .ok run →
      ∀ pref : List Nat, insidePrefixHypothesis run orderOptions pref

/-- The flat frame-clearance seam holds unconditionally once the inside-rank
bracket closure is produced: `bracket_inside_rank_below_bottom` supplies
`BracketInsideForAll` and `frameClearanceSeam_of_bracket` finishes. -/
theorem frameClearanceSeam_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hprem : BracketInsidePremises inp o res) : FrameClearanceSeam inp o res := by
  apply frameClearanceSeam_of_bracket
  intro execution comp candidate hcomp
  obtain ⟨hplainRank, hdummyRank, htitleSpan, hprefix⟩ := hprem execution
  exact bracket_inside_rank_below_bottom execution.graph_eq
    (executionLines_length execution.lines_eq) hcomp candidate
    (sideTitleHeightZero_of_measuredGraph execution.graph_eq)
    hplainRank hdummyRank (nonDummyBorderPlain_of_measuredGraph execution.graph_eq)
    htitleSpan (sidePathEq_of_measuredGraph execution.graph_eq) (hprefix comp hcomp candidate)

end Elegant.Layered.PipelineImpl
