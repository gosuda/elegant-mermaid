import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.SelectInputCaptionTextProof

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

open Layered Layered.PipelineImpl

abbrev captionWrapTarget (P : Params) (metric : Measure.Metric) (o : Options) : Int :=
  Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)

/-- The caption line table consumed by the outermost step of a successful exact run. -/
theorem layoutRecursiveB_caption_lines {ids : List String} {fuel : Nat} {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) :
    ∃ (P : Params) (metric : Measure.Metric) (lines : List (List Measure.Line)),
      checkedParams o.profile inp.kind = .ok P ∧ metricOf o.profile = .ok metric ∧
      boxLines metric (captionWrapTarget P metric o) inp = .ok lines := by
  have flat (hflat : layoutX ids inp o = .ok res) :
      ∃ (P : Params) (metric : Measure.Metric) (lines : List (List Measure.Line)),
        checkedParams o.profile inp.kind = .ok P ∧ metricOf o.profile = .ok metric ∧
        boxLines metric (captionWrapTarget P metric o) inp = .ok lines := by
    obtain ⟨P, metric, lines, _, _, _, _, _, hP, hm, hl, _⟩ := layoutX_success_phases hflat
    exact ⟨P, metric, lines, hP, hm, hl⟩
  cases fuel with
  | zero => exact flat h
  | succ fuel =>
    rcases layoutRecursiveB_succ_sources (layoutX ids) h with ⟨_, hflat⟩ |
      ⟨_, P, _, _, _, _, _, hP, _, _, _, _, hexpand⟩
    · exact flat hflat
    · obtain ⟨_, metric, _, lines, _, _, _, hm, _, hl, _⟩ := expandChild_sources hexpand
      exact ⟨P, metric, lines, hP, hm, hl⟩

theorem layoutRecursiveB_caption_lines_at {ids : List String} {fuel : Nat} {inp : Input}
    {o : Options} {res : FamilyResult} {P : Params} {metric : Measure.Metric}
    (h : layoutRecursiveB (layoutX ids) fuel inp o = .ok res)
    (hP : checkedParams o.profile inp.kind = .ok P) (hm : metricOf o.profile = .ok metric) :
    ∃ lines, boxLines metric (captionWrapTarget P metric o) inp = .ok lines := by
  obtain ⟨Q, subMetric, lines, hQ, hSubMetric, hl⟩ := layoutRecursiveB_caption_lines h
  have hParams : Q = P := Except.ok.inj (hQ.symm.trans hP)
  have hMetric : subMetric = metric := Except.ok.inj (hSubMetric.symm.trans hm)
  subst Q
  subst subMetric
  exact ⟨lines, hl⟩

/-- The two executed recursive calls and the expansion wrap the same effective caption
at corresponding box occurrences. Child direction can change; kind, profile, and
`maxWidth` do not. The parent's fixed geometry is not read by `boxLines`. -/
theorem exact_expansion_caption_lines {ids : List String} {fuel : Nat} {inp : Input}
    {o : Options} {group : ModelBox} {P : Params} {metric : Measure.Metric}
    {titleLines : List Measure.Line} {titleHeight : Int} {child parent res : FamilyResult}
    (hP : checkedParams o.profile inp.kind = .ok P) (hm : metricOf o.profile = .ok metric)
    (hchild : layoutRecursiveB (layoutX ids) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursiveB (layoutX ids) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ (lines childLines parentLines : List (List Measure.Line)),
      boxLines metric (captionWrapTarget P metric o) inp = .ok lines ∧
      boxLines metric (captionWrapTarget P metric o) (childSubInput inp group) = .ok childLines ∧
      boxLines metric (captionWrapTarget P metric o) (parentSubInput inp group P titleLines child) =
        .ok parentLines ∧
      (∀ {j : Nat} {q : ModelBox × Nat},
        (inp.boxes.zipIdx.filter fun entry => Compound.inside inp.boxes group.id entry.1.id)[j]? =
          some q → childLines.getD j [] = lines.getD q.2 []) ∧
      (∀ {j : Nat} {q : ModelBox × Nat},
        (inp.boxes.zipIdx.filter fun entry => !Compound.inside inp.boxes group.id entry.1.id)[j]? =
          some q → parentLines.getD j [] = lines.getD q.2 []) := by
  obtain ⟨_, expansionMetric, _, lines, _, _, _, hmExpansion, _, hl, _⟩ :=
    expandChild_sources hexpand
  have metricEq : expansionMetric = metric := Except.ok.inj (hmExpansion.symm.trans hm)
  subst expansionMetric
  obtain ⟨childLines, hlChild⟩ := layoutRecursiveB_caption_lines_at hchild hP hm
  obtain ⟨parentLines, hlParent⟩ := layoutRecursiveB_caption_lines_at hparent hP hm
  refine ⟨lines, childLines, parentLines, hl, hlChild, hlParent, ?_, ?_⟩
  · intro j q hq
    exact selectInput_boxLines_getD (fun box => Compound.inside inp.boxes group.id box.id)
      group.id hq hl hlChild
  · intro j q hq
    exact selectInput_boxLines_getD (fun box => !Compound.inside inp.boxes group.id box.id)
      "" hq hl hlParent

end Elegant.Kinds.Usecase
