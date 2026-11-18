import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveBLiftsA

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Validator

/-- Base-parametric copy of `FlatC6`: the base layout keeps C6. The
`FrameClearanceSeam` premise speaks about the plain `SceneExecution`, so it
is kept as a hypothesis inside the B def rather than re-parameterized. -/
abbrev FlatC6B (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    FrameClearanceSeam inp o res →
    base inp o = .ok res → Validator.C6 res.scene.layoutDump

/-- Base-parametric copy of `FlatC7`. The `PartsSeparated`,
`LabelRunsClearExclusiveBoxes`, and `SceneCaptionBoxContainment` premises
speak about the plain execution, so they stay hypotheses of the B def. -/
abbrev FlatC7B (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    PartsSeparated inp o res →
    LabelRunsClearExclusiveBoxes inp o res →
    SceneCaptionBoxContainment inp o res →
    base inp o = .ok res → Validator.C7 res.scene.layoutDump

/-- Base-parametric copy of `FlatC8a`: no side seams beyond well-formedness. -/
abbrev FlatC8aB (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    base inp o = .ok res → Validator.C8a res.scene.layoutDump

/-- Base-parametric copy of `FlatC8b`: no side seams beyond well-formedness. -/
abbrev FlatC8bB (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    base inp o = .ok res → Validator.C8b res.scene.layoutDump

/-- `layoutRecursiveB` preserves C6 from the flat B fact, the global
frame-clearance fact, the sub-input well-formedness fact stated over
`layoutRecursiveB base`, and a per-call step over `ExpandChildCallContextB`
followed by `ExpandChildCallParams`. -/
theorem layoutRecursiveB_c6
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat : FlatC6B base)
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hsub : ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
      (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
      (child parent : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      checkedParams o.profile inp.kind = .ok P →
      metricOf o.profile = .ok metric →
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
          group.id).toList = .ok titleLines →
      layoutRecursiveB base fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child →
      layoutRecursiveB base fuel
        (parentSubInput inp group P titleLines child) o = .ok parent →
      WellFormed (inputModel (childSubInput inp group)
        (childSubOptions o group)) ∧
      framedParents (childSubInput inp group) = true ∧
      WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
      framedParents (parentSubInput inp group P titleLines child) = true)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C6 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hframed h
    have hbase : base inp o = .ok res := by simpa [layoutRecursiveB] using h
    exact hflat inp o res hwf hframed (hclear inp o res hwf hframed) hbase
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hbase⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm,
        hchild, hwrap, hparent, hexpand⟩
    · exact hflat inp o res hwf hframed (hclear inp o res hwf hframed) hbase
    · obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        hsub fuel inp o group P metric titleLines child parent
          hwf hframed hP hm hwrap hchild hparent
      have hchildC6 := ih _ _ _ hwfChild hframedChild hchild
      have hparentC6 := ih _ _ _ hwfParent hframedParent hparent
      have hparams : ExpandChildCallParams P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) :=
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      have hctx : ExpandChildCallContextB base fuel P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) parent child res :=
        ⟨hwf, hg, rfl, hchild, hparent, hexpand⟩
      have hstep := hgeo fuel P inp o group titleLines
        ((max 1 titleLines.length : Int) * P.lineH) parent child res
        hexpand hframed hctx hparams
      exact expandChild_c6 hchildC6 hparentC6 hstep hexpand

/-- `layoutRecursiveB` preserves C7 from the flat B fact, the two `LabelsC7`
seam facts, the sub-input fact over `layoutRecursiveB base`, and a per-call
step over `ExpandChildCallContextB` followed by `ExpandChildCallParams`. -/
theorem layoutRecursiveB_c7
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat7 : FlatC7B base)
    (hsep : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      PartsSeparated inp o res)
    (hseam1 : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res)
    (hseam2 : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      SceneCaptionBoxContainment inp o res)
    (hsub : ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
      (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
      (child parent : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      checkedParams o.profile inp.kind = .ok P →
      metricOf o.profile = .ok metric →
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
          group.id).toList = .ok titleLines →
      layoutRecursiveB base fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child →
      layoutRecursiveB base fuel
        (parentSubInput inp group P titleLines child) o = .ok parent →
      WellFormed (inputModel (childSubInput inp group)
        (childSubOptions o group)) ∧
      framedParents (childSubInput inp group) = true ∧
      WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
      framedParents (parentSubInput inp group P titleLines child) = true)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C7 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hframed h
    have hbase : base inp o = .ok res := by simpa [layoutRecursiveB] using h
    exact hflat7 inp o res hwf hframed (hsep inp o res)
      (hseam1 inp o res hwf hframed) (hseam2 inp o res hwf hframed) hbase
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hbase⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm,
        hchild, hwrap, hparent, hexpand⟩
    · exact hflat7 inp o res hwf hframed (hsep inp o res)
        (hseam1 inp o res hwf hframed) (hseam2 inp o res hwf hframed) hbase
    · obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        hsub fuel inp o group P metric titleLines child parent
          hwf hframed hP hm hwrap hchild hparent
      have hchildC7 := ih _ _ _ hwfChild hframedChild hchild
      have hparentC7 := ih _ _ _ hwfParent hframedParent hparent
      have hparams : ExpandChildCallParams P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) :=
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      have hctx : ExpandChildCallContextB base fuel P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) parent child res :=
        ⟨hwf, hg, rfl, hchild, hparent, hexpand⟩
      have hstep := hgeo fuel P inp o group titleLines
        ((max 1 titleLines.length : Int) * P.lineH) parent child res
        hexpand hframed hctx hparams
      exact expandChild_c7 hchildC7 hparentC7 hstep hexpand

/-- `layoutRecursiveB` preserves C8a from the flat B fact, the sub-input fact
over `layoutRecursiveB base`, and a per-call step over
`ExpandChildCallContextB` followed by `ExpandChildCallParams`. -/
theorem layoutRecursiveB_c8a
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat8a : FlatC8aB base)
    (hsub : ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
      (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
      (child parent : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      checkedParams o.profile inp.kind = .ok P →
      metricOf o.profile = .ok metric →
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
          group.id).toList = .ok titleLines →
      layoutRecursiveB base fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child →
      layoutRecursiveB base fuel
        (parentSubInput inp group P titleLines child) o = .ok parent →
      WellFormed (inputModel (childSubInput inp group)
        (childSubOptions o group)) ∧
      framedParents (childSubInput inp group) = true ∧
      WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
      framedParents (parentSubInput inp group P titleLines child) = true)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C8a res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hframed h
    have hbase : base inp o = .ok res := by simpa [layoutRecursiveB] using h
    exact hflat8a inp o res hwf hframed hbase
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hbase⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm,
        hchild, hwrap, hparent, hexpand⟩
    · exact hflat8a inp o res hwf hframed hbase
    · obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        hsub fuel inp o group P metric titleLines child parent
          hwf hframed hP hm hwrap hchild hparent
      have hchildC8a := ih _ _ _ hwfChild hframedChild hchild
      have hparentC8a := ih _ _ _ hwfParent hframedParent hparent
      have hparams : ExpandChildCallParams P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) :=
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      have hctx : ExpandChildCallContextB base fuel P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) parent child res :=
        ⟨hwf, hg, rfl, hchild, hparent, hexpand⟩
      have hstep := hgeo fuel P inp o group titleLines
        ((max 1 titleLines.length : Int) * P.lineH) parent child res
        hexpand hframed hctx hparams
      exact expandChild_c8a hchildC8a hparentC8a hstep hexpand

/-- `layoutRecursiveB` preserves C8b from the flat B fact, the sub-input fact
over `layoutRecursiveB base`, and a per-call step over
`ExpandChildCallContextB` followed by `ExpandChildCallParams`. -/
theorem layoutRecursiveB_c8b
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat8b : FlatC8bB base)
    (hsub : ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
      (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
      (child parent : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      checkedParams o.profile inp.kind = .ok P →
      metricOf o.profile = .ok metric →
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
          group.id).toList = .ok titleLines →
      layoutRecursiveB base fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child →
      layoutRecursiveB base fuel
        (parentSubInput inp group P titleLines child) o = .ok parent →
      WellFormed (inputModel (childSubInput inp group)
        (childSubOptions o group)) ∧
      framedParents (childSubInput inp group) = true ∧
      WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
      framedParents (parentSubInput inp group P titleLines child) = true)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C8b res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hframed h
    have hbase : base inp o = .ok res := by simpa [layoutRecursiveB] using h
    exact hflat8b inp o res hwf hframed hbase
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hbase⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm,
        hchild, hwrap, hparent, hexpand⟩
    · exact hflat8b inp o res hwf hframed hbase
    · obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        hsub fuel inp o group P metric titleLines child parent
          hwf hframed hP hm hwrap hchild hparent
      have hchildC8b := ih _ _ _ hwfChild hframedChild hchild
      have hparentC8b := ih _ _ _ hwfParent hframedParent hparent
      have hparams : ExpandChildCallParams P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) :=
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      have hctx : ExpandChildCallContextB base fuel P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) parent child res :=
        ⟨hwf, hg, rfl, hchild, hparent, hexpand⟩
      have hstep := hgeo fuel P inp o group titleLines
        ((max 1 titleLines.length : Int) * P.lineH) parent child res
        hexpand hframed hctx hparams
      exact expandChild_c8b hchildC8b hparentC8b hstep hexpand

end Elegant.Layered.PipelineImpl
