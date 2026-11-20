import Elegant.Layered.Pipeline
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.SceneBounds
import Elegant.Layered.SizingFacts
import Elegant.Layered.LabelsC8bFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

def FixedSizesPositive (inp : Input) : Prop :=
  ∀ entry ∈ inp.fixedSizes, 0 < entry.2.w ∧ 0 < entry.2.h

theorem FixedSizesPositive.childSubInput {inp : Input}
    (h : FixedSizesPositive inp) (group : ModelBox) :
    FixedSizesPositive (PipelineImpl.childSubInput inp group) := h

/-- Caption room inside a fixed-size box. A group needs its title block strictly
inside the frame; a node needs its wrapped lines to fit the frame height. -/
def FixedSizeFit (P : Params) (role : BoxRole) (lines : List Measure.Line) (size : Size) : Prop :=
  match role with
  | .group => 2 * P.clusterPad ≤ size.w ∧
      P.clusterPad + (max 1 lines.length : Int) * P.lineH < size.h
  | .node => (lines.length : Int) * P.lineH ≤ size.h

/-- Input-level fit premise: every fixed-size entry naming a non-exclusive box
that owns a label fits that box's wrapped caption. Exclusive owners emit no
scene label, so they need no caption room. -/
def InputFixedFit (inp : Input) (o : Options) : Prop :=
  ∀ (entry : String × Size), entry ∈ inp.fixedSizes →
  ∀ (i : Nat) (box : ModelBox), inp.boxes[i]? = some box → box.id = entry.1 →
    box.exclusive = false → (∃ l ∈ inp.labels, l.owner = box.id) →
  ∀ (P : Params) (metric : Measure.Metric) (lines : List Measure.Line),
    checkedParams o.profile inp.kind = .ok P → metricOf o.profile = .ok metric →
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD i box.id).toList = .ok lines →
    FixedSizeFit P box.role lines entry.2

theorem FixedSizeFit.mono {P : Params} {role : BoxRole} {lines : List Measure.Line}
    {s s' : Size} (h : FixedSizeFit P role lines s)
    (hw : s.w ≤ s'.w) (hh : s.h ≤ s'.h) :
    FixedSizeFit P role lines s' := by
  cases role <;> simp only [FixedSizeFit] at h ⊢ <;> omega

theorem inputFixedFit_of_nil {inp : Input} {o : Options}
    (h : inp.fixedSizes = []) : InputFixedFit inp o := by
  intro entry hentry
  rw [h] at hentry
  simp at hentry

theorem inputFixedFit_of_fixedExclusive {inp : Input} {o : Options}
    (h : ∀ entry ∈ inp.fixedSizes, ∀ box ∈ inp.boxes,
      box.id = entry.1 → box.exclusive = true) :
    InputFixedFit inp o := by
  intro entry hentry i box hbox hid hexcl
  have hmem : box ∈ inp.boxes := List.mem_of_getElem? hbox
  have hex := h entry hentry box hmem hid
  rw [hexcl] at hex
  simp at hex

/-- Indexed `selectInput` transport: the kept box keeps id, role and exclusive,
and its caption is the source caption. -/
private theorem selectInput_indexed {inp : Input} (keep : ModelBox → Bool) (root : String)
    {i : Nat} {box : ModelBox} (hbox : (selectInput inp keep root).boxes[i]? = some box) :
    ∃ q, (inp.boxes.zipIdx.filter fun q => keep q.1)[i]? = some q ∧
      box.id = q.1.id ∧ box.role = q.1.role ∧ box.exclusive = q.1.exclusive ∧
      inp.boxes[q.2]? = some q.1 ∧
      (selectInput inp keep root).texts.getD i box.id = inp.texts.getD q.2 q.1.id := by
  unfold selectInput at hbox
  dsimp only at hbox
  rw [List.getElem?_map] at hbox
  obtain ⟨q, hq, hqb⟩ := Option.map_eq_some_iff.mp hbox
  have hidq : box.id = q.1.id := by rw [← hqb]; split <;> rfl
  have hroleq : box.role = q.1.role := by rw [← hqb]; split <;> rfl
  have hexq : box.exclusive = q.1.exclusive := by rw [← hqb]; split <;> rfl
  have hqmem : q ∈ inp.boxes.zipIdx.filter fun q => keep q.1 := by
    obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hq
    rw [← hget]
    exact List.getElem_mem hi
  have hsrc : inp.boxes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hqmem).1
  have hcap := selectInput_caption_at inp keep root i q hq
  have htext : (selectInput inp keep root).texts.getD i box.id = inp.texts.getD q.2 q.1.id := by
    rw [List.getD_eq_getElem?_getD, hcap, Option.getD_some]
  exact ⟨q, hq, hidq, hroleq, hexq, hsrc, htext⟩

/-- Shared transport of `InputFixedFit` across a box-filtering sub-input whose
fixed sizes, box identities and captions come from the source input. -/
private theorem select_transport {inp : Input} {o : Options}
    (h : InputFixedFit inp o) (keep : ModelBox → Bool)
    {o' : Options} (hp : o'.profile = o.profile) (hm : o'.maxWidth = o.maxWidth)
    {inp' : Input} (hkind : inp'.kind = inp.kind)
    (hfix : ∀ entry : String × Size, entry ∈ inp'.fixedSizes → entry ∈ inp.fixedSizes)
    (hidx : ∀ (i : Nat) (box : ModelBox), inp'.boxes[i]? = some box →
      ∃ q, (inp.boxes.zipIdx.filter fun q => keep q.1)[i]? = some q ∧
        box.id = q.1.id ∧ box.role = q.1.role ∧ box.exclusive = q.1.exclusive ∧
        inp.boxes[q.2]? = some q.1 ∧
        inp'.texts.getD i box.id = inp.texts.getD q.2 q.1.id)
    (hlabels : ∀ l : ModelLabel, l ∈ inp'.labels → l ∈ inp.labels) :
    InputFixedFit inp' o' := by
  intro entry hentry i box hbox hid hexcl hown P' metric' lines' hP' hm' hwrap'
  have hentry' := hfix entry hentry
  obtain ⟨q, hq, hidq, hroleq, hexq, hsrc, htext⟩ := hidx i box hbox
  obtain ⟨l, hlin, hlown⟩ := hown
  have hP'' : checkedParams o.profile inp.kind = .ok P' := by
    have hrew := hP'
    rw [hp, hkind] at hrew
    exact hrew
  have hm'' : metricOf o.profile = .ok metric' := by
    have hrew := hm'
    rw [hp] at hrew
    exact hrew
  have hwrap'' : StyledMeasure.wrap metric'
      (Measure.wrapTarget metric'.profile P'.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD q.2 q.1.id).toList = .ok lines' := by
    have htm : ((if o'.profile == .cell then o'.maxWidth else 0) : Int) =
        ((if o.profile == .cell then o.maxWidth else 0) : Int) := by rw [hp, hm]
    rw [htm, htext] at hwrap'
    exact hwrap'
  have hfit := h entry hentry' q.2 q.1 hsrc (hidq.symm.trans hid) (hexq.symm.trans hexcl)
    ⟨l, hlabels l hlin, hlown.trans hidq⟩ P' metric' lines' hP'' hm'' hwrap''
  rw [hroleq]
  exact hfit

theorem InputFixedFit.selectInput {inp : Input} {o : Options}
    (h : InputFixedFit inp o) (keep : ModelBox → Bool) (root : String)
    {o' : Options} (hp : o'.profile = o.profile) (hm : o'.maxWidth = o.maxWidth) :
    InputFixedFit (Elegant.Layered.PipelineImpl.selectInput inp keep root) o' := by
  have hkind : (Elegant.Layered.PipelineImpl.selectInput inp keep root).kind = inp.kind := rfl
  have hfix : ∀ entry : String × Size,
      entry ∈ (Elegant.Layered.PipelineImpl.selectInput inp keep root).fixedSizes →
      entry ∈ inp.fixedSizes := fun _ he => he
  exact select_transport h keep hp hm hkind hfix
    (fun i box hbox => selectInput_indexed _ _ hbox)
    (fun l hl => (List.mem_filter.mp hl).1)

theorem InputFixedFit.childSubInput {inp : Input} {o : Options}
    (h : InputFixedFit inp o) (group : ModelBox) :
    InputFixedFit (Elegant.Layered.PipelineImpl.childSubInput inp group)
      (Elegant.Layered.PipelineImpl.childSubOptions o group) := by
  show InputFixedFit
    (Elegant.Layered.PipelineImpl.selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id)
    { o with direction := directionOf group.direction }
  exact h.selectInput _ _ rfl rfl

theorem childFrameSize_fixedSizeFit (role : BoxRole) (P : Params) (dir : String)
    (titleLines : List Measure.Line) (content : Size)
    (hcp : 0 < P.clusterPad) (hl : 0 ≤ P.lineH)
    (hcw : 0 ≤ content.w) (hch : 0 ≤ content.h) :
    FixedSizeFit P role titleLines
      (childFrameSize dir P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        content) := by
  obtain ⟨hw, hh⟩ := childFrameSize_title_fit dir P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    content hcw hch
  have htw0 : 0 ≤ titleLines.foldl (fun width line => max width line.width) 0 := by
    have hgen : ∀ (ls : List Measure.Line) (start : Int), 0 ≤ start →
        0 ≤ ls.foldl (fun width line => max width line.width) start := by
      intro ls start hs
      induction ls generalizing start with
      | nil => simpa using hs
      | cons hd tl ih =>
        simp only [List.foldl_cons]
        have hmax : 0 ≤ max start (hd.width) := by omega
        exact ih _ hmax
    exact hgen _ 0 (by omega)
  have hle : (titleLines.length : Int) ≤ (max 1 titleLines.length : Int) :=
    Int.le_max_right _ _
  have hmul : (titleLines.length : Int) * P.lineH ≤
      (max 1 titleLines.length : Int) * P.lineH :=
    Int.mul_le_mul_of_nonneg_right hle hl
  cases role with
  | group =>
    simp only [FixedSizeFit]
    omega
  | node =>
    simp only [FixedSizeFit]
    exact Int.le_trans hmul (by omega)

theorem FixedSizesPositive.parentSubInput {inp : Input} {o : Options}
    {group : ModelBox} {P : Params} {titleLines : List Measure.Line} {child : FamilyResult}
    (h : FixedSizesPositive inp) (hP : checkedParams o.profile inp.kind = .ok P)
    (hw : 2 * P.canvasMargin ≤ child.scene.canvas.w)
    (hh : 2 * P.canvasMargin ≤ child.scene.canvas.h) :
    FixedSizesPositive (PipelineImpl.parentSubInput inp group P titleLines child) := by
  intro entry he
  change entry ∈ inp.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩)] at he
  rcases List.mem_append.mp he with hprior | hframe
  · exact h entry hprior
  · rw [List.mem_singleton] at hframe
    subst entry
    have hpad := checkedParams_clusterPad_pos hP
    have hline := Int.le_of_lt (checkedParams_lineH_pos hP)
    have hheight : 0 ≤ (max 1 titleLines.length : Int) * P.lineH :=
      Int.mul_nonneg (by omega) hline
    have hfit := childFrameSize_fixedSizeFit .group P group.direction titleLines
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩
      hpad hline (Int.sub_nonneg.mpr hw) (Int.sub_nonneg.mpr hh)
    simp only [FixedSizeFit] at hfit
    exact ⟨Int.lt_of_lt_of_le (by omega) hfit.1, Int.lt_trans (by omega) hfit.2⟩

theorem InputFixedFit.parentSubInput {inp : Input} {o : Options} {group : ModelBox}
    {P : Params} {metric : Measure.Metric} {titleLines : List Measure.Line}
    {child : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : InputFixedFit inp o)
    (hP : checkedParams o.profile inp.kind = .ok P)
    (hm : metricOf o.profile = .ok metric)
    (hwrap : StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
        group.id).toList = .ok titleLines)
    (hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w)
    (hch : 2 * P.canvasMargin ≤ child.scene.canvas.h) :
    InputFixedFit (Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child) o := by
  have hfixeq : (Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).fixedSizes =
      inp.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
  intro entry hentry i box hbox hid hexcl hown P' metric' lines' hP' hm' hwrap'
  rw [hfixeq] at hentry
  rcases List.mem_append.mp hentry with hold | hnew
  · have hsel : InputFixedFit
        (Elegant.Layered.PipelineImpl.selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "") o :=
      h.selectInput _ _ rfl rfl
    exact hsel entry hold i box hbox hid hexcl hown P' metric' lines' hP' hm' hwrap'
  · rw [List.mem_singleton] at hnew
    subst hnew
    clear hexcl hown
    have hPP : P' = P := by
      have h1 := hP'
      have h2 : (Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).kind =
          inp.kind := rfl
      rw [h2] at h1
      exact Except.ok.inj (h1.symm.trans hP)
    have hmm : metric' = metric := Except.ok.inj (hm'.symm.trans hm)
    rw [hPP] at hP' hwrap' ⊢
    rw [hmm] at hm' hwrap'
    clear P' metric' hP' hm' hPP hmm
    have hidg : box.id = group.id := hid
    have hsel_boxes : (Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).boxes =
        (Elegant.Layered.PipelineImpl.selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
    rw [hsel_boxes] at hbox
    obtain ⟨q, hq, hidq, _hroleq, _hexq, hsrc, htextsel⟩ :=
      selectInput_indexed _ "" hbox
    have hsel_texts : (Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).texts =
        (Elegant.Layered.PipelineImpl.selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").texts := rfl
    have htext' : (Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).texts.getD
        i box.id = inp.texts.getD q.2 q.1.id := by
      rw [hsel_texts]
      exact htextsel
    have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
    have hq1id : q.1.id = group.id := hidq.symm.trans hidg
    have hidx : inp.boxes.findIdx? (fun box => box.id == group.id) = some q.2 := by
      have hcap := caption_index_of_unique_ids hnodup hsrc
      rwa [hq1id] at hcap
    have htext2 : inp.texts.getD q.2 q.1.id =
        inp.texts.getD ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
          group.id := by
      rw [hidx]
      simp only [Option.getD_some, hq1id]
    rw [htext', htext2] at hwrap'
    have heq : lines' = titleLines := Except.ok.inj (hwrap'.symm.trans hwrap)
    have hcp : 0 < P.clusterPad := checkedParams_clusterPad_pos hP
    have hline : 0 ≤ P.lineH := Int.le_of_lt (checkedParams_lineH_pos hP)
    have hcw' : 0 ≤ child.scene.canvas.w - 2 * P.canvasMargin := by omega
    have hch' : 0 ≤ child.scene.canvas.h - 2 * P.canvasMargin := by omega
    have hfit := childFrameSize_fixedSizeFit box.role P group.direction titleLines
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩
      hcp hline hcw' hch'
    rw [heq]
    exact hfit

end PipelineImpl
end Layered
end Elegant
