import Elegant.Layered.CoordGraph
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem selectInput_box_lookup (inp : Input) (keep : ModelBox → Bool)
    (root : String) (j : Nat) :
    (selectInput inp keep root).boxes[j]? =
      ((inp.boxes.zipIdx.filter fun entry => keep entry.1)[j]?).map
        (fun q => if q.1.parent == root then { q.1 with parent := "" } else q.1) := by
  simp only [selectInput, List.getElem?_map]

private theorem filteredBox_source {inp : Input} {keep : ModelBox → Bool}
    {j : Nat} {q : ModelBox × Nat}
    (hq : (inp.boxes.zipIdx.filter fun entry => keep entry.1)[j]? = some q) :
    inp.boxes[q.2]? = some q.1 ∧ keep q.1 = true := by
  have hmem := List.mem_filter.mp (List.mem_of_getElem? hq)
  exact ⟨List.mem_zipIdx_iff_getElem?.mp hmem.1, hmem.2⟩

/-- A selected box and its caption come from the same source occurrence, even
when the source text list falls back to the box ID. -/
theorem selectInput_box_caption_source {inp : Input} (keep : ModelBox → Bool)
    (root : String) {j : Nat} {box : ModelBox}
    (hbox : (selectInput inp keep root).boxes[j]? = some box) :
    ∃ q : ModelBox × Nat,
      (inp.boxes.zipIdx.filter fun entry => keep entry.1)[j]? = some q ∧
      inp.boxes[q.2]? = some q.1 ∧ keep q.1 = true ∧
      box.id = q.1.id ∧ box.role = q.1.role ∧ box.exclusive = q.1.exclusive ∧
      (selectInput inp keep root).texts[j]? = some (inp.texts.getD q.2 q.1.id) ∧
      (selectInput inp keep root).texts.getD j box.id = inp.texts.getD q.2 q.1.id := by
  rw [selectInput_box_lookup] at hbox
  obtain ⟨q, hq, hselected⟩ := Option.map_eq_some_iff.mp hbox
  obtain ⟨hsource, hkeep⟩ := filteredBox_source (inp := inp) (keep := keep) hq
  have hfields : box.id = q.1.id ∧ box.role = q.1.role ∧ box.exclusive = q.1.exclusive := by
    rw [← hselected]
    split <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hid, hrole, hexcl⟩ := hfields
  have htext := selectInput_caption_at inp keep root j q hq
  refine ⟨q, hq, hsource, hkeep, hid, hrole, hexcl, htext, ?_⟩
  rw [List.getD_eq_getElem?_getD, htext, Option.getD_some]

theorem childSubInput_box_caption_source {inp : Input} (group : ModelBox)
    {j : Nat} {box : ModelBox}
    (hbox : (childSubInput inp group).boxes[j]? = some box) :
    ∃ q : ModelBox × Nat,
      (inp.boxes.zipIdx.filter fun entry =>
        Compound.inside inp.boxes group.id entry.1.id)[j]? = some q ∧
      inp.boxes[q.2]? = some q.1 ∧ Compound.inside inp.boxes group.id q.1.id = true ∧
      box.id = q.1.id ∧ box.role = q.1.role ∧ box.exclusive = q.1.exclusive ∧
      (childSubInput inp group).texts[j]? = some (inp.texts.getD q.2 q.1.id) ∧
      (childSubInput inp group).texts.getD j box.id = inp.texts.getD q.2 q.1.id :=
  selectInput_box_caption_source (inp := inp)
    (fun source => Compound.inside inp.boxes group.id source.id) group.id hbox

/-- The fixed frame inserted by the recursion changes none of the selected
boxes or caption slots. -/
theorem parentSubInput_box_caption_source {inp : Input} (group : ModelBox) (P : Params)
    (titleLines : List Measure.Line) (child : FamilyResult) {j : Nat} {box : ModelBox}
    (hbox : (parentSubInput inp group P titleLines child).boxes[j]? = some box) :
    ∃ q : ModelBox × Nat,
      (inp.boxes.zipIdx.filter fun entry =>
        !Compound.inside inp.boxes group.id entry.1.id)[j]? = some q ∧
      inp.boxes[q.2]? = some q.1 ∧ (!Compound.inside inp.boxes group.id q.1.id) = true ∧
      box.id = q.1.id ∧ box.role = q.1.role ∧ box.exclusive = q.1.exclusive ∧
      (parentSubInput inp group P titleLines child).texts[j]? =
        some (inp.texts.getD q.2 q.1.id) ∧
      (parentSubInput inp group P titleLines child).texts.getD j box.id =
        inp.texts.getD q.2 q.1.id :=
  selectInput_box_caption_source (inp := inp)
    (fun source => !Compound.inside inp.boxes group.id source.id) "" hbox

private theorem boxLines_wrap_at {inp : Input} {metric : Measure.Metric} {target : Int}
    {lines : List (List Measure.Line)} (h : boxLines metric target inp = .ok lines)
    {i : Nat} {box : ModelBox} (hbox : inp.boxes[i]? = some box) :
    StyledMeasure.wrap metric target (inp.texts.getD i box.id).toList =
      .ok (lines.getD i []) := by
  have hz : (inp.boxes.zipIdx)[i]? = some (box, i) := by
    simp only [List.getElem?_zipIdx, hbox, Option.map_some, Nat.zero_add]
  unfold boxLines at h
  obtain ⟨ls, hwrap, hls⟩ := (mapM_getElem? _ _ _ h).2 i (box, i) hz
  simpa only [List.getD_eq_getElem?_getD, hls, Option.getD_some] using hwrap

/-- Successful wrapping at the same metric and target preserves the line slot
of a selected caption at its filtered index. -/
theorem selectInput_boxLines_getD {inp : Input} (keep : ModelBox → Bool) (root : String)
    {j : Nat} {q : ModelBox × Nat}
    (hq : (inp.boxes.zipIdx.filter fun entry => keep entry.1)[j]? = some q)
    {metric : Measure.Metric} {target : Int} {lines subLines : List (List Measure.Line)}
    (hwhole : boxLines metric target inp = .ok lines)
    (hsub : boxLines metric target (selectInput inp keep root) = .ok subLines) :
    subLines.getD j [] = lines.getD q.2 [] := by
  have hbox : (selectInput inp keep root).boxes[j]? =
      some (if q.1.parent == root then { q.1 with parent := "" } else q.1) := by
    simp only [selectInput_box_lookup, hq, Option.map_some]
  have htext := selectInput_caption_at inp keep root j q hq
  have hwSub := boxLines_wrap_at hsub hbox
  rw [List.getD_eq_getElem?_getD, htext, Option.getD_some] at hwSub
  have hwWhole := boxLines_wrap_at hwhole (filteredBox_source (inp := inp) (keep := keep) hq).1
  exact Except.ok.inj (hwSub.symm.trans hwWhole)

end Elegant.Layered.PipelineImpl
