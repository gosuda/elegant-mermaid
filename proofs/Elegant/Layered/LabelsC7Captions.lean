import Elegant.Layered.LabelsC7
import Elegant.Layered.LabelsC8b

set_option autoImplicit false

/-! # Flat layered C7, caption seam

`PipelineImpl.label_source_split` splits the labels of a successful flat
`PipelineImpl.layout` into measured route labels and owner captions.  The
route-label half is `LabelRunsClearExclusiveBoxes` (`Layered/LabelsC7.lean`);
this file reduces the caption half, `SceneCaptionBoxContainment`, to one
executed geometric fact.

The reduction is complete: it identifies the emitted caption label with the
`sceneOf` construction (owner box at the model index that
`inp.boxes.findIdx?` selects, installed title when `packedAcc.titles` carries
one, `ownedTextRect` fallback otherwise) and passes the validator scope
`labelOwnerAnc` through unchanged.  `Label.owner` is the only field
`labelOwnerAnc` reads for a box-owned label (its `routes.find?` test is on
`owner`), so the identification needs no route analysis here.

The remaining geometric content is `CaptionScopeClearance`: the caption rect
of the non-exclusive owner at `ownerIndex` misses every exclusive dump box
outside the owner's validator scope.  Its discharge splits three ways.

* Cross component: `Pack.pack_components_disjoint` (plus part hull bounds)
  separates the owner's packed box from `b`'s, and the caption lies in the
  owner's dump rect (`SceneExecution.scene_caption_box_containment` for an
  installed title, the `ownedTextRect`/`titleRect` insets for the fallback).
* Same component, `b` a descendant of the owner group: the caption is the
  cluster-pad title band of `frameRect` (`componentTitles`), and exclusive
  member boxes sit below it — `component_caption_cross_axis_reservation`,
  `component_group_caption_rank_fit`, and the bottom conjunct of
  `PipelineImpl.FrameClearance`.
* Same component, `b` in another subtree: the owner frame/rect separation
  (`componentRun_positions_disjoint` for border-0 owners, the hull separation
  of `layout_c8a` for group owners).

None of those three mechanisms is stated as one lemma yet; this file keeps
the single fact that combines them, with the scene-label plumbing discharged. -/

namespace Elegant.Layered

namespace PipelineImpl

/-- The scene-coordinate caption rect that `sceneOf` gives the label owned by
the model box at `ownerIndex` (`owner` is that box's id): the installed title's
measured rect when the packed accumulator carries one for the owner, and the
`ownedTextRect` fallback otherwise.  This is the exact `find?`/`map`/`getD`
expression of `sceneOf`. -/
def sceneCaptionRect (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (packed : Acc)
    (ownerIndex : Nat) (owner : String) : Rect :=
  ((sceneTitlesExpr P inp o lines packed).find? (fun title => title.1 == owner)).map
      (·.2) |>.getD
    (ownedTextRect P
      ((sceneBoxesExpr P inp o packed).getD ownerIndex ⟨"", "", default, "", false⟩)
      (lines.getD ownerIndex []))

end PipelineImpl

/-- The caption label that the seam reasons about, built from the executed
caption data (`Label.owner` is what `labelOwnerAnc` reads). -/
def captionLabel (inp : Input) (o : Options) (res : FamilyResult)
    (execution : PipelineImpl.SceneExecution inp o res) (ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) : Label :=
  ⟨source.id, source.owner,
    PipelineImpl.sceneCaptionRect execution.params inp o execution.lines
      execution.packedAcc ownerIndex source.owner, lines⟩

/-- The single missing geometric fact of the caption seam: the caption rect of
the non-exclusive owner box at `ownerIndex` does not meet the interior of any
exclusive dump box outside that owner's validator scope.  Stated on the
executed `sceneOf` data (`sceneCaptionRect`), not on the seam's label. -/
def CaptionScopeClearance (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (captionLabel inp o res execution ownerIndex source lines) →
    ¬ (PipelineImpl.sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- For a caption label no dump route carries the owner id, so `labelOwnerAnc`
is the box branch: the owner and its proper ancestors. -/
theorem labelOwnerAnc_of_no_route {d : LayoutDump} {l : Label}
    (h : d.routes.find? (fun r => r.id == l.owner) = none) :
    d.labelOwnerAnc l = l.owner :: d.ancestors l.owner := by
  unfold LayoutDump.labelOwnerAnc
  rw [h]

/-- The scope exclusion of the caption seam in box-scope form: a box outside
`labelOwnerAnc` is neither the owner nor one of its proper ancestors. -/
theorem not_mem_of_labelOwnerAnc {d : LayoutDump} {l : Label} {id : String}
    (hno : d.routes.find? (fun r => r.id == l.owner) = none)
    (h : id ∉ d.labelOwnerAnc l) : id ≠ l.owner ∧ id ∉ d.ancestors l.owner := by
  rw [labelOwnerAnc_of_no_route hno] at h
  exact ⟨fun hid => h (hid ▸ List.mem_cons_self), fun hmem => h (List.mem_cons_of_mem _ hmem)⟩

/-- `labelOwnerAnc` of a label reads only the owner (its route test is on
`owner`, and the box branch chains `owner` through `ancestors`). -/
theorem labelOwnerAnc_congr_owner {d : LayoutDump} {a b : Label} (h : a.owner = b.owner) :
    d.labelOwnerAnc a = d.labelOwnerAnc b := by
  unfold LayoutDump.labelOwnerAnc
  rw [h]

/-- `eraseDups` never lengthens a string list. -/
private theorem caption_eraseDups_length_le : ∀ l : List String, l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have h1 := caption_eraseDups_length_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons]
    omega
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A string list whose `eraseDups` keeps the length has no duplicates. -/
private theorem caption_nodup_of_eraseDups_length :
    ∀ l : List String, l.eraseDups.length = l.length → l.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: as => by
    intro h
    rw [List.eraseDups_cons] at h
    simp only [List.length_cons] at h
    have h1 := caption_eraseDups_length_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    have hf : (as.filter fun b => !b == a).length = as.length := by omega
    have hall : ∀ b ∈ as, (!b == a) = true := List.length_filter_eq_length_iff.mp hf
    have hfe : (as.filter fun b => !b == a) = as := List.filter_eq_self.mpr hall
    have hn := caption_nodup_of_eraseDups_length (as.filter fun b => !b == a) (by omega)
    rw [hfe] at hn
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, hn⟩
    have := hall a hmem
    simp at this
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Model labels in a well-formed model have distinct ids. -/
theorem labelIds_nodup {m : Model} (h : WellFormed m) : (m.labels.map (·.id)).Nodup := by
  unfold WellFormed modelWellFormed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hl⟩, _⟩, _⟩, _⟩, _⟩ := h
  have hl' : ((m.labels.map (·.id)).eraseDups.length == (m.labels.map (·.id)).length) = true := hl
  exact caption_nodup_of_eraseDups_length _ (beq_iff_eq.mp hl')

/-- Two positions of a model label list whose labels share an id are equal. -/
private theorem caption_index_eq_of_id_eq {l : List ModelLabel}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelLabel}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hil : i < (l.map (·.id)).length := by rw [List.length_map]; exact hin
  have hjl : j < (l.map (·.id)).length := by rw [List.length_map]; exact hjn
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have hv : (l.map (·.id))[i] = (l.map (·.id))[j] := by
    have e1 : (l.map (·.id))[i]? = some ((l.map (·.id))[i]) :=
      List.getElem?_eq_getElem hil
    have e2 : (l.map (·.id))[j]? = some ((l.map (·.id))[j]) :=
      List.getElem?_eq_getElem hjl
    exact Option.some.inj (e1.symm.trans (hget.trans e2))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j hil hjl hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i hjl hil hjt)
    · omega

/-- The caption seam of flat clause 7 follows from the executed caption
clearance fact: `sceneOf` emits the caption label at the `ownedTextRect`/title
rect of the owner box `inp.boxes.findIdx?` selects, and `labelOwnerAnc` reads
only that owner. -/
theorem sceneCaptionBoxContainment {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hclear : CaptionScopeClearance inp o res) :
    SceneCaptionBoxContainment inp o res := by
  intro execution l index source hl hsrc hid hmeas howner b hb hex hscope
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨lmodel, lindex⟩ := q
  have hsrcL : inp.labels[lindex]? = some lmodel := List.mem_zipIdx_iff_getElem?.mp hq
  have hlabelNodes := labelIds_nodup hwf
  cases hexcl : inp.boxes.any
      (fun box => box.id == lmodel.owner && box.exclusive) with
  | true =>
    rw [hexcl] at hemitted
    simp only [↓reduceIte] at hemitted
    cases hemitted
  | false =>
    rw [hexcl] at hemitted
    simp only at hemitted
    cases hm : execution.measured.find? (fun item => item.index == lindex) with
    | some measured =>
      rw [hm] at hemitted
      have heq : l = _ := (Option.some.inj hemitted).symm
      have hidEq : lmodel.id = source.id := by
        have h1 : l.id = lmodel.id := by rw [heq]
        exact h1.symm.trans hid
      have hindex : lindex = index :=
        caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
      rw [hindex] at hm
      rw [hm] at hmeas
      cases hmeas
    | none =>
      rw [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == lmodel.owner && !box.exclusive) with
      | none =>
        rw [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        rw [ho] at hemitted
        have heq : l = _ := (Option.some.inj hemitted).symm
        have hidEq : lmodel.id = source.id := by
          have h1 : l.id = lmodel.id := by rw [heq]
          exact h1.symm.trans hid
        have hindex : lindex = index :=
          caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
        rw [hindex] at hsrcL
        have hlmodel : lmodel = source := Option.some.inj (hsrcL.symm.trans hsrc)
        have hoS : inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex := by
          rw [← hlmodel]
          exact ho
        -- the caption rect of the emitted label
        have hrect : l.rect = PipelineImpl.sceneCaptionRect execution.params inp o
            execution.lines execution.packedAcc ownerIndex source.owner := by
          rw [congrArg (fun s : SceneLabel => s.rect) heq]
          unfold PipelineImpl.sceneCaptionRect
          rw [hlmodel]
          rw [(Elegant.Layered.PipelineImpl.straightenAcc_fields execution.straight_eq).1,
            execution.straight_titles, execution.straight_canvasH]
          rfl
        -- the validator scope of the caption label
        have hscope' : b.id ∉ res.scene.layoutDump.labelOwnerAnc
            (captionLabel inp o res execution ownerIndex source l.lines) := by
          have hown : (captionLabel inp o res execution ownerIndex source l.lines).owner =
              l.toLabel.owner := by
            simp only [captionLabel]
            have h2 : l.owner = source.owner := by
              rw [congrArg (fun s : SceneLabel => s.owner) heq]
              rw [hlmodel]
            rw [h2]
          rw [labelOwnerAnc_congr_owner hown]
          exact hscope
        have hclr := hclear execution index ownerIndex source l.lines b hsrc
          (by rw [hindex] at hm; exact hm) hoS hb hex hscope'
        rw [hrect]
        exact hclr
