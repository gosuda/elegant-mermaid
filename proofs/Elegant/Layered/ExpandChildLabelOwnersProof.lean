import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.SelectInputWellFormed
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveCallContext

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Label-owner invariant of executed `expandChild` calls (W form).

Proved here:

* `expandChildLabelOwners_holds`: for an executed `expandChild` call — the
  recursion's well-formedness, the `find?` group witness, the two recursive
  successes at the actual `childSubInput`/`parentSubInput`, and the call
  params (`ExpandChildCallContext` + `ExpandChildCallParams`, `framedParents`)
  — both recursive sub-scenes satisfy `ExpandChildLabelOwners`: every label
  of the child (resp. parent) scene carries the owner of the input label with
  the same id. This discharges the `howners` premise that
  `ExactStepRecursionPremisesProof` (`XSRP_stepC7Caption_from_owners`) and
  `ExactStepLeafFactsProof` (`XSGL_stepC7Caption_of_owners`) take.

Proof ingredients (the facts the recursion keeps): the flat label facts
(`elop_sceneOf_label_mem`, `elop_layout_label_mem`: `sceneOf` emits each label
from the input label at the same `zipIdx`, keeping id and owner), the
expansion transport (`elop_expandChild_label_mem`: merged labels keep a
child/parent-scene label's id and owner), the fuel induction
(`elop_layoutRecursive_label_mem`, via `layoutRecursive_succ`), the
`selectInput` label sublist on both sides (`selectInput_labels_sublist`), and
input label-id uniqueness from well-formedness (`labelIds_nodup`, applied via
`expandChild_nodup_map_inj`). The private `elop_*` helpers replay the landed
`expandChild_label_owners` chain at the plain base; no B-form fact is used.

Open (not attempted here): a public B-form copy for the exact
(`layoutX exactIds`) or reindexing bases. `XB_label_owners` and
`RSA_label_owners` stay private to their files; rewiring the two consumer
files named above to a B-form public theorem belongs to the parent.

Probe: `ELOPT_run` below replicates one plain-base `expandChild` call per
input (same group selection, title wrap, and sub-input construction the
recursion performs) and reports whether every child/parent scene label with a
matching input id carries that input label's owner. All five inputs report
`cowners=true powners=true`:

| input | result |
|---|---|
| nested g(a,b) | true true |
| self-loop member a->a,a->b | true true |
| caption label owned by g | true true |
| empty group | true true |
| zero-size fixed child | true true |
-/

/-- Every label `sceneOf` emits comes from the input label at the same
`zipIdx` position, keeping its id and owner. Copies the landed flat fact at
the plain base. -/
private theorem elop_sceneOf_label_mem (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel) :
    ∀ sl ∈ (sceneOf P inp o lines acc measured).labels,
      ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  simp only [sceneOf]
  intro sl hsl
  obtain ⟨q, hq, hmem⟩ := List.mem_filterMap.mp hsl
  obtain ⟨q1, q2⟩ := q
  have key : sl.id = q1.id ∧ sl.owner = q1.owner := by
    dsimp only at hmem
    split at hmem
    · simp at hmem
    · split at hmem
      · next label hfind =>
        have hid : sl.id = q1.id :=
          (congrArg (fun s => s.toLabel.id) (Option.some.inj hmem)).symm
        have hown : sl.owner = q1.owner :=
          (congrArg (fun s => s.toLabel.owner) (Option.some.inj hmem)).symm
        exact ⟨hid, hown⟩
      · next hfind =>
        split at hmem
        · simp at hmem
        · next idx hidx =>
          have hid : sl.id = q1.id :=
            (congrArg (fun s => s.toLabel.id) (Option.some.inj hmem)).symm
          have hown : sl.owner = q1.owner :=
            (congrArg (fun s => s.toLabel.owner) (Option.some.inj hmem)).symm
          exact ⟨hid, hown⟩
  exact ⟨q1, List.fst_mem_of_mem_zipIdx hq, key.1.symm, key.2.symm⟩

/-- Flat layouts keep label ids and owners: every scene label comes from an
input label with the same id and owner. Copies the landed flat fact. -/
private theorem elop_layout_label_mem {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  unfold layout at h
  dsimp only at h
  obtain ⟨P, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨lines, _, h⟩ := bind_ok h
  obtain ⟨measured, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have heq := Except.ok.inj h
    subst heq
    intro sl hsl
    exact elop_sceneOf_label_mem P inp o lines acc measured sl hsl

/-- A successful `expandChild` labels every merged label from a child- or
parent-scene label, keeping its id and owner (the group caption only moves
the rect). Copies the landed expansion fact (base-independent). -/
private theorem elop_expandChild_label_mem
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res) :
    ∀ rl ∈ res.scene.labels,
      ∃ s ∈ child.scene.labels ++ parent.scene.labels,
        rl.id = s.id ∧ rl.owner = s.owner := by
  obtain ⟨frame₀, metric₀, tl₀, _, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _,
    hdx₀, hdy₀, _, _⟩ := expandChild_sources h
  have hwrap : ExpandChildTitleWrapped P inp o group tl₀ := ⟨metric₀, hmetric₀, htitle₀⟩
  have hlabels :=
    expandChild_labels_eq_wrapped h frame₀ tl₀ dx₀ dy₀ hframe₀ hdx₀ hdy₀ hwrap
  intro rl hrl
  rw [hlabels] at hrl
  obtain ⟨model, _, hdo⟩ := List.mem_filterMap.mp hrl
  cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
      { label with rect := shiftRect dx₀ dy₀ label.rect }) ++
      parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) with
  | none => rw [hfind] at hdo; simp at hdo
  | some label =>
    rw [hfind, Option.bind_some] at hdo
    have hif := Option.some.inj hdo
    by_cases hcond : (model.owner == group.id) = true
    · rw [hcond] at hif
      simp only [reduceIte] at hif
      have hid : rl.id = label.id := by rw [← hif]
      have hown : rl.owner = label.owner := by rw [← hif]
      have hmem2 := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hmem2 with hcl | hpl
      · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
        have e1 : label.id = cl.id := by rw [← hclEq]
        have e2 : label.owner = cl.owner := by rw [← hclEq]
        exact ⟨cl, List.mem_append_left _ hclmem, hid.trans e1, hown.trans e2⟩
      · exact ⟨label, List.mem_append_right _ hpl, hid, hown⟩
    · have hcondF : (model.owner == group.id) = false := by
        cases hb : (model.owner == group.id) with
        | false => rfl
        | true => exact absurd hb hcond
      rw [hcondF] at hif
      simp only [Bool.false_eq_true, reduceIte] at hif
      have hid : rl.id = label.id := by rw [← hif]
      have hown : rl.owner = label.owner := by rw [← hif]
      have hmem2 := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hmem2 with hcl | hpl
      · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
        have e1 : label.id = cl.id := by rw [← hclEq]
        have e2 : label.owner = cl.owner := by rw [← hclEq]
        exact ⟨cl, List.mem_append_left _ hclmem, hid.trans e1, hown.trans e2⟩
      · exact ⟨label, List.mem_append_right _ hpl, hid, hown⟩

/-- Labels of a successful `layoutRecursive` come from input labels with the
same id and owner. By induction on the fuel; the expansion step transports
the property through `selectInput` on both sides. Copies the landed fuel
induction at the plain base. -/
private theorem elop_layoutRecursive_label_mem :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res →
      ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h sl hsl
    exact elop_layout_label_mem h sl hsl
  | succ fuel ih =>
    intro inp o res h sl hsl
    rcases layoutRecursive_succ h with ⟨_, hlayout⟩ |
      ⟨group, _, _, _, child, parent, _, _, _, hchild, hparent, hexpand⟩
    · exact elop_layout_label_mem hlayout sl hsl
    · obtain ⟨s, hsmem, hsId, hsOwn⟩ := elop_expandChild_label_mem hexpand sl hsl
      rcases List.mem_append.mp hsmem with hsc | hsp
      · obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := ih _ _ _ hchild s hsc
        have hsub := selectInput_labels_sublist inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
        exact ⟨mc, hsub.subset hmcmem, hmcId.trans hsId.symm, hmcOwn.trans hsOwn.symm⟩
      · obtain ⟨mp, hmpmem, hmpId, hmpOwn⟩ := ih _ _ _ hparent s hsp
        have hsub := selectInput_labels_sublist inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
        exact ⟨mp, hsub.subset hmpmem, hmpId.trans hsId.symm, hmpOwn.trans hsOwn.symm⟩

/-- The label-owner invariant of one `expandChild` call the recursion
performs (W form): labels of both recursive sub-scenes carry the owner of the
input label with the same id. The recursion keeps exactly these premises in
`ExpandChildCallContext` (well-formedness plus the two recursive successes at
the actual sub-inputs); input label-id uniqueness resolves the owner. -/
theorem expandChildLabelOwners_holds
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildLabelOwners inp parent child := by
  obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctx
  have hnodup : (inp.labels.map (·.id)).Nodup := labelIds_nodup hwf
  have hmemC := elop_layoutRecursive_label_mem _ _ _ _ hchild
  have hmemP := elop_layoutRecursive_label_mem _ _ _ _ hparent
  have hsubC := selectInput_labels_sublist inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hsubP := selectInput_labels_sublist inp
    (fun box => !Compound.inside inp.boxes group.id box.id) ""
  constructor
  · intro cl hcl m hm heq
    obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := hmemC cl hcl
    have hmcIn : mc ∈ inp.labels := hsubC.subset hmcmem
    have heq' : m.id = mc.id := heq.trans hmcId.symm
    have hmmc : m = mc := expandChild_nodup_map_inj (·.id) hnodup hm hmcIn heq'
    rw [hmmc]
    exact hmcOwn
  · intro pl hpl m hm heq
    obtain ⟨mp, hmpmem, hmpId, hmpOwn⟩ := hmemP pl hpl
    have hmpIn : mp ∈ inp.labels := hsubP.subset hmpmem
    have heq' : m.id = mp.id := heq.trans hmpId.symm
    have hmmp : m = mp := expandChild_nodup_map_inj (·.id) hnodup hm hmpIn heq'
    rw [hmmp]
    exact hmpOwn
/-- Nested group with two children; labels on both sides of the split so both
sub-scenes are non-empty (`lg` is owned by the group, `la`/`lb` by members).
Every box is nonexclusive so `sceneOf` emits the labels. -/
def ELOPT_nested : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB", exclusive := false },
      { id := "a", role := .node, parent := "g", exclusive := false },
      { id := "b", role := .node, parent := "g", exclusive := false }]
    routes := []
    texts := ["G", "A", "B"]
    edges := []
    labels := [{ id := "lg", owner := "g", text := "G" },
      { id := "la", owner := "a", text := "A" },
      { id := "lb", owner := "b", text := "B" }] }

/-- Group with a self-loop on member `a` plus `a -> b`. -/
def ELOPT_selfloop : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB", exclusive := false },
      { id := "a", role := .node, parent := "g", exclusive := false },
      { id := "b", role := .node, parent := "g", exclusive := false }]
    routes := [{ id := "e1", fromId := "a", toId := "a" },
      { id := "e2", fromId := "a", toId := "b" }]
    texts := ["G", "A", "B"]
    edges := []
    labels := [{ id := "lg", owner := "g", text := "G" },
      { id := "la", owner := "a", text := "A" },
      { id := "lb", owner := "b", text := "B" }] }

/-- Group with a caption label owned by the group. -/
def ELOPT_caption : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB", exclusive := false },
      { id := "a", role := .node, parent := "g", exclusive := false }]
    routes := []
    texts := ["G", "A"]
    edges := []
    labels := [{ id := "cap", owner := "g", text := "Caption" },
      { id := "la", owner := "a", text := "A" }] }

/-- Degenerate empty group with one group-owned label. -/
def ELOPT_empty : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB", exclusive := false }]
    routes := []
    texts := ["G"]
    edges := []
    labels := [{ id := "lg", owner := "g", text := "G" }] }

/-- Child `a` pinned to a zero-size fixed box. -/
def ELOPT_zerosize : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB", exclusive := false },
      { id := "a", role := .node, parent := "g", exclusive := false },
      { id := "b", role := .node, parent := "g", exclusive := false }]
    routes := []
    texts := ["G", "A", "B"]
    edges := []
    fixedSizes := [("a", { w := 0, h := 0 })]
    labels := [{ id := "lg", owner := "g", text := "G" },
      { id := "la", owner := "a", text := "A" },
      { id := "lb", owner := "b", text := "B" }] }
def ELOPT_opts : Options := {}

/-- Replicate one plain-base `expandChild` call and report the label-owner
invariant on both sub-scenes as `Bool`s. `none` in the input-label lookup is
reported as `true`: the invariant only constrains labels whose id occurs in
the input. -/
def ELOPT_run (inp : Input) (o : Options) : String :=
  let fuel := inp.boxes.length + 1
  match inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
  | none => "no-group"
  | some group =>
    match checkedParams o.profile inp.kind with
    | .error _ => "params"
    | .ok P =>
    match metricOf o.profile with
    | .error _ => "metric"
    | .ok metric =>
      match layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) with
      | .error _ => "child"
      | .ok child =>
      let index := inp.boxes.findIdx? (fun box => box.id == group.id)
      let title := inp.texts.getD (index.getD 0) group.id
      match StyledMeasure.wrap metric
          (Measure.wrapTarget metric.profile P.wrapWidth
            (if o.profile == .cell then o.maxWidth else 0)) title.toList with
      | .error _ => "wrap"
      | .ok titleLines =>
        let titleHeight := (max 1 titleLines.length : Int) * P.lineH
        match layoutRecursive fuel (parentSubInput inp group P titleLines child) o with
        | .error _ => "parent"
        | .ok parent =>
        match expandChild P inp o group titleHeight parent child with
        | .error _ => "expand"
        | .ok res =>
          let cok := child.scene.labels.all (fun cl =>
            match inp.labels.find? (fun m => m.id == cl.id) with
            | none => true
            | some m => m.owner == cl.owner)
          let pok := parent.scene.labels.all (fun pl =>
            match inp.labels.find? (fun m => m.id == pl.id) with
            | none => true
            | some m => m.owner == pl.owner)
          let nres := res.scene.labels.length
          let nc := child.scene.labels.length
          let np := parent.scene.labels.length
          s!"cowners={cok} powners={pok} nc={nc} np={np} nres={nres}"

#eval ELOPT_run ELOPT_nested ELOPT_opts
#eval ELOPT_run ELOPT_selfloop ELOPT_opts
#eval ELOPT_run ELOPT_caption ELOPT_opts
#eval ELOPT_run ELOPT_empty ELOPT_opts
#eval ELOPT_run ELOPT_zerosize ELOPT_opts

end PipelineImpl
end Layered
end Elegant
