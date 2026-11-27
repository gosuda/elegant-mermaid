import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.SelectInputWellFormed
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

/-!
# Label-owner facts of the recursive `expandChild` step

`expandChild_label_owners` discharges the `stepLabelOwners` seam
(`ExpandChildLabelOwners`): every label of the two recursive sub-scenes
carries the owner of the input label with the same id.

`sceneOf` builds each scene label from the input label at the same `zipIdx`
position, keeping `id` and `owner` verbatim, so the flat case holds without
any uniqueness assumption. `selectInput` keeps labels verbatim (a filter),
so the property lifts through `layoutRecursive` by induction on the fuel as
plain membership; the final owner equality uses the input label-id
uniqueness from `WellFormed`.
-/

namespace Elegant.Layered.PipelineImpl

/-- Every label `sceneOf` emits comes from the input label at the same
`zipIdx` position, keeping its id and owner. -/
private theorem sceneOf_label_mem (P : Params) (inp : Input) (o : Options)
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
input label with the same id and owner. -/
private theorem layout_label_mem {inp : Input} {o : Options} {res : FamilyResult}
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
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have heq := Except.ok.inj h
    subst heq
    intro sl hsl
    exact sceneOf_label_mem P inp o lines acc measured sl hsl

/-- A successful `expandChild` labels every merged label from a child- or
parent-scene label, keeping its id and owner (the group caption only moves
the rect). -/
private theorem expandChild_label_mem
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
the property through `selectInput` on both sides. -/
private theorem layoutRecursive_label_mem :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res →
      ∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h sl hsl
    exact layout_label_mem h sl hsl
  | succ fuel ih =>
    intro inp o res h sl hsl
    rcases layoutRecursive_succ h with ⟨_, hlayout⟩ |
      ⟨group, _, _, _, child, parent, _, _, _, hchild, hparent, hexpand⟩
    · exact layout_label_mem hlayout sl hsl
    · obtain ⟨s, hsmem, hsId, hsOwn⟩ := expandChild_label_mem hexpand sl hsl
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
performs: labels of both recursive sub-scenes carry the owner of the input
label with the same id. -/
theorem expandChild_label_owners
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
  have hmemC := layoutRecursive_label_mem _ _ _ _ hchild
  have hmemP := layoutRecursive_label_mem _ _ _ _ hparent
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

/-! ## Scope residuals and the `stepC7LabelScopes` discharge -/

/-- Ancestor-list monotonicity of the merged dump over both sub-dumps: every
ancestor chain of either sub-scene is contained in the merged dump's chain
for the same id. For executed calls the child chains pass through the group
frame and the parent chains are verbatim, with disjoint box ids; no proved
fact of the expansion supplies the walks, so it stays a residual tied to the
call context through the two `layoutRecursive` successes. -/
def ExpandChildC7AncestorMono (parent child result : FamilyResult) : Prop :=
  (∀ (id x : String),
    x ∈ parent.scene.layoutDump.ancestors id →
      x ∈ result.scene.layoutDump.ancestors id) ∧
  (∀ (id x : String),
    x ∈ child.scene.layoutDump.ancestors id →
      x ∈ result.scene.layoutDump.ancestors id)

/-- Merged route-lookup agreement: the merged dump finds the same endpoints
as the first matching sub-dump (child first, else parent). For executed
calls the merged routes are the shifted child routes then the verbatim
parent routes filtered by input id, with disjoint id sets; the equation bakes
in that disjointness. Sampled true on executed calls. -/
def ExpandChildC7RouteAgreement (parent child result : FamilyResult) : Prop :=
  ∀ (owner : String),
    (result.scene.layoutDump.routes.find? (fun r => r.id == owner)).map
      (fun r => (r.fromId, r.toId)) =
    (((child.scene.layoutDump.routes.find? (fun r => r.id == owner)).map
      (fun r => (r.fromId, r.toId))).orElse (fun _ =>
      ((parent.scene.layoutDump.routes.find? (fun r => r.id == owner)).map
        (fun r => (r.fromId, r.toId)))))

/-- Cross-scene id separation for label owners and the group: a child label
owner resolves no parent route, a parent label owner resolves no child
route, and no sub-scene route is named after the group. For executed calls
box and route id spaces do not collide this way; the probe of 26 executed
calls found no counterexample. Strictly simpler than the scope goal (no
scopes, no merged dump, no group scope list). -/
def ExpandChildC7OwnerSeparation (group : ModelBox) (parent child : FamilyResult) : Prop :=
  (∀ cl ∈ child.scene.labels,
    (parent.scene.layoutDump.routes.find? (fun r => r.id == cl.owner)) = none) ∧
  (∀ pl ∈ parent.scene.labels,
    (child.scene.layoutDump.routes.find? (fun r => r.id == pl.owner)) = none) ∧
  (child.scene.layoutDump.routes.find? (fun r => r.id == group.id)) = none ∧
  (parent.scene.layoutDump.routes.find? (fun r => r.id == group.id)) = none

/-- Child route endpoints name child-scene boxes. Same statement as
`ExpandChildRouteEndpoints` in `ExpandChildAncestryProof` (which lives
outside the checked-in olean closure, so it cannot be imported here); kept
as a local residual tied to the call context until the parent unifies them.
For executed calls scene routes mirror the covered sub-input models. -/
def ExpandChildC7RouteEndpoints (child : FamilyResult) : Prop :=
  ∀ rt ∈ child.scene.routes,
    rt.fromId ∈ child.scene.boxes.map (·.id) ∧
      rt.toId ∈ child.scene.boxes.map (·.id)
/-- Every merged label comes from an input label with the same id and owner
(the group caption only moves the rect). -/
private theorem expandChild_label_model_mem
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res)
    (howners : ExpandChildLabelOwners inp parent child) :
    ∀ rl ∈ res.scene.layoutDump.labels,
      ∃ model ∈ inp.labels, rl.id = model.id ∧ rl.owner = model.owner := by
  obtain ⟨frame₀, metric₀, tl₀, _, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _,
    hdx₀, hdy₀, _, _⟩ := expandChild_sources h
  have hwrap : ExpandChildTitleWrapped P inp o group tl₀ := ⟨metric₀, hmetric₀, htitle₀⟩
  have hlabels :=
    expandChild_labels_eq_wrapped h frame₀ tl₀ dx₀ dy₀ hframe₀ hdx₀ hdy₀ hwrap
  intro rl hrl
  have hrls : rl ∈ res.scene.labels.map (·.toLabel) := hrl
  obtain ⟨sl, hsl, hto⟩ := List.mem_map.mp hrls
  subst hto
  rw [hlabels] at hsl
  obtain ⟨model, hmmem, hdo⟩ := List.mem_filterMap.mp hsl
  cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
      { label with rect := shiftRect dx₀ dy₀ label.rect }) ++
      parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) with
  | none => rw [hfind] at hdo; simp at hdo
  | some label =>
    rw [hfind, Option.bind_some] at hdo
    have hif := Option.some.inj hdo
    have hmem2 := List.mem_of_find?_eq_some hfind
    have hlid : label.id = model.id := by simpa using List.find?_some hfind
    have hlown : label.owner = model.owner := by
      rcases List.mem_append.mp hmem2 with hcl | hpl
      · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
        have e2 : label.owner = cl.owner := by rw [← hclEq]
        have hmid : model.id = cl.id := hlid.symm.trans (by rw [← hclEq])
        exact e2.trans (howners.1 cl hclmem model hmmem hmid).symm
      · exact (howners.2 label hpl model hmmem hlid.symm).symm
    by_cases hcond : (model.owner == group.id) = true
    · rw [hcond] at hif
      simp only [reduceIte] at hif
      exact ⟨model, hmmem, by rw [← hif]; exact hlid, by rw [← hif]; exact hlown⟩
    · have hcondF : (model.owner == group.id) = false := by
        cases hb : (model.owner == group.id) with
        | false => rfl
        | true => exact absurd hb hcond
      rw [hcondF] at hif
      simp only [Bool.false_eq_true, reduceIte] at hif
      exact ⟨model, hmmem, by rw [← hif]; exact hlid, by rw [← hif]; exact hlown⟩

/-- The label-scope invariant of one `expandChild` call the recursion
performs: owner scopes transport from both sub-scenes into the merged dump,
and the group scope anchors every group-owned or child-sourced merged label.
The anchor restriction is load-bearing: stated for every merged label the
claim is false (probe `ExpandChildStepProbe`, `labInOut`/`titleLabel`). -/
theorem expandChild_c7_label_scopes
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child result : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok result)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child result)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hmono : ExpandChildC7AncestorMono parent child result)
    (hagree : ExpandChildC7RouteAgreement parent child result)
    (hsep : ExpandChildC7OwnerSeparation group parent child)
    (hanc : ExpandChildC8aAncestry group parent child result)
    (hendpoints : ExpandChildC7RouteEndpoints child) :
    ExpandChildC7LabelScopes P group parent child result := by
  obtain howners := expandChild_label_owners fuel P inp o group titleLines titleHeight
    parent child result hexpand hframed hctx _hparams
  obtain ⟨_, _, _, hchild, _, _⟩ := hctx
  have hcovC : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp (fun box => Compound.inside inp.boxes group.id box.id) group.id
  have hidsC := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) _ _ _ _ hcovC hchild
  refine ⟨?_, ?_, ?_⟩
  · intro cl hcl rl hrl heq x hx
    obtain ⟨model, hmmem, hmid, hmown⟩ := expandChild_label_model_mem hexpand howners rl hrl
    have hmid' : model.id = cl.id := hmid.symm.trans heq
    have hmo : model.owner = cl.owner := howners.1 cl hcl model hmmem hmid'
    have hro : rl.owner = cl.owner := hmown.trans hmo
    cases hcf : child.scene.layoutDump.routes.find? (fun r => r.id == cl.owner) with
    | some r =>
      have hcscope : child.scene.layoutDump.labelOwnerAnc cl.toLabel =
          child.scene.layoutDump.ancestors r.fromId ++
            child.scene.layoutDump.ancestors r.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hcf]
      have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hro, hcf]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.1 cl hcl]
      have hrm' : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hagree rl.owner, hcm, hpm]
      obtain ⟨r', hr', hef, het⟩ : ∃ r',
          result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = some r' ∧
          r'.fromId = r.fromId ∧ r'.toId = r.toId := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rw [hr'] at hrm'; simp at hrm'
        | some r' =>
          have h2 := hrm'
          simp [hr'] at h2
          exact ⟨r', rfl, h2.1, h2.2⟩
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          result.scene.layoutDump.ancestors r'.fromId ++
            result.scene.layoutDump.ancestors r'.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hr']
      rw [hcscope] at hx
      rw [hrscope] at ⊢
      rw [hef, het] at ⊢
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hmono.2 _ _ h)
      · exact List.mem_append_right _ (hmono.2 _ _ h)
    | none =>
      have hcscope : child.scene.layoutDump.labelOwnerAnc cl.toLabel =
          cl.owner :: child.scene.layoutDump.ancestors cl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hcf]
      have hcm0 : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hcf]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.1 cl hcl]
      have hrm0 : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hagree rl.owner, hcm0, hpm]
      have hrnone : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rfl
        | some r' => rw [hr'] at hrm0; simp at hrm0
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hrnone]
      rw [hcscope] at hx
      rw [hrscope] at ⊢
      rw [hro] at ⊢
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hmono.2 _ _ h))
  · intro pl hpl rl hrl heq x hx
    obtain ⟨model, hmmem, hmid, hmown⟩ := expandChild_label_model_mem hexpand howners rl hrl
    have hmid' : model.id = pl.id := hmid.symm.trans heq
    have hmo : model.owner = pl.owner := howners.2 pl hpl model hmmem hmid'
    have hro : rl.owner = pl.owner := hmown.trans hmo
    cases hpf : parent.scene.layoutDump.routes.find? (fun r => r.id == pl.owner) with
    | some r =>
      have hpscope : parent.scene.layoutDump.labelOwnerAnc pl.toLabel =
          parent.scene.layoutDump.ancestors r.fromId ++
            parent.scene.layoutDump.ancestors r.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hpf]
      have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.2.1 pl hpl]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hro, hpf]
      have hrm' : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
        simp [hagree rl.owner, hcm, hpm]
      obtain ⟨r', hr', hef, het⟩ : ∃ r',
          result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = some r' ∧
          r'.fromId = r.fromId ∧ r'.toId = r.toId := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rw [hr'] at hrm'; simp at hrm'
        | some r' =>
          have h2 := hrm'
          simp [hr'] at h2
          exact ⟨r', rfl, h2.1, h2.2⟩
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          result.scene.layoutDump.ancestors r'.fromId ++
            result.scene.layoutDump.ancestors r'.toId := by
        unfold LayoutDump.labelOwnerAnc
        rw [hr']
      rw [hpscope] at hx
      rw [hrscope] at ⊢
      rw [hef, het] at ⊢
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hmono.1 _ _ h)
      · exact List.mem_append_right _ (hmono.1 _ _ h)
    | none =>
      have hpscope : parent.scene.layoutDump.labelOwnerAnc pl.toLabel =
          pl.owner :: parent.scene.layoutDump.ancestors pl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hpf]
      have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hsep.2.1 pl hpl]
      have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hro, hpf]
      have hrm0 : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hagree rl.owner, hcm, hpm]
      have hrnone : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rfl
        | some r' => rw [hr'] at hrm0; simp at hrm0
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hrnone]
      rw [hpscope] at hx
      rw [hrscope] at ⊢
      rw [hro] at ⊢
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hmono.1 _ _ h))
  · intro rl hrl hsrc x hx
    rcases hsrc with hcap | hchildsrc
    · have hcmG : (child.scene.layoutDump.routes.find? (fun r => r.id == group.id)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hsep.2.2.1]
      have hpmG : (parent.scene.layoutDump.routes.find? (fun r => r.id == group.id)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hsep.2.2.2]
      have hrmG : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
          (fun r => (r.fromId, r.toId)) = none := by
        simp [hcap, hagree group.id, hcmG, hpmG]
      have hresG : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
        cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
        | none => rfl
        | some r' => rw [hr'] at hrmG; simp at hrmG
      have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
          rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
        unfold LayoutDump.labelOwnerAnc
        rw [hresG]
      rw [hrscope, hcap] at ⊢
      rcases List.mem_cons.mp hx with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hmono.1 _ _ h))
    · obtain ⟨cl, hcl, _hid, hown⟩ := hchildsrc
      cases hcf : child.scene.layoutDump.routes.find? (fun r => r.id == cl.owner) with
      | some r =>
        have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hown, hsep.1 cl hcl]
        have hcm : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
          simp [hown, hcf]
        have hrm' : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = some (r.fromId, r.toId) := by
          simp [hagree rl.owner, hcm, hpm]
        obtain ⟨r', hr', hef, het⟩ : ∃ r',
            result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = some r' ∧
            r'.fromId = r.fromId ∧ r'.toId = r.toId := by
          cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
          | none => rw [hr'] at hrm'; simp at hrm'
          | some r' =>
            have h2 := hrm'
            simp [hr'] at h2
            exact ⟨r', rfl, h2.1, h2.2⟩
        have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
            result.scene.layoutDump.ancestors r'.fromId ++
              result.scene.layoutDump.ancestors r'.toId := by
          unfold LayoutDump.labelOwnerAnc
          rw [hr']
        have hrmem : r ∈ child.scene.routes := List.mem_of_find?_eq_some hcf
        obtain ⟨hfbox, _⟩ := hendpoints r hrmem
        obtain ⟨ob, hob, hobid⟩ := List.mem_map.mp hfbox
        have hchain := hanc.1 ob hob x hx
        rw [hobid] at hchain
        rw [hrscope, hef, het] at ⊢
        exact List.mem_append_left _ hchain
      | none =>
        have hpm : (parent.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hown, hsep.1 cl hcl]
        have hcm0 : (child.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hown, hcf]
        have hrm0 : (result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner)).map
            (fun r => (r.fromId, r.toId)) = none := by
          simp [hagree rl.owner, hcm0, hpm]
        have hrnone : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) = none := by
          cases hr' : result.scene.layoutDump.routes.find? (fun r => r.id == rl.owner) with
          | none => rfl
          | some r' => rw [hr'] at hrm0; simp at hrm0
        have hrscope : result.scene.layoutDump.labelOwnerAnc rl =
            rl.owner :: result.scene.layoutDump.ancestors rl.owner := by
          unfold LayoutDump.labelOwnerAnc
          rw [hrnone]
        obtain ⟨mc, hmcmem, _, hmcOwn⟩ :=
          layoutRecursive_label_mem _ _ _ _ hchild cl hcl
        have hmcsub : mc ∈ (selectInput inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id).labels := hmcmem
        have hvalid := selectInput_label_owner inp _ _ mc hmcsub
        have hmo : mc.owner = cl.owner := hmcOwn
        rcases hvalid with hbox | hroute
        · have h1' : mc.owner ∈ (childSubInput inp group).boxes.map (·.id) := hbox
          rw [← hidsC.1] at h1'
          obtain ⟨ob, hob, hobid⟩ := List.mem_map.mp h1'
          have e : ob.id = rl.owner := hobid.trans (hmo.trans hown.symm)
          have hchain := hanc.1 ob hob x hx
          rw [e] at hchain
          rw [hrscope] at ⊢
          exact List.mem_cons.mpr (Or.inr hchain)
        · have h1' : mc.owner ∈ (childSubInput inp group).routes.map (·.id) := hroute
          rw [← hidsC.2] at h1'
          obtain ⟨r, hr, hrid⟩ := List.mem_map.mp h1'
          have hne : child.scene.layoutDump.routes.find? (fun r => r.id == cl.owner) ≠ none := by
            intro hnone
            have hff := List.find?_eq_none.mp hnone r hr
            rw [hrid, hmo] at hff
            simp at hff
          exact absurd hcf hne

end Elegant.Layered.PipelineImpl
