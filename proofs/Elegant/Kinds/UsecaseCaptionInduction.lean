import Elegant.Kinds.UsecaseGroupCaptionTransport
import Elegant.Kinds.UsecaseNodeCaptionNormalForm
import Elegant.Kinds.UsecaseRecursiveLinesTransport
import Elegant.Kinds.UsecaseValid

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

open Layered Layered.PipelineImpl

/-- The unpacked validator label and the display text of a box have the same rectangle. -/
def NonedgeCaptionAgreement (s : Scene) : Prop :=
  ∀ {label : SceneLabel}, label ∈ s.labels → ∀ {display : Group}, display ∈ s.items →
    display.role ≠ .edge → display.owner = label.owner → firstText display.items = some label.rect

private def NodeCaptionAgreement (inp : Input) (s : Scene) : Prop :=
  ∀ {label : SceneLabel}, label ∈ s.labels → ∀ {source : ModelBox}, source ∈ inp.boxes →
    source.role = .node → source.id = label.owner → ∀ {display : Group}, display ∈ s.items →
    display.role ≠ .edge → display.owner = label.owner → firstText display.items = some label.rect

private def LabelOrigins (inp : Input) (s : Scene) : Prop :=
  ∀ {label : SceneLabel}, label ∈ s.labels →
    ∃ model ∈ inp.labels, model.id = label.id ∧ model.owner = label.owner

private theorem caption_box_ids {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) : res.scene.boxes.map Box.id = inp.boxes.map ModelBox.id := by
  have h := congrArg (List.map (Prod.fst : String × String → String)) a.box_keys
  simp only [List.map_map] at h
  exact h

private theorem caption_box_lookup {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) (hids : (inp.boxes.map ModelBox.id).Nodup)
    {box : Box} (hb : box ∈ res.scene.boxes) : res.scene.layoutDump.box? box.id = some box :=
  Assembly.keyed_lookup_eq Box.id res.scene.boxes (by rwa [caption_box_ids a]) box hb

private theorem caption_tables {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) {P : Params} {metric : Measure.Metric}
    {lines : List (List Measure.Line)} (hP : checkedParams o.profile inp.kind = .ok P)
    (hm : metricOf o.profile o.fontFamily = .ok metric)
    (hl : boxLines metric (captionWrapTarget P metric o) inp = .ok lines) :
    a.params = P ∧ a.lines = lines := by
  have hp := Except.ok.inj (a.checked.symm.trans hP)
  have hmetric := Except.ok.inj (a.metric_ok.symm.trans hm)
  have hal := a.lines_ok
  rw [hp, hmetric] at hal
  exact ⟨hp, Except.ok.inj (hal.symm.trans hl)⟩

private def shiftedLabel (dx dy : Int) (label : SceneLabel) : SceneLabel :=
  { label with rect := shiftRect dx dy label.rect }

private def installedCaption (owner : String) (title : Rect) (model : ModelLabel)
    (label : SceneLabel) : SceneLabel :=
  if model.owner == owner then { label with rect := title } else label

private theorem installedCaption_keys (owner : String) (title : Rect) (model : ModelLabel)
    (label : SceneLabel) :
    (installedCaption owner title model label).id = label.id ∧
      (installedCaption owner title model label).owner = label.owner := by
  unfold installedCaption
  split <;> exact ⟨rfl, rfl⟩

private theorem merged_caption_label {inp : Input} {group : ModelBox} {P : Params}
    {titleLines : List Measure.Line} {child parent res : FamilyResult}
    {dx dy : Int} {title : Rect} (hids : (inp.labels.map ModelLabel.id).Nodup)
    (hc : LabelOrigins (childSubInput inp group) child.scene)
    (hp : LabelOrigins (parentSubInput inp group P titleLines child) parent.scene)
    (hlabels : res.scene.labels = inp.labels.filterMap fun model =>
      ((child.scene.labels.map (shiftedLabel dx dy) ++ parent.scene.labels).find?
        (fun label => label.id == model.id)).bind
        (fun label => some (installedCaption group.id title model label)))
    {label : SceneLabel} (hl : label ∈ res.scene.labels) :
    ∃ model ∈ inp.labels, model.id = label.id ∧ model.owner = label.owner ∧
      ((model ∈ (childSubInput inp group).labels ∧ ∃ old ∈ child.scene.labels,
        old.owner = model.owner ∧
        label = installedCaption group.id title model (shiftedLabel dx dy old)) ∨
       (model ∈ (parentSubInput inp group P titleLines child).labels ∧
        ∃ old ∈ parent.scene.labels, old.owner = model.owner ∧
        label = installedCaption group.id title model old)) := by
  rw [hlabels] at hl
  obtain ⟨model, hmodel, hemit⟩ := List.mem_filterMap.mp hl
  obtain ⟨found, hfind, hemit⟩ := Option.bind_eq_some_iff.mp hemit
  have hemit := (Option.some.inj hemit).symm
  have hfId : found.id = model.id :=
    beq_iff_eq.mp (List.find?_some (p := fun label : SceneLabel => label.id == model.id) hfind)
  have hkeys := installedCaption_keys group.id title model found
  have hid : model.id = label.id :=
    hfId.symm.trans (hkeys.1.symm.trans (congrArg (fun l : SceneLabel => l.id) hemit).symm)
  have howner : label.owner = found.owner :=
    (congrArg (fun l : SceneLabel => l.owner) hemit).trans hkeys.2
  have match_model {sub : Input} {s : Scene} (hs : LabelOrigins sub s)
      (hsub : sub.labels.Sublist inp.labels) {old : SceneLabel} (hold : old ∈ s.labels)
      (hk : old.id = model.id) : model ∈ sub.labels ∧ old.owner = model.owner := by
    obtain ⟨source, hsource, hkey, ho⟩ := hs hold
    have hsame := expandChild_nodup_map_inj ModelLabel.id hids
      (hsub.subset hsource) hmodel (hkey.trans hk)
    rw [hsame] at hsource ho
    exact ⟨hsource, ho.symm⟩
  rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hchild | hparent
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hchild
    have hsub : (childSubInput inp group).labels.Sublist inp.labels :=
      selectInput_labels_sublist inp (fun box => Compound.inside inp.boxes group.id box.id) group.id
    obtain ⟨hs, ho⟩ := match_model hc hsub hold hfId
    exact ⟨model, hmodel, hid, ho.symm.trans howner.symm, Or.inl ⟨hs, old, hold, ho, hemit⟩⟩
  · have hsub : (parentSubInput inp group P titleLines child).labels.Sublist inp.labels :=
      selectInput_labels_sublist inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
    obtain ⟨hs, ho⟩ := match_model hp hsub hparent hfId
    exact ⟨model, hmodel, hid, ho.symm.trans howner.symm,
      Or.inr ⟨hs, found, hparent, ho, hemit⟩⟩

private theorem selected_node_firstText {inp sub : Input} {o oSub : Options}
    {res resSub : FamilyResult} (a : CaptionSceneAssembly inp o res)
    (aSub : CaptionSceneAssembly sub oSub resSub) (hids : (inp.boxes.map ModelBox.id).Nodup)
    (hsubIds : (sub.boxes.map ModelBox.id).Nodup) (hdisjoint : BoxRouteIdsDisjoint inp)
    (hsubAgree : NodeCaptionAgreement sub resSub.scene) {keep : ModelBox → Bool} {root : String}
    (hboxes : sub.boxes = (selectInput inp keep root).boxes) (hP : aSub.params = a.params)
    (hlines : ∀ {j : Nat} {q : ModelBox × Nat},
      (inp.boxes.zipIdx.filter fun entry => keep entry.1)[j]? = some q →
        aSub.lines.getD j [] = a.lines.getD q.2 [])
    {embed : Box → Box} {dx dy : Int}
    (hlookup : ∀ box : Box, resSub.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some (embed box))
    (hembed : ∀ box, (embed box).rect = shiftRect dx dy box.rect)
    {model : ModelLabel} (hm : model ∈ (selectInput inp keep root).labels)
    {old : SceneLabel} (hold : old ∈ resSub.scene.labels) (holdOwner : old.owner = model.owner)
    {source : ModelBox} (hsource : source ∈ inp.boxes) (hrole : source.role = .node)
    (hsourceId : source.id = model.owner) {display : Group} (hdisplay : display ∈ res.scene.items)
    (hne : display.role ≠ .edge) (howner : display.owner = model.owner) :
    firstText display.items = some (shiftRect dx dy old.rect) := by
  have hselected : model.owner ∈ (selectInput inp keep root).boxes.map ModelBox.id := by
    rcases selectInput_label_owner inp keep root model hm with hb | hr
    · exact hb
    · exact (hdisjoint model.owner (List.mem_map.mpr ⟨source, hsource, hsourceId⟩)
        ((selectInput_routes_ids_sublist inp keep root).subset hr)).elim
  obtain ⟨selected, hselected, hsid⟩ := List.mem_map.mp hselected
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hselected
  obtain ⟨q, hq, hqSource, _, hqId, hqRole, _, _, _⟩ :=
    selectInput_box_caption_source keep root hj
  have hqOwner : q.1.id = model.owner := hqId.symm.trans hsid
  have hsame := expandChild_nodup_map_inj ModelBox.id hids (List.mem_of_getElem? hqSource)
    hsource (hqOwner.trans hsourceId.symm)
  have hqr : q.1.role = .node := by rw [hsame, hrole]
  have hsubBox : sub.boxes[j]? = some selected := by rw [hboxes, hj]
  obtain ⟨before, hb, hbId, _, hcanonical, _, _⟩ :=
    aSub.node_normal_form hsubIds hsubBox (hqRole.trans hqr)
  obtain ⟨after, ha, haId, _, _, hcanonicalOut, _⟩ := a.node_normal_form hids hqSource hqr
  have hbefore := caption_box_lookup aSub hsubIds (List.mem_of_getElem? hb)
  have hafter := caption_box_lookup a hids (List.mem_of_getElem? ha)
  have hresult := hlookup before hbefore
  rw [hbId, hqId, ← haId] at hresult
  have hrect : after.rect = shiftRect dx dy before.rect :=
    (congrArg Box.rect (Option.some.inj (hafter.symm.trans hresult))).trans (hembed before)
  have hcanonicalRole : GroupRole.node ≠ .edge := by
    intro h
    cases h
  have hfirst := hsubAgree hold (List.mem_of_getElem? hsubBox) (hqRole.trans hqr)
    (hsid.trans holdOwner.symm) hcanonical hcanonicalRole (hsid.trans holdOwner.symm)
  change firstText (nodeItems aSub.params before.rect (aSub.lines.getD j [])) = some old.rect at hfirst
  rw [hcanonicalOut display hdisplay hne (howner.trans hqOwner.symm)]
  change firstText (nodeItems a.params after.rect (a.lines.getD q.2 [])) =
    some (shiftRect dx dy old.rect)
  rw [hrect, firstText_nodeItems_shiftRect, ← hP, ← hlines hq, hfirst, Option.map_some]

private theorem exact_leaf_caption_facts {ids : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (inputModel inp o)) (hfit : InputFixedFit inp o)
    (hdisjoint : BoxRouteIdsDisjoint inp) (hrun : layoutX ids inp o = .ok res) :
    GroupCaptionAgreement res.scene ∧ NodeCaptionAgreement inp res.scene ∧ LabelOrigins inp res.scene := by
  obtain ⟨e⟩ := layoutX_sceneExecution hrun
  refine ⟨exact_leaf_group_caption_agreement e hwf hfit hdisjoint, ?_, ?_⟩
  · intro label hl source hsource _ hid display hd hne ho
    have hb : label.owner ∈ res.scene.layoutDump.boxes.map Box.id := by
      change label.owner ∈ res.scene.boxes.map Box.id
      rw [(layoutX_ids hrun).1]
      exact List.mem_map.mpr ⟨source, hsource, hid⟩
    exact exact_leaf_caption_agreement e hwf hfit hdisjoint (List.mem_map_of_mem hl) hb hd hne ho
  · intro label hl
    rw [e.scene_eq] at hl
    exact sceneOf_label_mem _ _ _ _ _ _ label hl

private theorem exact_recursive_caption_facts {ids : List String} (fuel : Nat)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hfit : InputFixedFit inp o) (hdisjoint : BoxRouteIdsDisjoint inp)
    (hrun : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) :
    GroupCaptionAgreement res.scene ∧ NodeCaptionAgreement inp res.scene ∧ LabelOrigins inp res.scene := by
  induction fuel generalizing inp o res with
  | zero => exact exact_leaf_caption_facts hwf hfit hdisjoint hrun
  | succ fuel ih =>
    rcases layoutRecursiveB_succ_sources (layoutX ids) hrun with ⟨_, hflat⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, hw, hp, hexpand⟩
    · exact exact_leaf_caption_facts hwf hfit hdisjoint hflat
    · let height : Int := (max 1 titleLines.length : Int) * P.lineH
      change layoutRecursiveB (layoutX ids) fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child at hc
      change layoutRecursiveB (layoutX ids) fuel (parentSubInput inp group P titleLines child)
        o = .ok parent at hp
      change expandChild P inp o group height parent child = .ok res at hexpand
      have hctx : ExpandChildCallContextB (layoutX ids) fuel P inp o group titleLines height
          parent child res := ⟨hwf, hg, rfl, hc, hp, hexpand⟩
      have hparams : ExpandChildCallParams P inp o group titleLines height :=
        ⟨hP, rfl, ⟨metric, hm, hw⟩⟩
      obtain ⟨hwfc, hfrc, hwfp, hfrp⟩ := subInputWellFormedB_layoutX ids fuel inp o group
        P metric titleLines child parent hwf hframed hP hm hw hc hp
      have hmarg := exactCanvasMargins ids fuel (childSubInput inp group)
        (childSubOptions o group) child hc P hP
      obtain ⟨hgc, hnc, hoc⟩ := ih hwfc hfrc (hfit.childSubInput group)
        (hdisjoint.childSubInput group) hc
      obtain ⟨hgp, hnp, hop⟩ := ih hwfp hfrp
        (hfit.parentSubInput hwf hP hm hw hmarg.1 hmarg.2)
        (hdisjoint.parentSubInput group P titleLines child) hp
      have hids := Model.boxIds_nodup hwf
      have hidsC := Model.boxIds_nodup hwfc
      have hidsP := Model.boxIds_nodup hwfp
      obtain ⟨a⟩ := exact_recursive_caption_assembly (fuel + 1) hids hrun
      obtain ⟨ac⟩ := exact_recursive_caption_assembly fuel hidsC hc
      obtain ⟨ap⟩ := exact_recursive_caption_assembly fuel hidsP hp
      obtain ⟨frame, metric', tl, _, dx, dy, hf, hm', ht, _, hdx, hdy, _, _, _⟩ :=
        expandChild_assembly_sources hexpand
      have htWrap : ExpandChildTitleWrapped P inp o group tl := ⟨metric', hm', ht⟩
      have hlabels := expandChild_labels_eq_wrapped hexpand frame tl dx dy hf hdx hdy htWrap
      have label_source {label : SceneLabel} (hl : label ∈ res.scene.labels) :=
        merged_caption_label (P := P) (titleLines := titleLines) (labelIds_nodup hwf) hoc hop hlabels hl
      refine ⟨exact_expandChild_group_caption_agreement hctx hdisjoint hgp hgc, ?_, ?_⟩
      · intro label hl source hsource hrole hsourceId display hd hne ho
        obtain ⟨model, _, _, hmOwner, horigin⟩ := label_source hl
        have hid : source.id = model.owner := hsourceId.trans hmOwner.symm
        have hdisplayId : display.owner = model.owner := ho.trans hmOwner.symm
        have hgroupRole : group.role = .group := by
          have htest := List.find?_some (p := fun box : ModelBox =>
            Compound.independent inp.boxes inp.routes box &&
              !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) hg
          have hind := (Bool.and_eq_true_iff.mp htest).1
          simp only [Compound.independent, Bool.and_eq_true, beq_iff_eq] at hind
          exact hind.1.1
        have hkeep : ¬ ((model.owner == group.id) = true) := by
          intro he
          have hsame := expandChild_nodup_map_inj ModelBox.id hids hsource
            (List.mem_of_find?_eq_some hg) (hid.trans (beq_iff_eq.mp he))
          rw [hsame, hgroupRole] at hrole
          cases hrole
        obtain ⟨lines, linesC, linesP, hlAll, hlC, hlP, hslotsC, hslotsP⟩ :=
          exact_expansion_caption_lines hP hm hc hp hexpand
        obtain ⟨hpa, hla⟩ := caption_tables a hP hm hlAll
        obtain ⟨hpc, hlc⟩ := caption_tables ac hP hm hlC
        obtain ⟨hpp, hlp⟩ := caption_tables ap hP hm hlP
        obtain ⟨hfitStep, _, _⟩ := exactFitClosed ids fuel P inp o group titleLines height
          parent child res hexpand hctx hparams
        obtain ⟨_, hboxC, hboxP⟩ := hfitStep frame tl dx dy hf hdx hdy htWrap
        rcases horigin with ⟨hmodel, old, hold, holdOwner, hemit⟩ |
          ⟨hmodel, old, hold, holdOwner, hemit⟩
        · have hfirst := selected_node_firstText a ac hids hidsC hdisjoint hnc
            (keep := fun box => Compound.inside inp.boxes group.id box.id) (root := group.id) rfl
            (hpc.trans hpa.symm) (fun hq => by rw [hlc, hla]; exact hslotsC hq)
            (embed := embedBox group.id dx dy) (dx := dx) (dy := dy)
            hboxC (fun _ => rfl) hmodel hold holdOwner hsource hrole hid hd hne hdisplayId
          rw [hemit, installedCaption, ite_eq_right hkeep]
          exact hfirst
        · have hfirst := selected_node_firstText a ap hids hidsP hdisjoint hnp
            (keep := fun box => !Compound.inside inp.boxes group.id box.id) (root := "") rfl
            (hpp.trans hpa.symm) (fun hq => by rw [hlp, hla]; exact hslotsP hq)
            (embed := id) (dx := 0) (dy := 0) hboxP (fun box => by simp [shiftRect])
            hmodel hold holdOwner hsource hrole hid hd hne hdisplayId
          rw [hemit, installedCaption, ite_eq_right hkeep]
          simpa [shiftRect] using hfirst
      · intro label hl
        obtain ⟨model, hmodel, hid, ho, _⟩ := label_source hl
        exact ⟨model, hmodel, hid, ho⟩

private theorem display_node_source {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) {display : Group} (hd : display ∈ res.scene.items)
    (hr : display.role ≠ .edge) (hg : display.role ≠ .group) :
    ∃ source ∈ inp.boxes, source.role = .node ∧ source.id = display.owner := by
  rw [a.items_eq] at hd
  obtain ⟨raw, hraw, ho, hrole, _⟩ := applyTitles_firstText_source hd
  unfold sceneItems at hraw
  rcases List.mem_append.mp hraw with hleft | hnodes
  · rcases List.mem_append.mp hleft with hgroups | hedges
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hgroups
      exact (hg hrole).elim
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hedges
      exact (hr hrole).elim
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hnodes
    obtain ⟨hmem, hnode⟩ := List.mem_filter.mp hq
    have hbox := List.mem_zipIdx_iff_getElem?.mp hmem
    have hkeys := congrArg (fun keys : List (String × String) => keys[q.2]?) a.box_keys
    simp only [List.getElem?_map, hbox, Option.map_some] at hkeys
    cases hs : inp.boxes[q.2]? with
    | none => simp only [hs, Option.map_none] at hkeys; cases hkeys
    | some source =>
      simp only [hs, Option.map_some] at hkeys
      have hPair := Option.some.inj hkeys
      have hroleId : source.role.id = "node" := (congrArg Prod.snd hPair).symm.trans (beq_iff_eq.mp hnode)
      refine ⟨source, List.mem_of_getElem? hs, ?_, (congrArg Prod.fst hPair).symm.trans ho.symm⟩
      cases hrs : source.role with
      | node => rfl
      | group => simp [hrs, BoxRole.id] at hroleId

/-- Agreement for the actual recursive exact layout. Fixed fit is transported from
    this entry to each executed leaf; the parent's newly fixed frame is sized by
    the executed wrap and child canvas, not assumed exclusive. -/
theorem exact_recursive_caption_agreement {ids : List String} (fuel : Nat)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hfit : InputFixedFit inp o) (hdisjoint : BoxRouteIdsDisjoint inp)
    (hrun : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) :
    NonedgeCaptionAgreement res.scene := by
  obtain ⟨hgroup, hnode, _⟩ := exact_recursive_caption_facts fuel hwf hframed hfit hdisjoint hrun
  intro label hl display hd hr ho
  by_cases hg : display.role = .group
  · exact hgroup hl hd hg ho
  · obtain ⟨a⟩ := exact_recursive_caption_assembly fuel (Model.boxIds_nodup hwf) hrun
    obtain ⟨source, hs, hsRole, hsId⟩ := display_node_source a hd hr hg
    exact hnode hl hs hsRole (hsId.trans ho) hd hr ho

private theorem usecase_recursive_success {m : Model} {fixed : List (String × Size)}
    {res : FamilyResult}
    (h : layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
      (input m fixed) m.options = .ok res) :
    layoutRecursiveB (layoutX (actorIds m)) ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options = .ok res := by
  have hr := (layoutFamilyB_success h).2
  change layoutRecursiveB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
    (m.boxes.length + 1) (input m fixed) m.options = .ok res at hr
  unfold layoutRecursiveX at hr
  rwa [layoutRecursiveB_compose] at hr

/-- The exact run admitted by the public adapter needs no extra caption premise. -/
theorem usecase_executed_caption_agreement {m : Model} {fixed : List (String × Size)}
    {res : FamilyResult}
    (h : admit (input m fixed)
      (layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
        (input m fixed) m.options) = .ok res) : NonedgeCaptionAgreement res.scene := by
  obtain ⟨hadm, hrun⟩ := admit_ok h
  exact exact_recursive_caption_agreement _ (layoutFamilyB_success hrun).1
    (layoutFamilyB_framed_parents hrun) (layeredAdmissibleB_fit hadm m.options)
    (layeredAdmissibleB_disjoint hadm) (usecase_recursive_success hrun)

private theorem recursive_route_ids_subset {ids : List String} {fuel : Nat} {inp : Input}
    {o : Options} {res : FamilyResult} (hrun : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) :
    res.scene.routes.map Route.id ⊆ inp.routes.map ModelRoute.id := by
  intro id hid
  cases fuel with
  | zero =>
    rw [(layoutX_ids hrun).2] at hid
    exact hid
  | succ fuel =>
    rcases layoutRecursiveB_succ_sources (layoutX ids) hrun with ⟨_, hflat⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hexpand⟩
    · rw [(layoutX_ids hflat).2] at hid
      exact hid
    · obtain ⟨_, _, _, hroutes⟩ := expandChild_port_assembly hexpand
      obtain ⟨route, hroute, hkey⟩ := List.mem_map.mp hid
      rw [hroutes] at hroute
      obtain ⟨source, hs, hfind⟩ := List.mem_filterMap.mp hroute
      have he : route.id = source.id :=
        beq_iff_eq.mp (List.find?_some (p := fun r : Route => r.id == source.id) hfind)
      exact List.mem_map.mpr ⟨source, hs, he.symm.trans hkey⟩

private theorem display_edge_route {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) {display : Group} (hd : display ∈ res.scene.items)
    (hr : display.role = .edge) : display.owner ∈ res.scene.routes.map Route.id := by
  rw [a.items_eq] at hd
  obtain ⟨raw, hraw, ho, hrole, _⟩ := applyTitles_firstText_source hd
  have hedge := hrole.symm.trans hr
  unfold sceneItems at hraw
  rcases List.mem_append.mp hraw with hleft | hnodes
  · rcases List.mem_append.mp hleft with hgroups | hedges
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hgroups
      cases hedge
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hedges
      exact List.mem_map.mpr ⟨q.1, List.fst_mem_of_mem_zipIdx hq, ho.symm⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hnodes
    cases hedge

/-- A successful redraw preserves the validator geometry of each emitted label.
    Actor labels are suppressed; every remaining redraw witness copies a caption
    rectangle already used by the corresponding base label. -/
theorem usecase_executed_drawn_label_source {m : Model} {fixed : List (String × Size)}
    {base : FamilyResult} {drawn : Scene} (hwf : WellFormed m) (hfixed : sizes m = .ok fixed)
    (hadmit : admit (input m fixed)
      (layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
        (input m fixed) m.options) = .ok base)
    (hdraw : drawShapes m (base.scene.projectCellAttachments (Common.routeMarkers m)) = .ok drawn)
    {label : SceneLabel} (hl : label ∈ drawn.labels) :
    ∃ old ∈ base.scene.labels, label.id = old.id ∧ label.owner = old.owner ∧ label.rect = old.rect := by
  let projected := base.scene.projectCellAttachments (Common.routeMarkers m)
  have hlp : projected.labels = base.scene.labels := by
    dsimp only [projected]
    unfold Scene.projectCellAttachments
    split <;> rfl
  obtain ⟨old, hold, hid, ho, _, _, hcase⟩ := drawShapes_labels_spec hdraw label hl
  change old ∈ projected.labels at hold
  rw [hlp] at hold
  refine ⟨old, hold, hid, ho, ?_⟩
  rcases hcase with hrect | ⟨display, hd, hmove⟩
  · exact hrect
  · obtain ⟨hadm, hrun⟩ := admit_ok hadmit
    obtain ⟨hdb, hfirst⟩ := executed_movedLabel_source hadm hwf hfixed hrun rfl hdraw hl hd hmove
    obtain ⟨box, _, hbox, _, howner, _, _, _⟩ := hmove
    have hn : display.role ≠ .edge := by
      intro hedge
      obtain ⟨a⟩ := usecase_executed_caption_assembly hrun
      have hr := recursive_route_ids_subset (usecase_recursive_success hrun) (display_edge_route a hdb hedge)
      have hb : display.owner ∈ (input m fixed).boxes.map ModelBox.id :=
        List.mem_map.mpr ⟨box, List.mem_of_find?_eq_some hbox,
          beq_iff_eq.mp (List.find?_some (p := fun b : ModelBox => b.id == display.owner) hbox)⟩
      exact layeredAdmissibleB_disjoint hadm display.owner hb hr
    have holdRect := usecase_executed_caption_agreement hadmit hold hdb hn (howner.trans ho)
    exact Option.some.inj (hfirst.symm.trans holdRect)

/-- The admitted exact family result supplies both moved-label clearance
    clauses of the actual public redraw. -/
theorem usecase_executed_draw_clearance {m : Model} (hwf : WellFormed m) (hlim : WithinLimits m) :
    ExecutedDrawClearance m := by
  intro fixed base drawn hfixed hadmit projected hdraw
  obtain ⟨hadm, hrun⟩ := admit_ok hadmit
  obtain ⟨_, _, _, _, _, _, hc7, _, hc8b⟩ := usecase_exact_family_valid hadm hwf hlim hfixed hrun
  have hproj : projected.layoutDump = base.scene.layoutDump :=
    Scene.projectCellAttachments_layoutDump _ _
  have hbEq := (drawShapes_dump_boxes hdraw).trans (congrArg LayoutDump.boxes hproj)
  have hrEq := (drawShapes_dump_routes hdraw).trans (congrArg LayoutDump.routes hproj)
  constructor
  · intro label hl b hb hex _ hscope
    obtain ⟨old, hold, _, ho, hrect⟩ :=
      usecase_executed_drawn_label_source hwf hfixed hadmit hdraw hl
    have hold' : old.toLabel ∈ base.scene.layoutDump.labels := List.mem_map_of_mem hold
    have hb' : b ∈ base.scene.layoutDump.boxes := by rwa [hbEq] at hb
    have hanc := labelOwnerAnc_congr hrEq hbEq (l₁ := label.toLabel) (l₂ := old.toLabel) ho
    rw [hanc] at hscope
    rw [hrect]
    exact hc7 old.toLabel hold' b hb' hex hscope
  · intro group hg hgRole label hl _
    obtain ⟨old, hold, _, _, hrect⟩ :=
      usecase_executed_drawn_label_source hwf hfixed hadmit hdraw hl
    have hold' : old.toLabel ∈ base.scene.layoutDump.labels := List.mem_map_of_mem hold
    have hg' : group ∈ base.scene.layoutDump.boxes := by rwa [hbEq] at hg
    rw [hrect]
    exact hc8b group hg' hgRole old.toLabel hold'

end Elegant.Kinds.Usecase

namespace Elegant.Kinds

/-- Successful public usecase layouts satisfy the hard constraints. -/
theorem usecase_valid {m : Model} {res : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m) (hrun : Usecase.layout m = .ok res) :
    HardConstraints res.scene.layoutDump :=
  usecase_valid_of_executed_draw_clearance hwf hlim
    (Usecase.usecase_executed_draw_clearance hwf hlim) hrun

end Elegant.Kinds
