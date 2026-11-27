import Elegant.Kinds.UsecaseCaptionLeafAgreement
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.GroupTitleFirstTextProof
import Elegant.Layered.MergedRouteIdsProof
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.SelectInputWellFormed

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

open Layered Layered.PipelineImpl

def GroupCaptionAgreement (s : Scene) : Prop :=
  ∀ {label : SceneLabel}, label ∈ s.labels →
    ∀ {display : Group}, display ∈ s.items → display.role = .group →
      display.owner = label.owner → firstText display.items = some label.rect

private theorem paintedGroup_source {P : Params} {inp : Input} {boxes : List Box}
    {routes : List Route} {lines : List (List Measure.Line)} {labels : List SceneLabel}
    {titles : List (String × Rect)} {display : Group}
    (hdisplay : display ∈ applyTitles titles (sceneItems P inp boxes routes lines labels))
    (hrole : display.role = .group) :
    ∃ q ∈ boxes.zipIdx, q.1.role = "group" ∧ display.owner = q.1.id ∧
      firstText display.items = some (match titles.find? (fun title => title.1 == display.owner) with
        | some title => title.2
        | none => titleRect P q.1.rect (lines.getD q.2 [])) := by
  obtain ⟨raw, hraw, howner, hrawRole, htext⟩ := applyTitles_firstText_source hdisplay
  have hr : raw.role = .group := hrawRole.symm.trans hrole
  unfold sceneItems at hraw
  rcases List.mem_append.mp hraw with hframesOrEdges | hnodes
  · rcases List.mem_append.mp hframesOrEdges with hframes | hedges
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hframes
      obtain ⟨hmem, hgroup⟩ := List.mem_filter.mp hq
      refine ⟨q, hmem, beq_iff_eq.mp hgroup, howner, ?_⟩
      change display.owner = q.1.id at howner
      rw [howner]
      simp only [firstText_groupItems, Option.map_some] at htext
      cases hfind : titles.find? (fun title => title.1 == q.1.id) <;>
        rw [hfind] at htext <;> exact htext
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hedges
      cases hr
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hnodes
    cases hr

private theorem paintedGroup_exists {P : Params} {inp : Input} {boxes : List Box}
    {routes : List Route} {lines : List (List Measure.Line)} {labels : List SceneLabel}
    (titles : List (String × Rect)) {box : Box} (hbox : box ∈ boxes) (hrole : box.role = "group") :
    ∃ display ∈ applyTitles titles (sceneItems P inp boxes routes lines labels),
      display.role = .group ∧ display.owner = box.id := by
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hbox
  have hq : (box, index) ∈ boxes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hindex
  let raw : Group := ⟨.group, box.id, groupItems P box.rect (lines.getD index [])⟩
  have hraw : raw ∈ sceneItems P inp boxes routes lines labels := by
    unfold sceneItems
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨(box, index), List.mem_filter.mpr ⟨hq, beq_iff_eq.mpr hrole⟩, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hraw
  obtain ⟨display, hout, howner, hdisplayRole, _⟩ := applyTitles_getElem?_firstText titles hi
  exact ⟨display, List.mem_of_getElem? hout, hdisplayRole, howner⟩

private theorem findGroupTitle_of_agreement {s : Scene} (hagrees : GroupCaptionAgreement s)
    {label : SceneLabel} (hl : label ∈ s.labels)
    (hdisplay : ∃ display ∈ s.items, display.role = .group ∧ display.owner = label.owner) :
    (groupTitles s.items).find? (fun title => title.1 == label.owner) =
      some (label.owner, label.rect) := by
  cases hfind : (groupTitles s.items).find? (fun title => title.1 == label.owner) with
  | none =>
    obtain ⟨display, hd, hr, ho⟩ := hdisplay
    have hn := groupTitles_find?_eq_none_iff.mp hfind display hd ho hr
    rw [hagrees hl hd hr ho] at hn
    cases hn
  | some title =>
    obtain ⟨owner, rect⟩ := title
    have howner : owner = label.owner := beq_iff_eq.mp
      (List.find?_some (p := fun title : String × Rect => title.1 == label.owner) hfind)
    obtain ⟨display, hd, ho, hr, ht⟩ := mem_groupTitles_iff.mp (List.mem_of_find?_eq_some hfind)
    have hrect : rect = label.rect := Option.some.inj (ht.symm.trans (hagrees hl hd hr (ho.trans howner)))
    rw [howner, hrect]

private def shiftLabel (dx dy : Int) (label : SceneLabel) : SceneLabel :=
  { label with rect := shiftRect dx dy label.rect }

private def installTitle (owner : String) (rect : Rect) (model : ModelLabel) (label : SceneLabel) :
    SceneLabel :=
  if model.owner == owner then { label with rect := rect } else label

private theorem installTitle_keys (owner : String) (rect : Rect) (model : ModelLabel)
    (label : SceneLabel) :
    (installTitle owner rect model label).id = label.id ∧
      (installTitle owner rect model label).owner = label.owner := by
  unfold installTitle
  split <;> exact ⟨rfl, rfl⟩

private theorem mergedLabel_source {inp : Input} {parent child res : FamilyResult}
    {dx dy : Int} {owner : String} {rect : Rect}
    (hlabels : res.scene.labels = inp.labels.filterMap (fun model =>
      ((child.scene.labels.map (shiftLabel dx dy) ++ parent.scene.labels).find?
        (fun label => label.id == model.id)).bind
      (fun label => some (installTitle owner rect model label))))
    {label : SceneLabel} (hl : label ∈ res.scene.labels) :
    ∃ model ∈ inp.labels, ∃ found,
      (child.scene.labels.map (shiftLabel dx dy) ++ parent.scene.labels).find?
        (fun label => label.id == model.id) = some found ∧
      label = installTitle owner rect model found := by
  rw [hlabels] at hl
  obtain ⟨model, hmodel, hemit⟩ := List.mem_filterMap.mp hl
  cases hf : (child.scene.labels.map (shiftLabel dx dy) ++ parent.scene.labels).find?
      (fun label => label.id == model.id) with
  | none =>
    rw [hf, Option.bind_none] at hemit
    cases hemit
  | some found =>
    rw [hf, Option.bind_some] at hemit
    exact ⟨model, hmodel, found, hf, (Option.some.inj hemit).symm⟩

private structure CaptionSceneSources (inp : Input) (s : Scene) : Prop where
  boxId : ∀ {box : Box}, box ∈ s.boxes → box.id ∈ inp.boxes.map (·.id)
  label : ∀ {label : SceneLabel}, label ∈ s.labels →
    ∃ model ∈ inp.labels, model.id = label.id ∧ model.owner = label.owner
  groupBox : ∀ {display : Group}, display ∈ s.items → display.role = .group →
    ∃ box ∈ s.boxes, box.role = "group" ∧ display.owner = box.id
  boxGroup : ∀ {box : Box}, box ∈ s.boxes → box.role = "group" →
    ∃ display ∈ s.items, display.role = .group ∧ display.owner = box.id

private theorem captionSceneSources_of_items {inp : Input} {s : Scene} {P : Params}
    {lines : List (List Measure.Line)} {titles : List (String × Rect)}
    (hitems : s.items = applyTitles titles (sceneItems P inp s.boxes s.routes lines s.labels))
    (hboxes : ∀ {box : Box}, box ∈ s.boxes → box.id ∈ inp.boxes.map (·.id))
    (hlabels : ∀ {label : SceneLabel}, label ∈ s.labels →
      ∃ model ∈ inp.labels, model.id = label.id ∧ model.owner = label.owner) :
    CaptionSceneSources inp s := by
  refine ⟨hboxes, hlabels, ?_, ?_⟩
  · intro display hdisplay hrole
    rw [hitems] at hdisplay
    obtain ⟨q, hq, hr, ho, _⟩ := paintedGroup_source hdisplay hrole
    exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, hr, ho⟩
  · intro box hbox hrole
    rw [hitems]
    exact paintedGroup_exists titles hbox hrole

private theorem exactFlat_captionSources {ids : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hrun : layoutX ids inp o = .ok res) : CaptionSceneSources inp res.scene := by
  obtain ⟨execution⟩ := layoutX_sceneExecution hrun
  have hfields_items1 := straightenAcc_fields execution.straight_eq
  have hitems : res.scene.items =
      applyTitles (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc)
        (sceneItems execution.params inp res.scene.boxes res.scene.routes execution.lines res.scene.labels) := by
    rw [execution.scene_eq]
    simp only [sceneOf, hfields_items1.2.2.1, hfields_items1.2.2.2.2]
    rfl
  refine captionSceneSources_of_items hitems ?_ ?_
  · intro box hb
    rw [(layoutX_ids hrun).1.symm]
    exact List.mem_map_of_mem hb
  · intro label hl
    rw [execution.scene_eq] at hl
    exact sceneOf_label_mem _ _ _ _ _ _ label hl

private theorem exactRecursive_captionSources (ids : List String) (fuel : Nat)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hrun : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) :
    CaptionSceneSources inp res.scene := by
  induction fuel generalizing inp o res with
  | zero => exact exactFlat_captionSources hrun
  | succ fuel ih =>
    rcases layoutRecursiveB_succ_sources (layoutX ids) hrun with ⟨_, hflat⟩ |
      ⟨group, P, _, child, titleLines, parent, _, _, _, hchild, _, hparent, hexpand⟩
    · exact exactFlat_captionSources hflat
    · change layoutRecursiveB (layoutX ids) fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child at hchild
      change layoutRecursiveB (layoutX ids) fuel (parentSubInput inp group P titleLines child)
        o = .ok parent at hparent
      let titleHeight : Int := (max 1 titleLines.length : Int) * P.lineH
      change expandChild P inp o group titleHeight parent child = .ok res at hexpand
      have hc := ih hchild
      have hp := ih hparent
      obtain ⟨frame, metric, tl, _, dx, dy, hframe, hm, ht, _, hdx, hdy, hboxes, _, hitems⟩ :=
        expandChild_assembly_sources hexpand
      have hlabels := expandChild_labels_eq_wrapped hexpand frame tl dx dy hframe hdx hdy
        ⟨metric, hm, ht⟩
      refine captionSceneSources_of_items hitems ?_ ?_
      · intro box hb
        rw [hboxes] at hb
        obtain ⟨model, hmodel, hfind⟩ := List.mem_filterMap.mp hb
        have hid : box.id = model.id :=
          beq_iff_eq.mp (List.find?_some (p := fun box : Box => box.id == model.id) hfind)
        exact List.mem_map.mpr ⟨model, hmodel, hid.symm⟩
      · intro label hl
        let title := childTitleRect group.direction P.clusterPad
          (tl.foldl (fun w line => max w line.width) 0) titleHeight frame.rect
        obtain ⟨model, _, found, hf, he⟩ := mergedLabel_source
          (dx := dx) (dy := dy) (owner := group.id) (rect := title) hlabels hl
        have hfields := installTitle_keys group.id title model found
        rw [← he] at hfields
        rcases List.mem_append.mp (List.mem_of_find?_eq_some hf) with hcm | hpm
        · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hcm
          obtain ⟨source, hsource, hid, howner⟩ := hc.label hold
          have hsub := selectInput_labels_sublist inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id
          exact ⟨source, hsub.subset hsource,
            hid.trans hfields.1.symm, howner.trans hfields.2.symm⟩
        · obtain ⟨source, hsource, hid, howner⟩ := hp.label hpm
          change source ∈ (selectInput inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "").labels at hsource
          have hsub := selectInput_labels_sublist inp
            (fun box => !Compound.inside inp.boxes group.id box.id) ""
          exact ⟨source, hsub.subset hsource,
            hid.trans hfields.1.symm, howner.trans hfields.2.symm⟩

private theorem selectedBox_side {inp : Input} (side : String → Bool) (root : String)
    {id : String} (hbox : id ∈ (selectInput inp (fun box => side box.id) root).boxes.map (·.id)) :
    side id = true := by
  rw [selectInput_box_ids] at hbox
  obtain ⟨box, hb, rfl⟩ := List.mem_map.mp hbox
  exact (List.mem_filter.mp hb).2

private theorem selectedLabel_side {inp : Input} (side : String → Bool) (root : String)
    (hdisjoint : BoxRouteIdsDisjoint inp) {label : ModelLabel}
    (hlabel : label ∈ (selectInput inp (fun box => side box.id) root).labels)
    (hbox : label.owner ∈ inp.boxes.map (·.id)) : side label.owner = true := by
  rcases selectInput_label_owner inp (fun box => side box.id) root label hlabel with hb | hr
  · exact selectedBox_side side root hb
  · exact (hdisjoint label.owner hbox ((selectInput_routes_ids_sublist inp _ root).subset hr)).elim

private theorem sourceLabel_owner_side {inp : Input} (side : String → Bool) (root : String)
    (hids : (inp.labels.map (·.id)).Nodup) (hdisjoint : BoxRouteIdsDisjoint inp)
    {model : ModelLabel} {old : SceneLabel} (hmodel : model ∈ inp.labels) (hid : old.id = model.id)
    (hbox : old.owner ∈ inp.boxes.map (·.id))
    (hsource : ∃ source ∈ (selectInput inp (fun box => side box.id) root).labels,
      source.id = old.id ∧ source.owner = old.owner) :
    model.owner = old.owner ∧ side old.owner = true := by
  obtain ⟨source, hs, hsid, howner⟩ := hsource
  have he : source = model := expandChild_nodup_map_inj (·.id) hids
    ((selectInput_labels_sublist inp _ root).subset hs) hmodel (hsid.trans hid)
  refine ⟨he ▸ howner, ?_⟩
  rw [← howner]
  exact selectedLabel_side side root hdisjoint hs (howner.symm ▸ hbox)

/-- Transport the group part of caption agreement across an executed exact recursion split.
    The two induction hypotheses concern only the actual predecessor scenes. -/
theorem exact_expandChild_group_caption_cases {ids : List String} {fuel : Nat}
    {P : Params} {inp : Input} {o : Options} {group : ModelBox} {titleLines : List Measure.Line}
    {titleHeight : Int} {parent child res : FamilyResult}
    (hctx : ExpandChildCallContextB (layoutX ids) fuel P inp o group titleLines titleHeight
      parent child res)
    (hdisjoint : BoxRouteIdsDisjoint inp)
    (hparent : GroupCaptionAgreement parent.scene) (hchild : GroupCaptionAgreement child.scene) :
    ∃ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      ExpandChildTitleWrapped P inp o group tl ∧
      let width := tl.foldl (fun w line => max w line.width) 0
      let inset := childInset group.direction P.clusterPad width titleHeight
      let title := childTitleRect group.direction P.clusterPad width titleHeight frame.rect
      dx = frame.rect.x + inset.x - P.canvasMargin ∧
      dy = frame.rect.y + inset.y - P.canvasMargin ∧
      ∀ {label : SceneLabel}, label ∈ res.scene.labels →
        ∀ {display : Group}, display ∈ res.scene.items → display.role = .group →
          display.owner = label.owner →
          (label.owner = group.id ∧ ∃ source ∈ parent.scene.labels,
            label = { source with rect := title } ∧ firstText display.items = some title) ∨
          (label.owner ≠ group.id ∧ ∃ source ∈ child.scene.labels,
            source.owner = label.owner ∧
            label = { source with rect := shiftRect dx dy source.rect } ∧
            firstText display.items = some (shiftRect dx dy source.rect)) ∨
          (label.owner ≠ group.id ∧ ∃ source ∈ parent.scene.labels,
            label = source ∧ firstText display.items = some source.rect) := by
  obtain ⟨hwf, _, hparentBoxes, hrunC, hrunP, hexpand⟩ := hctx
  have hc := exactRecursive_captionSources ids fuel hrunC
  have hp := exactRecursive_captionSources ids fuel hrunP
  obtain ⟨frame, metric, tl, lines, dx, dy, hframe, hm, ht, _, hdx, hdy, hboxes, _, hitems⟩ :=
    expandChild_assembly_sources hexpand
  let side := Compound.inside inp.boxes group.id
  let outside := fun id => !side id
  let title := childTitleRect group.direction P.clusterPad
    (tl.foldl (fun w line => max w line.width) 0) titleHeight frame.rect
  let carriedChild := (groupTitles child.scene.items).map (fun t => (t.1, shiftRect dx dy t.2))
  let carriedParent := groupTitles parent.scene.items
  let titles := (group.id, title) :: (carriedChild ++ carriedParent)
  refine ⟨frame, tl, dx, dy, hframe, ⟨metric, hm, ht⟩, hdx, hdy, ?_⟩
  intro label hl display hd hr ho
  rw [hitems] at hd
  obtain ⟨q, hq, hboxRole, hboxOwner, hpaint⟩ := paintedGroup_source hd hr
  have hpaint' : firstText display.items = some (match titles.find? (fun t => t.1 == label.owner) with
      | some t => t.2
      | none => titleRect P q.1.rect (lines.getD q.2 [])) := by
    simpa only [ho] using hpaint
  have hb := List.fst_mem_of_mem_zipIdx hq
  rw [hboxes] at hb
  obtain ⟨modelBox, hmodelBox, hboxFind⟩ := List.mem_filterMap.mp hb
  have hboxId : q.1.id = label.owner := hboxOwner.symm.trans ho
  have hfoundBoxId : q.1.id = modelBox.id :=
    beq_iff_eq.mp (List.find?_some (p := fun box : Box => box.id == modelBox.id) hboxFind)
  have hmodelBoxId := hfoundBoxId.symm.trans hboxId
  have hownerIn : label.owner ∈ inp.boxes.map (·.id) :=
    List.mem_map.mpr ⟨modelBox, hmodelBox, hmodelBoxId⟩
  have hlabels := expandChild_labels_eq_wrapped hexpand frame tl dx dy hframe hdx hdy ⟨metric, hm, ht⟩
  obtain ⟨model, hmodel, found, hfind, hemit⟩ := mergedLabel_source
    (dx := dx) (dy := dy) (owner := group.id) (rect := title) hlabels hl
  have hid : found.id = model.id :=
    beq_iff_eq.mp (List.find?_some (p := fun label : SceneLabel => label.id == model.id) hfind)
  have hfoundOwner : found.owner = label.owner :=
    ((installTitle_keys group.id title model found).2).symm.trans
      (congrArg (fun l : SceneLabel => l.owner) hemit).symm
  have hlabelSide : model.owner = label.owner ∧
      ((∃ old ∈ child.scene.labels, found = shiftLabel dx dy old ∧ side label.owner = true) ∨
       (found ∈ parent.scene.labels ∧ outside label.owner = true)) := by
    have hfbox : found.owner ∈ inp.boxes.map (·.id) := hfoundOwner.symm ▸ hownerIn
    rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hfound | hfound
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hfound
      obtain ⟨hmowner, hs⟩ := sourceLabel_owner_side side group.id (labelIds_nodup hwf)
        hdisjoint (old := old) hmodel hid hfbox (hc.label hold)
      have holdOwner : old.owner = label.owner := hfoundOwner
      exact ⟨hmowner.trans holdOwner, Or.inl ⟨old, hold, rfl, holdOwner ▸ hs⟩⟩
    · have hsource := hp.label hfound
      change (∃ source ∈ (selectInput inp (fun box => outside box.id) "").labels,
        source.id = found.id ∧ source.owner = found.owner) at hsource
      obtain ⟨hmowner, hs⟩ := sourceLabel_owner_side outside "" (labelIds_nodup hwf)
        hdisjoint hmodel hid hfbox hsource
      exact ⟨hmowner.trans hfoundOwner, Or.inr ⟨hfound, hfoundOwner ▸ hs⟩⟩
  have hboxSideC {b : Box} (hb : b ∈ child.scene.boxes) : side b.id = true :=
    selectedBox_side side group.id (hc.boxId hb)
  have hboxSideP {b : Box} (hb : b ∈ parent.scene.boxes) : outside b.id = true := by
    have hsource := hp.boxId hb
    rw [hparentBoxes] at hsource
    exact selectedBox_side outside "" hsource
  have hseparate : ∀ id, side id = true → outside id = true → False := by
    intro id hs hn
    change (!side id) = true at hn
    rw [hs] at hn
    cases hn
  by_cases hcurrent : label.owner = group.id
  · have hsourceParent : found ∈ parent.scene.labels := by
      rcases hlabelSide.2 with ⟨_, _, _, hside⟩ | ⟨hsource, _⟩
      · have hframeId : frame.id = group.id :=
          beq_iff_eq.mp (List.find?_some (p := fun box : Box => box.id == group.id) hframe)
        have hframeSide := hboxSideP (List.mem_of_find?_eq_some hframe)
        exact (hseparate label.owner hside ((hframeId.trans hcurrent.symm) ▸ hframeSide)).elim
      · exact hsource
    have hlabel : label = { found with rect := title } := by
      have hinstall : (model.owner == group.id) = true := beq_iff_eq.mpr
        (hlabelSide.1.trans hcurrent)
      rw [hemit, installTitle, ite_eq_left hinstall]
    have htitle : titles.find? (fun t => t.1 == label.owner) = some (group.id, title) := by
      unfold titles
      simp only [List.find?_cons, hcurrent, beq_self_eq_true]
    refine Or.inl ⟨hcurrent, found, hsourceParent, hlabel, ?_⟩
    rw [hpaint', htitle]
  · have hkeep : label = found := by
      have hkeepOwner : ¬ ((model.owner == group.id) = true) :=
        fun h => hcurrent (hlabelSide.1.symm.trans (beq_iff_eq.mp h))
      rw [hemit, installTitle, ite_eq_right hkeepOwner]
    have hhead : (group.id == label.owner) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm hcurrent)
    have hmergedBox :
        (∃ b ∈ child.scene.boxes, b.role = "group" ∧ b.id = label.owner) ∨
        (∃ b ∈ parent.scene.boxes, b.role = "group" ∧ b.id = label.owner) := by
      rcases List.mem_append.mp (List.mem_of_find?_eq_some hboxFind) with hcb | hpb
      · obtain ⟨b, hb, he⟩ := List.mem_map.mp hcb
        rw [← he] at hboxRole hboxId
        exact Or.inl ⟨b, hb, hboxRole, hboxId⟩
      · exact Or.inr ⟨q.1, hpb, hboxRole, hboxId⟩
    rcases hlabelSide.2 with ⟨old, hold, hfound, hside⟩ | ⟨hold, hside⟩
    · have hgroupC : ∃ b ∈ child.scene.boxes, b.role = "group" ∧ b.id = label.owner := by
        rcases hmergedBox with hcb | ⟨b, hb, _, hid⟩
        · exact hcb
        · exact (hseparate label.owner hside (hid ▸ hboxSideP hb)).elim
      obtain ⟨b, hb, hbr, hbo⟩ := hgroupC
      have holdOwner : old.owner = label.owner :=
        (congrArg (fun l : SceneLabel => l.owner) hfound).symm.trans hfoundOwner
      have holdTitle := findGroupTitle_of_agreement hchild hold
        (by simpa only [hbo, holdOwner] using hc.boxGroup hb hbr)
      have hcarry : carriedChild.find? (fun t => t.1 == label.owner) =
          some (label.owner, shiftRect dx dy old.rect) := by
        unfold carriedChild
        simp only [groupTitles_find?_shiftRect, ← holdOwner, holdTitle, Option.map_some]
      refine Or.inr (Or.inl ⟨hcurrent, old, hold, holdOwner, hkeep.trans hfound, ?_⟩)
      rw [hpaint']
      unfold titles
      simp only [List.find?_cons, hhead, List.find?_append, hcarry, Option.some_or]
    · have hgroupP : ∃ b ∈ parent.scene.boxes, b.role = "group" ∧ b.id = label.owner := by
        rcases hmergedBox with ⟨b, hb, _, hid⟩ | hpb
        · exact (hseparate label.owner (hid ▸ hboxSideC hb) hside).elim
        · exact hpb
      obtain ⟨b, hb, hbr, hbo⟩ := hgroupP
      have holdTitle := findGroupTitle_of_agreement hparent hold
        (by simpa only [hbo, hfoundOwner] using hp.boxGroup hb hbr)
      have hchildNone : (groupTitles child.scene.items).find? (fun t => t.1 == label.owner) = none := by
        apply groupTitles_find?_eq_none_iff.mpr
        intro other hother howner hrole
        obtain ⟨cb, hcb, _, hkey⟩ := hc.groupBox hother hrole
        exact (hseparate label.owner ((hkey.symm.trans howner) ▸ hboxSideC hcb) hside).elim
      have hcarry : carriedChild.find? (fun t => t.1 == label.owner) = none := by
        unfold carriedChild
        rw [groupTitles_find?_shiftRect, hchildNone, Option.map_none]
      have hpTitle : carriedParent.find? (fun t => t.1 == label.owner) =
          some (label.owner, found.rect) := by
        simpa only [carriedParent, hfoundOwner] using holdTitle
      refine Or.inr (Or.inr ⟨hcurrent, found, hold, hkeep, ?_⟩)
      rw [hpaint']
      unfold titles
      simp only [List.find?_cons, hhead, List.find?_append, hcarry, Option.none_or, hpTitle]

theorem exact_expandChild_group_caption_agreement {ids : List String} {fuel : Nat}
    {P : Params} {inp : Input} {o : Options} {group : ModelBox} {titleLines : List Measure.Line}
    {titleHeight : Int} {parent child res : FamilyResult}
    (hctx : ExpandChildCallContextB (layoutX ids) fuel P inp o group titleLines titleHeight
      parent child res)
    (hdisjoint : BoxRouteIdsDisjoint inp)
    (hparent : GroupCaptionAgreement parent.scene) (hchild : GroupCaptionAgreement child.scene) :
    GroupCaptionAgreement res.scene := by
  obtain ⟨_, _, _, _, _, _, _, _, hcases⟩ :=
    exact_expandChild_group_caption_cases hctx hdisjoint hparent hchild
  intro label hl display hd hr ho
  rcases hcases hl hd hr ho with ⟨_, _, _, hlabel, htext⟩ |
    ⟨_, _, _, _, hlabel, htext⟩ | ⟨_, _, _, hlabel, htext⟩
  all_goals simpa only [hlabel] using htext

theorem exact_expandChild_group_validator_caption {ids : List String} {fuel : Nat}
    {P : Params} {inp : Input} {o : Options} {group : ModelBox} {titleLines : List Measure.Line}
    {titleHeight : Int} {parent child res : FamilyResult}
    (hctx : ExpandChildCallContextB (layoutX ids) fuel P inp o group titleLines titleHeight
      parent child res)
    (hdisjoint : BoxRouteIdsDisjoint inp)
    (hparent : GroupCaptionAgreement parent.scene) (hchild : GroupCaptionAgreement child.scene)
    {label : Label} (hl : label ∈ res.scene.layoutDump.labels)
    {display : Group} (hd : display ∈ res.scene.items) (hr : display.role = .group)
    (ho : display.owner = label.owner) : firstText display.items = some label.rect := by
  change label ∈ res.scene.labels.map (·.toLabel) at hl
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
  exact exact_expandChild_group_caption_agreement hctx hdisjoint hparent hchild hs hd hr ho

theorem exact_leaf_group_caption_agreement {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX ids inp o res) (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o) (hdisjoint : BoxRouteIdsDisjoint inp) :
    GroupCaptionAgreement res.scene := by
  have hfields_items2 := straightenAcc_fields execution.straight_eq
  have hitems : res.scene.items =
      applyTitles (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc)
        (sceneItems execution.params inp res.scene.boxes res.scene.routes execution.lines res.scene.labels) := by
    rw [execution.scene_eq]
    simp only [sceneOf, hfields_items2.2.2.1, hfields_items2.2.2.2]
    rfl
  intro label hl display hd hr ho
  have hd' := hd
  rw [hitems] at hd'
  obtain ⟨q, hq, _, hboxOwner, _⟩ := paintedGroup_source hd' hr
  have hbox : label.owner ∈ res.scene.layoutDump.boxes.map (·.id) :=
    List.mem_map.mpr ⟨q.1, List.fst_mem_of_mem_zipIdx hq, hboxOwner.symm.trans ho⟩
  have hl' : label.toLabel ∈ res.scene.layoutDump.labels := List.mem_map_of_mem hl
  exact exact_leaf_caption_agreement execution hwf hfit hdisjoint hl' hbox hd
    (by rw [hr]; decide) ho

/-- The installed title is used even for empty measured text. Emitting a label
    also needs an input label row and the actual first successful label lookup. -/
theorem expandChild_current_group_caption {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int} {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      ExpandChildTitleWrapped P inp o group tl ∧
      let width := tl.foldl (fun w line => max w line.width) 0
      let inset := childInset group.direction P.clusterPad width titleHeight
      let title := childTitleRect group.direction P.clusterPad width titleHeight frame.rect
      dx = frame.rect.x + inset.x - P.canvasMargin ∧
      dy = frame.rect.y + inset.y - P.canvasMargin ∧
      (∀ display ∈ res.scene.items, display.role = .group → display.owner = group.id →
        firstText display.items = some title) ∧
      (∀ model ∈ inp.labels, model.owner = group.id → ∀ source : SceneLabel,
        ((child.scene.labels.map fun label : SceneLabel => { label with rect := shiftRect dx dy label.rect }) ++
          parent.scene.labels).find? (fun label => label.id == model.id) = some source →
        { source with rect := title } ∈ res.scene.labels) := by
  obtain ⟨frame, metric, tl, _, dx, dy, hframe, hm, ht, _, hdx, hdy, _, _, hitems⟩ :=
    expandChild_assembly_sources hexpand
  have hwrap : ExpandChildTitleWrapped P inp o group tl := ⟨metric, hm, ht⟩
  refine ⟨frame, tl, dx, dy, hframe, hwrap, hdx, hdy, ?_, ?_⟩
  · intro display hd hr ho
    rw [hitems] at hd
    obtain ⟨_, _, _, _, hpaint⟩ := paintedGroup_source hd hr
    simp only [hpaint, ho, List.find?_cons, beq_self_eq_true]
  · intro model hmodel ho source hfind
    rw [expandChild_labels_eq_wrapped hexpand frame tl dx dy hframe hdx hdy hwrap]
    refine List.mem_filterMap.mpr ⟨model, hmodel, ?_⟩
    have hinstall : (model.owner == group.id) = true := beq_iff_eq.mpr ho
    rw [hfind, Option.bind_some, ite_eq_left hinstall]

end Elegant.Kinds.Usecase
