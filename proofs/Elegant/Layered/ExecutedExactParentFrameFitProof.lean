import Elegant.Layered.ExactFlatChildLabelsProof
import Elegant.Layered.ExactForeignFrameClearProof
import Elegant.Layered.ExactStepFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A foreign label strictly inside a collapsed frame in an actual flat exact run. -/
inductive ExactFlatFixedLeafLabelObstruction (exactIds : List String) : Prop where
  | found {inp : Input} {o : Options} {res : FamilyResult} {id : String}
      {entry : String × Size} {frame : Box} {label : SceneLabel}
      (run : layoutX exactIds inp o = .ok res) (wellFormed : WellFormed (inputModel inp o))
      (framed : framedParents inp = true) (fit : InputFixedFit inp o)
      (fixed : inp.fixedSizes.find? (fun row => row.1 == id) = some entry)
      (leaf : ExactFixedLeaf inp id)
      (lookup : res.scene.boxes.find? (fun box => box.id == id) = some frame)
      (role : frame.role = "group")
      (member : label ∈ res.scene.labels) (foreignOwner : label.owner ≠ id)
      (inside : frame.rect.StrictInside label.rect)

abbrev ExactFlatFixedLeafLabelExclusion (exactIds : List String) : Prop :=
  ¬ ExactFlatFixedLeafLabelObstruction exactIds

private theorem titleWidth_nonneg (lines : List Measure.Line) (acc : Int) (hacc : 0 ≤ acc) :
    0 ≤ lines.foldl (fun width line => max width line.width) acc := by
  induction lines generalizing acc with
  | nil => exact hacc
  | cons line rest ih => exact ih _ (Int.le_trans hacc (Int.le_max_left _ _))

private theorem captionDims (group : ModelBox) (P : Params) (lines : List Measure.Line)
    (height : Int) (frame : Box) (hh : 0 ≤ height) :
    0 ≤ (groupTitleRectC8 group P lines height frame).w ∧
    0 ≤ (groupTitleRectC8 group P lines height frame).h := by
  unfold groupTitleRectC8 childTitleRect
  split <;> exact ⟨titleWidth_nonneg lines 0 (Int.le_refl 0), hh⟩

private theorem orientedDims (dir : Direction) {r : Rect} {height margin : Int}
    (hdims : 0 ≤ r.w ∧ 0 ≤ r.h) :
    0 ≤ (shiftRect margin margin (orientRect dir height r)).w ∧
    0 ≤ (shiftRect margin margin (orientRect dir height r)).h := by
  cases dir <;> first | exact hdims | exact ⟨hdims.2, hdims.1⟩

private theorem flatLabelDims {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hrun : layoutX exactIds inp o = .ok res) :
    ∀ label ∈ res.scene.labels, 0 ≤ label.rect.w ∧ 0 ≤ label.rect.h := by
  obtain ⟨execution⟩ := layoutX_sceneExecution hrun
  have hacc := SceneExecutionX.straightAcc_bounded execution (exactPartsBounded' execution)
  have hline := checkedParams_lineH_nonneg execution.checked
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  have hboxes := sceneOf_boxes_bounded execution.params inp o execution.lines
    execution.straightAcc execution.measured hacc (by omega)
  intro label hlabel
  rw [execution.scene_eq] at hlabel
  obtain ⟨q, _, hemitted⟩ := List.mem_filterMap.mp hlabel
  cases hex : inp.boxes.any (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hex, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hex, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hmeasured : execution.measured.find? (fun item => item.index == q.2) with
    | some measured =>
      simp only [hmeasured, Option.some.injEq] at hemitted
      subst label
      apply orientedDims
      cases hget : execution.straightAcc.labels[measured.index]? with
      | none =>
        rw [Array.getD_eq_getD_getElem?, hget]
        exact ⟨Int.le_refl 0, Int.le_refl 0⟩
      | some r =>
        rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
        exact (hacc.labels_bounded measured.index r hget).2.2.2.2
    | none =>
      simp only [hmeasured] at hemitted
      cases howner : inp.boxes.findIdx? (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [howner] at hemitted; cases hemitted
      | some index =>
        simp only [howner, Option.some.injEq] at hemitted
        subst label
        change 0 ≤ (sceneCaptionRect execution.params inp o execution.lines
            execution.straightAcc index q.1.owner).w ∧
          0 ≤ (sceneCaptionRect execution.params inp o execution.lines
            execution.straightAcc index q.1.owner).h
        unfold sceneCaptionRect
        cases htitle : (sceneTitlesExpr execution.params inp o execution.lines
            execution.straightAcc).find? (fun title => title.1 == q.1.owner) with
        | some title =>
          simp only [Option.map_some, Option.getD_some]
          obtain ⟨stored, _, hstored⟩ :=
            List.mem_filterMap.mp (List.mem_of_find?_eq_some htitle)
          obtain ⟨_, _, hemitted⟩ := Option.bind_eq_some_iff.mp hstored
          rw [← Option.some.inj hemitted]
          let lines := execution.lines.getD stored.1 []
          have hw := titleWidth_nonneg lines 0 (Int.le_refl 0)
          have hh : 0 ≤ (max 1 lines.length : Int) * execution.params.lineH :=
            Int.mul_nonneg (by omega) hline
          apply orientedDims
          change 0 ≤ (titleCaptionSize execution.params o lines).w ∧
            0 ≤ (titleCaptionSize execution.params o lines).h
          cases hdir : o.direction <;> simp only [titleCaptionSize, hdir] <;>
            first | exact ⟨hw, hh⟩ | exact ⟨hh, hw⟩
        | none =>
          simp only [Option.map_none, Option.getD_none]
          let boxes := (sceneOf execution.params inp o execution.lines
            execution.straightAcc execution.measured).boxes
          let box := boxes.getD index ⟨"", "", default, "", false⟩
          let lines := execution.lines.getD index []
          change 0 ≤ (ownedTextRect execution.params box lines).w ∧
            0 ≤ (ownedTextRect execution.params box lines).h
          unfold ownedTextRect
          split
          · exact ⟨Int.le_max_left _ _, Int.mul_nonneg (by omega) hline⟩
          · have hw : 0 ≤ box.rect.w := by
              dsimp only [box]
              rw [List.getD_eq_getElem?_getD]
              cases hb : boxes[index]? with
              | none => exact Int.le_refl 0
              | some b =>
                have hbound := hboxes (b, index) (List.mem_zipIdx_iff_getElem?.mpr hb)
                simp only [Size.containsCellRect, decide_eq_true_iff] at hbound
                exact hbound.2.2.1
            exact ⟨hw, Int.mul_nonneg (Int.natCast_nonneg _) hline⟩

private theorem exactRecursiveLabelDims (exactIds : List String) (fuel : Nat) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}, WellFormed (inputModel inp o) →
      framedParents inp = true → layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ label ∈ res.scene.labels, 0 ≤ label.rect.w ∧ 0 ≤ label.rect.h := by
  induction fuel with
  | zero =>
    intro inp o res _ _ hrun
    exact flatLabelDims hrun
  | succ fuel ih =>
    intro inp o res hwf hframed hrun label hlabel
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) hrun with ⟨_, hflat⟩ |
      ⟨group, P, metric, child, lines, parent, hg, hP, hm, hc, ht, hp, hx⟩
    · exact flatLabelDims hflat label hlabel
    let height := (max 1 lines.length : Int) * P.lineH
    have hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group lines height
        parent child res := ⟨hwf, hg, rfl, hc, hp, hx⟩
    have hparams : ExpandChildCallParams P inp o group lines height := ⟨hP, rfl, metric, hm, ht⟩
    obtain ⟨hwc, hfc, hwp, hfp⟩ := subInputWellFormedB_layoutX exactIds fuel inp o group
      P metric lines child parent hwf hframed hP hm ht hc hp
    obtain ⟨frame, metric', titles, _, dx, dy, hframe, hm', ht', _, hdx, hdy, _, _⟩ :=
      expandChild_sources hx
    have hwrap : ExpandChildTitleWrapped P inp o group titles := ⟨metric', hm', ht'⟩
    have howners := XB_label_owners exactIds fuel P inp o group lines height parent child res
      hx hframed hctx hparams
    have hclass := expandChild_c8b_structure_wrapped hx howners frame titles dx dy
      hframe hdx hdy hwrap label.toLabel (List.mem_map.mpr ⟨label, hlabel, rfl⟩)
    rcases hclass with ⟨_, hcap⟩ | ⟨cl, hcl, _, _, _, hrect⟩ | ⟨pl, hpl, _, _, _, hrect⟩
    · change label.rect = groupTitleRectC8 group P titles height frame at hcap
      rw [hcap]
      exact captionDims group P titles height frame
        (Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP))
    · change label.rect = shiftRect dx dy cl.rect at hrect
      rw [hrect]
      exact ih hwc hfc hc cl hcl
    · change label.rect = pl.rect at hrect
      rw [hrect]
      exact ih hwp hfp hp pl hpl

private theorem selectedGroup_notFixed {inp : Input} {group : ModelBox}
    (hg : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun row => row.1 == box.id)) = some group) :
    inp.fixedSizes.find? (fun row => row.1 == group.id) = none := by
  have hpred := List.find?_some hg
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
  exact List.find?_eq_none.mpr (List.any_eq_false.mp hpred.2)

private theorem fixedLeaf_select {inp : Input} {id : String} (h : ExactFixedLeaf inp id)
    (keep : ModelBox → Bool) (root : String) : ExactFixedLeaf (selectInput inp keep root) id := by
  intro box hbox hne
  obtain ⟨source, hsource, _, _, hparent⟩ := selectInput_box_spec inp keep root hbox
  split at hparent
  · exact False.elim (hne hparent)
  · rw [hparent] at hne ⊢
    exact h source hsource hne

private theorem freshFixedLeaf {inp : Input} {group : ModelBox} {P : Params}
    {lines : List Measure.Line} {child : FamilyResult}
    (hnodup : (inp.boxes.map (·.id)).Nodup) (hgroup : group ∈ inp.boxes) :
    ExactFixedLeaf (parentSubInput inp group P lines child) group.id := by
  intro box hbox hne hpar
  change box ∈ (selectInput inp (fun b => !Compound.inside inp.boxes group.id b.id) "").boxes
    at hbox
  obtain ⟨source, hsource, hkeep, _, hparent⟩ := selectInput_box_spec inp
    (fun b => !Compound.inside inp.boxes group.id b.id) "" hbox
  split at hparent
  · exact hne hparent
  · rw [hparent] at hne hpar
    have hin := inside_of_parent hnodup hgroup hsource hpar.symm hne
    simp [hin] at hkeep

private theorem freshFixedEntry {inp : Input} {group : ModelBox} {P : Params}
    {lines : List Measure.Line} {child : FamilyResult}
    (hnone : inp.fixedSizes.find? (fun row => row.1 == group.id) = none) :
    ∃ entry, (parentSubInput inp group P lines child).fixedSizes.find?
      (fun row => row.1 == group.id) = some entry := by
  let entry : String × Size := (group.id, childFrameSize group.direction P.clusterPad
    (lines.foldl (fun width line => max width line.width) 0)
    ((max 1 lines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩)
  refine ⟨entry, ?_⟩
  change (inp.fixedSizes ++ [entry]).find? (fun row => row.1 == group.id) = some entry
  rw [List.find?_append, hnone]
  simp [entry]

private theorem freshFrameRole (exactIds : List String)
    {fuel : Nat} {inp : Input} {o : Options} {group : ModelBox} {P : Params}
    {lines : List Measure.Line} {child parent : FamilyResult} {entry : String × Size}
    (hwf : WellFormed (inputModel inp o))
    (hwp : WellFormed (inputModel (parentSubInput inp group P lines child) o))
    (hfp : framedParents (parentSubInput inp group P lines child) = true)
    (hg : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun row => row.1 == box.id)) = some group)
    (hp : layoutRecursiveB (layoutX exactIds) fuel (parentSubInput inp group P lines child) o =
      .ok parent)
    (hfixed : (parentSubInput inp group P lines child).fixedSizes.find?
      (fun row => row.1 == group.id) = some entry)
    {frame : Box} (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.role = "group" := by
  let parentInput := parentSubInput inp group P lines child
  have hids := (layoutRecursiveB_c5_facts (flatC5B_layoutX_closed exactIds)
    (subInputWellFormedB_layoutX exactIds) fuel hwp hfp hp).1
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hmem : group.id ∈ parentInput.boxes.map (·.id) := by
    rw [← hids, ← hframeId]
    exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
  obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hmem
  obtain ⟨original, horiginal, _, hsourceEq⟩ := selectInput_box_source inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" source hsource
  have hid : original.id = group.id := by
    rw [hsourceEq] at hsourceId
    split at hsourceId <;> exact hsourceId
  have heq : original = group := expandChild_nodup_map_inj (·.id) (Model.boxIds_nodup hwf)
    horiginal (List.mem_of_find?_eq_some hg) hid
  have hrole : group.role = .group := by
    have hs := List.find?_some hg
    simp only [Bool.and_eq_true] at hs
    have hi := hs.1
    unfold Compound.independent at hi
    simp only [Bool.and_eq_true] at hi
    exact beq_iff_eq.mp hi.1.1
  have hsourceRole : source.role = .group := by
    rw [hsourceEq]
    split <;> simpa only [heq] using hrole
  obtain ⟨actual, hactual, hactualRole, _, _⟩ := xExactFixedMin exactIds fuel parentInput o
    parent source entry (Model.boxIds_nodup hwp) (routesCovered_of_wellFormed hwp) hp hsource
    (by simpa only [hsourceId] using hfixed)
  rw [hsourceId] at hactual
  have hactualEq : actual = frame := Option.some.inj (hactual.symm.trans hframe)
  simpa only [hactualEq, hsourceRole, BoxRole.id] using hactualRole

private theorem mergedFrameSources {inp : Input} {group : ModelBox}
    {parent child res : FamilyResult} {dx dy : Int}
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun model =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
        (fun box => box.id == model.id)))
    {id : String} {frame : Box}
    (hframe : res.scene.boxes.find? (fun box => box.id == id) = some frame) :
    (∃ cb, child.scene.boxes.find? (fun box => box.id == id) = some cb ∧
      frame = embedBox group.id dx dy cb) ∨
      parent.scene.boxes.find? (fun box => box.id == id) = some frame := by
  have hid : frame.id = id := by simpa using List.find?_some hframe
  have hmem := List.mem_of_find?_eq_some hframe
  rw [hboxes] at hmem
  obtain ⟨model, _, hlookup⟩ := List.mem_filterMap.mp hmem
  have hmodel : frame.id = model.id := by simpa using List.find?_some hlookup
  rw [hmodel.symm.trans hid, List.find?_append, List.find?_map] at hlookup
  change ((child.scene.boxes.find? (fun box => box.id == id)).map
    (embedBox group.id dx dy)).or
      (parent.scene.boxes.find? (fun box => box.id == id)) = some frame at hlookup
  cases hc : child.scene.boxes.find? (fun box => box.id == id) with
  | none => exact Or.inr (by simpa only [hc, Option.map_none, Option.none_or] using hlookup)
  | some cb =>
    refine Or.inl ⟨cb, rfl, ?_⟩
    apply Option.some.inj
    symm
    simpa only [hc, Option.map_some, Option.some_or] using hlookup

private theorem strictOverlap {a b r : Rect} (ha : a.StrictInside r) (hb : b.StrictInside r)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) : a.meetsInterior b := by
  simp only [Rect.StrictInside, Rect.meetsInterior] at *
  constructor <;> omega

private theorem childBox_not_strictInside_title {direction : String}
    {pad tw th margin dx dy : Int} {frame box : Rect} {canvas : Size}
    (htw : 0 ≤ tw) (hth : 0 ≤ th)
    (hfw : (childFrameSize direction pad tw th ⟨canvas.w - 2 * margin, canvas.h - 2 * margin⟩).w ≤
      frame.w)
    (hfh : (childFrameSize direction pad tw th ⟨canvas.w - 2 * margin, canvas.h - 2 * margin⟩).h ≤
      frame.h)
    (hdx : dx = frame.x + (childInset direction pad tw th).x - margin)
    (hdy : dy = frame.y + (childInset direction pad tw th).y - margin)
    (hbox : (insetRect canvas margin).Contained box) :
    ¬ (shiftRect dx dy box).StrictInside (childTitleRect direction pad tw th frame) := by
  intro hstrict
  by_cases hLR : direction = "LR"
  · rw [hLR] at hdx hstrict
    simp only [childInset, childTitleRect, shiftRect, insetRect, Rect.Contained,
      Rect.StrictInside] at hdx hbox hstrict
    omega
  by_cases hRL : direction = "RL"
  · rw [hRL] at hdx hfw hstrict
    change canvas.w - 2 * margin + tw + 2 * pad ≤ frame.w at hfw
    simp only [childInset, childTitleRect, shiftRect, insetRect,
      Rect.Contained, Rect.StrictInside] at hdx hbox hstrict
    omega
  by_cases hBT : direction = "BT"
  · rw [hBT] at hdy hfh hstrict
    change canvas.h - 2 * margin + th + 2 * pad ≤ frame.h at hfh
    simp only [childInset, childTitleRect, shiftRect, insetRect,
      Rect.Contained, Rect.StrictInside] at hdy hbox hstrict
    omega
  · simp only [childInset, childTitleRect, shiftRect, insetRect, Rect.Contained,
      Rect.StrictInside] at hdy hbox hstrict
    omega

set_option maxHeartbeats 800000 in
/-- Reduce strict containment of a foreign label in an exact fixed leaf to an
actual flat exact run. Each recursive branch consumes less fuel; the split
needs neither recursive C8b nor parent-frame strictness at the current fuel. -/
theorem layoutRecursiveX_fixedLeaf_label_obstruction (exactIds : List String) (fuel : Nat) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult} {id : String} {entry : String × Size},
      WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      inp.fixedSizes.find? (fun row => row.1 == id) = some entry → ExactFixedLeaf inp id →
      ∀ frame, res.scene.boxes.find? (fun box => box.id == id) = some frame → frame.role = "group" →
        ∀ label ∈ res.scene.labels, label.owner ≠ id → frame.rect.StrictInside label.rect →
          ExactFlatFixedLeafLabelObstruction exactIds := by
  induction fuel with
  | zero =>
    intro inp o res id entry hwf hframed hfit hrun hfixed hleaf
      tracked htracked hrole label hlabel howner hstrict
    exact .found hrun hwf hframed hfit hfixed hleaf htracked hrole hlabel howner hstrict
  | succ fuel ih =>
    intro inp o res id entry hwf hframed hfit hrun hfixed hleaf
      tracked htracked hrole label hlabel howner hstrict
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) hrun with ⟨_, hbase⟩ |
      ⟨group, P, metric, child, lines, parent, hg, hP, hm, hc, ht, hp, hx⟩
    · exact .found hbase hwf hframed hfit hfixed hleaf htracked hrole hlabel howner hstrict
    let height := (max 1 lines.length : Int) * P.lineH
    let parentInput := parentSubInput inp group P lines child
    have hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group lines height
        parent child res := ⟨hwf, hg, rfl, hc, hp, hx⟩
    have hparams : ExpandChildCallParams P inp o group lines height := ⟨hP, rfl, metric, hm, ht⟩
    obtain ⟨hwc, hfc, hwp, hfp⟩ := subInputWellFormedB_layoutX exactIds fuel inp o group
      P metric lines child parent hwf hframed hP hm ht hc hp
    have hmargins := exactCanvasMargins exactIds fuel (childSubInput inp group)
      (childSubOptions o group) child hc P hP
    have hfitP : InputFixedFit parentInput o :=
      InputFixedFit.parentSubInput hwf hfit hP hm ht hmargins.1 hmargins.2
    have hleafC : ExactFixedLeaf (childSubInput inp group) id := fixedLeaf_select hleaf _ _
    have hleafP : ExactFixedLeaf parentInput id := by
      change ExactFixedLeaf
        (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "") id
      exact fixedLeaf_select hleaf _ _
    have hfixedP : parentInput.fixedSizes.find? (fun row => row.1 == id) = some entry := by
      change (inp.fixedSizes ++ _).find? (fun row => row.1 == id) = some entry
      rw [List.find?_append, hfixed, Option.some_or]
    have hnone := selectedGroup_notFixed hg
    have hne : id ≠ group.id := by
      intro heq
      rw [heq, hnone] at hfixed
      cases hfixed
    obtain ⟨_, hfresh⟩ := freshFixedEntry (P := P) (lines := lines) (child := child) hnone
    have hfreshLeaf : ExactFixedLeaf parentInput group.id :=
      freshFixedLeaf (Model.boxIds_nodup hwf) (List.mem_of_find?_eq_some hg)
    obtain ⟨frame, metric', titles, _, dx, dy, hframe, hm', ht', _, hdx, hdy, _, hboxes⟩ :=
      expandChild_sources hx
    have hwrap : ExpandChildTitleWrapped P inp o group titles := ⟨metric', hm', ht'⟩
    have howners := XB_label_owners exactIds fuel P inp o group lines height parent child res
      hx hframed hctx hparams
    have hclass := expandChild_c8b_structure_wrapped hx howners frame titles dx dy
      hframe hdx hdy hwrap label.toLabel (List.mem_map.mpr ⟨label, hlabel, rfl⟩)
    have hfitStrict := XG_content_fit_strict exactIds fuel P inp o group lines height parent child res
      hx hframed hctx hparams frame titles dx dy hframe hdx hdy hwrap
    rcases mergedFrameSources (group := group) hboxes htracked with ⟨cb, hcb, rfl⟩ | htrackedP
    · change (shiftRect dx dy cb.rect).StrictInside label.rect at hstrict
      have hbIn := XG_child_boxes_insetB exactIds fuel P inp o group lines height parent child res
        hx hframed hctx hparams cb (List.mem_of_find?_eq_some hcb)
      rcases hclass with ⟨_, hcap⟩ | ⟨cl, hcl, _, _, hclOwner, hrect⟩ |
        ⟨pl, hpl, hnotCaption, _, hplOwner, hrect⟩
      · change label.rect = groupTitleRectC8 group P titles height frame at hcap
        rw [hcap] at hstrict
        have hsize := XG_frame_size_bounds exactIds fuel P inp o group lines height parent child res
          hx hframed hctx hparams frame titles hframe hwrap
        have htw := titleWidth_nonneg titles 0 (Int.le_refl 0)
        have hth : 0 ≤ height := Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
        exact False.elim
          (childBox_not_strictInside_title htw hth hsize.1 hsize.2 hdx hdy hbIn hstrict)
      · change label.owner = cl.owner at hclOwner
        change label.rect = shiftRect dx dy cl.rect at hrect
        rw [hrect] at hstrict
        have hnative : cb.rect.StrictInside cl.rect := by
          simp only [Rect.StrictInside, shiftRect] at hstrict ⊢
          omega
        exact ih hwc hfc (hfit.childSubInput group) hc hfixed hleafC cb hcb hrole cl hcl
          (hclOwner ▸ howner) hnative
      · change label.owner = pl.owner at hplOwner
        change label.owner ≠ group.id at hnotCaption
        change label.rect = pl.rect at hrect
        rw [hrect] at hstrict
        have hinside := hfitStrict cb.rect hbIn
        have htrans : frame.rect.StrictInside pl.rect := by
          simp only [Rect.StrictInside] at hinside hstrict ⊢
          omega
        have hframeRole := freshFrameRole exactIds hwf hwp hfp hg hp hfresh hframe
        exact ih hwp hfp hfitP hp hfresh hfreshLeaf frame hframe hframeRole pl hpl
          (hplOwner ▸ hnotCaption) htrans
    · have hdisj := layoutRecursiveX_fixedFrames_disjoint exactIds fuel hwp hfp hp
        hne hfixedP hfresh htrackedP hframe
      rcases hclass with ⟨_, hcap⟩ | ⟨cl, hcl, _, _, _, hrect⟩ | ⟨pl, hpl, _, _, hplOwner, hrect⟩
      · change label.rect = groupTitleRectC8 group P titles height frame at hcap
        rw [hcap] at hstrict
        have hcaption := XSGL_stepC8bCapStrict exactIds fuel P inp o group lines height parent child res
          hx hframed hctx hparams frame titles dx dy hframe hdx hdy hwrap
        obtain ⟨hw, hh⟩ := captionDims group P titles height frame
          (Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP))
        exact False.elim (hdisj (strictOverlap hstrict hcaption hw hh))
      · change label.rect = shiftRect dx dy cl.rect at hrect
        rw [hrect] at hstrict
        have hlabelIn := xsgl_stepC8bChildLabelsFit_closed exactIds fuel P inp o group lines height
          parent child res hx hframed hctx hparams hfit cl hcl
        have hinside := hfitStrict cl.rect hlabelIn
        have hdims := exactRecursiveLabelDims exactIds fuel hwc hfc hc cl hcl
        exact False.elim (hdisj (strictOverlap hstrict hinside hdims.1 hdims.2))
      · change label.owner = pl.owner at hplOwner
        change label.rect = pl.rect at hrect
        rw [hrect] at hstrict
        exact ih hwp hfp hfitP hp hfixedP hleafP tracked htrackedP hrole pl hpl
          (hplOwner ▸ howner) hstrict

/-- Trace a violation in the actual parent result to a flat fixed-leaf violation. -/
theorem executedExactParentFrameStrict_obstruction
    {exactIds : List String} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {lines : List Measure.Line} {height : Int} {parent child res : FamilyResult}
    {frame : Box} {label : SceneLabel}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group lines height parent child res)
    (hparams : ExpandChildCallParams P inp o group lines height)
    (hfit : InputFixedFit inp o)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hlabel : label ∈ parent.scene.labels) (hforeign : label.owner ≠ group.id)
    (hstrict : frame.rect.StrictInside label.rect) :
    ExactFlatFixedLeafLabelObstruction exactIds := by
  obtain ⟨hwf, hg, _, hc, hp, _⟩ := hctx
  obtain ⟨hP, _, metric, hm, ht⟩ := hparams
  obtain ⟨_, _, hwp, hfp⟩ := subInputWellFormedB_layoutX exactIds fuel inp o group
    P metric lines child parent hwf hframed hP hm ht hc hp
  have hmargins := exactCanvasMargins exactIds fuel (childSubInput inp group)
    (childSubOptions o group) child hc P hP
  have hfitP : InputFixedFit (parentSubInput inp group P lines child) o :=
    InputFixedFit.parentSubInput hwf hfit hP hm ht hmargins.1 hmargins.2
  obtain ⟨_, hfresh⟩ := freshFixedEntry (P := P) (lines := lines) (child := child)
    (selectedGroup_notFixed hg)
  have hleaf := freshFixedLeaf (P := P) (lines := lines) (child := child)
    (Model.boxIds_nodup hwf) (List.mem_of_find?_eq_some hg)
  have hframeRole := freshFrameRole exactIds hwf hwp hfp hg hp hfresh hframe
  exact layoutRecursiveX_fixedLeaf_label_obstruction exactIds fuel hwp hfp hfitP hp
    hfresh hleaf frame hframe hframeRole label hlabel hforeign hstrict

/-- The executed parent call supplies the parent sub-input's fit and leaf
evidence. Only exclusion in the flat exact base remains to be supplied. -/
theorem executedExactParentFrameStrict_of_flat_fit
    {exactIds : List String} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {lines : List Measure.Line} {height : Int} {parent child res : FamilyResult}
    (hflat : ExactFlatFixedLeafLabelExclusion exactIds)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group lines height parent child res)
    (hparams : ExpandChildCallParams P inp o group lines height)
    (hfit : InputFixedFit inp o) : ExpandChildParentFrameStrict group parent := by
  intro frame hframe label hlabel hforeign hstrict
  exact hflat (executedExactParentFrameStrict_obstruction hframed hctx hparams hfit
    hframe hlabel hforeign hstrict)

end Elegant.Layered.PipelineImpl
