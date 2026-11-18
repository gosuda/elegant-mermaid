import Elegant.Layered.ExpandChildStepsFacts

/-!
# The structural residuals of one `expandChild`, discharged

This module proves the three purely structural residuals
`ExpandChildC8aStructure`, `ExpandChildC8bStructure`, and
`ExpandChildC7Structure` of `Elegant.Layered.ExpandChildStepsFacts` for an
actual successful `expandChild` run under the `ExpandChildCallContext` the
recursion supplies.

The one executed fact the transports and the label classification additionally
need is that the `titleLines` they are stated at is the wrapped group title the
expansion itself measured: `expandChild` stores its merged child boxes at the
offset built from the wrapped title's width, so an `LR` group whose caller
width differs from the wrapped width pins a different `dx` than the one the
merged scene actually used.  `ExpandChildTitleWrapped` names that fact.
-/

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The executed title fact: `titleLines` is the wrapped group title
`expandChild` measures the frame size from, at the run's own metric and wrap
target.  `expandChild_sources` exposes exactly this equation for the lines of
a successful run. -/
def ExpandChildTitleWrapped (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) : Prop :=
  ∃ metric : Measure.Metric,
    metricOf o.profile = .ok metric ∧
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
        group.id).toList = .ok titleLines


/-- The two ancestry conjuncts of `ExpandChildC8aStructure`, split out as a
named residual: the scope anchors `{group.id} ++ ancestors group.id` of every
embedded child box inside the merged dump, and the isolation of the group's
ancestor chain from the other parent boxes.  Both describe the `parent`-chain
walk of the merged and parent dumps; no proved fact of the expansion or the
recursion supplies the scene ancestry they presuppose. -/
def ExpandChildC8aAncestry (group : ModelBox) (parent child result : FamilyResult) : Prop :=
  (∀ cb ∈ child.scene.boxes,
      ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
        x ∈ result.scene.layoutDump.ancestors cb.id) ∧
  (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
      group.id ∉ parent.scene.layoutDump.ancestors pb.id)

/-- The shared structural core of a successful `expandChild` at the wrapped
title lines the expansion measured: the box-lookup transports of both merged
scenes, the scene-size bounds, the frame's `"group"` role, and the
child/group id isolation.  The transports are stated at the caller's
`dx dy`, which the wrapped premise pins to the offsets the merged scene
actually used. -/
private theorem expandChild_core_wrapped
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some b) ∧
      child.scene.boxes.length ≤ res.scene.boxes.length ∧
      parent.scene.boxes.length ≤ res.scene.boxes.length ∧
      frame.role = "group" ∧
      (∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  -- pin the caller's frame, lines, and offsets to the run's own
  obtain ⟨frame₀, metric₀, tl₀, _lines₀, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _hlines₀,
    hdx₀, hdy₀, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  have hff : frame₀ = frame := Option.some.inj (hframe₀.symm.trans hframe)
  rw [hff] at hdx₀ hdy₀
  obtain ⟨metricW, hmetricW, hwrapW⟩ := hwrap
  have hmetricEq : metricW = metric₀ := Except.ok.inj (hmetricW.symm.trans hmetric₀)
  rw [hmetricEq] at hwrapW
  have htl : tl = tl₀ := Except.ok.inj (hwrapW.symm.trans htitle₀)
  rw [← htl] at hdx₀ hdy₀
  have hdxEq : dx = dx₀ := by omega
  have hdyEq : dy = dy₀ := by omega
  rw [← hdxEq, ← hdyEq] at hboxes
  -- the transports, at the pinned offsets
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ :=
    expandChild_selected_ids hwf hchild hparent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hbMem : b ∈ child.scene.boxes := List.mem_of_find?_eq_some hb
    have hidC : b.id ∈ (inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hcid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidC
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hchildFirst : ∀ (cb : Box), cb ∈ child.scene.boxes → cb.id = b.id → cb = b := by
      intro cb hcbmem hcbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hcid]; exact hnC) hcbmem hbMem hcbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some (embedBox group.id dx dy b)
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := embedBox group.id dx dy b) (s := b.id)
      ⟨m, hmin, ?_⟩ rfl ?_
    · have hcf : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = some (embedBox group.id dx dy b) := by
        rw [List.find?_map]
        have hinside : (child.scene.boxes.find?
            ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy)) = some b := by
          have hpred : ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy) =
              (fun cb => cb.id == b.id) := by
            funext cb
            simp only [Function.comp_apply, embedBox]
            rw [hmid]
          rw [hpred]
          exact hb
        rw [hinside]
        rfl
      rw [List.find?_append]
      rw [hcf]
      rfl
    · intro m' hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        rw [hchildFirst cb hcb hcbkey]
      · exfalso
        exact hdisj z.id
          (by rw [hzid, ← hcid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
          (by rw [← hpid]; exact List.mem_map.mpr ⟨z, hzp, rfl⟩)
  · intro b hb
    have hbMem : b ∈ parent.scene.boxes := List.mem_of_find?_eq_some hb
    have hidP : b.id ∈ (inp.boxes.filter
        (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hpid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidP
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hparentFirst : ∀ (pb : Box), pb ∈ parent.scene.boxes → pb.id = b.id → pb = b := by
      intro pb hpmem hpbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hpid]; exact hnP) hpmem hbMem hpbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some b
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := b) (s := b.id) ⟨m, hmin, ?_⟩ rfl ?_
    · have hcfNone : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = none := by
        rw [List.find?_eq_none]
        intro cb hcb hp
        obtain ⟨cd, hcd, hcdrfl⟩ := List.mem_map.mp hcb
        subst hcdrfl
        have hkey : (embedBox group.id dx dy cd).id = m.id := beq_iff_eq.mp hp
        rw [show (embedBox group.id dx dy cd).id = cd.id from rfl] at hkey
        exact hdisj cd.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cd, hcd, rfl⟩)
          (by rw [hkey]; exact List.mem_map.mpr ⟨m, hmf, rfl⟩)
      have hcfP : parent.scene.boxes.find? (fun box => box.id == m.id) = some b := by
        show parent.scene.layoutDump.box? m.id = some b
        rw [hmid]
        exact hb
      rw [List.find?_append, hcfNone, hcfP]
      rfl
    · intro m' hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        exfalso
        exact hdisj cb.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cb, hcb, rfl⟩)
          (by rw [hcbkey, ← hpid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
      · rw [hparentFirst z hzp hzid]
  · exact (expandChild_merge_bounds hwf hgroup hchild hparent hexpand).1
  · exact (expandChild_merge_bounds hwf hgroup hchild hparent hexpand).2.1
  · -- the frame's role, from the parent run's fixed-source box
    have hparentIds : ((parentSubInput inp group P titleLines child).boxes.map (·.id)).Nodup := by
      show ((selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)).Nodup
      rw [selectInput_box_ids]
      exact List.Nodup.sublist ((List.filter_sublist).map _) hids
    have hparentCovered : RoutesCovered (parentSubInput inp group P titleLines child) :=
      selectInput_routesCovered inp
        (fun box => !Compound.inside inp.boxes group.id box.id) ""
    have hparentOutputIds := (layoutRecursive_ids (fun _ _ _ h => layout_ids h)
      fuel (parentSubInput inp group P titleLines child) o parent hparentCovered hparent).1
    have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
    have hparentSourceId : group.id ∈ (parentSubInput inp group P titleLines child).boxes.map
        (·.id) := by
      rw [← hparentOutputIds, ← hframeId]
      exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
    obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
    have hsourceBase : source ∈ (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := hsource
    obtain ⟨original, horiginal, _hkeep, hsourceEq⟩ :=
      selectInput_box_source inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" source hsourceBase
    have horiginalId : original.id = group.id := by
      have h1 : original.id = source.id := by
        rw [hsourceEq]
        split <;> rfl
      exact h1.trans hsourceId
    have horiginalLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hids original horiginal
    have hgroupLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hids group
      (List.mem_of_find?_eq_some hgroup)
    rw [horiginalId] at horiginalLookup
    have horiginalEq : original = group :=
      Option.some.inj (horiginalLookup.symm.trans hgroupLookup)
    have hsourceRole : source.role = group.role := by
      rw [hsourceEq]
      split <;> simp only [horiginalEq]
    have hgroupRole : group.role = .group := by
      have hs := List.find?_some hgroup
      simp only [Bool.and_eq_true] at hs
      have hi := hs.1
      unfold Compound.independent at hi
      simp only [Bool.and_eq_true] at hi
      exact beq_iff_eq.mp hi.1.1
    have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
      have hs := List.find?_some hgroup
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
      exact hs.2
    have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
      List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
    have hfixed : (parentSubInput inp group P titleLines child).fixedSizes.find?
        (fun fixed => fixed.1 == source.id) =
          some (group.id, childFrameSize group.direction P.clusterPad
            (titleLines.foldl (fun width line => max width line.width) 0)
            ((max 1 titleLines.length : Int) * P.lineH)
            ⟨child.scene.canvas.w - 2 * P.canvasMargin,
              child.scene.canvas.h - 2 * P.canvasMargin⟩) := by
      show (inp.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
            (titleLines.foldl (fun width line => max width line.width) 0)
            ((max 1 titleLines.length : Int) * P.lineH)
            ⟨child.scene.canvas.w - 2 * P.canvasMargin,
              child.scene.canvas.h - 2 * P.canvasMargin⟩)]).find? _ = _
      simp [List.find?_append, hsourceId, hnone]
    obtain ⟨actual, hactual, hactualRole, _, _⟩ :=
      layoutRecursive_fixed_source_box_minimum_dimensions_with_role fuel hparentIds
        hparentCovered hparent hsource hfixed
    rw [hsourceId] at hactual
    have hactualEq : actual = frame := by
      have h1 : parent.scene.layoutDump.box? group.id = some frame := by
        show parent.scene.boxes.find? (fun box => box.id == group.id) = some frame
        exact hframe
      exact Option.some.inj (hactual.symm.trans h1)
    subst actual
    rw [hactualRole, hsourceRole, hgroupRole]
    rfl
  · exact (expandChild_merge_bounds hwf hgroup hchild hparent hexpand).2.2 frame hframe

/-- The structural residual `ExpandChildC8aStructure` reduces to, for a
successful `expandChild` under the recursion's call context: the shared core
(box-lookup transports, scene-size bounds, the frame's `"group"` role, and
the child/group id isolation) together with the split-out ancestry residual,
each stated at the wrapped title lines the expansion measured. -/
theorem expandChild_c8a_structure_wrapped
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hanc : ExpandChildC8aAncestry group parent child res) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some b) ∧
      child.scene.boxes.length ≤ res.scene.boxes.length ∧
      parent.scene.boxes.length ≤ res.scene.boxes.length ∧
      frame.role = "group" ∧
      (∀ cb ∈ child.scene.boxes, cb.id ≠ group.id) ∧
      ExpandChildC8aAncestry group parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hcore := expandChild_core_wrapped hwf hgroup hchild hparent hexpand
    frame tl dx dy hframe hdx hdy hwrap
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
    hcore.2.2.2.2.2, hanc⟩

/-- The label-list equation of a successful `expandChild`, stated at the
wrapped title lines and the offsets they pin: the merged scene keeps one
label per input label model that resolves in the child-then-parent label
list, with the caption rect installed for the group's own labels. -/
theorem expandChild_labels_eq_wrapped
    {P : Params} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {child parent : FamilyResult} {titleHeight : Int}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (frame : Box) (tl : List Measure.Line) (dx dy : Int)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin)
    (hwrap : ExpandChildTitleWrapped P inp o group tl) :
    res.scene.labels = inp.labels.filterMap fun model =>
      (((child.scene.labels.map fun label : SceneLabel =>
          { label with rect := shiftRect dx dy label.rect }) ++
        parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)).bind
        fun label =>
        some (if model.owner == group.id then
          { label with rect := (childTitleRect group.direction P.clusterPad
              (tl.foldl (fun width (line : Measure.Line) => max width line.width) 0) titleHeight
              frame.rect) }
          else label) := by
  obtain ⟨metricW, hmetricW, hwrapW⟩ := hwrap
  obtain ⟨frame₀, metric₀, tl₀, _lines₀, _dx₀, _dy₀, hframe₀, hmetric₀, htitle₀, _,
    _, _, _, _⟩ := expandChild_sources hexpand
  have hff : frame₀ = frame := Option.some.inj (hframe₀.symm.trans hframe)
  have hm : metricW = metric₀ := Except.ok.inj (hmetricW.symm.trans hmetric₀)
  rw [hm] at hwrapW
  have htl : tl = tl₀ := Except.ok.inj (hwrapW.symm.trans htitle₀)
  subst hm
  subst tl₀
  unfold expandChild at hexpand
  cases hf : parent.scene.boxes.find? (fun box => box.id == group.id) with
  | none => rw [hframe] at hf; simp at hf
  | some fr =>
    simp only [hf] at hexpand
    have hfr : fr = frame := Option.some.inj (hf.symm.trans hframe)
    subst fr
    obtain ⟨frame', hframe', hexpand⟩ := bind_ok' hexpand
    have hefr : frame = frame' := Except.ok.inj hframe'
    subst frame'
    obtain ⟨metric', hmetric', hexpand⟩ := bind_ok' hexpand
    obtain ⟨titleLines', htitle', hexpand⟩ := bind_ok' hexpand
    obtain ⟨itemMetric', hitemMetric', hexpand⟩ := bind_ok' hexpand
    have hem : itemMetric' = metric' := Except.ok.inj (hitemMetric'.symm.trans hmetric')
    subst itemMetric'
    obtain ⟨lines', hlines', hexpand⟩ := bind_ok' hexpand
    have hme : metric' = metricW := Except.ok.inj (hmetric'.symm.trans hmetricW)
    rw [hme] at htitle'
    have htl' : tl = titleLines' := Except.ok.inj (htitle₀.symm.trans htitle')
    subst titleLines'
    have he := Except.ok.inj hexpand
    subst res
    rw [hdx, hdy]
    rfl

/-- The label classification of both merge variants for a successful
`expandChild` under the recursion's call context and the label-owner
invariant `ExpandChildLabelOwners`: every merged label is the group's
caption at the title rect, a shifted child-scene label, or a verbatim
parent-scene label. -/
theorem expandChild_label_classes_wrapped
    {P : Params} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {child parent : FamilyResult} {titleHeight : Int}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (howners : ExpandChildLabelOwners inp parent child) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      ExpandChildLabelClassesC8 P group tl titleHeight frame dx dy parent child res ∧
      ExpandChildLabelClasses P group tl titleHeight frame dx dy parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hlabels := expandChild_labels_eq_wrapped hexpand frame tl dx dy hframe hdx hdy hwrap
  have hcl : ∀ rl ∈ res.scene.layoutDump.labels,
      (rl.owner = group.id ∧
          rl.rect = childTitleRect group.direction P.clusterPad
            (tl.foldl (fun width line => max width line.width) 0) titleHeight frame.rect) ∨
      (∃ cl ∈ child.scene.labels, rl.owner ≠ group.id ∧ rl.id = cl.id ∧
          rl.owner = cl.owner ∧ rl.rect = shiftRect dx dy cl.rect) ∨
      (∃ pl ∈ parent.scene.labels, rl.owner ≠ group.id ∧ rl.id = pl.id ∧
          rl.owner = pl.owner ∧ rl.rect = pl.rect) := by
    intro rl hrl
    simp only [Scene.layoutDump, List.mem_map] at hrl
    obtain ⟨sl, hslmem, hslr⟩ := hrl
    rw [hlabels] at hslmem
    obtain ⟨model, hmodel, hprod⟩ := List.mem_filterMap.mp hslmem
    obtain ⟨label, hfind, hbody⟩ : ∃ label : SceneLabel,
        (((child.scene.labels.map
            (fun l : SceneLabel => { l with rect := shiftRect dx dy l.rect })) ++
          parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) =
          some label ∧
        (if model.owner == group.id then
          { label with rect := (childTitleRect group.direction P.clusterPad
            (tl.foldl (fun width line => max width line.width) 0) titleHeight
            frame.rect) }
          else label) = sl := by
      cases hfind : (((child.scene.labels.map
          (fun l : SceneLabel => { l with rect := shiftRect dx dy l.rect })) ++
          parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) with
      | none => rw [hfind] at hprod; simp at hprod
      | some label =>
        rw [hfind] at hprod
        rw [Option.bind_some] at hprod
        exact ⟨label, rfl, Option.some.inj hprod⟩
    have hsl : sl = if model.owner == group.id then
        { label with rect := (childTitleRect group.direction P.clusterPad
            (tl.foldl (fun width line => max width line.width) 0) titleHeight
            frame.rect) }
        else label := hbody.symm
    have hlabelId : label.id = model.id := by
      have hp := List.find?_some hfind
      exact beq_iff_eq.mp hp
    have hlabelMem : label ∈ (child.scene.labels.map
        (fun l => { l with rect := shiftRect dx dy l.rect })) ++
        parent.scene.labels := List.mem_of_find?_eq_some hfind
    have howner : label.owner = model.owner := by
      rcases List.mem_append.mp hlabelMem with hcm | hpm
      · obtain ⟨cl, hclMem, hclEq⟩ := List.mem_map.mp hcm
        have h1 : label.id = cl.id := by rw [← hclEq]
        have h2 : model.owner = cl.owner :=
          howners.1 cl hclMem model hmodel (hlabelId.symm.trans h1)
        rw [← hclEq]
        exact h2.symm
      · have h1 : label = id label := rfl
        have h2 : model.owner = label.owner :=
          howners.2 label hpm model hmodel hlabelId.symm
        exact h2.symm
    by_cases hcond : (model.owner == group.id) = true
    · have hog : model.owner = group.id := beq_iff_eq.mp hcond
      rw [hcond] at hsl
      simp only [reduceIte] at hsl
      refine Or.inl ⟨?_, ?_⟩
      · rw [← hslr, hsl]
        show label.owner = group.id
        rw [howner]
        exact hog
      · rw [← hslr, hsl]
    · have hog : ¬(model.owner = group.id) := fun h => hcond (by simp [h])
      have hcondF : (model.owner == group.id) = false := by
        cases hb : (model.owner == group.id) with
        | false => rfl
        | true => exact absurd hb hcond
      rw [hcondF] at hsl
      simp only [Bool.false_eq_true, reduceIte] at hsl
      rcases List.mem_append.mp hlabelMem with hcm | hpm
      · obtain ⟨cl, hclMem, hclEq⟩ := List.mem_map.mp hcm
        refine Or.inr (Or.inl ⟨cl, hclMem, ?_, ?_, ?_, ?_⟩)
        · rw [← hslr, hsl]
          show label.owner ≠ group.id
          rw [howner]
          exact hog
        · rw [← hslr, hsl]
          show label.id = cl.id
          rw [← hclEq]
        · rw [← hslr, hsl]
          show label.owner = cl.owner
          rw [← hclEq]
        · rw [← hslr, hsl]
          show label.rect = shiftRect dx dy cl.rect
          rw [← hclEq]
      · refine Or.inr (Or.inr ⟨label, hpm, ?_, ?_, ?_, ?_⟩)
        · rw [← hslr, hsl]
          show label.owner ≠ group.id
          rw [howner]
          exact hog
        · rw [← hslr, hsl]
        · rw [← hslr, hsl]
        · rw [← hslr, hsl]
  refine ⟨fun rl hrl => hcl rl hrl, fun rl hrl => hcl rl hrl⟩

/-- The structural residual `ExpandChildC8bStructure` reduces to, for a
successful `expandChild`: the label classification, stated at the wrapped
title lines the expansion measured, under the label-owner invariant. -/
theorem expandChild_c8b_structure_wrapped
    {P : Params} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {child parent : FamilyResult} {titleHeight : Int}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (howners : ExpandChildLabelOwners inp parent child) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      ExpandChildLabelClassesC8 P group tl titleHeight frame dx dy parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  exact (expandChild_label_classes_wrapped hexpand howners frame tl dx dy hframe hdx hdy
    hwrap).1

/-- The three label-scope conjuncts of `ExpandChildC7Structure`, split out as
a named residual: the owner-scope transports of child and parent labels into
the merged dump, and the scope anchors of every merged label.  All three
presuppose the `labelOwnerAnc` route-endpoint and ancestor walks of the
merged dump; no proved fact of the expansion supplies them yet. -/
def ExpandChildC7LabelScopes (_P : Params) (group : ModelBox)
    (parent child result : FamilyResult) : Prop :=
  (∀ cl ∈ child.scene.labels, ∀ rl ∈ result.scene.layoutDump.labels, rl.id = cl.id →
      ∀ x ∈ child.scene.layoutDump.labelOwnerAnc cl.toLabel,
        x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
  (∀ pl ∈ parent.scene.labels, ∀ rl ∈ result.scene.layoutDump.labels, rl.id = pl.id →
      ∀ x ∈ parent.scene.layoutDump.labelOwnerAnc pl.toLabel,
        x ∈ result.scene.layoutDump.labelOwnerAnc rl) ∧
  (∀ rl ∈ result.scene.layoutDump.labels,
      ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
        x ∈ result.scene.layoutDump.labelOwnerAnc rl)

/-- The structural residual `ExpandChildC7Structure` reduces to, for a
successful `expandChild` under the recursion's call context: the shared core
(box-lookup transports and scene-size bounds), the label classification
under the label-owner invariant, and the split-out label-scope residual,
each stated at the wrapped title lines the expansion measured. -/
theorem expandChild_c7_structure_wrapped
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hchild : layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (howners : ExpandChildLabelOwners inp parent child)
    (hscopes : ExpandChildC7LabelScopes P group parent child res) :
    ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
      (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
          res.scene.layoutDump.box? b.id = some b) ∧
      child.scene.boxes.length ≤ res.scene.boxes.length ∧
      parent.scene.boxes.length ≤ res.scene.boxes.length ∧
      ExpandChildLabelClasses P group tl titleHeight frame dx dy parent child res ∧
      (∀ cl ∈ child.scene.labels, ∀ rl ∈ res.scene.layoutDump.labels, rl.id = cl.id →
          ∀ x ∈ child.scene.layoutDump.labelOwnerAnc cl.toLabel,
            x ∈ res.scene.layoutDump.labelOwnerAnc rl) ∧
      (∀ pl ∈ parent.scene.labels, ∀ rl ∈ res.scene.layoutDump.labels, rl.id = pl.id →
          ∀ x ∈ parent.scene.layoutDump.labelOwnerAnc pl.toLabel,
            x ∈ res.scene.layoutDump.labelOwnerAnc rl) ∧
      (∀ rl ∈ res.scene.layoutDump.labels,
          ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
            x ∈ res.scene.layoutDump.labelOwnerAnc rl) := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hcore := expandChild_core_wrapped hwf hgroup hchild hparent hexpand
    frame tl dx dy hframe hdx hdy hwrap
  have hcl := (expandChild_label_classes_wrapped hexpand howners frame tl dx dy hframe
    hdx hdy hwrap).2
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcl,
    hscopes.1, hscopes.2.1, hscopes.2.2⟩
end Elegant.Layered.PipelineImpl
