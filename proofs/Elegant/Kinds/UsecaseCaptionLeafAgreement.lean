import Elegant.Kinds.UsecaseDrawShapesExecutedProof

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

open Layered Layered.PipelineImpl

private theorem measuredLabel_route_source {P : Params} {metric : Measure.Metric}
    {target : Int} {inp : Input} {direction : Direction} {measured : List MeasuredLabel}
    (h : measureLabels P metric target inp direction = .ok measured)
    {l : MeasuredLabel} (hl : l ∈ measured) :
    ∃ source, inp.labels[l.index]? = some source ∧ source.owner ∈ inp.routes.map (·.id) := by
  unfold measureLabels at h
  obtain ⟨options, hoptions, h⟩ := bind_ok h
  rw [← Except.ok.inj h] at hl
  obtain ⟨opt, hopt, hval⟩ := List.mem_filterMap.mp hl
  have hsome : opt = some l := hval
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hsome ▸ hopt)
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hoptions
  have hiz : i < inp.labels.zipIdx.length := hlen ▸ (List.getElem?_eq_some_iff.mp hi).1
  have hil : i < inp.labels.length := by simpa only [List.length_zipIdx] using hiz
  let source := inp.labels[i]
  have hsource : inp.labels[i]? = some source := List.getElem?_eq_getElem hil
  have hget : inp.labels.zipIdx[i]? = some (source, i) := by
    simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add]
  obtain ⟨result, hstep, hresult⟩ := hidx i (source, i) hget
  rw [hi] at hresult
  have he : result = some l := (Option.some.inj hresult).symm
  subst result
  dsimp only at hstep
  split at hstep
  · change Except.ok none = Except.ok (some l) at hstep
    cases hstep
  · next edge hroute =>
    obtain ⟨hedge, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hroute
    have hrouteMem : source.owner ∈ inp.routes.map (·.id) :=
      List.mem_map.mpr ⟨inp.routes[edge], List.getElem_mem hedge, beq_iff_eq.mp hmatch⟩
    obtain ⟨lines, _, hstep⟩ := bind_ok hstep
    by_cases hover :
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 ∨
        I32_MAX < (lines.length : Int) * P.lineH ∨
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 +
          (if metric.profile == .cell then P.slot else 0) ∨
        I32_MAX < (lines.length : Int) * P.lineH +
          (if metric.profile == .cell then P.slot else 0)
    · simp only [hover, ↓reduceIte] at hstep
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
    · simp only [hover, ↓reduceIte] at hstep
      cases direction <;>
        dsimp only at hstep <;>
        have he := Option.some.inj (Except.ok.inj hstep) <;>
        subst l
      all_goals exact ⟨source, hsource, hrouteMem⟩

private theorem leaf_caption_source {ids : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX ids inp o res)
    (hids : BoxRouteIdsDisjoint inp) {l : SceneLabel} (hl : l ∈ res.scene.labels)
    (hbox : l.owner ∈ inp.boxes.map (·.id)) :
    ∃ key box, inp.boxes[key]? = some box ∧ box.exclusive = false ∧ box.id = l.owner ∧
      (∃ source ∈ inp.labels, source.owner = box.id) ∧
      l.rect = sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc key box.id := by
  rw [execution.scene_eq] at hl
  simp only [sceneOf] at hl
  obtain ⟨⟨source, index⟩, hq, hemitted⟩ := List.mem_filterMap.mp hl
  have hsource : inp.labels[index]? = some source := List.mem_zipIdx_iff_getElem?.mp hq
  cases hex : inp.boxes.any (fun box => box.id == source.owner && box.exclusive) with
  | true => simp only [hex, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hex, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == index) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      have howner : l.owner = source.owner :=
        (congrArg (fun label : SceneLabel => label.toLabel.owner) hemitted).symm
      obtain ⟨model, hmodel, hroute⟩ := measuredLabel_route_source execution.measured_eq
        (List.mem_of_find?_eq_some hm)
      have hpred : (measured.index == index) = true :=
        List.find?_some (p := fun item : MeasuredLabel => item.index == index) hm
      have hindex : measured.index = index := beq_iff_eq.mp hpred
      rw [hindex, hsource] at hmodel
      have he := Option.some.inj hmodel
      exact (hids l.owner hbox (by simpa only [howner, he] using hroute)).elim
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some key =>
        simp only [ho, Option.some.injEq] at hemitted
        obtain ⟨hkey, hpred, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
        let box := inp.boxes[key]
        have hget : inp.boxes[key]? = some box := List.getElem?_eq_getElem hkey
        have hp : box.id = source.owner ∧ box.exclusive = false := by
          simpa only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] using hpred
        have howner : l.owner = source.owner :=
          (congrArg (fun label : SceneLabel => label.toLabel.owner) hemitted).symm
        refine ⟨key, box, hget, hp.2, hp.1.trans howner.symm,
          ⟨source, List.mem_of_getElem? hsource, hp.1.symm⟩, ?_⟩
        rw [hp.1]
        have heq : l = _ := hemitted.symm
        rw [congrArg (fun s : SceneLabel => s.rect) heq]
        unfold sceneCaptionRect
        have hfields := straightenAcc_fields execution.straight_eq
        rw [hfields.1, hfields.2.2.1, hfields.2.2.2.2]
        rfl

private theorem nonedge_sceneItem_source {P : Params} {inp : Input} {boxes : List Box}
    {routes : List Route} {lines : List (List Measure.Line)} {labels : List SceneLabel}
    {raw : Group} (hraw : raw ∈ sceneItems P inp boxes routes lines labels)
    (hrole : raw.role ≠ .edge) :
    ∃ q ∈ boxes.zipIdx, raw.owner = q.1.id ∧
      raw = if q.1.role == "group" then
        ⟨.group, q.1.id, groupItems P q.1.rect (lines.getD q.2 [])⟩
      else ⟨.node, q.1.id, nodeItems P q.1.rect (lines.getD q.2 [])⟩ := by
  unfold sceneItems at hraw
  rcases List.mem_append.mp hraw with hframesOrEdges | hnodes
  · rcases List.mem_append.mp hframesOrEdges with hframes | hedges
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hframes
      obtain ⟨hmem, hgroup⟩ := List.mem_filter.mp hq
      exact ⟨q, hmem, rfl, (ite_eq_left hgroup).symm⟩
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hedges
      exact (hrole rfl).elim
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hnodes
    obtain ⟨hmem, hnode⟩ := List.mem_filter.mp hq
    have hnot : ¬ (q.1.role == "group") = true := by
      rw [beq_iff_eq.mp hnode]
      decide
    exact ⟨q, hmem, rfl, (ite_eq_right hnot).symm⟩

private theorem nonedge_sceneItem_owner_unique {P : Params} {inp : Input} {boxes : List Box}
    {routes : List Route} {lines : List (List Measure.Line)} {labels : List SceneLabel}
    {titles : List (String × Rect)} (hids : (boxes.map (·.id)).Nodup) {a b : Group}
    (ha : a ∈ applyTitles titles (sceneItems P inp boxes routes lines labels))
    (hb : b ∈ applyTitles titles (sceneItems P inp boxes routes lines labels))
    (har : a.role ≠ .edge) (hbr : b.role ≠ .edge) (howner : a.owner = b.owner) : a = b := by
  let paint (raw : Group) : Group :=
    match titles.find? (fun title => title.1 == raw.owner) with
    | none => raw
    | some title => { raw with items := raw.items.map fun item =>
        match item with
        | .text text => .text { text with rect := title.2 }
        | _ => item }
  have fields (raw : Group) : (paint raw).owner = raw.owner ∧ (paint raw).role = raw.role := by
    cases h : titles.find? (fun title => title.1 == raw.owner) <;> simp [paint, h]
  change a ∈ (sceneItems P inp boxes routes lines labels).map paint at ha
  change b ∈ (sceneItems P inp boxes routes lines labels).map paint at hb
  obtain ⟨rawA, hrawA, rfl⟩ := List.mem_map.mp ha
  obtain ⟨rawB, hrawB, rfl⟩ := List.mem_map.mp hb
  obtain ⟨qa, hqa, hoa, hshapeA⟩ := nonedge_sceneItem_source hrawA
    (fun h => har ((fields rawA).2.trans h))
  obtain ⟨qb, hqb, hob, hshapeB⟩ := nonedge_sceneItem_source hrawB
    (fun h => hbr ((fields rawB).2.trans h))
  have hid : qa.1.id = qb.1.id :=
    hoa.symm.trans ((fields rawA).1.symm.trans (howner.trans ((fields rawB).1.trans hob)))
  have hgetA : boxes[qa.2]? = some qa.1 := List.mem_zipIdx_iff_getElem?.mp hqa
  have hgetB : boxes[qb.2]? = some qb.1 := List.mem_zipIdx_iff_getElem?.mp hqb
  have hlookup : (boxes.map (·.id))[qa.2]? = (boxes.map (·.id))[qb.2]? := by
    simp only [List.getElem?_map, hgetA, hgetB, Option.map_some, hid]
  have hbound : qa.2 < (boxes.map (·.id)).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hgetA).1
  have hkey := (List.Nodup.getElem?_inj hbound hids).mp hlookup
  rw [hkey] at hgetA
  have hpair : qa = qb := Prod.ext (Option.some.inj (hgetA.symm.trans hgetB)) hkey
  apply congrArg paint
  rw [hshapeA, hshapeB, hpair]

/-- Every emitted box-owned validator label uses the first display text rectangle
of its owner in the same exact flat scene. -/
theorem exact_leaf_caption_agreement {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX ids inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfit : InputFixedFit inp o)
    (hdisjoint : BoxRouteIdsDisjoint inp)
    {l : Label} (hl : l ∈ res.scene.layoutDump.labels)
    (hbox : l.owner ∈ res.scene.layoutDump.boxes.map (·.id))
    {g : Group} (hg : g ∈ res.scene.items) (hrole : g.role ≠ .edge)
    (howner : g.owner = l.owner) : firstText g.items = some l.rect := by
  change l ∈ res.scene.labels.map (·.toLabel) at hl
  obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hl
  have hsceneIds : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapX, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hmodelOwner : label.owner ∈ inp.boxes.map (·.id) := by
    rw [← hsceneIds]
    exact hbox
  obtain ⟨key, box, hkey, hex, hboxOwner, howned, hrect⟩ :=
    leaf_caption_source execution hdisjoint hlabel hmodelOwner
  obtain ⟨actual, ha, haOwner, haRole, haFirst⟩ :=
    exact_leaf_caption_firstText execution hwf hfit hkey hex howned
  have hfields_items := straightenAcc_fields execution.straight_eq
  have hitems : res.scene.items =
      applyTitles (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc)
        (sceneItems execution.params inp res.scene.boxes res.scene.routes execution.lines
          res.scene.labels) := by
    rw [execution.scene_eq]
    simp only [sceneOf, hfields_items.2.2.1, hfields_items.2.2.2.2]
    rfl
  have hids : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hsceneIds]
    exact Model.boxIds_nodup hwf
  rw [hitems] at hg ha
  have heq : g = actual := nonedge_sceneItem_owner_unique hids hg ha hrole haRole
    (howner.trans (hboxOwner.symm.trans haOwner.symm))
  rw [heq, haFirst]
  exact congrArg Option.some hrect.symm

end Elegant.Kinds.Usecase
