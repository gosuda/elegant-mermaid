import Elegant.Layered.ExactAttachedFlatFrameProof
import Elegant.Layered.ExpandChildParentRouteAttachedCtxProof
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.SubInputWellFormedFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- An attached route and frame come from the same successful flat call with the
    same fixed-size entry. Child embeddings translate their geometry together;
    parent embeddings leave it unchanged. -/
def AttachedFixedLeaf (base : Input → Options → Except LayoutError FamilyResult)
    (boxId : String) (entry : String × Size) (frame : Box) (route : Route) : Prop :=
  ∃ (inp : Input) (o : Options) (res : FamilyResult) (nativeFrame : Box)
    (nativeRoute : Route) (dx dy : Int),
    base inp o = .ok res ∧ WellFormed (inputModel inp o) ∧
    inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry ∧
    res.scene.layoutDump.box? boxId = some nativeFrame ∧ nativeRoute ∈ res.scene.routes ∧
    route.fromId = nativeRoute.fromId ∧ route.toId = nativeRoute.toId ∧
    route.points = nativeRoute.points.map (shiftPoint dx dy) ∧
    frame.rect = shiftRect dx dy nativeFrame.rect

private theorem attachedFixedLeaf_flat
    {base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : base inp o = .ok res) (hwf : WellFormed (inputModel inp o))
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry)
    {frame : Box} (hframe : res.scene.layoutDump.box? boxId = some frame)
    {route : Route} (hroute : route ∈ res.scene.routes) :
    AttachedFixedLeaf base boxId entry frame route := by
  refine ⟨inp, o, res, frame, route, 0, 0, h, hwf, hfixed, hframe, hroute,
    rfl, rfl, ?_, ?_⟩
  · have hz : shiftPoint 0 0 = id := by
      funext p
      cases p
      simp [shiftPoint]
    rw [hz, List.map_id]
  · cases frame.rect
    simp [shiftRect]

private theorem selected_box_kept {inp : Input} {keep : String → Bool} {root : String}
    {box : ModelBox} (h : box ∈ (selectInput inp (fun b => keep b.id) root).boxes) :
    keep box.id = true := by
  obtain ⟨_, _, hkeep, hid, _⟩ := selectInput_box_spec inp (fun b => keep b.id) root h
  rw [hid]
  exact hkeep

private theorem selected_route_endpoint_kept
    {inp : Input} {keep : String → Bool} {root : String} {model : ModelRoute}
    (h : model ∈ (selectInput inp (fun b => keep b.id) root).routes)
    {key : String} (hkey : model.fromId = key ∨ model.toId = key) : keep key = true := by
  obtain ⟨⟨fromBox, hfrom, hfid⟩, ⟨toBox, hto, htid⟩⟩ :=
    selectInput_routesCovered inp (fun b => keep b.id) root model h
  rcases hkey with hkey | hkey
  · rw [← hkey, ← hfid]
    exact selected_box_kept (inp := inp) (root := root) (keep := keep) hfrom
  · rw [← hkey, ← htid]
    exact selected_box_kept (inp := inp) (root := root) (keep := keep) hto

private theorem parent_fixed_lookup_preserved {inp : Input} {group : ModelBox}
    {P : Params} {titleLines : List Measure.Line} {child : FamilyResult}
    {boxId : String} {entry : String × Size}
    (h : inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry) :
    (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun fixed => fixed.1 == boxId) = some entry := by
  change (inp.fixedSizes ++ [_]).find? (fun fixed => fixed.1 == boxId) = some entry
  rw [List.find?_append, h, Option.some_or]

set_option maxHeartbeats 600000 in
private theorem layoutRecursiveB_attached_origins
    (base : Input → Options → Except LayoutError FamilyResult)
    (hscene : ∀ {inp o res}, base inp o = .ok res →
      ∃ P lines acc measured, res.scene = sceneOf P inp o lines acc measured) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → layoutRecursiveB base fuel inp o = .ok res →
      (∀ box ∈ res.scene.boxes, ∃ model ∈ inp.boxes, model.id = box.id) ∧
      (∀ route ∈ res.scene.routes, ∃ model ∈ inp.routes,
        route.fromId = model.fromId ∧ route.toId = model.toId) ∧
      ∀ {boxId : String} {entry : String × Size},
        inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry →
        ∀ {frame : Box}, res.scene.layoutDump.box? boxId = some frame →
        ∀ {route : Route}, route ∈ res.scene.routes →
          (route.fromId = boxId ∨ route.toId = boxId) →
          AttachedFixedLeaf base boxId entry frame route := by
  have flat : ∀ {inp o res}, WellFormed (inputModel inp o) → base inp o = .ok res →
      (∀ box ∈ res.scene.boxes, ∃ model ∈ inp.boxes, model.id = box.id) ∧
      (∀ route ∈ res.scene.routes, ∃ model ∈ inp.routes,
        route.fromId = model.fromId ∧ route.toId = model.toId) ∧
      ∀ {boxId : String} {entry : String × Size},
        inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry →
        ∀ {frame : Box}, res.scene.layoutDump.box? boxId = some frame →
        ∀ {route : Route}, route ∈ res.scene.routes →
          (route.fromId = boxId ∨ route.toId = boxId) →
          AttachedFixedLeaf base boxId entry frame route := by
    intro inp o res hwf h
    obtain ⟨P, lines, acc, measured, hs⟩ := hscene h
    refine ⟨?_, ?_, ?_⟩
    · intro box hb
      simp only [hs, sceneOf] at hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl⟩
    · intro route hr
      simp only [hs, sceneOf] at hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩
    · intro boxId entry hfix frame hf route hr _
      exact attachedFixedLeaf_flat h hwf hfix hf hr
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf h
    exact flat hwf h
  | succ fuel ih =>
    intro inp o res hwf h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hl⟩ |
      ⟨group, P, _metric, child, titleLines, parent, _hg, _hP, _hm, hc, _ht, hp, hx⟩
    · exact flat hwf hl
    have hsub := subInputWellFormedC2 inp o group hwf
    have hcWF : WellFormed (inputModel (childSubInput inp group)
        (childSubOptions o group)) := hsub.1
    let parentInput := parentSubInput inp group P titleLines child
    have hpWF : WellFormed (inputModel parentInput o) :=
      hsub.2 parentInput.fixedSizes parentInput.fixedChildren parentInput.fixedAreas
    have childOrigins := ih (childSubInput inp group) (childSubOptions o group) child hcWF hc
    have parentOrigins := ih parentInput o parent hpWF hp
    obtain ⟨groupFrame, metric, titles, _, dx, dy, hgFrame, hm, ht, _, hdx, hdy, _, hb⟩ :=
      expandChild_sources hx
    have hr := expandChild_routes_eq hx groupFrame metric titles dx dy hgFrame hm ht hdx hdy
    have routeSide : ∀ route ∈ res.scene.routes,
        (∃ native ∈ child.scene.routes,
          { native with points := native.points.map (shiftPoint dx dy) } = route) ∨
        route ∈ parent.scene.routes := by
      intro route hroute
      rw [hr] at hroute
      obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hroute
      rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hchild | hparent
      · exact Or.inl (List.mem_map.mp hchild)
      · exact Or.inr hparent
    refine ⟨?_, ?_, ?_⟩
    · intro box hbox
      rw [hb] at hbox
      obtain ⟨model, hmodel, hfind⟩ := List.mem_filterMap.mp hbox
      have hboxId : (box.id == model.id) = true :=
        List.find?_some (p := fun candidate : Box => candidate.id == model.id) hfind
      exact ⟨model, hmodel, (beq_iff_eq.mp hboxId).symm⟩
    · intro route hroute
      rcases routeSide route hroute with ⟨native, hnative, rfl⟩ | hparent
      · obtain ⟨model, hmodel, hfrom, hto⟩ := childOrigins.2.1 native hnative
        exact ⟨model, ((selectInput_route_mem inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id model).mp hmodel).1,
          hfrom, hto⟩
      · obtain ⟨model, hmodel, hfrom, hto⟩ := parentOrigins.2.1 route hparent
        exact ⟨model, ((selectInput_route_mem inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" model).mp hmodel).1,
          hfrom, hto⟩
    · intro boxId entry hfixed frame hframe route hroute hatt
      have hframe' : res.scene.boxes.find? (fun box => box.id == boxId) = some frame := hframe
      have hmem := List.mem_of_find?_eq_some hframe'
      rw [hb] at hmem
      obtain ⟨model, _, hlookup⟩ := List.mem_filterMap.mp hmem
      have hmodelId : (frame.id == model.id) = true :=
        List.find?_some (p := fun candidate : Box => candidate.id == model.id) hlookup
      have hframeId : (frame.id == boxId) = true :=
        List.find?_some (p := fun candidate : Box => candidate.id == boxId) hframe'
      have hid : model.id = boxId :=
        (beq_iff_eq.mp hmodelId).symm.trans (beq_iff_eq.mp hframeId)
      rw [hid, List.find?_append, List.find?_map] at hlookup
      change ((child.scene.boxes.find? (fun box => box.id == boxId)).map
        (embedBox group.id dx dy)).or
          (parent.scene.boxes.find? (fun box => box.id == boxId)) = some frame at hlookup
      cases hchildFrame : child.scene.boxes.find? (fun box => box.id == boxId) with
      | none =>
        have hparentFrame : parent.scene.layoutDump.box? boxId = some frame := by
          simpa only [Scene.layoutDump, LayoutDump.box?, hchildFrame, Option.map_none,
            Option.none_or] using hlookup
        rcases routeSide route hroute with ⟨native, hnative, rfl⟩ | hparent
        · change native.fromId = boxId ∨ native.toId = boxId at hatt
          obtain ⟨source, hsource, hfrom, hto⟩ := childOrigins.2.1 native hnative
          have hkept : Compound.inside inp.boxes group.id boxId = true :=
            selected_route_endpoint_kept (inp := inp) (root := group.id)
              (keep := Compound.inside inp.boxes group.id) hsource
              (by simpa only [hfrom, hto] using hatt)
          have hpf : parent.scene.boxes.find? (fun box => box.id == boxId) = some frame :=
            hparentFrame
          obtain ⟨sourceBox, hsourceBox, hsid⟩ :=
            parentOrigins.1 frame (List.mem_of_find?_eq_some hpf)
          have hpfId : (frame.id == boxId) = true :=
            List.find?_some (p := fun candidate : Box => candidate.id == boxId) hpf
          have hpid : sourceBox.id = boxId :=
            hsid.trans (beq_iff_eq.mp hpfId)
          have hn : (!Compound.inside inp.boxes group.id sourceBox.id) = true :=
            selected_box_kept (inp := inp) (root := "")
              (keep := fun key => !Compound.inside inp.boxes group.id key) hsourceBox
          simp [hpid, hkept] at hn
        · exact parentOrigins.2.2 (parent_fixed_lookup_preserved hfixed) hparentFrame hparent hatt
      | some nativeFrame =>
        have hembed : embedBox group.id dx dy nativeFrame = frame := by
          apply Option.some.inj
          simpa only [hchildFrame, Option.map_some, Option.some_or] using hlookup
        rcases routeSide route hroute with ⟨native, hnative, rfl⟩ | hparent
        · have hcf : child.scene.layoutDump.box? boxId = some nativeFrame := hchildFrame
          obtain ⟨leaf, lo, lr, lf, lrt, sx, sy, hl, hw, hfix, hlf, hlrt, hfrom, hto,
            hpoints, hrect⟩ := childOrigins.2.2 hfixed hcf hnative hatt
          refine ⟨leaf, lo, lr, lf, lrt, sx + dx, sy + dy, hl, hw, hfix, hlf, hlrt,
            hfrom, hto, ?_, ?_⟩
          · change native.points.map (shiftPoint dx dy) = _
            rw [hpoints, List.map_map]
            apply List.map_congr_left
            intro pt _
            simp [Function.comp_apply, shiftPoint, Int.add_assoc]
          · rw [← hembed]
            change shiftRect dx dy nativeFrame.rect = _
            rw [hrect]
            simp [shiftRect, Int.add_assoc]
        · obtain ⟨source, hsource, hfrom, hto⟩ := parentOrigins.2.1 route hparent
          have hkept : (!Compound.inside inp.boxes group.id boxId) = true :=
            selected_route_endpoint_kept (inp := inp) (root := "")
              (keep := fun key => !Compound.inside inp.boxes group.id key) hsource
              (by simpa only [hfrom, hto] using hatt)
          obtain ⟨sourceBox, hsourceBox, hsid⟩ :=
            childOrigins.1 nativeFrame (List.mem_of_find?_eq_some hchildFrame)
          have hcfId : (nativeFrame.id == boxId) = true :=
            List.find?_some (p := fun candidate : Box => candidate.id == boxId) hchildFrame
          have hcid : sourceBox.id = boxId :=
            hsid.trans (beq_iff_eq.mp hcfId)
          have hy : Compound.inside inp.boxes group.id sourceBox.id = true :=
            selected_box_kept (inp := inp) (root := group.id)
              (keep := Compound.inside inp.boxes group.id) hsourceBox
          rw [hcid] at hy
          simp [hy] at hkept

/-- The exact flat endpoint theorem lifts through the actual exact recursion.
    No cross-side geometry or completed recursive C5 is required. -/
theorem layoutRecursiveX_attached_fixed_frame_miss
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : layoutRecursiveX exactIds fuel inp o = .ok res)
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry)
    {frame : Box} (hframe : res.scene.layoutDump.box? boxId = some frame)
    {route : Route} (hroute : route ∈ res.scene.routes)
    (hatt : route.fromId = boxId ∨ route.toId = boxId) :
    ¬ Polyline.hitsRect route.points frame.rect := by
  have origins := layoutRecursiveB_attached_origins (layoutX exactIds) (by
    intro ip op rr hl
    obtain ⟨execution⟩ := layoutX_sceneExecution hl
    exact ⟨execution.params, execution.lines, execution.packedAcc, execution.measured,
      execution.scene_eq⟩) fuel inp o res hwf h
  obtain ⟨_, _, _, _, _, dx, dy, hl, hw, hfix, hf, hr, hfrom, hto, hpoints, hrect⟩ :=
    origins.2.2 hfixed hframe hroute hatt
  obtain ⟨execution⟩ := layoutX_sceneExecution hl
  rw [hpoints, hrect, hitsRect_shift]
  exact execution.attached_fixed_frame_miss hw hfix hf hr (by simpa only [hfrom, hto] using hatt)

/-- The ordinary call context supplies the fixed entry for the frame being
    expanded and a successful ordinary flat ancestor for each attached route. -/
theorem expandChild_parent_attached_fixed_leaf
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res) :
    ∃ entry : String × Size,
      ∀ {frame : Box}, parent.scene.layoutDump.box? group.id = some frame →
      ∀ {route : Route}, route ∈ parent.scene.routes →
        (route.fromId = group.id ∨ route.toId = group.id) →
        AttachedFixedLeaf layout group.id entry frame route := by
  obtain ⟨entry, hfixed⟩ := parentInput_group_fixedEntry hctx
  let parentInput := parentSubInput inp group P titleLines child
  have hwf : WellFormed (inputModel parentInput o) :=
    (subInputWellFormedC2 inp o group hctx.1).2
      parentInput.fixedSizes parentInput.fixedChildren parentInput.fixedAreas
  have hp := hctx.2.2.2.2.1
  rw [layoutRecursive_eq_B] at hp
  have origins := layoutRecursiveB_attached_origins layout (by
    intro ip op rr h
    obtain ⟨execution⟩ := layout_sceneExecution h
    exact ⟨execution.params, execution.lines, execution.packedAcc, execution.measured,
      execution.scene_eq⟩) fuel parentInput o parent hwf hp
  refine ⟨entry, ?_⟩
  intro frame hframe route hroute hatt
  exact origins.2.2 hfixed hframe hroute hatt

/-- The ordinary seam needs router clearance only at an ordinary flat leaf.
    The exact leaf theorem has different placement and loop premises and is
    not a witness for this leaf obligation. -/
theorem parentRouteAttachedClear_of_ordinary_flat
    (flatMiss : ∀ {inp : Input} {o : Options} {res : FamilyResult},
      SceneExecution inp o res → WellFormed (inputModel inp o) →
      ∀ {boxId : String} {entry : String × Size},
        inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry →
        ∀ {frame : Box}, res.scene.layoutDump.box? boxId = some frame →
        ∀ {route : Route}, route ∈ res.scene.routes →
          (route.fromId = boxId ∨ route.toId = boxId) →
          ¬ Polyline.hitsRect route.points frame.rect)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hvalid : ParentRouteAttachedCtxPremise group parent) :
    ExpandChildParentRouteAttachedClear group parent := by
  obtain ⟨_, source⟩ := expandChild_parent_attached_fixed_leaf hctx
  apply parentRouteAttachedClear_of_recursion_ctx fuel P inp o group titleLines titleHeight
    parent child res hctx.2.2.2.2.2 hframed hctx hparams hvalid
  intro frame hframe route hroute hatt _ _ _ _ _ _ _ _ _ _
  obtain ⟨_, _, _, _, _, dx, dy, hl, hw, hfix, hf, hr, hfrom, hto, hpoints, hrect⟩ :=
    source (hvalid.2 frame hframe) hroute hatt
  obtain ⟨execution⟩ := layout_sceneExecution hl
  rw [hpoints, hrect, hitsRect_shift]
  exact flatMiss execution hw hfix hf hr (by simpa only [hfrom, hto] using hatt)

end Elegant.Layered.PipelineImpl
