import Elegant.Layered.RecursiveBEq
import Elegant.Layered.FamilyC5Measured
import Elegant.Layered.RecursiveC6
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RouteTransport
import Elegant.Layered.RecursiveBLiftsA

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The flat endpoint fact at an arbitrary base: every successful `base`
call on a well-formed framed-parents input preserves the box and route id
lists (the `layout_ids` content) and satisfies the flat group-endpoint
invariant `GroupEndpointInvariantMeasured`.  The id equalities are what the
`expandChild` transport consumes; for `base = layout` they are exactly
`layout_ids` and `FlatGroupEndpoints`, recovered by `flatC5B_of_endpoints`. -/
def FlatC5B (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    WellFormed (inputModel inp o) → framedParents inp = true →
    base inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
    res.scene.routes.map (·.id) = inp.routes.map (·.id) ∧
    GroupEndpointInvariantMeasured inp res.scene

/-- The sub-input well-formedness seam at `layoutRecursiveB base`, the
`SubInputWellFormed` shape with the base-parametric recursion in place of
`layoutRecursive`. -/
def SubInputWellFormedB
    (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
    (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
    (child parent : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    checkedParams o.profile inp.kind = .ok P →
    metricOf o.profile = .ok metric →
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
          .ok titleLines →
    layoutRecursiveB base fuel (childSubInput inp group) (childSubOptions o group) = .ok child →
    layoutRecursiveB base fuel (parentSubInput inp group P titleLines child) o = .ok parent →
    WellFormed (inputModel (childSubInput inp group) (childSubOptions o group)) ∧
    framedParents (childSubInput inp group) = true ∧
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
    framedParents (parentSubInput inp group P titleLines child) = true

/-- The fused per-call lift: for every successful `layoutRecursiveB base`
call on a well-formed framed-parents input, the result preserves the box
and route id lists and satisfies the flat group-endpoint invariant.  The id
conclusions are the `layoutRecursive_ids` argument at `expandChild_ids`; the
invariant is the embedding transport of
`layoutRecursive_group_endpoint_source_invariant_measured`, with the dump
box lookups discharged through `keyed_lookup_eq` on the result nodup this
same step produces. -/
theorem layoutRecursiveB_c5_facts
    {base : Input → Options → Except LayoutError FamilyResult}
    (hflat : FlatC5B base) (hsub : SubInputWellFormedB base) :
    ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult},
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) ∧
      GroupEndpointInvariantMeasured inp res.scene := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hfp hrec
    have hb : base inp o = .ok res := hrec
    exact hflat hwf hfp hb
  | succ fuel ih =>
    intro inp o res hwf hfp hrec
    rcases layoutRecursiveB_succ_sources base hrec with ⟨hnone, hb⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hchild, hwrap,
        hparentAt, hexpand⟩
    · exact hflat hwf hfp hb
    · obtain ⟨hwfChild, hfpChild, hwfParent, hfpParent⟩ :=
        hsub fuel inp o group P metric titleLines child parent
          hwf hfp hP hm hwrap hchild hparentAt
      obtain ⟨hcBoxIds, hcRouteIds, hcInv⟩ := ih hwfChild hfpChild hchild
      obtain ⟨hpBoxIds, hpRouteIds, hpInv⟩ := ih hwfParent hfpParent hparentAt
      simp only [childSubInput] at hcBoxIds hcRouteIds hcInv
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := inputRoutesCovered hwf
      have hgi := List.find?_some hg
      simp only [Bool.and_eq_true] at hgi
      have hin := independent_inside hgi.1
      have idsC := selectInput_box_ids inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      have idsP := selectInput_box_ids inp
        (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have resIds := expandChild_ids hexpand (by
        intro bx hbx
        by_cases hi : Compound.inside inp.boxes group.id bx.id = true
        · have hm : bx.id ∈ child.scene.boxes.map (·.id) := by
            rw [hcBoxIds, idsC]
            exact mem_filter_ids inp _ bx hbx hi
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hm : bx.id ∈ parent.scene.boxes.map (·.id) := by
            rw [hpBoxIds]
            show bx.id ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)
            rw [idsP]
            exact mem_filter_ids inp _ bx hbx (by simpa using hi)
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩) (by
        intro r hr
        obtain ⟨⟨bf, hbf, ef⟩, ⟨bt, hbt, et⟩⟩ := hcovered r hr
        have heq := hin r hr
        by_cases hi : Compound.inside inp.boxes group.id r.fromId = true
        · have hit : Compound.inside inp.boxes group.id r.toId = true := by rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsC]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; exact hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; exact hit)
          have hm : r.id ∈ child.scene.routes.map (·.id) := by
            rw [hcRouteIds]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hit : ¬ Compound.inside inp.boxes group.id r.toId = true := by rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsP]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; simpa using hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; simpa using hit)
          have hm : r.id ∈ parent.scene.routes.map (·.id) := by
            rw [hpRouteIds]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩)
      obtain ⟨resBoxIds, resRouteIds⟩ := resIds
      -- Disjointness of the child and parent box id lists.
      have hdisjoint : ∀ id ∈ child.scene.boxes.map (·.id),
          id ∉ parent.scene.boxes.map (·.id) := by
        intro id hidChild hidParent
        rw [hcBoxIds] at hidChild
        rw [hpBoxIds] at hidParent
        change id ∈ (selectInput inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map (·.id)
          at hidChild
        change id ∈ (selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)
          at hidParent
        rw [selectInput_box_ids] at hidChild hidParent
        obtain ⟨childBox, hchildBox, hchildId⟩ := List.mem_map.mp hidChild
        obtain ⟨parentBox, hparentBox, hparentId⟩ := List.mem_map.mp hidParent
        have hBoxEq : childBox.id = parentBox.id := hchildId.trans hparentId.symm
        have hInsideC : Compound.inside inp.boxes group.id childBox.id = true :=
          (List.mem_filter.mp hchildBox).2
        have hInsideP : Compound.inside inp.boxes group.id parentBox.id = false := by
          have h := (List.mem_filter.mp hparentBox).2
          simpa using h
        rw [hBoxEq] at hInsideC
        exact Bool.noConfusion (hInsideC.symm.trans hInsideP)
      -- Expansion assembly: offsets and the box/route list equations.
      obtain ⟨_frame, _ametric, _atitleLines, _alines, dx, dy,
        _hframe, _hametric, _hattr, _halines, _hdx, _hdy, hboxes, hroutes, _hitems⟩ :=
        expandChild_assembly_sources hexpand
      let embed := fun box : Box => { box with
        rect := shiftRect dx dy box.rect,
        parent := if box.parent == "" then group.id else box.parent }
      have hresNodup : (res.scene.boxes.map (·.id)).Nodup := by
        rw [resBoxIds]; exact hboxIds
      have hchildLookup : ∀ box : Box, child.scene.layoutDump.box? box.id = some box →
          res.scene.layoutDump.box? box.id = some (embed box) := by
        intro box hbox
        have hbox' : child.scene.boxes.find? (fun b => b.id == box.id) = some box := hbox
        have hmem : box ∈ child.scene.boxes := List.mem_of_find?_eq_some hbox'
        have hid : box.id ∈ child.scene.boxes.map (·.id) := List.mem_map_of_mem hmem
        rw [hcBoxIds] at hid
        change box.id ∈ (selectInput inp
          (fun b => Compound.inside inp.boxes group.id b.id) group.id).boxes.map (·.id)
          at hid
        rw [selectInput_box_ids] at hid
        obtain ⟨model, hmodelFilter, hmodelId⟩ := List.mem_map.mp hid
        have hmodelMem : model ∈ inp.boxes := (List.mem_filter.mp hmodelFilter).1
        have hfindChild : (child.scene.boxes.map embed).find? (fun c => c.id == box.id)
            = some (embed box) := by
          rw [List.find?_map]
          have hinner : child.scene.boxes.find?
              ((fun c : Box => c.id == box.id) ∘ embed) = some box := hbox'
          rw [hinner]; rfl
        have hfind : ((child.scene.boxes.map embed) ++ parent.scene.boxes).find?
            (fun c => c.id == model.id) = some (embed box) := by
          rw [hmodelId, List.find?_append, hfindChild]
          rfl
        have hemitted : embed box ∈ res.scene.boxes := by
          rw [hboxes]
          apply List.mem_filterMap.mpr
          exact ⟨model, hmodelMem, hfind⟩
        exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hresNodup (embed box) hemitted
      have hparentLookup : ∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
          res.scene.layoutDump.box? box.id = some box := by
        intro box hbox
        have hbox' : parent.scene.boxes.find? (fun b => b.id == box.id) = some box := hbox
        have hmem : box ∈ parent.scene.boxes := List.mem_of_find?_eq_some hbox'
        have hidP0 : box.id ∈ parent.scene.boxes.map (·.id) := List.mem_map_of_mem hmem
        have hidP : box.id ∈ parent.scene.boxes.map (·.id) := hidP0
        rw [hpBoxIds] at hidP
        change box.id ∈ (selectInput inp
          (fun b => !Compound.inside inp.boxes group.id b.id) "").boxes.map (·.id)
          at hidP
        rw [selectInput_box_ids] at hidP
        obtain ⟨model, hmodelFilter, hmodelId⟩ := List.mem_map.mp hidP
        have hmodelMem : model ∈ inp.boxes := (List.mem_filter.mp hmodelFilter).1
        have hnone : (child.scene.boxes.map embed).find?
            (fun c => c.id == box.id) = none := by
          apply List.find?_eq_none.mpr
          intro c hc
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
          intro hEq
          have hcid : (embed c').id = box.id := beq_iff_eq.mp hEq
          have hcid' : c'.id = box.id := hcid
          have hcId : c'.id ∈ child.scene.boxes.map (·.id) :=
            List.mem_map.mpr ⟨c', hc', rfl⟩
          have hboxMemChild : box.id ∈ child.scene.boxes.map (·.id) := by
            rw [← hcid']; exact hcId
          have hboxMemParent : box.id ∈ parent.scene.boxes.map (·.id) := hidP0
          exact hdisjoint box.id hboxMemChild hboxMemParent
        have hfind : ((child.scene.boxes.map embed) ++ parent.scene.boxes).find?
            (fun c => c.id == model.id) = some box := by
          rw [hmodelId, List.find?_append, hnone, hbox']
          rfl
        have hemitted : box ∈ res.scene.boxes := by
          rw [hboxes]
          apply List.mem_filterMap.mpr
          exact ⟨model, hmodelMem, hfind⟩
        exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hresNodup box hemitted
      refine ⟨resBoxIds, resRouteIds, ?_⟩
      intro out hout
      rw [hroutes] at hout
      obtain ⟨model, _, hfind⟩ := List.mem_filterMap.mp hout
      have houtMember := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp houtMember with hshifted | hparentRoute
      · obtain ⟨native, hnative, houtEq⟩ := List.mem_map.mp hshifted
        subst out
        obtain ⟨selS, hselS, selT, hselT, hsId, htId, hports⟩ := hcInv native hnative
        have lift : ∀ (keep : ModelBox → Bool) (root : String) (selected : ModelBox),
            selected ∈ (selectInput inp keep root).boxes →
            ∃ source ∈ inp.boxes, source.id = selected.id ∧ source.role = selected.role := by
          intro keep root selected hselected
          obtain ⟨source, hsource, _, heq⟩ :=
            selectInput_box_source inp keep root selected hselected
          refine ⟨source, hsource, ?_, ?_⟩
          · rw [heq]; split <;> rfl
          · rw [heq]; split <;> rfl
        obtain ⟨source, hsource, hsId0, _⟩ :=
          lift (fun box => Compound.inside inp.boxes group.id box.id) group.id _ hselS
        obtain ⟨target, htarget, htId0, _⟩ :=
          lift (fun box => Compound.inside inp.boxes group.id box.id) group.id _ hselT
        refine ⟨source, hsource, target, htarget, hsId0.trans hsId,
          htId0.trans htId, ?_⟩
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ := hports
        have hfromBoxId : fromBox.id = native.fromId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == native.fromId) hfrom)
        have htoBoxId : toBox.id = native.toId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == native.toId) hto)
        refine ⟨shiftPoint dx dy start, shiftPoint dx dy finish,
          embed fromBox, embed toBox, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.head?_map, hstart, Option.map_some]
        · simp only [List.getLast?_map, hfinish, Option.map_some]
        · rw [← hfromBoxId]
          exact hchildLookup fromBox (by rw [hfromBoxId]; exact hfrom)
        · rw [← htoBoxId]
          exact hchildLookup toBox (by rw [htoBoxId]; exact hto)
        · exact (onBoundary_shift dx dy start fromBox.rect).mpr hfromBoundary
        · exact (onBoundary_shift dx dy finish toBox.rect).mpr htoBoundary
      · obtain ⟨selS, hselS, selT, hselT, hsId, htId, hports⟩ := hpInv out hparentRoute
        have lift : ∀ (keep : ModelBox → Bool) (root : String) (selected : ModelBox),
            selected ∈ (selectInput inp keep root).boxes →
            ∃ source ∈ inp.boxes, source.id = selected.id ∧ source.role = selected.role := by
          intro keep root selected hselected
          obtain ⟨source, hsource, _, heq⟩ :=
            selectInput_box_source inp keep root selected hselected
          refine ⟨source, hsource, ?_, ?_⟩
          · rw [heq]; split <;> rfl
          · rw [heq]; split <;> rfl
        obtain ⟨source, hsource, hsId0, _⟩ :=
          lift (fun box => !Compound.inside inp.boxes group.id box.id) "" _ hselS
        obtain ⟨target, htarget, htId0, _⟩ :=
          lift (fun box => !Compound.inside inp.boxes group.id box.id) "" _ hselT
        refine ⟨source, hsource, target, htarget, hsId0.trans hsId,
          htId0.trans htId, ?_⟩
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ := hports
        have hfromBoxId : fromBox.id = out.fromId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == out.fromId) hfrom)
        have htoBoxId : toBox.id = out.toId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == out.toId) hto)
        refine ⟨start, finish, fromBox, toBox, hstart, hfinish, ?_, ?_,
          hfromBoundary, htoBoundary⟩
        · rw [← hfromBoxId]
          exact hparentLookup fromBox (by rw [hfromBoxId]; exact hfrom)
        · rw [← htoBoxId]
          exact hparentLookup toBox (by rw [htoBoxId]; exact hto)

/-- The C5 invariant lift at `layoutRecursiveB`: the clause conclusion is the
third component of `layoutRecursiveB_c5_facts`. -/
theorem layoutRecursiveB_c5
    {base : Input → Options → Except LayoutError FamilyResult}
    (hflat : FlatC5B base) (hsub : SubInputWellFormedB base)
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hrec : layoutRecursiveB base fuel inp o = .ok res) :
    GroupEndpointInvariantMeasured inp res.scene :=
  (layoutRecursiveB_c5_facts hflat hsub fuel hwf hfp hrec).2.2

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered

open PipelineImpl

/-- The family gate admits a successful `layoutRecursiveB base` run on a
well-formed input, mirroring `layoutFamily_success` for `layoutFamilyB`
(which additionally gates on `attachedNoteParents`). -/
theorem layoutFamilyB_success
    {base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamilyB base inp o = .ok res) :
    WellFormed (inputModel inp o) ∧
      layoutRecursiveB base (inp.boxes.length + 1) inp o = .ok res := by
  unfold layoutFamilyB at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i h1 h2 h3 hmw hfp hnote
              cases hr : layoutRecursiveB base (inp.boxes.length + 1) inp o with
              | error error => simp [hr] at h
              | ok out =>
                simp only [hr, Except.ok.injEq] at h
                subst res
                have hwf : WellFormed (inputModel inp o) := by
                  unfold WellFormed
                  cases hb : modelWellFormed (inputModel inp o) with
                  | false => simp [hb] at hmw
                  | true => rfl
                exact ⟨hwf, rfl⟩

/-- Clause C5 for a successful `layoutFamilyB`: every route's endpoints land
on the boundary of its `from`/`to` dump boxes, from `FlatC5B base` and the
sub-input facts. -/
theorem layoutFamilyB_c5
    {base : Input → Options → Except LayoutError FamilyResult}
    (hflat : PipelineImpl.FlatC5B base) (hsub : PipelineImpl.SubInputWellFormedB base)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hfamily : layoutFamilyB base inp o = .ok res) :
    Validator.C5 res.scene.layoutDump := by
  obtain ⟨hwf, hrecursive⟩ := layoutFamilyB_success hfamily
  have hfp := layoutFamilyB_framed_parents hfamily
  intro route hroute
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    PipelineImpl.layoutRecursiveB_c5 hflat hsub (inp.boxes.length + 1)
      hwf hfp hrecursive route hroute
  exact hports

end Elegant.Layered

namespace Elegant.Layered.PipelineImpl

/-- Sanity check: for `base = layout`, `FlatC5B` is exactly `layout_ids`
plus `FlatGroupEndpoints`. -/
theorem flatC5B_of_endpoints (hflat : FlatGroupEndpoints) : FlatC5B layout := by
  intro inp o res hwf hfp hb
  obtain ⟨execution⟩ := layout_sceneExecution hb
  have hids := layout_ids hb
  exact ⟨hids.1, hids.2, hflat hwf hfp execution⟩

end Elegant.Layered.PipelineImpl
