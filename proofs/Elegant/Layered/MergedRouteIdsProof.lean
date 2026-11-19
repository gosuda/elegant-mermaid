import Elegant.Layered.PipelineFacts
import Elegant.Layered.SelectFacts
import Elegant.Layered.SelectInputWellFormed
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.MergedAncestorsProof

set_option autoImplicit false

/-!
# Route lookups and owner separation of the merged `expandChild` scene

For one executed `expandChild` call (`hexpand`, `hframed`, `hctx`, `hparams`):

* `expandChild_route_agreement` — the merged dump finds a route's endpoints
  as the child dump does, else as the parent dump does;
* `expandChild_owner_separation` — the owner-separation clauses, under the
  additional hypothesis that no route id names a box id (the unconditional
  form is false: `modelWellFormed` does not separate the route and box id
  namespaces, so a route can be named after a child box that owns a label);
* `expandChild_child_route_endpoints` — child scene route endpoints name
  child-scene boxes.

The workhorse is `layoutRecursive_scene_mirror`: by induction on the fuel,
every scene route's endpoints name scene boxes and every scene label comes
from an input label with the same id and owner.
-/

namespace Elegant.Layered.PipelineImpl

/-! ### List and `find?` helpers -/

/-- `find?` returns `some a` when `a` satisfies the predicate, is a member,
and every satisfying member equals `a`. -/
theorem find?_eq_some_of_unique {α : Type} (p : α → Bool) {l : List α} {a : α}
    (ha : a ∈ l) (hp : p a = true) (hu : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hx : p x = true
    · have hxa : x = a := hu x List.mem_cons_self hx
      subst hxa
      simp only [List.find?_cons, hp]
    · have hxs : ∀ b ∈ xs, p b = true → b = a :=
        fun b hb hbq => hu b (List.mem_cons.mpr (Or.inr hb)) hbq
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | h
        · exact absurd hx (by simp [hp])
        · exact h
      have hfind := ih ha' hxs
      simp only [List.find?_cons, hx]
      exact hfind

/-- An id names a selected box iff some kept input box has it. -/
theorem mem_selected_box_ids (inp : Input) (keep : ModelBox → Bool) (_root : String)
    (s : String) :
    s ∈ (inp.boxes.filter keep).map (·.id) ↔
      ∃ b ∈ inp.boxes, keep b = true ∧ b.id = s := by
  constructor
  · intro h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact ⟨b, (List.mem_filter.mp hb).1, (List.mem_filter.mp hb).2, rfl⟩
  · rintro ⟨b, hb, hk, rfl⟩
    exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hk⟩, rfl⟩

theorem selectInput_route_iff (inp : Input) (keep : ModelBox → Bool) (root : String)
    (r : ModelRoute) :
    r ∈ (selectInput inp keep root).routes ↔
      r ∈ inp.routes ∧ r.fromId ∈ (inp.boxes.filter keep).map (·.id) ∧
        r.toId ∈ (inp.boxes.filter keep).map (·.id) := by
  rw [selectInput_route_mem]
  simp only [any_id_iff, selectInput_box_ids]

/-- Every label `sceneOf` emits comes from the input label at the same
`zipIdx` position, keeping its id and owner. -/
theorem sceneOf_label_mem (P : Params) (inp : Input) (o : Options)
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
      · next hfind =>
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

/-! ### Flat layouts mirror the input -/

/-- For a successful flat `layout`: every scene route's endpoints name scene
boxes, and every scene label comes from an input label with the same id and
owner. -/
private theorem layout_scene_mirror {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (h : layout inp o = .ok res) :
    (∀ rt ∈ res.scene.routes,
      rt.fromId ∈ res.scene.boxes.map (·.id) ∧ rt.toId ∈ res.scene.boxes.map (·.id)) ∧
    (∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner) := by
  have hcov : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hids := layout_ids h
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
  · have hres := Except.ok.inj h
    have hsc : res.scene = sceneOf P inp o lines acc measured :=
      (congrArg FamilyResult.scene hres).symm
    constructor
    · intro rt hrt
      rw [hsc] at hrt
      obtain ⟨k, hkget⟩ := List.mem_iff_getElem?.mp hrt
      obtain ⟨hk, _hget⟩ := List.getElem?_eq_some_iff.mp hkget
      rw [sceneOf_routes_length] at hk
      have hrec := sceneOf_routes_getElem? P inp o lines acc measured k hk
      have hrtEq : rt = ⟨(inp.routes[k]).id, (inp.routes[k]).fromId,
          (inp.routes[k]).toId, (inp.routes[k]).orthogonal,
          (acc.routes.getD k []).map (fun p =>
            shiftPoint P.canvasMargin P.canvasMargin
              (orientPoint o.direction acc.canvasH p))⟩ :=
        Option.some.inj (hkget.symm.trans hrec)
      have hfrom : rt.fromId = (inp.routes[k]).fromId := congrArg Route.fromId hrtEq
      have hto : rt.toId = (inp.routes[k]).toId := congrArg Route.toId hrtEq
      have hkmem : inp.routes[k] ∈ inp.routes := List.getElem_mem hk
      obtain ⟨hfromCov, htoCov⟩ := hcov _ hkmem
      obtain ⟨bf, hbf, hbfid⟩ := hfromCov
      obtain ⟨bt, hbt, hbtid⟩ := htoCov
      constructor
      · rw [hfrom]
        have hbid : (inp.routes[k]).fromId ∈ inp.boxes.map (·.id) :=
          List.mem_map.mpr ⟨bf, hbf, hbfid⟩
        rwa [hids.1]
      · rw [hto]
        have hbid : (inp.routes[k]).toId ∈ inp.boxes.map (·.id) :=
          List.mem_map.mpr ⟨bt, hbt, hbtid⟩
        rwa [hids.1]
    · intro sl hsl
      rw [hsc] at hsl
      exact sceneOf_label_mem P inp o lines acc measured sl hsl

/-! ### The recursive mirror -/

/-- By induction on the fuel: every scene route's endpoints name scene
boxes, and every scene label comes from an input label with the same id and
owner. -/
private theorem layoutRecursive_scene_mirror
    (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (h : layoutRecursive fuel inp o = .ok res) :
    (∀ rt ∈ res.scene.routes,
      rt.fromId ∈ res.scene.boxes.map (·.id) ∧ rt.toId ∈ res.scene.boxes.map (·.id)) ∧
    (∀ sl ∈ res.scene.labels, ∃ m ∈ inp.labels, m.id = sl.id ∧ m.owner = sl.owner) := by
  revert hwf hframed h
  induction fuel generalizing inp o res with
  | zero =>
    intro hwf _hframed h
    exact layout_scene_mirror hwf h
  | succ fuel ih =>
    intro hwf hframed h
    rcases layoutRecursive_succ_sources h with ⟨hn, hl⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, hexpand⟩
    · exact layout_scene_mirror hwf hl
    · obtain ⟨hwfC, hframedC, hwfP, hframedP⟩ :=
        subInputWellFormed fuel inp o group P metric titleLines child parent
          hwf hframed hP hm ht hc hp
      have ihC := ih _ _ _ hwfC hframedC hc
      have ihP := ih _ _ _ hwfP hframedP hp
      have hcovC : RoutesCovered (childSubInput inp group) :=
        selectInput_routesCovered inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
      have hcovP : RoutesCovered (parentSubInput inp group P titleLines child) :=
        selectInput_routesCovered inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have hchildIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
        hcovC hc
      have hparentIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
        hcovP hp
      -- every input box id is a child-scene or parent-scene box id
      have hboxPart : ∀ b ∈ inp.boxes,
          b.id ∈ child.scene.boxes.map (·.id) ++ parent.scene.boxes.map (·.id) := by
        intro b hb
        by_cases hi : Compound.inside inp.boxes group.id b.id = true
        · have hmem : b.id ∈ (inp.boxes.filter
              (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) :=
            (mem_selected_box_ids inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id b.id).mpr
              ⟨b, hb, hi, rfl⟩
          have hcid : child.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hchildIds.1]
            show (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
              (·.id) = _
            rw [selectInput_box_ids]
          rw [← hcid] at hmem
          exact List.mem_append_left _ hmem
        · have hn : (!Compound.inside inp.boxes group.id b.id) = true := by
            simp [hi]
          have hmem : b.id ∈ (inp.boxes.filter
              (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) :=
            (mem_selected_box_ids inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "" b.id).mpr
              ⟨b, hb, hn, rfl⟩
          have hpid : parent.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hparentIds.1]
            show (parentSubInput inp group P titleLines child).boxes.map (·.id) = _
            show (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
              (·.id) = _
            rw [selectInput_box_ids]
          rw [← hpid] at hmem
          exact List.mem_append_right _ hmem
      -- the merged box ids are exactly the input box ids
      obtain ⟨frameS, metricS, tlS, _linesS, dxS, dyS, hframeS, hmetricS, htitleS,
        _hlinesS, hdxS, hdyS, _hcanvasS, hboxesS⟩ := expandChild_sources hexpand
      have hboxIds : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
        rw [hboxesS]
        refine filterMap_find_ids (fun box : Box => box.id) (inp.boxes.map (·.id))
          (child.scene.boxes.map (embedBox group.id dxS dyS) ++ parent.scene.boxes)
          ?_ inp.boxes (·.id) rfl
        intro id hid
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hid
        have hbp := hboxPart b hb
        rcases List.mem_append.mp hbp with hcl | hpr
        · obtain ⟨cb, hcb, hcbid⟩ := List.mem_map.mp hcl
          refine ⟨embedBox group.id dxS dyS cb, ?_, ?_⟩
          · exact List.mem_append_left _
              (List.mem_map.mpr ⟨cb, hcb, rfl⟩)
          · exact hcbid
        · obtain ⟨pb, hpb, hpbid⟩ := List.mem_map.mp hpr
          exact ⟨pb, List.mem_append_right _ hpb, hpbid⟩
      constructor
      · -- route endpoints
        intro rt hrt
        have hroutes := expandChild_routes_eq hexpand frameS metricS tlS dxS dyS
          hframeS hmetricS htitleS hdxS hdyS
        rw [hroutes] at hrt
        obtain ⟨model, hmMem, hfind⟩ := List.mem_filterMap.mp hrt
        have hrtMem : rt ∈ (child.scene.routes.map (fun route : Route =>
            { route with points := route.points.map (shiftPoint dxS dyS) })) ++
          parent.scene.routes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hrtMem with hcl | hpr
        · obtain ⟨cr, hcr, hrtEq⟩ := List.mem_map.mp hcl
          have hfrom : rt.fromId = cr.fromId := by rw [← hrtEq]
          have hto : rt.toId = cr.toId := by rw [← hrtEq]
          obtain ⟨ihCfrom, ihCto⟩ := ihC.1 cr hcr
          have hcid : child.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hchildIds.1]
            show (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
              (·.id) = _
            rw [selectInput_box_ids]
          have hsubC : ∀ x ∈ child.scene.boxes.map (·.id),
              x ∈ inp.boxes.map (·.id) := by
            intro x hx
            rw [hcid] at hx
            exact (List.Sublist.map (fun box : ModelBox => box.id)
              (List.filter_sublist (l := inp.boxes))).subset hx
          constructor
          · rw [hfrom, hboxIds]
            exact hsubC _ ihCfrom
          · rw [hto, hboxIds]
            exact hsubC _ ihCto
        · obtain ⟨ihPfrom, ihPto⟩ := ihP.1 rt hpr
          have hpid : parent.scene.boxes.map (·.id) =
              (inp.boxes.filter
                (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
            rw [hparentIds.1]
            show (parentSubInput inp group P titleLines child).boxes.map (·.id) = _
            show (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
              (·.id) = _
            rw [selectInput_box_ids]
          have hsubP : ∀ x ∈ parent.scene.boxes.map (·.id),
              x ∈ inp.boxes.map (·.id) := by
            intro x hx
            rw [hpid] at hx
            exact (List.Sublist.map (fun box : ModelBox => box.id)
              (List.filter_sublist (l := inp.boxes))).subset hx
          constructor
          · rw [hboxIds]
            exact hsubP _ ihPfrom
          · rw [hboxIds]
            exact hsubP _ ihPto
      · -- labels
        intro sl hsl
        have hwrap : ExpandChildTitleWrapped P inp o group tlS :=
          ⟨metricS, hmetricS, htitleS⟩
        have hlabels := expandChild_labels_eq_wrapped hexpand frameS tlS dxS dyS
          hframeS hdxS hdyS hwrap
        rw [hlabels] at hsl
        obtain ⟨model, hmMem, hdo⟩ := List.mem_filterMap.mp hsl
        cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
            { label with rect := shiftRect dxS dyS label.rect }) ++
          parent.scene.labels).find? (fun label : SceneLabel => label.id == model.id)) with
        | none => rw [hfind] at hdo; simp at hdo
        | some label =>
          rw [hfind, Option.bind_some] at hdo
          have hif := Option.some.inj hdo
          have hslid : sl.id = label.id ∧ sl.owner = label.owner := by
            by_cases hcond : (model.owner == group.id) = true
            · rw [hcond] at hif
              simp only [reduceIte] at hif
              constructor
              · exact congrArg (fun s => s.toLabel.id) hif.symm
              · exact congrArg (fun s => s.toLabel.owner) hif.symm
            · have hcondF : (model.owner == group.id) = false := by
                cases hb : (model.owner == group.id) with
                | false => rfl
                | true => exact absurd hb hcond
              rw [hcondF] at hif
              simp only [Bool.false_eq_true, reduceIte] at hif
              constructor
              · exact congrArg (fun s => s.toLabel.id) hif.symm
              · exact congrArg (fun s => s.toLabel.owner) hif.symm
          have hmem2 := List.mem_of_find?_eq_some hfind
          rcases List.mem_append.mp hmem2 with hcl | hpl
          · obtain ⟨cl, hclmem, hclEq⟩ := List.mem_map.mp hcl
            obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := ihC.2 cl hclmem
            have hsubC := selectInput_labels_sublist inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id
            have hmcIn : mc ∈ inp.labels := hsubC.subset hmcmem
            have hlabelId : label.id = cl.id := congrArg (fun s => s.toLabel.id) hclEq.symm
            have hlabelOwn : label.owner = cl.owner :=
              congrArg (fun s => s.toLabel.owner) hclEq.symm
            refine ⟨mc, hmcIn, ?_, ?_⟩
            · calc mc.id = cl.id := hmcId
                _ = label.id := hlabelId.symm
                _ = sl.id := hslid.1.symm
            · calc mc.owner = cl.owner := hmcOwn
                _ = label.owner := hlabelOwn.symm
                _ = sl.owner := hslid.2.symm
          · obtain ⟨mc, hmcmem, hmcId, hmcOwn⟩ := ihP.2 label hpl
            have hsubP := selectInput_labels_sublist inp
              (fun box => !Compound.inside inp.boxes group.id box.id) ""
            have hmcIn : mc ∈ inp.labels := hsubP.subset hmcmem
            refine ⟨mc, hmcIn, ?_, ?_⟩
            · calc mc.id = label.id := hmcId
                _ = sl.id := hslid.1.symm
            · calc mc.owner = label.owner := hmcOwn
                _ = sl.owner := hslid.2.symm
/-! ### Route-lookup and owner-separation facts -/

private theorem option_map_or {α β : Type} (o₁ o₂ : Option α) (g : α → β) :
    (o₁.or o₂).map g = (o₁.map g).or (o₂.map g) := by
  cases o₁ <;> cases o₂ <;> rfl

private theorem selectInput_box_ids_subset (inp : Input) (keep : ModelBox → Bool)
    (root : String) :
    ∀ x ∈ (selectInput inp keep root).boxes.map (·.id), x ∈ inp.boxes.map (·.id) := by
  intro x hx
  rw [selectInput_box_ids] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨b, (List.mem_filter.mp hb).1, rfl⟩

private theorem selectInput_label_owner_mem (inp : Input) (keep : ModelBox → Bool)
    (root : String) (l : ModelLabel)
    (hl : l ∈ (selectInput inp keep root).labels) :
    l.owner ∈ (selectInput inp keep root).boxes.map (·.id) ∨
      l.owner ∈ (selectInput inp keep root).routes.map (·.id) := by
  unfold selectInput at hl
  obtain ⟨_, hflt⟩ := List.mem_filter.mp hl
  have hcases := Bool.or_eq_true_iff.mp hflt
  rcases hcases with hbox | hroute
  · rw [List.any_eq_true] at hbox
    obtain ⟨b, hb, he⟩ := hbox
    left
    apply List.mem_map.mpr
    refine ⟨b, ?_, ?_⟩
    · exact hb
    · exact beq_iff_eq.mp he
  · rw [List.any_eq_true] at hroute
    obtain ⟨rt, hrt, he⟩ := hroute
    right
    apply List.mem_map.mpr
    refine ⟨rt.1, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨rt, hrt, rfl⟩
    · exact beq_iff_eq.mp he

/-- The child-scene route endpoints name child-scene boxes: the first
component of the recursive mirror applied to the child success. -/
theorem expandChild_child_route_endpoints
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7RouteEndpoints child := by
  obtain ⟨hwf, _hfind, _hpboxes, hchild, hparent, _⟩ := hctx
  obtain ⟨frameS, metricS, tlS, _lS, _dxS, _dyS, hframeS, hmetricS, htitleS,
    _hlS, _hdxS, _hdyS, _hcS, _hbS⟩ := expandChild_sources hexpand
  obtain ⟨hP, _ht, hwrapE⟩ := hparams
  obtain ⟨metricW, hMW, hTW⟩ := hwrapE
  have hmet : metricS = metricW := Except.ok.inj (hmetricS.symm.trans hMW)
  subst hmet
  have hsub := subInputWellFormed fuel inp o group P metricS titleLines child parent
    hwf hframed hP hmetricS hTW hchild hparent
  exact (layoutRecursive_scene_mirror fuel _ _ _ hsub.1 hsub.2.1 hchild).1

/-- Merged route-lookup agreement: the merged dump finds the same endpoints
as the first matching sub-dump (child first, else parent). -/
theorem expandChild_route_agreement
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7RouteAgreement parent child res := by
  obtain ⟨hwf, _hfind, _hpboxes, hchild, hparent, _⟩ := hctx
  obtain ⟨frameS, metricS, tlS, _lS, dxS, dyS, hframeS, hmetricS, htitleS,
    _hlS, hdxS, hdyS, _hcS, _hbS⟩ := expandChild_sources hexpand
  have hroutes := expandChild_routes_eq hexpand frameS metricS tlS dxS dyS
    hframeS hmetricS htitleS hdxS hdyS
  have hrouteNodup : (inp.routes.map (·.id)).Nodup := Model.routeIds_nodup hwf
  have hcovC : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp _ _
  have hcovP : RoutesCovered (parentSubInput inp group P titleLines child) := by
    show RoutesCovered (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "")
    exact selectInput_routesCovered inp _ _
  have hchildIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hcovC hchild
  have hparentIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hcovP hparent
  have hdisj : ∀ id ∈ child.scene.routes.map (·.id),
      id ∉ parent.scene.routes.map (·.id) :=
    recursive_selected_route_ids_disjoint hwf hchild hparent
  intro owner
  change (res.scene.routes.find? (fun r : Route => r.id == owner)).map
      (fun r => (r.fromId, r.toId)) =
    (((child.scene.routes.find? (fun r : Route => r.id == owner)).map
      (fun r => (r.fromId, r.toId))).orElse (fun _ =>
      ((parent.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r => (r.fromId, r.toId)))))
  rw [hroutes]
  have hmerged : (inp.routes.filterMap (fun model =>
      ((child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun route : Route => route.id == model.id))).find?
      (fun r : Route => r.id == owner) =
      ((child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun r : Route => r.id == owner) := by
    cases hSP : ((child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun r : Route => r.id == owner) with
    | none =>
      apply List.find?_eq_none.mpr
      intro rt hrt htest
      obtain ⟨model, hmMem, hfind⟩ := List.mem_filterMap.mp hrt
      have hrtId : rt.id = model.id := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hfind).1
      have hro : rt.id = owner := beq_iff_eq.mp htest
      have hmo : model.id = owner := hrtId.symm.trans hro
      have hg : ((child.scene.routes.map (fun route : Route =>
            { route with points := route.points.map (shiftPoint dxS dyS) })) ++
          parent.scene.routes).find? (fun route : Route => route.id == model.id) = none := by
        rw [hmo]; exact hSP
      rw [hg] at hfind
      cases hfind
    | some r =>
      have hrId : r.id = owner := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hSP).1
      have hrMem : r ∈ (child.scene.routes.map (fun route : Route =>
          { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes := List.mem_of_find?_eq_some hSP
      obtain ⟨m₀, hm₀mem, hm₀id⟩ : ∃ m₀ ∈ inp.routes, m₀.id = owner := by
        rcases List.mem_append.mp hrMem with hrS | hrP
        · obtain ⟨cr, hcr, hrEq⟩ := List.mem_map.mp hrS
          have hcrid : cr.id = owner := by
            have e := congrArg (fun x : Route => x.id) hrEq
            exact e.trans hrId
          have hownMem : owner ∈ child.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨cr, hcr, hcrid⟩
          rw [hchildIds.2] at hownMem
          obtain ⟨mC, hmCsub, hmCid⟩ := List.mem_map.mp hownMem
          exact ⟨mC, (selectInput_route_mem inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id mC).mp
            hmCsub |>.1, hmCid⟩
        · have hownMem : owner ∈ parent.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨r, hrP, hrId⟩
          rw [hparentIds.2] at hownMem
          obtain ⟨mP, hmPsub, hmPid⟩ := List.mem_map.mp hownMem
          have hmPsel : mP ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes :=
            hmPsub
          exact ⟨mP, (selectInput_route_mem inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" mP).mp
            hmPsel |>.1, hmPid⟩
      have hg₀ : ((child.scene.routes.map (fun route : Route =>
            { route with points := route.points.map (shiftPoint dxS dyS) })) ++
          parent.scene.routes).find? (fun route : Route => route.id == m₀.id) = some r := by
        rw [hm₀id]; exact hSP
      have hrRes : r ∈ res.scene.routes := by
        rw [hroutes]
        exact List.mem_filterMap.mpr ⟨m₀, hm₀mem, hg₀⟩
      cases hf : res.scene.routes.find? (fun r' : Route => r'.id == owner) with
      | none =>
        have hp : (fun r' : Route => r'.id == owner) r = true := beq_iff_eq.mpr hrId
        exact absurd hp ((List.find?_eq_none.mp hf) r hrRes)
      | some b =>
        have hbmem : b ∈ res.scene.routes := List.mem_of_find?_eq_some hf
        have hbp : b.id = owner := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hf).1
        rw [hroutes] at hbmem
        obtain ⟨m', hm'mem, hg'm⟩ := List.mem_filterMap.mp hbmem
        have hbm'id : b.id = m'.id := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hg'm).1
        have hm'id : m'.id = owner := hbm'id.symm.trans hbp
        have hm'eq : m' = m₀ := expandChild_nodup_map_inj (·.id) hrouteNodup
          hm'mem hm₀mem (hm'id.trans hm₀id.symm)
        have hg'm' : ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
            parent.scene.routes).find? (fun route : Route => route.id == m'.id) = some b := hg'm
        have hgg : ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
            parent.scene.routes).find? (fun route : Route => route.id == m'.id) =
            ((child.scene.routes.map (fun route : Route =>
              { route with points := route.points.map (shiftPoint dxS dyS) })) ++
            parent.scene.routes).find? (fun route : Route => route.id == m₀.id) := by rw [hm'eq]
        rw [hg'm', hg₀] at hgg
        have hbr : b = r := Option.some.inj hgg
        rw [hroutes] at hf
        rw [hbr] at hf
        exact hf
  rw [hmerged]
  have hSmap : ((child.scene.routes.map (fun route : Route =>
        { route with points := route.points.map (shiftPoint dxS dyS) })).find?
        (fun r : Route => r.id == owner)).map (fun r : Route => (r.fromId, r.toId)) =
      (child.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId)) := by
    rw [List.find?_map, Option.map_map]
    rfl
  have hPmap : (parent.scene.routes.find? (fun r : Route => r.id == owner)).map
      (fun r : Route => (r.fromId, r.toId)) =
      (parent.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId)) := rfl
  have hkey : (((child.scene.routes.map (fun route : Route =>
        { route with points := route.points.map (shiftPoint dxS dyS) })) ++
        parent.scene.routes).find? (fun r : Route => r.id == owner)).map
      (fun r : Route => (r.fromId, r.toId)) =
      ((child.scene.routes.find? (fun r : Route => r.id == owner)).map
        (fun r : Route => (r.fromId, r.toId))).orElse (fun _ =>
        ((parent.scene.routes.find? (fun r : Route => r.id == owner)).map
          (fun r : Route => (r.fromId, r.toId)))) := by
    rw [List.find?_append, option_map_or, hSmap, hPmap, Option.orElse_eq_or]
  exact hkey

/-- The parent-scene route endpoints name parent-scene boxes: the first
component of the recursive mirror applied to the parent success. -/
theorem expandChild_parent_route_endpoints
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7RouteEndpoints parent := by
  obtain ⟨hwf, _hfind, _hpboxes, hchild, hparent, _⟩ := hctx
  obtain ⟨_frameS, metricS, _tlS, _lS, _dxS, _dyS, _hframeS, hmetricS, htitleS,
    _hlS, _hdxS, _hdyS, _hcS, _hbS⟩ := expandChild_sources hexpand
  obtain ⟨hP, _ht, hwrapE⟩ := hparams
  obtain ⟨metricW, hMW, hTW⟩ := hwrapE
  have hmet : metricS = metricW := Except.ok.inj (hmetricS.symm.trans hMW)
  subst hmet
  have hsub := subInputWellFormed fuel inp o group P metricS titleLines child parent
    hwf hframed hP hmetricS hTW hchild hparent
  exact (layoutRecursive_scene_mirror fuel _ _ _ hsub.2.2.1 hsub.2.2.2 hparent).1

/-- Owner separation under box/route id disjointness: no label owner of one
sub-scene names a route of the other, and neither sub-scene routes on the
group id. Without disjointness this is false (`modelWellFormed` separates
the box and route id namespaces only within each kind): a route can be
named after a box that owns a label on the other side, or after the group
itself (see `wip/Probe/OwnerSeparationProbe.lean`: `groupRoute` refutes the
fourth conjunct, `labelRoute` refutes the first, both well-formed with
`Validator.c7` true). No kind `input` adapter guarantees the premise: they
copy `m.routes` verbatim (`Flowchart`, `C4`, `Class`, `Er`, `Agentflow`
all have `routes := m.routes`), so it stays an explicit hypothesis. -/
theorem expandChild_owner_separation
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hdisjoint : BoxRouteIdsDisjoint inp) :
    ExpandChildC7OwnerSeparation group parent child := by
  obtain ⟨hwf, hfind, _hpboxes, hchild, hparent, _⟩ := hctx
  obtain ⟨_frameS, metricS, _tlS, _lS, _dxS, _dyS, _hframeS, hmetricS, htitleS,
    _hlS, _hdxS, _hdyS, _hcS, _hbS⟩ := expandChild_sources hexpand
  obtain ⟨hP, _ht, hwrapE⟩ := hparams
  obtain ⟨metricW, hMW, hTW⟩ := hwrapE
  have hmet : metricS = metricW := Except.ok.inj (hmetricS.symm.trans hMW)
  subst hmet
  have hsub := subInputWellFormed fuel inp o group P metricS titleLines child parent
    hwf hframed hP hmetricS hTW hchild hparent
  have hCmirror := layoutRecursive_scene_mirror fuel _ _ _ hsub.1 hsub.2.1 hchild
  have hPmirror := layoutRecursive_scene_mirror fuel _ _ _ hsub.2.2.1 hsub.2.2.2 hparent
  have hcovC : RoutesCovered (childSubInput inp group) :=
    selectInput_routesCovered inp _ _
  have hcovP : RoutesCovered (parentSubInput inp group P titleLines child) := by
    show RoutesCovered (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "")
    exact selectInput_routesCovered inp _ _
  have hchildIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hcovC hchild
  have hparentIds := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hcovP hparent
  have hdisjRoutes : ∀ id ∈ child.scene.routes.map (·.id),
      id ∉ parent.scene.routes.map (·.id) :=
    recursive_selected_route_ids_disjoint hwf hchild hparent
  have hgroup : group ∈ inp.boxes := List.mem_of_find?_eq_some hfind
  have hgroupBox : group.id ∈ inp.boxes.map (·.id) :=
    List.mem_map.mpr ⟨group, hgroup, rfl⟩
  have hchildRouteInp : ∀ id ∈ child.scene.routes.map (·.id),
      id ∈ inp.routes.map (·.id) := by
    intro id hid
    rw [hchildIds.2] at hid
    change id ∈ (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).routes.map (·.id) at hid
    exact (selectInput_routes_ids_sublist inp _ _).subset hid
  have hparentRouteInp : ∀ id ∈ parent.scene.routes.map (·.id),
      id ∈ inp.routes.map (·.id) := by
    intro id hid
    rw [hparentIds.2] at hid
    change id ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").routes.map (·.id) at hid
    exact (selectInput_routes_ids_sublist inp _ _).subset hid
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cl hcl
    show (parent.scene.routes.find? (fun r => r.id == cl.owner)) = none
    obtain ⟨m, hmlab, _hmid, hmown⟩ := hCmirror.2 cl hcl
    change m ∈ (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).labels at hmlab
    have hown := selectInput_label_owner_mem inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id m hmlab
    cases h : (parent.scene.routes.find? (fun r => r.id == cl.owner)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ parent.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = cl.owner :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have heq : rt.id = m.owner := hrtid.trans hmown.symm
      rcases hown with hboxown | hrouteown
      · have hboxIn : m.owner ∈ inp.boxes.map (·.id) :=
          selectInput_box_ids_subset inp _ _ _ hboxown
        have hrouteIn : m.owner ∈ inp.routes.map (·.id) :=
          heq ▸ hparentRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
        exact False.elim (hdisjoint m.owner hboxIn hrouteIn)
      · have hcown : m.owner ∈ child.scene.routes.map (·.id) :=
          hchildIds.2.symm ▸ hrouteown
        have hpown : m.owner ∈ parent.scene.routes.map (·.id) := by
          have hpm : cl.owner ∈ parent.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨rt, hrtmem, hrtid⟩
          rwa [← hmown] at hpm
        exact False.elim (hdisjRoutes m.owner hcown hpown)
  · intro pl hpl
    show (child.scene.routes.find? (fun r => r.id == pl.owner)) = none
    obtain ⟨m, hmlab, _hmid, hmown⟩ := hPmirror.2 pl hpl
    change m ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").labels at hmlab
    have hown := selectInput_label_owner_mem inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "" m hmlab
    cases h : (child.scene.routes.find? (fun r => r.id == pl.owner)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ child.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = pl.owner :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have heq : rt.id = m.owner := hrtid.trans hmown.symm
      rcases hown with hboxown | hrouteown
      · have hboxIn : m.owner ∈ inp.boxes.map (·.id) :=
          selectInput_box_ids_subset inp _ _ _ hboxown
        have hrouteIn : m.owner ∈ inp.routes.map (·.id) :=
          heq ▸ hchildRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
        exact False.elim (hdisjoint m.owner hboxIn hrouteIn)
      · have hpown : m.owner ∈ parent.scene.routes.map (·.id) :=
          hparentIds.2.symm ▸ hrouteown
        have hcown : m.owner ∈ child.scene.routes.map (·.id) := by
          have hcm : pl.owner ∈ child.scene.routes.map (·.id) :=
            List.mem_map.mpr ⟨rt, hrtmem, hrtid⟩
          rwa [← hmown] at hcm
        exact False.elim (hdisjRoutes m.owner hcown hpown)
  · show (child.scene.routes.find? (fun r => r.id == group.id)) = none
    cases h : (child.scene.routes.find? (fun r => r.id == group.id)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ child.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = group.id :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have hrouteIn : group.id ∈ inp.routes.map (·.id) :=
        hrtid ▸ hchildRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
      exact False.elim (hdisjoint group.id hgroupBox hrouteIn)
  · show (parent.scene.routes.find? (fun r => r.id == group.id)) = none
    cases h : (parent.scene.routes.find? (fun r => r.id == group.id)) with
    | none => rfl
    | some rt =>
      have hrtmem : rt ∈ parent.scene.routes := List.mem_of_find?_eq_some h
      have hrtid : rt.id = group.id :=
        beq_iff_eq.mp (List.find?_eq_some_iff_append.mp h).1
      have hrouteIn : group.id ∈ inp.routes.map (·.id) :=
        hrtid ▸ hparentRouteInp rt.id (List.mem_map.mpr ⟨rt, hrtmem, rfl⟩)
      exact False.elim (hdisjoint group.id hgroupBox hrouteIn)

/-- C7 label scopes from disjointness. Applies the landed
`expandChild_c7_label_scopes` to ancestor monotonicity (executed calls),
the merged route agreement, owner separation under `BoxRouteIdsDisjoint`,
and the child route endpoints. The remaining `hanc` premise
(`ExpandChildC8aAncestry`, a named residual about this same call, strictly
simpler than the scope goal) has no executed-call proof in the tree yet:
every consumer takes it as a hypothesis (`ParentFrameProof.hancAll`, the
`FamilyAssembly.stepC8aAncestry` seam field). When its proof lands, delete
the `hanc` binder to close this step. -/
theorem expandChild_c7_label_scopes_of_disjoint
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hdisjoint : BoxRouteIdsDisjoint inp)
    (hanc : ExpandChildC8aAncestry group parent child res) :
    ExpandChildC7LabelScopes P group parent child res :=
  expandChild_c7_label_scopes fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
    (expandChild_ancestor_mono hexpand hframed hctx hparams)
    (expandChild_route_agreement hexpand hframed hctx hparams)
    (expandChild_owner_separation hexpand hframed hctx hparams hdisjoint)
    hanc
    (expandChild_child_route_endpoints hexpand hframed hctx hparams)

