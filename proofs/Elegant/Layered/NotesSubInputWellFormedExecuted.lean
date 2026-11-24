import Elegant.Layered.NotesFoundation
import Elegant.Layered.RegionFoundation
import Elegant.Layered.SubInputWellFormedFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private def rootNoteBox (top : String) (b : ModelBox) : ModelBox :=
  if b.id == top then { b with parent := "" } else b

private theorem rootNoteBox_id (top : String) (b : ModelBox) :
    (rootNoteBox top b).id = b.id := by
  unfold rootNoteBox
  split <;> rfl

private theorem rootNoteBox_role (top : String) (b : ModelBox) :
    (rootNoteBox top b).role = b.role := by
  unfold rootNoteBox
  split <;> rfl

private theorem rootNoteBox_exclusive (top : String) (b : ModelBox) :
    (rootNoteBox top b).exclusive = b.exclusive := by
  unfold rootNoteBox
  split <;> rfl

private theorem rootNoteBox_parent (top : String) (b : ModelBox) :
    (rootNoteBox top b).parent = if b.id == top then "" else b.parent := by
  by_cases h : b.id = top <;> simp [rootNoteBox, h]

private theorem rootNoteBox_parent_eq {top : String} {b : ModelBox}
    (h : (rootNoteBox top b).parent ≠ "") : (rootNoteBox top b).parent = b.parent := by
  by_cases ht : b.id = top
  · exact (h (by simp [rootNoteBox_parent, ht])).elim
  · simp [rootNoteBox_parent, ht]

private theorem subInput_boxes_map (inp : Input) (keep : ModelBox → Bool) (top : String) :
    (subInput inp keep top).boxes = (inp.boxes.filter keep).map (rootNoteBox top) := by
  unfold subInput selectInput
  dsimp only
  rw [List.map_map, ← zipIdx_filter_map_fst keep (rootNoteBox top) inp.boxes 0]
  apply List.map_congr_left
  intro q _
  change rootNoteBox top (if q.1.parent == "" then { q.1 with parent := "" } else q.1) =
    rootNoteBox top q.1
  split
  · rename_i hp
    have heq : q.1.parent = "" := beq_iff_eq.mp hp
    cases q with
    | mk b idx =>
      cases b
      simp_all
  · rfl

private theorem subInput_boxIds (inp : Input) (keep : ModelBox → Bool) (top : String) :
    (subInput inp keep top).boxes.map (·.id) = (selectInput inp keep).boxes.map (·.id) := by
  rw [subInput_boxes_map, selectInput_box_ids, List.map_map]
  apply List.map_congr_left
  intro b _
  exact rootNoteBox_id top b

private theorem box_findIdx_some {boxes : List ModelBox} {id : String} {b : ModelBox}
    (hb : b ∈ boxes) (hid : b.id = id) : ∃ i, boxes.findIdx? (·.id == id) = some i := by
  cases hfind : boxes.findIdx? (·.id == id) with
  | none =>
    have hfalse := List.findIdx?_eq_none_iff.mp hfind b hb
    simp [hid] at hfalse
  | some i => exact ⟨i, rfl⟩

private theorem chainTerm_at_box {boxes : List ModelBox} {b : ModelBox} {id : String}
    (hnd : (boxes.map (·.id)).Nodup) (hb : b ∈ boxes) (hid : b.id = id)
    (hne : id ≠ "") (n : Nat) : chainTerm boxes (n + 1) id = chainTerm boxes n b.parent := by
  obtain ⟨i, hi⟩ := box_findIdx_some hb hid
  obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
  have heq : boxes[i] = b := eq_of_mem_id hnd (List.getElem_mem hlt) hb
    ((beq_iff_eq.mp hmatch).trans hid.symm)
  rw [chainTerm.eq_3 boxes id n hne, hi]
  change (match boxes[i]? with
    | none => false
    | some x => chainTerm boxes n x.parent) = chainTerm boxes n b.parent
  rw [List.getElem?_eq_getElem hlt, heq]

private theorem subInput_parent_mem {inp : Input} {keep : ModelBox → Bool} {top : String}
    (hclose : ∀ b ∈ inp.boxes, keep b = true → b.id ≠ top → b.parent ≠ "" →
      ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true)
    {b : ModelBox} (hb : b ∈ (subInput inp keep top).boxes) (hne : b.parent ≠ "") :
    ∃ p ∈ (subInput inp keep top).boxes, p.id = b.parent := by
  rw [subInput_boxes_map] at hb
  obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hsrc
  have hnotTop : src.id ≠ top := by
    intro heq
    apply hne
    simp [rootNoteBox_parent, heq]
  have hp := rootNoteBox_parent_eq hne
  obtain ⟨p, hpmem, hpid, hkp⟩ := hclose src hmem hkeep hnotTop (fun h => hne (hp.trans h))
  rw [subInput_boxes_map]
  exact ⟨rootNoteBox top p, List.mem_map_of_mem (List.mem_filter.mpr ⟨hpmem, hkp⟩),
    (rootNoteBox_id top p).trans (hpid.trans hp.symm)⟩

private theorem chainTerm_subInput {inp : Input} {keep : ModelBox → Bool} {top : String}
    (hf : InputFacts inp) (hnd : ((subInput inp keep top).boxes.map (·.id)).Nodup)
    (hclose : ∀ b ∈ (subInput inp keep top).boxes, b.parent ≠ "" →
      ∃ p ∈ (subInput inp keep top).boxes, p.id = b.parent) :
    ∀ n id, chainTerm inp.boxes n id = true →
      (id = "" ∨ ∃ b ∈ (subInput inp keep top).boxes, b.id = id) →
      chainTerm (subInput inp keep top).boxes n id = true := by
  intro n
  induction n with
  | zero =>
    intro id hs _
    by_cases hid : id = ""
    · subst id
      exact chainTerm.eq_1 _ _
    · rw [chainTerm.eq_2 _ _ hid] at hs
      contradiction
  | succ n ih =>
    intro id hs hmem
    by_cases hid : id = ""
    · subst id
      exact chainTerm.eq_1 _ _
    obtain ⟨b, hb, hbid⟩ := hmem.resolve_left hid
    rw [chainTerm_at_box hnd hb hbid hid]
    have hb' := hb
    rw [subInput_boxes_map] at hb'
    obtain ⟨src, hsrc, heq⟩ := List.mem_map.mp hb'
    have hsrcId : src.id = id := (rootNoteBox_id top src).symm.trans
      ((congrArg ModelBox.id heq).trans hbid)
    rw [chainTerm_at_box hf.nodup (List.mem_filter.mp hsrc).1 hsrcId hid] at hs
    by_cases hpar : b.parent = ""
    · rw [hpar]
      exact chainTerm.eq_1 _ _
    · have hroot : (rootNoteBox top src).parent ≠ "" := heq.symm ▸ hpar
      have hsame := (congrArg ModelBox.parent heq).symm.trans (rootNoteBox_parent_eq hroot)
      exact ih b.parent (hsame.symm ▸ hs) (Or.inr (hclose b hb hpar))

private theorem subInput_wellFormed (inp : Input) (o : Options) (keep : ModelBox → Bool)
    (top : String) (hwf : WellFormed (inputModel inp o))
    (hclose : ∀ b ∈ inp.boxes, keep b = true → b.id ≠ top → b.parent ≠ "" →
      ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true) :
    WellFormed (inputModel (subInput inp keep top) o) := by
  have hf := inputFacts_of_wellFormed hwf
  have hnd : ((subInput inp keep top).boxes.map (·.id)).Nodup := by
    rw [subInput_boxIds]
    exact selectInput_boxes_nodup keep "" hf.nodup
  have hsource := (wellFormed_iff (inputModel inp o)).mp hwf
  rw [wellFormed_iff]
  refine ⟨nodup_eraseDups_length _ hnd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nodup_eraseDups_length _ (selectInput_routes_nodup keep "" (Model.routeIds_nodup hwf))
  · exact nodup_eraseDups_length _ (selectInput_labels_nodup keep "" (labelIds_nodup hwf))
  · intro b hb
    change b ∈ (subInput inp keep top).boxes at hb
    have hclosed : ∀ c ∈ (subInput inp keep top).boxes, c.parent ≠ "" →
        ∃ p ∈ (subInput inp keep top).boxes, p.id = c.parent :=
      fun _ hc hp => subInput_parent_mem hclose hc hp
    apply chainTerm_parentReaches hnd
    by_cases hr : b.parent = ""
    · rw [hr]
      exact chainTerm.eq_1 _ _
    · have hbig : chainTerm (subInput inp keep top).boxes inp.boxes.length b.parent = true := by
        have hcopy := hb
        rw [subInput_boxes_map] at hcopy
        obtain ⟨src, hsrc, heq⟩ := List.mem_map.mp hcopy
        have hroot : (rootNoteBox top src).parent ≠ "" := heq.symm ▸ hr
        have hp := (congrArg ModelBox.parent heq).symm.trans (rootNoteBox_parent_eq hroot)
        apply chainTerm_subInput hf hnd hclosed
        · rw [hp]
          exact hf.term src (List.mem_filter.mp hsrc).1 inp.boxes.length (Nat.le_succ _)
        · exact Or.inr (hclosed b hb hr)
      exact chainTerm_mono _ _ (chainTerm_depth hbig hb rfl) _ (Nat.sub_le _ _)
  · intro r hr
    have hends := selectInput_route_endpoints inp keep "" r hr
    change r.fromId ∈ (subInput inp keep top).boxes.map (·.id) ∧
      r.toId ∈ (subInput inp keep top).boxes.map (·.id)
    rwa [subInput_boxIds]
  · intro l hl
    have howner := selectInput_label_owner inp keep "" l hl
    change l.owner ∈ (subInput inp keep top).boxes.map (·.id) ∨
      l.owner ∈ (selectInput inp keep).routes.map (·.id)
    rwa [subInput_boxIds]
  · intro b hb hrole
    change b ∈ (subInput inp keep top).boxes at hb
    rw [subInput_boxes_map] at hb
    obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hb
    rw [rootNoteBox_role] at hrole
    rw [rootNoteBox_exclusive]
    exact hsource.2.2.2.2.2.2 src (List.mem_filter.mp hsrc).1 hrole

private theorem partSelection_parent {inp : Input} {top : String} (hf : InputFacts inp)
    {b : ModelBox} (hb : b ∈ inp.boxes)
    (hk : (b.id == top || Compound.inside inp.boxes top b.id) = true)
    (ht : b.id ≠ top) (hp : b.parent ≠ "") :
    ∃ p ∈ inp.boxes, p.id = b.parent ∧ (p.id == top || Compound.inside inp.boxes top p.id) = true := by
  have hins : Compound.inside inp.boxes top b.id = true := by simpa [ht] using hk
  rcases keepInside_close hf hb hins with hroot | htop | ⟨p, hm, hid, hi⟩
  · exact (hp hroot).elim
  · obtain ⟨p, hm, hid⟩ := (hf.parents b hb).resolve_left hp
    exact ⟨p, hm, hid, by simp [hid, beq_iff_eq.mp htop]⟩
  · exact ⟨p, hm, hid, by simp [hi]⟩

private theorem framedParents_of_rootedSelection {inp : Input} {o : Options}
    {keep : ModelBox → Bool} {top : String} (hwf : WellFormed (inputModel inp o))
    (hframe : framedParents inp = true)
    (hclose : ∀ b ∈ inp.boxes, keep b = true → b.id ≠ top → b.parent ≠ "" →
      ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true) :
    framedParents (subInput inp keep top) = true := by
  have hf := inputFacts_of_wellFormed hwf
  unfold framedParents
  rw [List.all_eq_true, subInput_boxes_map]
  intro b hb
  obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hsrc
  by_cases ht : src.id = top
  · simp [rootNoteBox_parent, ht]
  by_cases hp : src.parent = ""
  · simp [rootNoteBox_parent, ht, hp]
  obtain ⟨picked, hpicked, hpid, hkp⟩ := hclose src hmem hkeep ht hp
  obtain ⟨parent, hparent, hid, hrole, hfixed⟩ := framedParents_parent hframe hmem hp
  have heq : picked = parent := eq_of_mem_id hf.nodup hpicked hparent (hpid.trans hid.symm)
  have himg : rootNoteBox top picked ∈ (inp.boxes.filter keep).map (rootNoteBox top) :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hpicked, hkp⟩)
  have hfixed_eq : (subInput inp keep top).fixedSizes = inp.fixedSizes := rfl
  rw [hfixed_eq]
  have hany : ((inp.boxes.filter keep).map (rootNoteBox top)).any
      (fun p => p.id == (rootNoteBox top src).parent && p.role == .group &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == p.id)) = true := by
    refine List.any_eq_true.mpr ⟨rootNoteBox top picked, himg, ?_⟩
    have hpr : picked.role = .group := heq.symm ▸ hrole
    have hf' : inp.fixedSizes.any (fun fixed => fixed.1 == picked.id) = false := heq.symm ▸ hfixed
    have hsrcParent : (rootNoteBox top src).parent = src.parent := by
      simp [rootNoteBox_parent, ht]
    rw [rootNoteBox_id, rootNoteBox_role, hsrcParent]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hpid, by simp [hpr]⟩, by simp [hf']⟩
  simp only [hany, Bool.or_true]

/-- Selecting the bundle part keeps the top and its descendants, cutting only the top's parent. -/
theorem notePartSubInput_wellFormed {inp : Input} {o : Options} (top : String)
    (hwf : WellFormed (inputModel inp o)) :
    WellFormed (inputModel (subInput inp
      (fun b => b.id == top || Compound.inside inp.boxes top b.id) top) o) :=
  subInput_wellFormed inp o _ top hwf fun _ hb hk ht hp =>
    partSelection_parent (inputFacts_of_wellFormed hwf) hb hk ht hp

/-- The part roots at its top; every uncut parent is an unfixed group in the same selection. -/
theorem notePartSubInput_framedParents {inp : Input} {o : Options} (top : String)
    (hwf : WellFormed (inputModel inp o)) (hframe : framedParents inp = true) :
    framedParents (subInput inp
      (fun b => b.id == top || Compound.inside inp.boxes top b.id) top) = true :=
  framedParents_of_rootedSelection hwf hframe fun _ hb hk ht hp =>
    partSelection_parent (inputFacts_of_wellFormed hwf) hb hk ht hp

/-- A note fragment selects only its own id and clears its parent. -/
theorem noteSubInput_wellFormed {inp : Input} {o : Options} (id : String)
    (hwf : WellFormed (inputModel inp o)) :
    WellFormed (inputModel (subInput inp (fun b => b.id == id) id) o) :=
  subInput_wellFormed inp o _ id hwf fun _ _ hk hid _ => (hid (beq_iff_eq.mp hk)).elim

theorem noteSubInput_framedParents (inp : Input) (id : String) :
    framedParents (subInput inp (fun b => b.id == id) id) = true := by
  unfold framedParents
  rw [List.all_eq_true, subInput_boxes_map]
  intro b hb
  obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hb
  have hid := beq_iff_eq.mp (List.mem_filter.mp hsrc).2
  simp [rootNoteBox_parent, hid]

theorem NotesExecution.fragmentSubInputsWellFormed
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframe : framedParents inp = true) :
    ∀ l ∈ e.layouts,
      WellFormed (inputModel (subInput inp
        (fun b => b.id == l.top.id || Compound.inside inp.boxes l.top.id b.id) l.top.id) o) ∧
      framedParents (subInput inp
        (fun b => b.id == l.top.id || Compound.inside inp.boxes l.top.id b.id) l.top.id) = true ∧
      ∀ q ∈ l.notes,
        WellFormed (inputModel (subInput inp (fun b => b.id == q.1.id) q.1.id) o) ∧
        framedParents (subInput inp (fun b => b.id == q.1.id) q.1.id) = true := by
  intro l _
  exact ⟨notePartSubInput_wellFormed l.top.id hwf, notePartSubInput_framedParents l.top.id hwf hframe,
    fun q _ => ⟨noteSubInput_wellFormed q.1.id hwf, noteSubInput_framedParents inp q.1.id⟩⟩

private def contractKeptBoxes (inp : Input) (l : BundleLayout) : List (ModelBox × Nat) :=
  inp.boxes.zipIdx.filter fun q =>
    !(Compound.inside inp.boxes l.top.id q.1.id || (l.notes.map (·.1.id)).contains q.1.id)

private def contractKeptRoutes (inp : Input) (l : BundleLayout) : List (ModelRoute × Nat) :=
  inp.routes.zipIdx.filter fun q =>
    !((Compound.inside inp.boxes l.top.id q.1.fromId || q.1.fromId == l.top.id) &&
      (Compound.inside inp.boxes l.top.id q.1.toId || q.1.toId == l.top.id))

private theorem contractOne_boxIds (inp : Input) (l : BundleLayout) :
    (contractOne inp l).boxes.map (·.id) = (contractKeptBoxes inp l).map (·.1.id) := by
  unfold contractOne contractKeptBoxes
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_apply]
  split <;> rfl

private theorem contractOne_routeIds (inp : Input) (l : BundleLayout) :
    (contractOne inp l).routes.map (·.id) = (contractKeptRoutes inp l).map (·.1.id) := by
  simp only [contractOne, contractKeptRoutes, List.map_map, Function.comp_def]

private theorem contractOne_label_owner (inp : Input) (l : BundleLayout) {label : ModelLabel}
    (hlabel : label ∈ (contractOne inp l).labels) :
    label.owner ∈ (contractOne inp l).boxes.map (·.id) ∨
      label.owner ∈ (contractOne inp l).routes.map (·.id) := by
  change label ∈ inp.labels.filter (fun a =>
    (contractKeptBoxes inp l).any (·.1.id == a.owner) ||
    (contractKeptRoutes inp l).any (·.1.id == a.owner)) at hlabel
  have howner := (List.mem_filter.mp hlabel).2
  rw [contractOne_boxIds, contractOne_routeIds]
  simp only [Bool.or_eq_true] at howner
  rcases howner with hb | hr
  · obtain ⟨q, hq, heq⟩ := List.any_eq_true.mp hb
    exact Or.inl (List.mem_map.mpr ⟨q, hq, beq_iff_eq.mp heq⟩)
  · obtain ⟨q, hq, heq⟩ := List.any_eq_true.mp hr
    exact Or.inr (List.mem_map.mpr ⟨q, hq, beq_iff_eq.mp heq⟩)

private theorem contractOne_groups (inp : Input) (l : BundleLayout)
    (hgroup : ∀ b ∈ inp.boxes, b.role = .group → b.exclusive = false) :
    ∀ b ∈ (contractOne inp l).boxes, b.role = .group → b.exclusive = false := by
  intro b hb hr
  unfold contractOne at hb
  dsimp only at hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  by_cases ht : q.1.id = l.top.id
  · simp [ht] at hr
  · have hmem := getElem?_mem' (List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hq).1)
    simp [ht] at hr ⊢
    exact hgroup q.1 hmem hr

private theorem contractFold_fields (layouts : List BundleLayout) (inp : Input)
    (hb : (inp.boxes.map (·.id)).Nodup) (hr : (inp.routes.map (·.id)).Nodup)
    (hl : (inp.labels.map (·.id)).Nodup)
    (hgroup : ∀ b ∈ inp.boxes, b.role = .group → b.exclusive = false)
    (howner : ∀ a ∈ inp.labels, a.owner ∈ inp.boxes.map (·.id) ∨ a.owner ∈ inp.routes.map (·.id)) :
    let out := layouts.foldl contractOne inp
    (out.boxes.map (·.id)).Nodup ∧ (out.routes.map (·.id)).Nodup ∧
    (out.labels.map (·.id)).Nodup ∧
    (∀ b ∈ out.boxes, b.role = .group → b.exclusive = false) ∧
    (∀ a ∈ out.labels, a.owner ∈ out.boxes.map (·.id) ∨ a.owner ∈ out.routes.map (·.id)) := by
  induction layouts generalizing inp with
  | nil => exact ⟨hb, hr, hl, hgroup, howner⟩
  | cons l rest ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [contractOne_boxIds]
      apply List.Nodup.sublist _ hb
      unfold contractKeptBoxes
      simpa only [List.map_map, Function.comp_def] using
        (zipIdx_filter_map_fst_sublist (fun q =>
          !(Compound.inside inp.boxes l.top.id q.1.id ||
            (l.notes.map (·.1.id)).contains q.1.id)) inp.boxes).map ModelBox.id
    · rw [contractOne_routeIds]
      apply List.Nodup.sublist _ hr
      unfold contractKeptRoutes
      simpa only [List.map_map, Function.comp_def] using
        (zipIdx_filter_map_fst_sublist (fun q =>
          !((Compound.inside inp.boxes l.top.id q.1.fromId || q.1.fromId == l.top.id) &&
            (Compound.inside inp.boxes l.top.id q.1.toId || q.1.toId == l.top.id))) inp.routes).map ModelRoute.id
    · apply List.Nodup.sublist _ hl
      unfold contractOne
      dsimp only
      exact List.Sublist.map ModelLabel.id List.filter_sublist
    · exact contractOne_groups inp l hgroup
    · intro label hlabel
      exact contractOne_label_owner inp l hlabel

private theorem findIdx_boxId_mem {boxes : List ModelBox} {id : String} {i : Nat}
    (hf : boxes.findIdx? (·.id == id) = some i) : id ∈ boxes.map (·.id) := by
  obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
  exact List.mem_map.mpr ⟨boxes[i], List.getElem_mem hlt, beq_iff_eq.mp hmatch⟩

private theorem edgeOf_endpoints {inp : Input} {route : ModelRoute} {i : Nat} {edge : Edge}
    (h : edgeOf inp route i = .ok edge) :
    route.fromId ∈ inp.boxes.map (·.id) ∧ route.toId ∈ inp.boxes.map (·.id) := by
  unfold edgeOf at h
  cases hfrom : inp.boxes.findIdx? (·.id == route.fromId) with
  | none => simp [hfrom] at h
  | some fromIdx =>
    cases hto : inp.boxes.findIdx? (·.id == route.toId) with
    | none => simp [hfrom, hto] at h
    | some toIdx => exact ⟨findIdx_boxId_mem hfrom, findIdx_boxId_mem hto⟩

private theorem graphEdgesFrom_endpoints (inp : Input) (routes : List ModelRoute) :
    ∀ {i : Nat} {edges : List Edge}, graphEdgesFrom inp i routes = .ok edges →
      ∀ route ∈ routes,
        route.fromId ∈ inp.boxes.map (·.id) ∧ route.toId ∈ inp.boxes.map (·.id) := by
  induction routes with
  | nil =>
    intro _ _ _ _ h
    cases h
  | cons head tail ih =>
    intro i edges h route hroute
    unfold graphEdgesFrom at h
    obtain ⟨_, hhead, htail⟩ := bind_ok h
    obtain ⟨_, htail, _⟩ := bind_ok htail
    rcases List.mem_cons.mp hroute with rfl | hmem
    · exact edgeOf_endpoints hhead
    · exact ih htail route hmem

private theorem measuredGraph_endpoints {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (h : measuredGraph P inp o lines = .ok graph) :
    ∀ route ∈ inp.routes,
      route.fromId ∈ inp.boxes.map (·.id) ∧ route.toId ∈ inp.boxes.map (·.id) := by
  unfold measuredGraph at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hgraph, _⟩ := bind_ok h
  exact graphEdgesFrom_endpoints inp inp.routes hgraph

/-- The real contraction fold preserves declaration identity and label ownership. A successful
region base additionally checks every surviving route endpoint. Parent closure is separate. -/
theorem NotesExecution.contractedInput_wellFormed_fields
    {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids (reindexRegionSets idSets sub) sub opt)
      exactIds fuel inp o res) (hwf : WellFormed (inputModel inp o)) :
    let out := e.contractedInput
    (out.boxes.map (·.id)).Nodup ∧ (out.routes.map (·.id)).Nodup ∧
    (out.labels.map (·.id)).Nodup ∧
    (∀ b ∈ out.boxes, b.role = .group → b.exclusive = false) ∧
    (∀ a ∈ out.labels, a.owner ∈ out.boxes.map (·.id) ∨ a.owner ∈ out.routes.map (·.id)) ∧
    (∀ r ∈ out.routes, r.fromId ∈ out.boxes.map (·.id) ∧ r.toId ∈ out.boxes.map (·.id)) := by
  have hw := (wellFormed_iff (inputModel inp o)).mp hwf
  obtain ⟨hb, hr, hl, hg, ho⟩ := contractFold_fields e.layouts inp
    (inputFacts_of_wellFormed hwf).nodup (Model.routeIds_nodup hwf) (labelIds_nodup hwf)
    hw.2.2.2.2.2.2 hw.2.2.2.2.2.1
  obtain ⟨exec⟩ := layoutRIds_sceneExecution e.contracted_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, measuredGraph_endpoints exec.graph0_eq⟩ <;>
    rw [e.contractedInput_eq] <;> assumption

private def witnessNote : ModelBox :=
  { id := "T.note", role := .group, exclusive := false, shape := "note", direction := "right" }

private def witnessBundle : Bundle :=
  ⟨0, [⟨0, 1, true⟩]⟩

/-- A group is allowed to have note shape. Contraction deletes the attached group itself,
but does not delete or reparent that group's child. -/
def notesGroupParentWitness : Input :=
  { kind := "state"
    boxes := [{ id := "T" }, witnessNote, { id := "C", parent := "T.note" }, { id := "U" }]
    routes := [{ id := "R", fromId := "C", toId := "U" }]
    texts := [], edges := [] }

theorem notesGroupParentWitness_input_guards :
    WellFormed (inputModel notesGroupParentWitness {}) ∧
      framedParents notesGroupParentWitness = true ∧ attachedNoteParents notesGroupParentWitness = true :=
  ⟨rfl, rfl, rfl⟩

theorem notesGroupParentWitness_contract_invalid (part note : FamilyResult) (envelope : Footprint) :
    let out := contractOne notesGroupParentWitness
      ⟨{ id := "T" }, witnessBundle, part, [(witnessNote, note)], envelope⟩
    modelWellFormed (inputModel out {}) = false ∧ framedParents out = false :=
  ⟨rfl, rfl⟩

private theorem singletonMapM_ok {α β : Type} {f : α → Except LayoutError β} {x : α}
    {ys : List β} (h : [x].mapM f = .ok ys) : ∃ y, f x = .ok y ∧ [y] = ys := by
  rw [List.mapM_cons, List.mapM_nil] at h
  obtain ⟨y, hy, h⟩ := bind_ok h
  exact ⟨y, hy, Except.ok.inj h⟩

private def witnessBase (ids : List String) (inp : Input) (o : Options) :
    Except LayoutError FamilyResult :=
  layoutRIds ids [] inp o

/-- Any completed note execution on the witness has an invalid contracted input. -/
theorem notesGroupParentWitness_executed_contract_invalid {fuel : Nat} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids [] sub opt) [] fuel
      notesGroupParentWitness {} res) :
    modelWellFormed (inputModel e.contractedInput {}) = false ∧
      framedParents e.contractedInput = false := by
  have hb : e.bundles = [witnessBundle] := by
    rw [e.bundles_eq, e.atts_eq] <;> rfl
  have hmap : [witnessBundle].mapM
      (bundleLayout (layoutNotes witnessBase [] fuel) (witnessBase [])
        notesGroupParentWitness {} e.margin e.gap) = .ok e.layouts := by
    rw [← hb]
    exact e.layouts_eq
  obtain ⟨l, hl, hls⟩ := singletonMapM_ok hmap
  have htop : notesGroupParentWitness.boxes[witnessBundle.target]? = some { id := "T" } := rfl
  unfold bundleLayout at hl
  rw [htop] at hl
  obtain ⟨part, _, hl⟩ := bind_ok hl
  obtain ⟨notes, hnotes, hl⟩ := bind_ok hl
  have hlist : [⟨0, 1, true⟩].mapM (fun _ : Attach => do
      let note ← witnessBase []
        (subInput notesGroupParentWitness (fun b => b.id == witnessNote.id) witnessNote.id) {}
      pure (witnessNote, note)) = .ok notes := hnotes
  obtain ⟨pair, hpair, hns⟩ := singletonMapM_ok hlist
  obtain ⟨note, _, hpair⟩ := bind_ok hpair
  rw [e.contractedInput_eq, ← hls, List.foldl_cons, List.foldl_nil,
    ← Except.ok.inj hl, ← hns, ← Except.ok.inj hpair]
  exact notesGroupParentWitness_contract_invalid part note _

end Elegant.Layered.PipelineImpl
