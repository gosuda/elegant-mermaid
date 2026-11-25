import Elegant.Layered.NotesFlagFactsProof
import Elegant.Layered.NotesGeomC68Proof
import Elegant.Layered.RecursiveFit

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem contractOne_boxes_eq (inp : Input) (l : BundleLayout) :
    (contractOne inp l).boxes =
      (inp.boxes.filter fun b =>
        !(Compound.inside inp.boxes l.top.id b.id || (l.notes.map (·.1.id)).contains b.id)).map
        (fun b => if b.id == l.top.id then { b with role := .node, direction := "" } else b) := by
  unfold contractOne
  exact zipIdx_filter_map_fst
    (fun b => !(Compound.inside inp.boxes l.top.id b.id || (l.notes.map (·.1.id)).contains b.id))
    (fun b => if b.id == l.top.id then { b with role := .node, direction := "" } else b)
    inp.boxes 0

private theorem contractOne_box_source {inp : Input} {l : BundleLayout}
    (b : ModelBox) (hb : b ∈ (contractOne inp l).boxes) :
    ∃ a ∈ inp.boxes, b.id = a.id ∧ b.parent = a.parent := by
  rw [contractOne_boxes_eq] at hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  refine ⟨a, (List.mem_filter.mp ha).1, ?_, ?_⟩ <;> split <;> rfl

private theorem contractOne_box_ids_nodup (inp : Input) (l : BundleLayout)
    (hnd : (inp.boxes.map (·.id)).Nodup) : ((contractOne inp l).boxes.map (·.id)).Nodup := by
  rw [contractOne_boxes_eq, List.map_map]
  have hid :
      (ModelBox.id ∘ fun b : ModelBox =>
        if b.id == l.top.id then { b with role := .node, direction := "" } else b) =
        ModelBox.id := by
    funext b
    change (if b.id == l.top.id then { b with role := .node, direction := "" } else b).id = b.id
    split <;> rfl
  rw [hid]
  exact List.Nodup.sublist (List.Sublist.map ModelBox.id List.filter_sublist) hnd

private theorem index_parent_source {before after : List ModelBox}
    (hnd : (before.map (·.id)).Nodup)
    (hsource : ∀ b ∈ after, ∃ a ∈ before, b.id = a.id ∧ b.parent = a.parent)
    {id : String} {i : Nat} (hfind : after.findIdx? (·.id == id) = some i) :
    ∃ j, before.findIdx? (·.id == id) = some j ∧
      ∃ a b, after[i]? = some a ∧ before[j]? = some b ∧ a.parent = b.parent := by
  obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  obtain ⟨b, hb, hkey, hparent⟩ := hsource after[i] (List.getElem_mem hi)
  have hid : b.id = id := hkey.symm.trans (beq_iff_eq.mp hmatch)
  cases hfindBefore : before.findIdx? (·.id == id) with
  | none =>
    have hnone := List.findIdx?_eq_none_iff.mp hfindBefore b hb
    simp [hid] at hnone
  | some j =>
    obtain ⟨hj, hmatchBefore, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfindBefore
    have heq : before[j] = b := eq_of_mem_id hnd (List.getElem_mem hj) hb
      ((beq_iff_eq.mp hmatchBefore).trans hid.symm)
    refine ⟨j, rfl, after[i], b, List.getElem?_eq_getElem hi, ?_, hparent⟩
    rw [List.getElem?_eq_getElem hj, heq]

private theorem ancestor_mem_source {before after : List ModelBox}
    (hnd : (before.map (·.id)).Nodup)
    (hsource : ∀ b ∈ after, ∃ a ∈ before, b.id = a.id ∧ b.parent = a.parent)
    {group : String} {i j : Nat}
    (hi : after.findIdx? (·.id == group) = some i)
    (hj : before.findIdx? (·.id == group) = some j)
    {small large : Nat} (hle : small ≤ large) {id : String}
    (hmem : i ∈ Compound.ancestors after small id) :
    j ∈ Compound.ancestors before large id := by
  induction small generalizing large id with
  | zero => cases hmem
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      by_cases hid : id = ""
      · subst id
        rw [CompoundHelpers.ancestors_empty] at hmem
        cases hmem
      rw [Compound.ancestors.eq_3 after id small hid] at hmem
      cases hfind : after.findIdx? (·.id == id) with
      | none => rw [hfind] at hmem; cases hmem
      | some k =>
        obtain ⟨q, hfindBefore, a, b, ha, hb, hparent⟩ := index_parent_source hnd hsource hfind
        simp only [hfind, ha] at hmem
        simp only [Compound.ancestors.eq_3 before id large hid, hfindBefore, hb]
        rcases List.mem_append.mp hmem with htail | hhead
        · rw [hparent] at htail
          exact List.mem_append.mpr (Or.inl (ih (Nat.le_of_succ_le_succ hle) htail))
        · have hik : i = k := List.mem_singleton.mp hhead
          have hi' : after.findIdx? (·.id == group) = some k := hi.trans (congrArg some hik)
          obtain ⟨_, hidMatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
          obtain ⟨_, hgroupMatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi'
          have heq : id = group := (beq_iff_eq.mp hidMatch).symm.trans (beq_iff_eq.mp hgroupMatch)
          rw [heq] at hfindBefore
          have hjq : j = q := Option.some.inj (hj.symm.trans hfindBefore)
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hjq))

/-- Deleting boxes and collapsing the top's role cannot create a proper descendant. -/
theorem contractOne_inside_source {inp : Input} {l : BundleLayout}
    (hnd : (inp.boxes.map (·.id)).Nodup) {group id : String}
    (hin : Compound.inside (contractOne inp l).boxes group id = true) :
    Compound.inside inp.boxes group id = true := by
  obtain ⟨b, hb, hid, i, hi, _, _, _, hmem⟩ := inside_spec hin
  have hsource := contractOne_box_source (inp := inp) (l := l)
  obtain ⟨a, ha, hkey, hparent⟩ := hsource b hb
  obtain ⟨j, hj, _, _, _, _, _⟩ := index_parent_source hnd hsource hi
  apply inside_of_ancestors hnd ha (hkey.symm.trans hid) hj
  rw [← hparent]
  have hlen : (contractOne inp l).boxes.length ≤ inp.boxes.length := fold_length_le inp [l]
  exact ancestor_mem_source hnd hsource hi hj hlen hmem

private theorem contractOne_routes_eq (inp : Input) (l : BundleLayout) :
    (contractOne inp l).routes =
      (inp.routes.filter fun r =>
        !((Compound.inside inp.boxes l.top.id r.fromId || r.fromId == l.top.id) &&
          (Compound.inside inp.boxes l.top.id r.toId || r.toId == l.top.id))).map
        (fun r => { r with
          fromId := if Compound.inside inp.boxes l.top.id r.fromId then l.top.id else r.fromId
          toId := if Compound.inside inp.boxes l.top.id r.toId then l.top.id else r.toId }) := by
  unfold contractOne
  exact zipIdx_filter_map_fst
    (fun r => !((Compound.inside inp.boxes l.top.id r.fromId || r.fromId == l.top.id) &&
      (Compound.inside inp.boxes l.top.id r.toId || r.toId == l.top.id)))
    (fun r => { r with
      fromId := if Compound.inside inp.boxes l.top.id r.fromId then l.top.id else r.fromId
      toId := if Compound.inside inp.boxes l.top.id r.toId then l.top.id else r.toId })
    inp.routes 0

private theorem contractOne_route_mem_of_outside {inp : Input} {l : BundleLayout}
    {r : ModelRoute} (hr : r ∈ inp.routes)
    (hfrom : (l.top.id == r.fromId || Compound.inside inp.boxes l.top.id r.fromId) = false)
    (hto : (l.top.id == r.toId || Compound.inside inp.boxes l.top.id r.toId) = false) :
    r ∈ (contractOne inp l).routes := by
  obtain ⟨hfromTop, hfromInside⟩ := Bool.or_eq_false_iff.mp hfrom
  have htoInside := (Bool.or_eq_false_iff.mp hto).2
  have hfromTop' : (r.fromId == l.top.id) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hfromTop))
  rw [contractOne_routes_eq]
  refine List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, ?_⟩, ?_⟩
  · simp [hfromInside, hfromTop']
  · simp [hfromInside, htoInside]

private theorem contractFold_route_mem_of_kept (layouts : List BundleLayout) (inp : Input)
    (hnd : (inp.boxes.map (·.id)).Nodup) {r : ModelRoute} (hr : r ∈ inp.routes)
    (hkept : notesKept inp layouts r) : r ∈ (layouts.foldl contractOne inp).routes := by
  induction layouts generalizing inp with
  | nil => exact hr
  | cons l rest ih =>
    have hfrom := List.findIdx?_eq_none_iff.mp hkept.1
    have hto := List.findIdx?_eq_none_iff.mp hkept.2
    have hr' := contractOne_route_mem_of_outside (l := l) hr
      (hfrom l List.mem_cons_self) (hto l List.mem_cons_self)
    have outside {group id : String}
        (h : (group == id || Compound.inside inp.boxes group id) = false) :
        (group == id || Compound.inside (contractOne inp l).boxes group id) = false := by
      obtain ⟨htop, hin⟩ := Bool.or_eq_false_iff.mp h
      refine Bool.or_eq_false_iff.mpr ⟨htop, Bool.eq_false_iff.mpr ?_⟩
      intro hnew
      exact Bool.noConfusion (hin.symm.trans (contractOne_inside_source hnd hnew))
    have hkept' : notesKept (contractOne inp l) rest r := by
      constructor
      · exact List.findIdx?_eq_none_iff.mpr fun b hb =>
          outside (hfrom b (List.mem_cons_of_mem l hb))
      · exact List.findIdx?_eq_none_iff.mpr fun b hb =>
          outside (hto b (List.mem_cons_of_mem l hb))
    rw [List.foldl_cons]
    exact ih (contractOne inp l) (contractOne_box_ids_nodup inp l hnd) hr' hkept'

private theorem contractFold_route_ids_nodup (layouts : List BundleLayout) (inp : Input)
    (hnd : (inp.routes.map (·.id)).Nodup) :
    ((layouts.foldl contractOne inp).routes.map (·.id)).Nodup := by
  induction layouts generalizing inp with
  | nil => exact hnd
  | cons l rest ih =>
    rw [List.foldl_cons]
    apply ih
    simp only [contractOne_routes_eq, List.map_map, Function.comp_def]
    exact List.Nodup.sublist (List.Sublist.map ModelRoute.id List.filter_sublist) hnd

/-- A kept route survives the executed contraction as the same model route. -/
theorem NotesExecution.keptRoute_mem
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) (hwf : WellFormed (inputModel inp o))
    {r : ModelRoute} (hr : r ∈ inp.routes) (hkept : notesKept inp e.layouts r) :
    r ∈ e.contractedInput.routes := by
  rw [e.contractedInput_eq]
  exact contractFold_route_mem_of_kept e.layouts inp (Model.boxIds_nodup hwf) hr hkept

/-- A mirror of the executed contracted input preserves the kept routes' flags and ends. -/
theorem notesFlagsKept_of_route_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) (hwf : WellFormed (inputModel inp o))
    (hmirror : NotesRouteMirror e.contractedInput e.contracted) :
    notesFlagsKept inp e.layouts e.contracted := by
  have hnd := contractFold_route_ids_nodup e.layouts inp (Model.routeIds_nodup hwf)
  rw [← e.contractedInput_eq] at hnd
  apply notesFlagsKept_of_keptBase (e := e)
  intro r hr hkept
  have hrc := e.keptRoute_mem hwf hr hkept
  refine ⟨r, hrc, rfl, rfl, rfl, rfl, ?_⟩
  intro cr hcr hid
  obtain ⟨source, hsource, hkey, hfrom, hto, hortho⟩ := hmirror cr hcr
  have hsourceLookup := Assembly.keyed_lookup_eq ModelRoute.id _ hnd source hsource
  have hkeptLookup := Assembly.keyed_lookup_eq ModelRoute.id _ hnd r hrc
  rw [hkey.symm.trans hid] at hsourceLookup
  have heq : source = r := Option.some.inj (hsourceLookup.symm.trans hkeptLookup)
  subst source
  exact ⟨hortho, hfrom, hto⟩

theorem NotesExecution.region_flags_kept
    {idSets : List (String × List String)} {exactIds : List String} {fuel : Nat}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res) (hwf : WellFormed (inputModel inp o)) :
    notesFlagsKept inp e.layouts e.contracted :=
  notesFlagsKept_of_route_mirror e hwf (layoutRIds_routes_mirror e.contracted_eq)

end Elegant.Layered.PipelineImpl
