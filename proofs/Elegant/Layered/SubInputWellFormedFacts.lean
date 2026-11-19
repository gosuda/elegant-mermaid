import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveC78
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.LabelsC7Captions

set_option autoImplicit false

/-!
# The sub-input well-formedness seams of `layoutRecursive`

`SubInputWellFormedC2` (`RecursiveC2.lean`), `SubInputWellFormed`
(`RecursiveC6.lean`) and `SubInputsWellFormed` (`RecursiveC78.lean`) carry
`WellFormed` — and, for the latter two, framed parents — into both sub-inputs
the recursion builds.  All three reduce to one fact about `selectInput`: a
keep-selection that is parent-closed (a kept box either roots at the
selection root or keeps its parent inside the selection) preserves
well-formedness, because `modelWellFormed` reads only the boxes, routes, and
labels of the input.  Parent-closedness of the two selections the recursion
performs is `keepInside_close`/`keepOutside_close` (`RecursiveFit.lean`); the
fuel-sharp `InputFacts` transport is `selectInput_facts` (`RecursiveC1C3.lean`,
which runs the terminating chain walk at exactly the sub-input's own length).
The one missing piece is the bridge from the public `chainTerm` mirror to
`Model.ParentReaches`, which `wellFormed_iff` expects; it needs unique box
ids to reconcile `chainTerm`'s `findIdx?` lookup with `ParentReaches`'
`find?`.
-/

namespace Elegant.Layered.PipelineImpl

/-! ### The `chainTerm` → `ParentReaches` bridge -/

/-- `chainTerm` (the public mirror of the private `Model.parentTerminates`)
implies `ParentReaches` at the same fuel for box lists with unique ids. -/
theorem chainTerm_parentReaches {boxes : List ModelBox}
    (hnodup : (boxes.map (·.id)).Nodup) :
    ∀ (n : Nat) (id : String), chainTerm boxes n id = true → ParentReaches boxes n id := by
  intro n
  induction n with
  | zero =>
    intro id h
    by_cases hid : id = ""
    · subst hid; exact trivial
    · rw [chainTerm.eq_2 boxes id hid] at h; simp at h
  | succ n ih =>
    intro id h
    by_cases hid : id = ""
    · subst hid; exact trivial
    · rw [chainTerm.eq_3 boxes id n hid] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i idx heq opt b hb
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp heq
          obtain ⟨_, hbsame⟩ := List.getElem?_eq_some_iff.mp hb
          have hmatchb : (b.id == id) = true := by rw [← hbsame]; exact hmatch
          have hmem : b ∈ boxes := by rw [← hbsame]; exact List.getElem_mem hlt
          cases hf : boxes.find? (fun x => x.id == id) with
          | none =>
              rw [List.find?_eq_none] at hf
              exact (hf b hmem hmatchb).elim
          | some b' =>
              have hb'id : (b'.id == id) = true :=
                List.find?_some (p := fun x : ModelBox => x.id == id) hf
              have hbb : boxes[idx] = b' :=
                eq_of_mem_id hnodup (List.getElem_mem hlt)
                  (List.mem_of_find?_eq_some hf)
                  (by rw [hbsame]; exact (beq_iff_eq.mp hmatchb).trans (beq_iff_eq.mp hb'id).symm)
              rw [ParentReaches.eq_3 boxes id n hid]
              exact ⟨b', hf, ih b'.parent (by rw [← hbsame, hbb] at h; exact h)⟩

/-! ### `WellFormed` of a parent-closed selection -/

/-- A parent-closed `selectInput` selection of a well-formed input is
well-formed under any options, since `modelWellFormed` reads only the boxes,
routes, and labels of the input. -/
theorem selectInput_wellFormed (inp : Input) (o : Options) (keep : ModelBox → Bool)
    (root : String) (hwf : WellFormed (inputModel inp o))
    (hclose : ∀ b ∈ inp.boxes, keep b = true →
      b.parent = "" ∨ (b.parent == root) = true ∨
        ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true) (o' : Options) :
    WellFormed (inputModel (selectInput inp keep root) o') := by
  have hf : InputFacts inp := inputFacts_of_wellFormed hwf
  have hsf : InputFacts (selectInput inp keep root) :=
    selectInput_facts inp keep root hf hclose
  have hlabels : (inp.labels.map (·.id)).Nodup := labelIds_nodup hwf
  have hwf7 := ((wellFormed_iff (inputModel inp o)).mp hwf).2.2.2.2.2.2
  rw [wellFormed_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nodup_eraseDups_length _ hsf.nodup
  · exact nodup_eraseDups_length _
      (selectInput_routes_nodup keep root (Model.routeIds_nodup hwf))
  · exact nodup_eraseDups_length _ (selectInput_labels_nodup keep root hlabels)
  · intro b hb
    exact chainTerm_parentReaches hsf.nodup _ _
      (hsf.term b hb (selectInput inp keep root).boxes.length (by omega))
  · intro r hr
    exact selectInput_route_endpoints inp keep root r hr
  · intro l hl
    exact selectInput_label_owner inp keep root l hl
  · intro b hb hrole
    obtain ⟨m, hmem, _, hroleq, hexclq⟩ := selectInput_box_fields inp keep root hb
    rw [hroleq] at hrole
    rw [hexclq]
    exact hwf7 m hmem hrole

/-- `inputModel` reads only the boxes, routes, and labels of an input, so
replacing the fixed side tables preserves well-formedness. -/
theorem inputModel_wellFormed_fixed_congr {p : Input} {o : Options}
    (a : List (String × Size)) (b : List (String × Scene)) (c : List (String × Int))
    (h : WellFormed (inputModel p o)) :
    WellFormed (inputModel { p with fixedSizes := a, fixedChildren := b, fixedAreas := c } o) :=
  h

/-! ### The three seams -/

theorem subInputWellFormedC2 : SubInputWellFormedC2 := by
  intro inp o group hwf
  refine ⟨selectInput_wellFormed inp o
      (fun box => Compound.inside inp.boxes group.id box.id) group.id hwf
      (fun c hc hkept => keepInside_close (group := group.id)
        (inputFacts_of_wellFormed hwf) hc hkept)
      { o with direction := directionOf group.direction }, ?_⟩
  intro a b c
  exact inputModel_wellFormed_fixed_congr a b c
    (selectInput_wellFormed inp o
      (fun box => !Compound.inside inp.boxes group.id box.id) "" hwf
      (fun c hc hkept => keepOutside_close (group := group.id)
        (inputFacts_of_wellFormed hwf) hc hkept) o)

theorem subInputWellFormed : SubInputWellFormed := by
  intro _fuel inp o group _P _metric _titleLines child _parent hwf hframed
    _hP _hM _hT _hC _hPa
  refine ⟨selectInput_wellFormed inp o
      (fun box => Compound.inside inp.boxes group.id box.id) group.id hwf
      (fun c hc hkept => keepInside_close (group := group.id)
        (inputFacts_of_wellFormed hwf) hc hkept)
      (childSubOptions o group),
    framedParents_selectInput_inside inp o group hwf hframed, ?_, ?_⟩
  · exact inputModel_wellFormed_fixed_congr
        (p := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "") _ _ _
      (selectInput_wellFormed inp o
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hwf
        (fun c hc hkept => keepOutside_close (group := group.id)
          (inputFacts_of_wellFormed hwf) hc hkept) o)
  · exact framedParents_selectInput_outside_append inp o group hwf hframed
      _ child.scene child.itemArea

theorem subInputsWellFormed : SubInputsWellFormed := subInputWellFormed

end Elegant.Layered.PipelineImpl
