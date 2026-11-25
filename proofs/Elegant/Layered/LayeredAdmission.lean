import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint

set_option autoImplicit false

/-!
# Shared admission guard for the layered kind adapters.

The user approved four layered-adapter admission guards (parity-neutral on real
inputs: engine-built models never hit them): each adapter answers
`.error (.geometry .domain)` for a model with (1) a fixed-size box that is not
exclusive, (2) a box id equal to a route id, (3) an empty box id, or (9) a fixed
size with zero or negative width or height.

This module is the shared core: four computable `Bool` guards on
`Layered.Input` (so each adapter applies them to the input it builds) plus the
proofs that turn `layeredAdmissibleB inp = true` into the interim premises of
the kind validity theorems (`hids`, `hdisj`, `hfix` in
`LayeredSeamAdapters.lean`):

* `inputBoxIdsNonemptyB`: guard (3).
* `inputBoxRouteIdsDisjointB`: guard (2); uses the same id fields
  (`ModelBox.id`, `ModelRoute.id`) as `BoxRouteIdsDisjoint`.
* `inputFixedExclusiveB`: guard (1); every `fixedSizes` entry that names a box
  names an exclusive box. Entries naming no box are ignored, exactly as
  `InputFixedFit` ignores them (its premise quantifies only over boxes with
  `box.id = entry.1`, so an entry with no such box holds vacuously).
* `inputFixedPositiveB`: guard (9).

Exclusivity alone DOES make `InputFixedFit` hold, so no extra guard is needed
for `layeredAdmissibleB_fit`: `InputFixedFit` only constrains non-exclusive
boxes that own a label (`box.exclusive = false` is a premise), and exclusive
owners emit no scene label, so when every named box is exclusive the premise is
vacuous. The proof applies `inputFixedFit_of_fixedExclusive` directly.
Positivity (guard (9)) is kept as a separate conjunct because `InputFixedFit`
never constrains the sizes of exclusive boxes.
-/

namespace Elegant
namespace Layered

/-- Guard (3): every box id is nonempty. -/
def inputBoxIdsNonemptyB (inp : Input) : Bool :=
  inp.boxes.all (fun b => b.id != "")

/-- Guard (2): no box id equals a route id. -/
def inputBoxRouteIdsDisjointB (inp : Input) : Bool :=
  inp.boxes.all (fun b => !inp.routes.any (fun r => r.id == b.id))

/-- Guard (1): every fixed-size entry that names a box names an exclusive box.

Entries naming no box pass vacuously: a non-matching box contributes
`b.id != e.1 = true`, so only boxes with `b.id = e.1` must be exclusive. -/
def inputFixedExclusiveB (inp : Input) : Bool :=
  inp.fixedSizes.all (fun e => inp.boxes.all (fun b => (b.id != e.1 || b.exclusive)))

/-- Guard (9): every fixed size has positive width and height. -/
def inputFixedPositiveB (inp : Input) : Bool :=
  inp.fixedSizes.all (fun e => decide (0 < e.2.w ∧ 0 < e.2.h))

/-- Conjunction of the four admission guards. -/
def layeredAdmissibleB (inp : Input) : Bool :=
  inputBoxIdsNonemptyB inp && inputBoxRouteIdsDisjointB inp &&
    inputFixedExclusiveB inp && inputFixedPositiveB inp

/-- Each conjunct follows from the conjunction. -/
private theorem layeredAdmissibleB_conjuncts {inp : Input}
    (h : layeredAdmissibleB inp = true) :
    inputBoxIdsNonemptyB inp = true ∧ inputBoxRouteIdsDisjointB inp = true ∧
      inputFixedExclusiveB inp = true ∧ inputFixedPositiveB inp = true := by
  have e1 : inputBoxIdsNonemptyB inp = true := by
    cases hc : inputBoxIdsNonemptyB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have e2 : inputBoxRouteIdsDisjointB inp = true := by
    cases hc : inputBoxRouteIdsDisjointB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have e3 : inputFixedExclusiveB inp = true := by
    cases hc : inputFixedExclusiveB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have e4 : inputFixedPositiveB inp = true := by
    cases hc : inputFixedPositiveB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  exact ⟨e1, e2, e3, e4⟩

/-- Guard (3) gives nonempty box ids. -/
theorem layeredAdmissibleB_ids {inp : Input} (h : layeredAdmissibleB inp = true) :
    ∀ b ∈ inp.boxes, b.id ≠ "" := by
  have h1 := (layeredAdmissibleB_conjuncts h).1
  intro b hbmem heq
  have hall := List.all_eq_true.mp h1 b hbmem
  rw [heq] at hall
  simp at hall

/-- Guard (2) gives box/route id disjointness. -/
theorem layeredAdmissibleB_disjoint {inp : Input} (h : layeredAdmissibleB inp = true) :
    PipelineImpl.BoxRouteIdsDisjoint inp := by
  have h2 := (layeredAdmissibleB_conjuncts h).2.1
  intro id hid hcon
  obtain ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hid
  obtain ⟨r, hrmem, hreq⟩ := List.mem_map.mp hcon
  have hall := List.all_eq_true.mp h2 b hbmem
  have hfalse : inp.routes.any (fun r => r.id == b.id) = false := by
    cases hc : inp.routes.any (fun r => r.id == b.id) with
    | true => simp [hc] at hall
    | false => rfl
  have htrue : inp.routes.any (fun r => r.id == b.id) = true := by
    rw [List.any_eq_true]
    exact ⟨r, hrmem, by simp [hreq, hbeq]⟩
  rw [htrue] at hfalse
  simp at hfalse

/-- Guard (1) gives the input fixed-size fit: exclusive fixed boxes are exempt
from caption room, so the `InputFixedFit` premise over non-exclusive boxes is
vacuous. -/
theorem layeredAdmissibleB_fit {inp : Input} (h : layeredAdmissibleB inp = true)
    (o : Options) : PipelineImpl.InputFixedFit inp o := by
  apply PipelineImpl.inputFixedFit_of_fixedExclusive
  intro entry hentry box hbmem hid
  have h3 := (layeredAdmissibleB_conjuncts h).2.2.1
  have hall := List.all_eq_true.mp h3 entry hentry
  have hbox := List.all_eq_true.mp hall box hbmem
  rw [hid] at hbox
  simpa using hbox

/-- Guard (9) gives positive fixed sizes. -/
theorem layeredAdmissibleB_positive {inp : Input} (h : layeredAdmissibleB inp = true) :
    ∀ e ∈ inp.fixedSizes, 0 < e.2.w ∧ 0 < e.2.h := by
  have h4 := (layeredAdmissibleB_conjuncts h).2.2.2
  intro e he
  have hall := List.all_eq_true.mp h4 e he
  exact of_decide_eq_true hall

/-- Bundle: one admission check yields all four interim premises. -/
theorem layeredAdmissibleB_spec {inp : Input} (h : layeredAdmissibleB inp = true)
    (o : Options) :
    (∀ b ∈ inp.boxes, b.id ≠ "") ∧ PipelineImpl.BoxRouteIdsDisjoint inp ∧
      PipelineImpl.InputFixedFit inp o ∧
        (∀ e ∈ inp.fixedSizes, 0 < e.2.w ∧ 0 < e.2.h) :=
  ⟨layeredAdmissibleB_ids h, layeredAdmissibleB_disjoint h,
    layeredAdmissibleB_fit h o, layeredAdmissibleB_positive h⟩

/-- Tiny adapter helper: run `r` only when the input is admissible, else answer
the approved `.geometry .domain` error. -/
def admit (inp : Input) (r : Except LayoutFailure FamilyResult) :
    Except LayoutFailure FamilyResult :=
  if layeredAdmissibleB inp then r else .error (.geometry .domain)

/-- A successful `admit` means the input was admissible and `r` succeeded. -/
theorem admit_ok {inp : Input} {r : Except LayoutFailure FamilyResult}
    {res : FamilyResult} (h : admit inp r = .ok res) :
    layeredAdmissibleB inp = true ∧ r = .ok res := by
  unfold admit at h
  cases hb : layeredAdmissibleB inp with
  | true =>
    simp [hb] at h
    exact ⟨rfl, h⟩
  | false =>
    simp [hb] at h

end Layered
end Elegant
