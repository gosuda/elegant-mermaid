import Elegant.Layered.LayeredAdmission
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveC2
import Elegant.Layered.BoxRouteIdsDisjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant.Layered.Compound

/-! # The notes-step guard premises cannot be recovered from the call context

Finding, with the definitions quoted:

- `ExpandChildCallContextB` (`RecursiveBEq.lean`) unfolds to
  `WellFormed (inputModel inp o) ∧ inp.boxes.find? ... = some group ∧
  (parentSubInput inp group P titleLines child).boxes =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
      "").boxes ∧
  layoutRecursiveB base fuel (childSubInput inp group) (childSubOptions o group)
    = .ok child ∧
  layoutRecursiveB base fuel (parentSubInput inp group P titleLines child) o
    = .ok parent ∧
  expandChild P inp o group titleLines titleHeight parent child = .ok res`.
  It carries no top-input identity, no reachability evidence, and no
  `layeredAdmissibleB` / `inputBoxIdsNonemptyB` /
  `inputBoxRouteIdsDisjointB` fact about `inp`. `modelWellFormed` does not
  check nonempty box ids or box/route id disjointness (the
  `RecursiveCallContext.lean` docstring: "Premises some steps need beyond this
  package — nonempty box ids (`hids`, which `modelWellFormed` does not check)
  and `framedParents` — stay separate `hgeo` binders"), so the two premises
  of `RegionNotesSeams.stepC2N` / `stepC7N` are independent of the context
  and cannot be derived from it.

- The fields must keep their current shapes: `rnNotesBaseSeams`
  (`RegionNotesFamilyValid.lean`) must produce `BaseSeams.stepC2` /
  `BaseSeams.stepC7` (`FamilyAssemblyB.lean`), whose types require exactly
  those premises as ∀-binders, and the lifts `layoutRecursiveB_c2`
  (`RecursiveBLiftsA.lean`) / `layoutRecursiveB_c7` (`RecursiveBLiftsB.lean`)
  apply the fields at each executed call with those premises threaded by
  their own fuel induction from the top input (`selectInput_ids_nonempty`,
  `BoxRouteIdsDisjoint.childSubInput` / `.parentSubInput`). Those files are
  not owned by this module, so dropping the premises from
  `RegionNotesSeams.stepC2N` / `stepC7N` (or re-shaping them to carry a
  top-input guard) would break `rnNotesBaseSeams`.

What IS provable from the guard, and is the smallest W-form fact needed:
the descent relation `NotesCallReached` from a top input through exactly
the child/parent sub-input steps `layoutRecursiveB` performs, and the two
guard facts at every reached input (`notesCallReached_ids_nonempty`,
`notesCallReached_disjoint`, combined in `notesCallInput_guards`). The top
guard `layeredAdmissibleB tin = true` supplies both facts at `tin`
(`layeredAdmissibleB_ids`, `layeredAdmissibleB_disjoint`), and both
transport UNCONDITIONALLY through `childSubInput` / `parentSubInput` — the
appended fixed entry touches only the fixed side tables, never boxes or
routes — so no `ParentAppendAdmissible`-style extra fact is needed for
these two conjuncts.

Remaining gap, stated precisely: no producer of `NotesCallReached` is
threaded through the recursion lifts; the lifts discharge the same two
facts by their own fuel induction instead. Wiring `NotesCallReached` into
the seam fields would require re-shaping `BaseSeams.stepC2` / `stepC7` and
the lifts (files not owned here), so the field statements stay as they are.
-/

/-- Reachability of a `layoutRecursiveB`-base call input from a top input:
the same child/parent sub-input descent the recursion performs, carried
without options (the two id guards do not depend on them) and without
per-step premises (both guards transport unconditionally; see the module
docstring). The parent step is an over-approximation — any `P`,
`titleLines`, `child` — which is sound for the guards because
`parentSubInput`'s boxes and routes are exactly the `selectInput` lists
regardless of those arguments. -/
inductive NotesCallReached (tin : Input) : Input → Prop where
  | refl : NotesCallReached tin tin
  | child (mid : Input) (group : ModelBox) (base : NotesCallReached tin mid) :
      NotesCallReached tin (childSubInput mid group)
  | parent (mid : Input) (group : ModelBox) (P : Params)
      (titleLines : List Measure.Line) (child : FamilyResult)
      (base : NotesCallReached tin mid) :
      NotesCallReached tin (parentSubInput mid group P titleLines child)

/-- Nonempty box ids at every input reached from an admissible top input:
induction on the descent, `layeredAdmissibleB_ids` at the top and
`selectInput_ids_nonempty` at each step (`childSubInput` and the boxes of
`parentSubInput` are both `selectInput` applications). -/
theorem notesCallReached_ids_nonempty {tin : Input}
    (htop : layeredAdmissibleB tin = true) {inp : Input}
    (hr : NotesCallReached tin inp) : ∀ m ∈ inp.boxes, m.id ≠ "" := by
  induction hr with
  | refl => exact layeredAdmissibleB_ids htop
  | child mid group base ih =>
      exact selectInput_ids_nonempty ih
        (fun box => Compound.inside mid.boxes group.id box.id) group.id
  | parent mid group P titleLines child base ih =>
      exact selectInput_ids_nonempty ih
        (fun box => !Compound.inside mid.boxes group.id box.id) ""

/-- Box/route id disjointness at every input reached from an admissible top
input: induction on the descent, `layeredAdmissibleB_disjoint` at the top
and the unconditional `BoxRouteIdsDisjoint.childSubInput` /
`.parentSubInput` transports at each step. -/
theorem notesCallReached_disjoint {tin : Input}
    (htop : layeredAdmissibleB tin = true) {inp : Input}
    (hr : NotesCallReached tin inp) : BoxRouteIdsDisjoint inp := by
  induction hr with
  | refl => exact layeredAdmissibleB_disjoint htop
  | child mid group base ih => exact ih.childSubInput group
  | parent mid group P titleLines child base ih =>
      exact ih.parentSubInput group P titleLines child

/-- The two seam-field premises together at a reached call input, from one
top-level admission guard: the W-form fact the `stepC2N` / `stepC7N`
premises express, discharged here for every input the recursion can reach
from an admitted top. -/
theorem notesCallInput_guards {tin inp : Input}
    (htop : layeredAdmissibleB tin = true) (hr : NotesCallReached tin inp) :
    (∀ m ∈ inp.boxes, m.id ≠ "") ∧ BoxRouteIdsDisjoint inp :=
  ⟨notesCallReached_ids_nonempty htop hr, notesCallReached_disjoint htop hr⟩

/-- The W-form fact the two seam premises need at an executed
`layoutNotes`-base call input: the top input is admissible and the call
input is reached from it through the recursion's child/parent descent. -/
def NotesCallInputsAdmissible (tin inp : Input) : Prop :=
  layeredAdmissibleB tin = true ∧ NotesCallReached tin inp

/-- Proved from the guard: admissible reachability yields both premises at
the call input. -/
theorem notesCallInputsAdmissible {tin inp : Input}
    (h : NotesCallInputsAdmissible tin inp) :
    (∀ m ∈ inp.boxes, m.id ≠ "") ∧ BoxRouteIdsDisjoint inp :=
  notesCallInput_guards h.1 h.2

end PipelineImpl
end Layered
end Elegant
