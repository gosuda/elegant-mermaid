import Elegant.Layered.LayeredAdmission
import Elegant.Layered.ExpandChildFitPerCallProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.Pipeline
import Elegant.Layered.SelectFacts

set_option autoImplicit false

/-!
# Per-call fixed fit from the admission guard

Proved: with the user-approved admission guard `layeredAdmissibleB top = true`
(all fixed-size entries name exclusive boxes, all fixed sizes positive),
every executed `expandChild` call input satisfies `InputFixedFit`:
`fitPerCall_of_admissible` (the exact `LayeredSeams.fitPerCall` field type
plus the top-input premise `layeredAdmissibleB tin = true` and the
recursion-context reachability premise `FitReached tin to inp o`), and the
parent-fit companion `fitParent_of_admissible`. The guard itself threads
through the recursion sub-inputs: `layeredAdmissible_childSubInput`
(unconditional) and `layeredAdmissible_parentSubInput` (conditional on the
appended group entry, see below).

Open: `layeredAdmissibleB` alone does NOT imply admissibility of the parent
sub-input, because `parentSubInput` appends one fresh fixed entry
`(group.id, childFrameSize ...)` that the top guard never constrained:
when the expanded group is non-exclusive, that entry names a non-exclusive
box, and its positivity needs the executed child canvas. The exact extra
fact is the public residual `ParentAppendAdmissible` (exclusivity of every
`group.id` box in the parent sub-input plus positivity of the appended
size). It is strictly narrower than the seam field (one entry, not the
whole input) and holds on the probe below.

`InputFixedFit.parentSubInput` (landed) already covers the appended entry
for the FIT: it proves the new entry fits by construction via
`childFrameSize_fixedSizeFit`, unconditionally on exclusivity. So the extra
fact is needed only to transport the Bool guard itself, never for the fit;
`fitPerCall_of_admissible` needs no `ParentAppendAdmissible` hypothesis.

FamilyAssembly consumption (parent rewires the seam): replace each
`S.fitPerCall fuel P inp o group titleLines titleHeight parent child res
hexpand hframed hctx hparams` argument with
`fitPerCall_of_admissible htop hr _hexpand _hframed _hctx _hparams`,
where `htop : layeredAdmissibleB tin = true` is the admitted top input's
guard and `hr : FitReached tin to inp o` is the call's reachability
evidence threaded through the existing recursion lifts at the same sites
that thread `hfitChild`/`hfitParent` (`RecursiveC7.lean`, `RecursiveC78.lean`).
Likewise `fitParent_of_seams S ...` becomes
`fitParent_of_admissible htop hr hctx hparams`. The recursion-context
premise carrying admissibility is `FitReached` (`ExpandChildFitPerCallProof`):
it mirrors exactly the child/parent sub-input steps `layoutRecursive`
takes, and the proof is induction on that structure via `fitPerCall_of_top`.

Probe: `proofs/wip/Probe/FitPerCallGuardProbe.lean` (top input with an
exclusive fixed node and an exclusive group; guard holds at the top and at
both sub-inputs, and the residual holds at the executed call).
-/

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Every `selectInput` box comes from a kept input box with the same id,
role and exclusive flag (`selectInput` only rewrites the parent pointer). -/
private theorem fpg_box_source {inp : Input} {keep : ModelBox → Bool} {root : String}
    {b : ModelBox} (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧ b.role = m.role ∧
      b.exclusive = m.exclusive := by
  unfold selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  have hget : inp.boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hqzip
  refine ⟨q.1, List.mem_of_getElem? hget, hkq, ?_, ?_, ?_⟩ <;>
    rw [← hbq] <;> split <;> rfl

/-- The nonempty-id guard survives `selectInput`: kept boxes keep their ids. -/
private theorem fpg_select_nonempty {inp : Input} {keep : ModelBox → Bool}
    {root : String} (h : inputBoxIdsNonemptyB inp = true) :
    inputBoxIdsNonemptyB (selectInput inp keep root) = true := by
  unfold inputBoxIdsNonemptyB
  apply List.all_eq_true.mpr
  intro b hb
  show ((b.id != "") = true)
  obtain ⟨m, hmem, _, hid, _, _⟩ := fpg_box_source hb
  rw [hid]
  exact List.all_eq_true.mp h m hmem

/-- The box/route id disjointness guard survives `selectInput`: both id
lists are sublists with the same ids. -/
private theorem fpg_select_disjoint {inp : Input} {keep : ModelBox → Bool}
    {root : String} (h : inputBoxRouteIdsDisjointB inp = true) :
    inputBoxRouteIdsDisjointB (selectInput inp keep root) = true := by
  unfold inputBoxRouteIdsDisjointB
  apply List.all_eq_true.mpr
  intro b hb
  show ((!((selectInput inp keep root).routes.any fun r => r.id == b.id)) = true)
  obtain ⟨m, hmem, _, hidm, _, _⟩ := fpg_box_source hb
  have hbox : (!(inp.routes.any fun r => r.id == m.id)) = true :=
    List.all_eq_true.mp h m hmem
  have hx : inp.routes.any (fun r => r.id == m.id) = false := by
    cases ha : inp.routes.any (fun r => r.id == m.id) with
    | true => simp [ha] at hbox
    | false => rfl
  have hall : ∀ x ∈ inp.routes, ¬ (x.id == m.id) = true :=
    List.any_eq_false.mp hx
  have hfalse : (selectInput inp keep root).routes.any (fun r => r.id == b.id) =
      false := by
    apply List.any_eq_false.mpr
    intro r hr
    show (¬ (r.id == b.id) = true)
    have hrIn : r ∈ inp.routes := ((selectInput_route_mem inp keep root r).mp hr).1
    have hnr := hall r hrIn
    rw [hidm]
    exact hnr
  simp [hfalse]

private theorem fpg_select_positive {inp : Input} {keep : ModelBox → Bool}
    {root : String} (h : inputFixedPositiveB inp = true) :
    inputFixedPositiveB (selectInput inp keep root) = true := by
  have hfix : (selectInput inp keep root).fixedSizes = inp.fixedSizes := rfl
  unfold inputFixedPositiveB
  rw [hfix]
  apply List.all_eq_true.mpr
  intro e he
  show ((decide (0 < e.2.w ∧ 0 < e.2.h)) = true)
  exact decide_eq_true (of_decide_eq_true (List.all_eq_true.mp h e he))

private theorem fpg_select_exclusive {inp : Input} {keep : ModelBox → Bool}
    {root : String} (h : inputFixedExclusiveB inp = true) :
    inputFixedExclusiveB (selectInput inp keep root) = true := by
  have hfix : (selectInput inp keep root).fixedSizes = inp.fixedSizes := rfl
  unfold inputFixedExclusiveB
  rw [hfix]
  apply List.all_eq_true.mpr
  intro entry hentry
  apply List.all_eq_true.mpr
  intro b hb
  show (((b.id != entry.1 || b.exclusive)) = true)
  obtain ⟨m, hmem, _, hid, _, hex⟩ := fpg_box_source hb
  have hbox := List.all_eq_true.mp (List.all_eq_true.mp h entry hentry) m hmem
  rw [hid, hex]
  exact hbox

/-- Admissibility of the child sub-input: `childSubInput` is a `selectInput`
with unchanged fixed sizes, so every guard conjunct transports. -/
theorem layeredAdmissible_childSubInput {inp : Input} (group : ModelBox)
    (h : layeredAdmissibleB inp = true) :
    layeredAdmissibleB (childSubInput inp group) = true := by
  have h1 : inputBoxIdsNonemptyB inp = true := by
    cases hc : inputBoxIdsNonemptyB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have h2 : inputBoxRouteIdsDisjointB inp = true := by
    cases hc : inputBoxRouteIdsDisjointB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have h3 : inputFixedExclusiveB inp = true := by
    cases hc : inputFixedExclusiveB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have h4 : inputFixedPositiveB inp = true := by
    cases hc : inputFixedPositiveB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have c1 : inputBoxIdsNonemptyB (childSubInput inp group) = true :=
    fpg_select_nonempty
      (keep := fun box => Compound.inside inp.boxes group.id box.id)
      (root := group.id) h1
  have c2 : inputBoxRouteIdsDisjointB (childSubInput inp group) = true :=
    fpg_select_disjoint
      (keep := fun box => Compound.inside inp.boxes group.id box.id)
      (root := group.id) h2
  have c3 : inputFixedExclusiveB (childSubInput inp group) = true :=
    fpg_select_exclusive
      (keep := fun box => Compound.inside inp.boxes group.id box.id)
      (root := group.id) h3
  have c4 : inputFixedPositiveB (childSubInput inp group) = true :=
    fpg_select_positive
      (keep := fun box => Compound.inside inp.boxes group.id box.id)
      (root := group.id) h4
  show ((inputBoxIdsNonemptyB (childSubInput inp group) &&
    inputBoxRouteIdsDisjointB (childSubInput inp group) &&
    inputFixedExclusiveB (childSubInput inp group) &&
    inputFixedPositiveB (childSubInput inp group)) = true)
  simp [c1, c2, c3, c4]

/-- The exact extra fact the parent sub-input's appended fixed entry needs:
every box in the parent sub-input carrying the group id is exclusive, and
the appended `childFrameSize` has positive width and height. The top guard
covers all older entries; only this one fresh entry is new. -/
def ParentAppendAdmissible (inp : Input) (group : ModelBox) (P : Params)
    (titleLines : List Measure.Line) (child : FamilyResult) : Prop :=
  (∀ b ∈ (parentSubInput inp group P titleLines child).boxes,
    b.id = group.id → b.exclusive = true) ∧
  0 < (childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩).w ∧
  0 < (childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩).h

/-- Admissibility of the parent sub-input: boxes, routes and old fixed
entries transport through `selectInput`; the one appended group entry is
discharged by `ParentAppendAdmissible`. -/
theorem layeredAdmissible_parentSubInput {inp : Input} {group : ModelBox}
    {P : Params} {titleLines : List Measure.Line} {child : FamilyResult}
    (h : layeredAdmissibleB inp = true)
    (hnew : ParentAppendAdmissible inp group P titleLines child) :
    layeredAdmissibleB (parentSubInput inp group P titleLines child) = true := by
  have h1 : inputBoxIdsNonemptyB inp = true := by
    cases hc : inputBoxIdsNonemptyB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have h2 : inputBoxRouteIdsDisjointB inp = true := by
    cases hc : inputBoxRouteIdsDisjointB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have h3 : inputFixedExclusiveB inp = true := by
    cases hc : inputFixedExclusiveB inp with
    | true => rfl
    | false => simp [layeredAdmissibleB, hc] at h
  have hpos : ∀ e ∈ inp.fixedSizes, 0 < e.2.w ∧ 0 < e.2.h :=
    layeredAdmissibleB_positive h
  have hfixP : (parentSubInput inp group P titleLines child).fixedSizes =
      inp.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
  have p1 : inputBoxIdsNonemptyB (parentSubInput inp group P titleLines child) =
      true :=
    fpg_select_nonempty
      (keep := fun box => !Compound.inside inp.boxes group.id box.id)
      (root := "") h1
  have p2 : inputBoxRouteIdsDisjointB
      (parentSubInput inp group P titleLines child) = true :=
    fpg_select_disjoint
      (keep := fun box => !Compound.inside inp.boxes group.id box.id)
      (root := "") h2
  have p3 : inputFixedExclusiveB (parentSubInput inp group P titleLines child) =
      true := by
    unfold inputFixedExclusiveB
    rw [hfixP]
    apply List.all_eq_true.mpr
    intro entry hentry
    apply List.all_eq_true.mpr
    intro b hb
    show (((b.id != entry.1 || b.exclusive)) = true)
    have hb' : b ∈ (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := hb
    rcases List.mem_append.mp hentry with hold | hsingle
    · obtain ⟨m, hmem, _, hid, _, hex⟩ := fpg_box_source hb'
      have hbox :=
        List.all_eq_true.mp (List.all_eq_true.mp h3 entry hold) m hmem
      rw [hid, hex]
      exact hbox
    · rw [List.mem_singleton] at hsingle
      subst hsingle
      show (((b.id != group.id || b.exclusive)) = true)
      cases hexb' : b.exclusive with
      | true => simp
      | false =>
        have hne : b.id ≠ group.id := by
          intro heq
          have hcon := hnew.1 b hb' heq
          rw [hexb'] at hcon
          simp at hcon
        have hdis : (b.id != group.id) = true := bne_iff_ne.mpr hne
        simp [hdis]
  have p4 : inputFixedPositiveB (parentSubInput inp group P titleLines child) =
      true := by
    unfold inputFixedPositiveB
    rw [hfixP]
    apply List.all_eq_true.mpr
    intro entry hentry
    show ((decide (0 < entry.2.w ∧ 0 < entry.2.h)) = true)
    rcases List.mem_append.mp hentry with hold | hsingle
    · exact decide_eq_true (hpos entry hold)
    · rw [List.mem_singleton] at hsingle
      subst hsingle
      exact decide_eq_true ⟨hnew.2.1, hnew.2.2⟩
  show ((inputBoxIdsNonemptyB (parentSubInput inp group P titleLines child) &&
    inputBoxRouteIdsDisjointB (parentSubInput inp group P titleLines child) &&
    inputFixedExclusiveB (parentSubInput inp group P titleLines child) &&
    inputFixedPositiveB (parentSubInput inp group P titleLines child)) = true)
  simp [p1, p2, p3, p4]

/-- The seam field `LayeredSeams.fitPerCall` (`FamilyAssembly.lean`) derived
from the top input's admission guard: the top fit comes from
`layeredAdmissibleB_fit`, and `FitReached` threads it down the exact
sub-inputs the recursion builds (induction via `fitPerCall_of_top`). The
unused binders are the field's executed-call premises, kept so the
statement matches the field type up to the added `htop`/`hr`. -/
theorem fitPerCall_of_admissible {tin : Input} {to : Options} {fuel : Nat}
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (htop : layeredAdmissibleB tin = true) (hr : FitReached tin to inp o)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    InputFixedFit inp o :=
  fitPerCall_of_top (layeredAdmissibleB_fit htop to) hr

/-- The parent-fit companion: `fitParent_of_seams` with the `S.fitPerCall`
field replaced by the top guard. -/
theorem fitParent_of_admissible {tin : Input} {to : Options} {fuel : Nat}
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (htop : layeredAdmissibleB tin = true) (hr : FitReached tin to inp o)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    InputFixedFit (parentSubInput inp group P titleLines child) o :=
  fitParent_of_top (layeredAdmissibleB_fit htop to) hr hctx hparams

end PipelineImpl
end Layered
end Elegant
