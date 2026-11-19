import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.CompoundPathFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Bottom frame clearance: nesting-closure helpers

The bottom conjunct of `FrameClearance` (the `IsBottom` horizontal clearance) needs a rank
closure over group nesting: every candidate-graph group top whose cluster path extends a
fixed outer group's path ranks strictly below the outer bottom marker.  These helpers are
the pure list-level facts used by that closure. -/

set_option linter.unusedSimpArgs false in
set_option linter.deprecated false in
/-- The ancestor path of `Compound.ancestors` never exceeds its fuel bound. -/
theorem ancestors_length_le : ∀ (boxes : List ModelBox) (fuel : Nat) (id : String),
    (Compound.ancestors boxes fuel id).length ≤ fuel := by
  intro boxes fuel
  induction fuel with
  | zero => intro id; simp [Compound.ancestors]
  | succ fuel ih =>
    intro id
    by_cases hid : id = ""
    · simp [Compound.ancestors, hid]
    · simp only [Compound.ancestors, hid, if_neg hid]
      cases hfind : boxes.findIdx? (fun box => box.id == id) with
      | none => simp
      | some index =>
        simp only [hfind, if_pos rfl]
        cases hbox : boxes[index]? with
        | none => simp
        | some b => simp [ih b.parent]

/-- A strict prefix survives dropping the last element. -/
theorem prefix_dropLast {pre l : List Nat} (h : pre <+: l)
    (hlen : pre.length < l.length) : pre <+: l.dropLast := by
  obtain ⟨tail, htail⟩ := h
  cases tail with
  | nil => rw [List.append_nil] at htail; subst htail; simp at hlen
  | cons t ts =>
    refine ⟨(t :: ts).dropLast, ?_⟩
    rw [← htail, List.dropLast_append_of_ne_nil (by simp)]

/-- `OrderImpl.commonPath` is a prefix of both of its arguments. -/
theorem commonPath_prefix : ∀ a b : List Nat,
    OrderImpl.commonPath a b <+: a ∧ OrderImpl.commonPath a b <+: b := by
  intro a
  induction a with
  | nil => intro b; simp [OrderImpl.commonPath]
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp [OrderImpl.commonPath]
    | cons y ys =>
      by_cases hxy : x = y
      · obtain ⟨hp1, hp2⟩ := ih ys
        obtain ⟨t1, he1⟩ := hp1
        obtain ⟨t2, he2⟩ := hp2
        refine ⟨⟨t1, ?_⟩, ⟨t2, ?_⟩⟩
        · simp [OrderImpl.commonPath, hxy, he1]
        · simp [OrderImpl.commonPath, hxy, he2]
      · simp [OrderImpl.commonPath, hxy]

end Elegant.Layered.PipelineImpl
