import Elegant.Layered.InsetFit

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Elegant.Layered.Compound

/-- The inside sub-input of `selectInput` keeps framed parents, given a
well-formed input with framed parents.  `WellFormed` is needed for unique box
ids: without it two boxes can share an id, `Compound.inside` then resolves the
shared id through the first occurrence's ancestor path, and a kept box can
survive while its (distinct) parent is filtered out. -/
theorem framedParents_selectInput_inside (inp : Input) (o : Options)
    (group : ModelBox) (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) :
    framedParents (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) = true := by
  have hf : InputFacts inp := inputFacts_of_wellFormed hwf
  unfold framedParents
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨m, hmmem, hkeep, hbmid, hbpar⟩ := selectInput_box_spec inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id hb
  have hmin : Compound.inside inp.boxes group.id m.id = true := hkeep
  by_cases hroot : b.parent = ""
  · simp [hroot]
  · simp only [Bool.or_eq_true, beq_iff_eq]
    right
    have hmparent_ne : m.parent ≠ "" :=
      inside_parent_ne_empty hf.nodup hmin hmmem rfl
    by_cases hgid : m.parent = group.id
    · exfalso
      apply hroot
      rw [hbpar]
      simp [hgid]
    · have hbpar' : b.parent = m.parent := by
        rw [hbpar]
        simp only [beq_iff_eq, hgid, ↓reduceIte]
      rcases keepInside_close hf (b := m) hmmem hmin with h1 | h2 | ⟨p, hpmem, hpid, hpinside⟩
      · exact absurd h1 hmparent_ne
      · exact absurd (beq_iff_eq.mp h2) hgid
      · obtain ⟨img, himgmem, himgid, _⟩ := selectInput_box_exists inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id hpmem hpinside
        obtain ⟨parent, hparentmem, hpid2, hprole, hpfixed⟩ :=
          framedParents_parent hframed hmmem hmparent_ne
        have hid : img.id = b.parent := by
          rw [himgid, hpid, hbpar']
        have hrole : img.role = .group := by
          obtain ⟨src, hsmmem, _, himgeq⟩ := selectInput_box_source inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id img himgmem
          have himgid2 : img.id = src.id := by rw [himgeq]; split <;> rfl
          have himgrole : img.role = src.role := by rw [himgeq]; split <;> rfl
          have hsrcEq : src = p := eq_of_mem_id hf.nodup hsmmem hpmem
            (himgid2.symm.trans himgid)
          have hppEq : p = parent := eq_of_mem_id hf.nodup hpmem hparentmem
            (hpid.trans hpid2.symm)
          rw [himgrole, hsrcEq, hppEq]
          exact hprole
        have hfix : (inp.fixedSizes.any fun fixed => fixed.1 == img.id) = false := by
          rw [himgid, hpid, ← hpid2]
          exact hpfixed
        refine List.any_eq_true.mpr ⟨img, himgmem, ?_⟩
        have h1 : (img.id == b.parent) = true := by rw [hid]; exact beq_self_eq_true _
        have h2 : (img.role == .group) = true := by rw [hrole]; exact beq_self_eq_true _
        have h3 : (!(inp.fixedSizes.any fun fixed => fixed.1 == img.id)) = true := by
          rw [Bool.not_eq_true']; exact hfix
        exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨h1, h2⟩, h3⟩

/-- The outside sub-input keeps framed parents when the fixed side tables are
appended exactly as `layoutRecursive` appends them: the group's own measured
frame.  The second conjunct of `FramedParentsSub` as stated is false (it
*replaces* `fixedSizes` with an arbitrary list that can name a surviving
parent); this is the corrected form the consumer needs.  No surviving box has
`group.id` as parent (such a box would be inside the group), so the appended
`group.id` entry cannot shadow a real parent. -/
theorem framedParents_selectInput_outside_append (inp : Input) (o : Options)
    (group : ModelBox) (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) (size : Size) (scene : Scene)
    (area : Int) :
    framedParents { selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := inp.fixedSizes ++ [(group.id, size)],
        fixedChildren := inp.fixedChildren ++ [(group.id, scene)],
        fixedAreas := inp.fixedAreas ++ [(group.id, area)] } = true := by
  have hf : InputFacts inp := inputFacts_of_wellFormed hwf
  let target : Input := { selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) with
      fixedSizes := inp.fixedSizes ++ [(group.id, size)],
      fixedChildren := inp.fixedChildren ++ [(group.id, scene)],
      fixedAreas := inp.fixedAreas ++ [(group.id, area)] }
  have hboxes : target.boxes =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
  have hfixed : target.fixedSizes = inp.fixedSizes ++ [(group.id, size)] := rfl
  unfold framedParents
  rw [hboxes, hfixed, List.all_eq_true]
  intro bx hbx
  obtain ⟨m, hmmem, hkeep, hbmid, hbpar⟩ := selectInput_box_spec inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" hbx
  by_cases hmp : m.parent = ""
  · simp only [Bool.or_eq_true, beq_iff_eq]
    left
    rw [hbpar]
    simp [hmp]
  · simp only [Bool.or_eq_true, beq_iff_eq]
    right
    have hbpar' : bx.parent = m.parent := by
      rw [hbpar]
      simp only [beq_iff_eq, hmp, ↓reduceIte]
    rcases keepOutside_close hf (b := m) hmmem hkeep with h1 | h2 | ⟨p, hpmem, hpid, hpoutside⟩
    · exact absurd h1 hmp
    · exact absurd (beq_iff_eq.mp h2) hmp
    · obtain ⟨img, himgmem, himgid, _⟩ := selectInput_box_exists inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hpmem hpoutside
      obtain ⟨parent, hparentmem, hpid2, hprole, hpfixed⟩ :=
        framedParents_parent hframed hmmem hmp
      have hid : img.id = bx.parent := by
        rw [himgid, hpid, hbpar']
      have hrole : img.role = .group := by
        obtain ⟨src, hsmmem, _, himgeq⟩ := selectInput_box_source inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" img himgmem
        have himgid2 : img.id = src.id := by rw [himgeq]; split <;> rfl
        have himgrole : img.role = src.role := by rw [himgeq]; split <;> rfl
        have hsrcEq : src = p := eq_of_mem_id hf.nodup hsmmem hpmem
          (himgid2.symm.trans himgid)
        have hppEq : p = parent := eq_of_mem_id hf.nodup hpmem hparentmem
          (hpid.trans hpid2.symm)
        rw [himgrole, hsrcEq, hppEq]
        exact hprole
      have hout' : Compound.inside inp.boxes group.id m.id = false := by
        have hk := hkeep
        simp only [Bool.not_eq_true'] at hk
        exact hk
      have hpg : group.id ≠ parent.id := by
        intro hcon
        have hpin : Compound.inside inp.boxes p.id m.id = true :=
          inside_of_parent hf.nodup hpmem hmmem hpid hmp
        have hpidEq : p.id = parent.id := hpid.trans hpid2.symm
        rw [hpidEq, ← hcon] at hpin
        rw [hpin] at hout'
        simp at hout'
      have hfix : ((inp.fixedSizes ++ [(group.id, size)]).any
          fun fixed => fixed.1 == img.id) = false := by
        rw [himgid, hpid, ← hpid2]
        rw [List.any_append]
        simp only [Bool.or_eq_false_iff]
        refine ⟨hpfixed, ?_⟩
        have hsingleton : ([(group.id, size)].any
            fun fixed => fixed.1 == parent.id) = false := by
          simp only [List.any_cons, List.any_nil, Bool.or_false]
          show ((group.id, size).1 == parent.id) = false
          rw [beq_eq_false_iff_ne]
          exact hpg
        exact hsingleton
      refine List.any_eq_true.mpr ⟨img, himgmem, ?_⟩
      have h1 : (img.id == bx.parent) = true := by rw [hid]; exact beq_self_eq_true _
      have h2 : (img.role == .group) = true := by rw [hrole]; exact beq_self_eq_true _
      have h3 : (!((inp.fixedSizes ++ [(group.id, size)]).any
          fun fixed => fixed.1 == img.id)) = true := by
        rw [Bool.not_eq_true']; exact hfix
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨h1, h2⟩, h3⟩

/-- The corrected `framedParents` preservation seam of `InsetFit.lean`. -/
theorem framedParentsSub : FramedParentsSub := fun inp o group hwf hframed =>
  ⟨framedParents_selectInput_inside inp o group hwf hframed,
    fun size scene area =>
      framedParents_selectInput_outside_append inp o group hwf hframed size scene area⟩

/-- The C1/C3 lift over `layoutRecursive`: only the flat C3 clause and the
sub-input well-formedness seam `SubInputWellFormedC2` remain. -/
theorem layoutRecursive_c1_c3 (hsub : SubInputWellFormedC2) (hflat3 : FlatC3')
    (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive fuel inp o = .ok res →
      Validator.C1 res.scene.layoutDump ∧ Validator.C3 res.scene.layoutDump :=
  layoutRecursive_c1_c3_of_inset hsub framedParentsSub hflat3 fuel

end Elegant.Layered.PipelineImpl
