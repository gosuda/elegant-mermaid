import Elegant.Layered.Pipeline
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.RecursiveFit
import Elegant.Model
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Witness: inp boxes [B parent A group TB, A parent root group TB, x parent B node, y parent A node, z parent root node] routes [] texts [B A x y z] edges [] labels [], group B, parent ancestors of B = [A], g A has g.id in ancestors, framedParents = true, WellFormed = true (see wip Probe ExpandChildParentFixedForeignProbe nestedInnerFirst). The printed field (forall g) is false; the use site in FamilyAssembly fixedDisjoint_of_foreign only needs fixed g with a parent frame, which holds because framed parents are never fixed. Change the use site to pass the fixed-entry witness to the narrow form below. -/

private theorem ecpff_go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]
private theorem ecpff_go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

private theorem ecpff_go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

private theorem ecpff_empty_not_mem_go {d : LayoutDump} (k : Nat) (s : String) :
    "" ∉ LayoutDump.ancestors.go d k s := by
  revert s
  induction k with
  | zero =>
    intro s hmem
    cases hmem
  | succ k ih =>
    intro s hmem
    simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hmem
    match h : d.boxes.find? (fun b => b.id == s) with
    | none =>
      simp only [h] at hmem
      cases hmem
    | some b =>
      simp only [h] at hmem
      by_cases hp : b.parent = ""
      · simp only [hp, ↓reduceIte] at hmem
        cases hmem
      · simp only [hp, ↓reduceIte, List.mem_cons] at hmem
        have hne : ("" : String) ≠ b.parent := Ne.symm hp
        have hmem' : "" ∈ LayoutDump.ancestors.go d k b.parent := by
          rcases hmem with hcontra | hrest
          · exact absurd hcontra hne
          · exact hrest
        exact ih _ hmem'

private theorem ecpff_empty_not_mem {d : LayoutDump} (s : String) :
    "" ∉ d.ancestors s := by
  unfold LayoutDump.ancestors
  exact ecpff_empty_not_mem_go d.boxes.length s

private theorem ecpff_framed_no_fixed_parent
    {inp : Input} {g : ModelBox}
    (hframed : framedParents inp = true)
    (hg : ∃ _entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry)
    (hne : g.id ≠ "") {m : ModelBox} (hm : m ∈ inp.boxes)
    (hpar : m.parent = g.id) : False := by
  have hall : ∀ b ∈ inp.boxes,
      ((b.parent == "") ||
        inp.boxes.any (fun parent =>
          parent.id == b.parent && parent.role == .group &&
            !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id))) = true := by
    have h := hframed
    simp only [framedParents] at h
    exact List.all_eq_true.mp h
  have hmPred := hall m hm
  rw [hpar] at hmPred
  have hempty : ((g.id == "") = false) := by
    cases hbe : (g.id == "") with
    | true => exact absurd (beq_iff_eq.mp hbe) hne
    | false => rfl
  simp only [hempty, Bool.false_or] at hmPred
  obtain ⟨p, _, hpred⟩ := List.any_eq_true.mp hmPred
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨⟨hpid, _hrole⟩, hnfixed⟩ := hpred
  have hpidEq : p.id = g.id := beq_iff_eq.mp hpid
  have hfalseP : inp.fixedSizes.any (fun fixed => fixed.1 == p.id) = false := by
    simpa using hnfixed
  have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == g.id) = false := by
    rwa [hpidEq] at hfalseP
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfalse)
  obtain ⟨entry, hentry⟩ := hg
  rw [hnone] at hentry
  cases hentry

private theorem ecpff_scene_parent_mirror
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    {bb : Box} (hbb : bb ∈ parent.scene.boxes) :
    ∃ m ∈ inp.boxes, m.id = bb.id ∧ bb.parent = m.parent := by
  obtain ⟨hwf, _, hpboxes, _, hparent, _⟩ := hctx
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hpnodup : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hnodup
  obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ :=
    layoutRecursive_scene_box_parent fuel _ _ _ hpnodup hparent bb hbb
  rw [hpboxes] at hsbmem
  obtain ⟨m, hmmem, _, hmsbid, hmsbpar⟩ :=
    selectInput_box_spec inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
  have hsp : sb.parent = m.parent := by
    rw [hmsbpar]
    exact selectInput_parent_root m.parent
  exact ⟨m, hmmem, hmsbid.symm.trans hsbid, hsbpar.trans hsp⟩

private theorem ecpff_go_finds_fixed_parent
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} {g : ModelBox}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (k : Nat) (s : String)
    (hmem : g.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump k s) :
    ∃ m ∈ inp.boxes, m.parent = g.id := by
  induction k generalizing s with
  | zero =>
    simp only [LayoutDump.ancestors.go] at hmem
    cases hmem
  | succ k ih =>
    cases hbox : parent.scene.layoutDump.box? s with
    | none =>
      have e := ecpff_go_none (d := parent.scene.layoutDump) (k := k) (s := s) hbox
      rw [e] at hmem
      cases hmem
    | some b =>
      by_cases hpar : b.parent = ""
      · have e := ecpff_go_root (d := parent.scene.layoutDump) (k := k)
          (s := s) (b := b) hbox hpar
        rw [e] at hmem
        cases hmem
      · have e := ecpff_go_succ (d := parent.scene.layoutDump) (k := k)
          (s := s) (b := b) hbox hpar
        rw [e] at hmem
        rcases List.mem_cons.mp hmem with heq | htail
        · have hbb : b ∈ parent.scene.boxes := List.mem_of_find?_eq_some hbox
          obtain ⟨m, hmmem, _, hmpar⟩ := ecpff_scene_parent_mirror hctx hbb
          exact ⟨m, hmmem, (heq.trans hmpar).symm⟩
        · exact ih b.parent htail

/-- The use-site form of the `parentFixedForeign` seam: a fixed entry of the
call input never names an ancestor of the expanded group in the parent scene.
The printed field (every `g`) is false: with nested groups the outer group is
such an ancestor (see the header witness). The frame-clear lift only applies
it to fixed `g`, where `framedParents` rules the ancestor link out. -/
theorem parentFixedForeign_narrow_holds :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult) (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id := by
  intro fuel P inp o group titleLines titleHeight parent child res g
    _hexpand hframed hctx _hparams hgFixed
  by_cases hne : g.id = ""
  · rw [hne]
    exact ecpff_empty_not_mem _
  · intro hmem
    have hmemGo : g.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        parent.scene.layoutDump.boxes.length group.id := hmem
    obtain ⟨m, hmmem, hpar⟩ := ecpff_go_finds_fixed_parent hctx _ _ hmemGo
    exact ecpff_framed_no_fixed_parent hframed hgFixed hne hmmem hpar

end PipelineImpl
end Layered
end Elegant
