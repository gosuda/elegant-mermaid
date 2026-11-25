import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildLabelFactsProof

set_option autoImplicit false

/-!
# Ancestor monotonicity of one `expandChild` merge

For an executed `expandChild` call the merged box list is the parent boxes
verbatim (same parent links) plus the shifted child boxes (same ids; child
roots re-parented to the group).  Ancestor walks in either sub-dump are
therefore prefixes of the merged walk from the same id: the parent walk is
reproduced link for link, and the child walk is reproduced until the child
root, after which the merged walk continues through the group frame.  Fuel
can only grow across the merge, so membership transports to the merged
`ancestors` lists.  This discharges `ExpandChildC7AncestorMono` with no new
residual.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-! ## Walk toolkit -/

/-- One unfolded step of the ancestor walk. -/
private theorem go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty. -/
private theorem go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty. -/
private theorem go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- A `box?` hit names its own id. -/
private theorem box_id_of_box_some {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : b.id = s := by
  simp only [LayoutDump.box?] at h
  have hpred := List.find?_some h
  have htrue : (b.id == s) = true := hpred
  exact beq_iff_eq.mp htrue

/-- Parent walks reproduce link for link in the merged dump. -/
private theorem parent_go_prefix {dP dM : LayoutDump}
    (htrans : ∀ b : Box, dP.box? b.id = some b → dM.box? b.id = some b)
    (k : Nat) : ∀ (m : Nat) (s : String), k ≤ m →
    ∃ suf, LayoutDump.ancestors.go dM m s =
      LayoutDump.ancestors.go dP k s ++ suf := by
  induction k with
  | zero =>
    intro m s _
    refine ⟨LayoutDump.ancestors.go dM m s, ?_⟩
    have h0 : LayoutDump.ancestors.go dP 0 s = [] := by
      simp only [LayoutDump.ancestors.go]
    rw [h0, List.nil_append]
  | succ k ih =>
    intro m s hle
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases hP : dP.box? s with
    | none =>
      refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
      have h0 : LayoutDump.ancestors.go dP (k + 1) s = [] := go_none hP
      rw [h0, List.nil_append]
    | some b =>
      by_cases hpar : b.parent = ""
      · refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
        have h0 : LayoutDump.ancestors.go dP (k + 1) s = [] := go_root hP hpar
        rw [h0, List.nil_append]
      · have hbid : b.id = s := box_id_of_box_some hP
        have hMs : dM.box? s = some b := by
          have h2 := htrans b (by rw [hbid]; exact hP)
          rwa [hbid] at h2
        have eP : LayoutDump.ancestors.go dP (k + 1) s =
            b.parent :: LayoutDump.ancestors.go dP k b.parent :=
          go_succ hP hpar
        have eM : LayoutDump.ancestors.go dM (m' + 1) s =
            b.parent :: LayoutDump.ancestors.go dM m' b.parent :=
          go_succ hMs hpar
        have hle' : k ≤ m' := by omega
        obtain ⟨suf, hsuf⟩ := ih m' b.parent hle'
        refine ⟨suf, ?_⟩
        rw [eM, eP, hsuf, List.cons_append]

/-- Child walks reproduce link for link in the merged dump until the child
root, after which the merged walk continues through the group. -/
private theorem child_go_prefix {dC dM : LayoutDump} (groupId : String)
    (dx dy : Int)
    (htrans : ∀ b : Box, dC.box? b.id = some b →
      dM.box? b.id = some (embedBox groupId dx dy b))
    (k : Nat) : ∀ (m : Nat) (s : String), k ≤ m →
    ∃ suf, LayoutDump.ancestors.go dM m s =
      LayoutDump.ancestors.go dC k s ++ suf := by
  induction k with
  | zero =>
    intro m s _
    refine ⟨LayoutDump.ancestors.go dM m s, ?_⟩
    have h0 : LayoutDump.ancestors.go dC 0 s = [] := by
      simp only [LayoutDump.ancestors.go]
    rw [h0, List.nil_append]
  | succ k ih =>
    intro m s hle
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases hC : dC.box? s with
    | none =>
      refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
      have h0 : LayoutDump.ancestors.go dC (k + 1) s = [] := go_none hC
      rw [h0, List.nil_append]
    | some b =>
      by_cases hpar : b.parent = ""
      · refine ⟨LayoutDump.ancestors.go dM (m' + 1) s, ?_⟩
        have h0 : LayoutDump.ancestors.go dC (k + 1) s = [] := go_root hC hpar
        rw [h0, List.nil_append]
      · have hbid : b.id = s := box_id_of_box_some hC
        have hMb : dM.box? s = some (embedBox groupId dx dy b) := by
          have h2 := htrans b (by rw [hbid]; exact hC)
          rwa [hbid] at h2
        have hcond : (b.parent == "") = false := by
          cases hc : (b.parent == "") with
          | true => exact absurd (beq_iff_eq.mp hc) hpar
          | false => rfl
        have hparE : (embedBox groupId dx dy b).parent = b.parent := by
          simp [embedBox, hcond]
        have hneE : (embedBox groupId dx dy b).parent ≠ "" := by
          rw [hparE]; exact hpar
        have eC : LayoutDump.ancestors.go dC (k + 1) s =
            b.parent :: LayoutDump.ancestors.go dC k b.parent :=
          go_succ hC hpar
        have eM : LayoutDump.ancestors.go dM (m' + 1) s =
            (embedBox groupId dx dy b).parent ::
              LayoutDump.ancestors.go dM m' (embedBox groupId dx dy b).parent :=
          go_succ hMb hneE
        have hle' : k ≤ m' := by omega
        obtain ⟨suf, hsuf⟩ := ih m' b.parent hle'
        refine ⟨suf, ?_⟩
        rw [eM, eC, hparE, hsuf, List.cons_append]

/-- Ancestor chains of both sub-dumps are contained in the merged dump's
chain for the same id. -/
theorem expandChild_ancestor_mono
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {fuel : Nat} {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC7AncestorMono parent child res := by
  obtain ⟨hwf, hgroup, _hboxes, hchild, hparent, _hexpand2⟩ := hctx
  obtain ⟨_frame, _tl, dx, dy, _hframe, _hdx, _hdy, htransC, htransP⟩ :=
    expandChild_boxLookup_transport hwf hchild hparent hexpand
  obtain ⟨hleC, hleP, _hne⟩ :=
    expandChild_merge_bounds hwf hgroup hchild hparent hexpand
  have hleP' : (parent.scene.layoutDump).boxes.length ≤
      (res.scene.layoutDump).boxes.length := hleP
  have hleC' : (child.scene.layoutDump).boxes.length ≤
      (res.scene.layoutDump).boxes.length := hleC
  constructor
  · intro id x hx
    have hx' : x ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        (parent.scene.layoutDump).boxes.length id := hx
    obtain ⟨suf, hsuf⟩ := parent_go_prefix htransP _ _ id hleP'
    show x ∈ LayoutDump.ancestors.go res.scene.layoutDump
      (res.scene.layoutDump).boxes.length id
    rw [hsuf]
    exact List.mem_append.mpr (Or.inl hx')
  · intro id x hx
    have hx' : x ∈ LayoutDump.ancestors.go child.scene.layoutDump
        (child.scene.layoutDump).boxes.length id := hx
    obtain ⟨suf, hsuf⟩ := child_go_prefix group.id dx dy htransC _ _ id hleC'
    show x ∈ LayoutDump.ancestors.go res.scene.layoutDump
      (res.scene.layoutDump).boxes.length id
    rw [hsuf]
    exact List.mem_append.mpr (Or.inl hx')

end Elegant.Layered.PipelineImpl
