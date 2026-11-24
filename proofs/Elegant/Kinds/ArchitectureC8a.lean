import Elegant.GridArchitectureCellContracts
import Elegant.GridArchitectureRouteClearanceFacts
import Elegant.GridArchitectureClauses
import Elegant.GridArchitectureValidity
import Elegant.Kinds.Architecture
import Elegant.Kinds.ArchitectureC6

set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Elegant.Kinds.Architecture

open Elegant.Grid.Architecture
open Elegant.Grid.Architecture.ClearanceAux
open Elegant.Grid.Architecture.CellContracts

private instance : Inhabited Elegant.ModelBox := ⟨{ id := "" }⟩

/-! ### Dump ancestors as a model-level walk

`LayoutDump.ancestors` walks `parent` strings over dump boxes. The architecture

dump mirrors the model boxes one to one, so the walk agrees with the same walk
over `m.boxes`. -/

/-- Model-level ancestor walk, mirroring `LayoutDump.ancestors.go`. -/
def archAncestors (boxes : List ModelBox) : Nat → String → List String
  | 0, _ => []
  | n + 1, s =>
    match boxes.find? (fun b => b.id == s) with
    | none => []
    | some b => if b.parent = "" then [] else b.parent :: archAncestors boxes n b.parent

theorem archAncestors_succ (boxes : List ModelBox) (k : Nat) (s : String) :
    archAncestors boxes (k + 1) s =
      match boxes.find? (fun b => b.id == s) with
      | none => []
      | some b =>
        if b.parent = "" then [] else b.parent :: archAncestors boxes k b.parent := by
  rw [archAncestors.eq_2]

theorem archAncestors_mono (boxes : List ModelBox) (k n : Nat) (s x : String)
    (hx : x ∈ archAncestors boxes k s) : x ∈ archAncestors boxes (k + n) s := by
  induction k generalizing s with
  | zero => simp only [archAncestors, List.not_mem_nil] at hx
  | succ k ih =>
    have hshift : k + 1 + n = (k + n) + 1 := by omega
    rw [archAncestors_succ] at hx
    rw [hshift, archAncestors_succ]
    cases hfind : boxes.find? (fun b => b.id == s) with
    | none => simp only [hfind, List.not_mem_nil] at hx
    | some b =>
      simp only [hfind] at hx ⊢
      by_cases hp : b.parent = ""
      · simp only [ite_eq_left hp, List.not_mem_nil] at hx
      · simp only [ite_eq_right hp] at hx ⊢
        rcases List.mem_cons.mp hx with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih _ htail)

/-- Case analysis on one dump-box equation: a group-role model box resolves to a
translated frame, a node-role box to a translated node box. -/
theorem c8a_dump_box_cases (groups nodes : List ModelBox)
    (frames boxes : List Rect) (mb : ModelBox) (g : Box)
    (h : ((do
      let r ← if mb.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == mb.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == mb.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk mb.id mb.role.id r mb.parent mb.exclusive)) : Except LayoutError Box) = .ok g) :
    (∃ gi, (mb.role == BoxRole.group) = true ∧
      groups.findIdx? (fun q => q.id == mb.id) = some gi ∧
      g = Box.mk mb.id mb.role.id (frames.getD gi ⟨0, 0, 0, 0⟩) mb.parent mb.exclusive) ∨
    (∃ ni, (mb.role == BoxRole.group) = false ∧
      nodes.findIdx? (fun q => q.id == mb.id) = some ni ∧
      g = Box.mk mb.id mb.role.id (boxes.getD ni ⟨0, 0, 0, 0⟩) mb.parent mb.exclusive) := by
  by_cases hrole : (mb.role == BoxRole.group) = true
  · left
    simp only [hrole, ↓reduceIte] at h
    cases hfind : groups.findIdx? (fun q => q.id == mb.id) with
    | none =>
      simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw,
        throwThe, MonadExceptOf.throw] at h
      cases h
    | some gi =>
      simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at h
      cases h
      exact ⟨gi, hrole, rfl, rfl⟩
  · right
    have hroleF : (mb.role == BoxRole.group) = false := by simp [hrole]
    simp only [hroleF, ↓reduceIte] at h
    cases hfind : nodes.findIdx? (fun q => q.id == mb.id) with
    | none =>
      simp only [hfind, pure, Except.pure, Bind.bind, Except.bind, throw,
        throwThe, MonadExceptOf.throw] at h
      cases h
    | some ni =>
      simp only [hfind, pure, Except.pure, Bind.bind, Except.bind] at h
      cases h
      exact ⟨ni, hroleF, rfl, rfl⟩

/-- Every dump box comes from a model box with the same id and parent. -/
theorem c8a_dump_mem_origin (m : Model) (groups nodes : List ModelBox)
    (frames boxes : List Rect) (dumpBoxes : List Box)
    (hdumpBoxes : m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes)
    (db : Box) (hdb : db ∈ dumpBoxes) :
    ∃ mb ∈ m.boxes, mb.id = db.id ∧ mb.parent = db.parent := by
  obtain ⟨x, hmem, hmap⟩ := mapM_output_origin hdumpBoxes hdb
  rcases c8a_dump_box_cases groups nodes frames boxes x db hmap with
    ⟨_, _, _, hg⟩ | ⟨_, _, _, hg⟩ <;>
    exact ⟨x, hmem, by rw [hg], by rw [hg]⟩

/-- A dump box with a known model id is the `find?` result for that id. -/
theorem c8a_find_of_origin (m : Model) (groups nodes : List ModelBox)
    (frames boxes : List Rect) (dumpBoxes : List Box)
    (hdumpBoxes : m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes)
    (hwf : WellFormed m) (s : String) (mb : ModelBox)
    (hsid : mb.id = s) (db : Box) (hdbmem : db ∈ dumpBoxes)
    (hdbid : db.id = mb.id) :
    dumpBoxes.find? (fun b => b.id == s) = some db := by
  have hlen := (Elegant.Grid.mapM_ok_pairs _ _ hdumpBoxes).1
  have hnodupM : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hall : ∀ (j : Nat) (hjd : j < dumpBoxes.length) (hjm : j < m.boxes.length),
      (dumpBoxes[j]'hjd).id = (m.boxes[j]'hjm).id ∧
        (dumpBoxes[j]'hjd).parent = (m.boxes[j]'hjm).parent := by
    intro j hjd hjm
    have hpt := mapM_pointwise hdumpBoxes j hjm hjd
    rcases c8a_dump_box_cases groups nodes frames boxes _ _ hpt with
      ⟨_, _, _, hcon⟩ | ⟨_, _, _, hcon⟩
    · rw [hcon]; exact ⟨rfl, rfl⟩
    · rw [hcon]; exact ⟨rfl, rfl⟩
  obtain ⟨i, hilen, hieq⟩ := List.mem_iff_getElem.mp hdbmem
  have him : i < m.boxes.length := by omega
  have hdi : (dumpBoxes[i]'hilen).id = s := by rw [hieq, hdbid, hsid]
  have key : ∀ (j : Nat) (hj : j < dumpBoxes.length),
      ((dumpBoxes[j]'hj).id == s) = true → j = i := by
    intro j hj hjs
    have e1 : (dumpBoxes[j]'hj).id = s := beq_iff_eq.mp hjs
    have hjm : j < m.boxes.length := by omega
    have f1 : (m.boxes[j]'hjm).id = (m.boxes[i]'him).id := by
      have ⟨q1, _⟩ := hall j hj hjm
      have ⟨q2, _⟩ := hall i hilen him
      rw [← q1, ← q2, e1, hieq, hdbid, hsid]
    have hjmap : j < (m.boxes.map (fun b => b.id)).length := by
      simpa only [List.length_map] using hjm
    have himap : i < (m.boxes.map (fun b => b.id)).length := by
      simpa only [List.length_map] using him
    have fmap : ((m.boxes.map (fun b => b.id))[j]'hjmap) =
        ((m.boxes.map (fun b => b.id))[i]'himap) := by
      simpa only [List.getElem_map] using f1
    exact hnodupM.eq_of_getElem_eq hjmap himap fmap
  have hidx : dumpBoxes.findIdx? (fun b => b.id == s) = some i := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hilen, ?_, ?_⟩
    · simpa only [beq_iff_eq] using hdi
    · intro j hji
      intro htrue
      have hji_eq := key j (Nat.lt_trans hji hilen) htrue
      omega
  have hbind := List.find?_eq_bind_findIdx?_getElem? (xs := dumpBoxes)
    (p := fun b => b.id == s)
  rw [hidx] at hbind
  rw [← hieq]
  simpa only [Option.bind, List.getElem?_eq_getElem hilen] using hbind

/-- A model box found by id has its dump counterpart under the same id. -/
theorem c8a_find_correspond (m : Model) (groups nodes : List ModelBox)
    (frames boxes : List Rect) (dumpBoxes : List Box)
    (hdumpBoxes : m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes)
    (hwf : WellFormed m) (s : String) (mb : ModelBox)
    (hm : m.boxes.find? (fun b => b.id == s) = some mb) :
    ∃ db, dumpBoxes.find? (fun b => b.id == s) = some db ∧
      db.id = mb.id ∧ db.parent = mb.parent := by
  have hmem : mb ∈ m.boxes := List.mem_of_find?_eq_some hm
  have hsid : mb.id = s := by
    have hpm := List.find?_some hm
    simpa only [beq_iff_eq] using hpm
  obtain ⟨db, hdbmem, hdbmap⟩ := mapM_input_origin hdumpBoxes hmem
  rcases c8a_dump_box_cases groups nodes frames boxes mb db hdbmap with
    ⟨_, _, _, hg⟩ | ⟨_, _, _, hg⟩
  · have hdbid : db.id = mb.id := by rw [hg]
    have hdbpar : db.parent = mb.parent := by rw [hg]
    exact ⟨db, c8a_find_of_origin m groups nodes frames boxes dumpBoxes
      hdumpBoxes hwf s mb hsid db hdbmem hdbid, hdbid, hdbpar⟩
  · have hdbid : db.id = mb.id := by rw [hg]
    have hdbpar : db.parent = mb.parent := by rw [hg]
    exact ⟨db, c8a_find_of_origin m groups nodes frames boxes dumpBoxes
      hdumpBoxes hwf s mb hsid db hdbmem hdbid, hdbid, hdbpar⟩

/-- The dump ancestor walk agrees with the model-level walk. -/
theorem c8a_ancestors_eq (m : Model) (groups nodes : List ModelBox)
    (frames boxes : List Rect) (dumpBoxes : List Box)
    (hdumpBoxes : m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes)
    (hwf : WellFormed m) (d : LayoutDump)
    (hd : d.boxes = dumpBoxes) :
    ∀ (fuel : Nat) (s : String),
      LayoutDump.ancestors.go d fuel s = archAncestors m.boxes fuel s := by
  intro fuel s
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih =>
    have hgo : LayoutDump.ancestors.go d (f + 1) s =
        match d.box? s with
        | none => []
        | some b =>
          if b.parent = "" then [] else b.parent :: LayoutDump.ancestors.go d f b.parent := rfl
    rw [hgo, archAncestors_succ]
    simp only [LayoutDump.box?, hd]
    cases hmfind : m.boxes.find? (fun b => b.id == s) with
    | none =>
      have hnone : dumpBoxes.find? (fun b => b.id == s) = none := by
        cases hdb : dumpBoxes.find? (fun b => b.id == s) with
        | none => rfl
        | some db =>
          obtain ⟨mb, hmbmem, hmbid, _⟩ :=
            c8a_dump_mem_origin m groups nodes frames boxes dumpBoxes hdumpBoxes db
              (List.mem_of_find?_eq_some hdb)
          have hpred : (mb.id == s) = true := by
            have hps := List.find?_some hdb
            simpa only [hmbid] using hps
          have hcon : m.boxes.find? (fun b => b.id == s) ≠ none := by
            intro hnone
            rw [List.find?_eq_none] at hnone
            exact hnone mb hmbmem hpred
          exact False.elim (hcon hmfind)
      simp only [hnone, hmfind]
    | some mb =>
      obtain ⟨db, hdb, _, hpar⟩ :=
        c8a_find_correspond m groups nodes frames boxes dumpBoxes hdumpBoxes hwf s mb hmfind
      simp only [hdb, hmfind]
      rw [← hpar]
      by_cases hp : db.parent = ""
      · simp only [ite_eq_left hp]
      · simp only [ite_eq_right hp]
        exact congrArg _ (ih _)


/-- A member box is found by its own id when ids are unique. -/
theorem c8a_model_find_self (mboxes : List ModelBox)
    (hnodup : (mboxes.map (fun b => b.id)).Nodup) (mb : ModelBox)
    (hmem : mb ∈ mboxes) :
    mboxes.find? (fun b => b.id == mb.id) = some mb := by
  obtain ⟨i, hilen, hieq⟩ := List.mem_iff_getElem.mp hmem
  have hdi : (mboxes[i]'hilen).id = mb.id := by rw [hieq]
  have key : ∀ (j : Nat) (hj : j < mboxes.length),
      ((mboxes[j]'hj).id == mb.id) = true → j = i := by
    intro j hj hjs
    have e1 : (mboxes[j]'hj).id = mb.id := beq_iff_eq.mp hjs
    have f1 : (mboxes[j]'hj).id = (mboxes[i]'hilen).id := by rw [e1, hieq]
    have hjmap : j < (mboxes.map (fun b => b.id)).length := by
      simpa only [List.length_map] using hj
    have himap : i < (mboxes.map (fun b => b.id)).length := by
      simpa only [List.length_map] using hilen
    have fmap : ((mboxes.map (fun b => b.id))[j]'hjmap) =
        ((mboxes.map (fun b => b.id))[i]'himap) := by
      simpa only [List.getElem_map] using f1
    exact hnodup.eq_of_getElem_eq hjmap himap fmap
  have hidx : mboxes.findIdx? (fun b => b.id == mb.id) = some i := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hilen, ?_, ?_⟩
    · simpa only [beq_iff_eq] using hdi
    · intro j hji
      intro htrue
      have hji_eq := key j (Nat.lt_trans hji hilen) htrue
      omega
  have hbind := List.find?_eq_bind_findIdx?_getElem? (xs := mboxes)
    (p := fun b => b.id == mb.id)
  rw [hidx] at hbind
  simpa only [Option.bind, List.getElem?_eq_getElem hilen, hieq] using hbind

/-- A negative group index contributes no chain units. -/
theorem c8a_groupChain_neg (groups : List Elegant.Grid.Architecture.Group) (k : Nat) (p : Int)
    (hneg : p < 0) : groupChain groups k p = [] := by
  cases k with
  | zero => rfl
  | succ k => simp only [groupChain, hneg, ↓reduceIte]

/-- A group chain always reaches its own group unit. -/
theorem c8a_groupChain_self_mem (groups : List Elegant.Grid.Architecture.Group) (len : Nat) (g : Nat)
    (hg : g < len) :
    (⟨-1, (g : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈ groupChain groups len (Int.ofNat g) := by
  induction len with
  | zero => simp at hg
  | succ k _ =>
    have hunfold : groupChain groups (k + 1) (Int.ofNat g) =
        groupChain groups k (groups.getD (Int.ofNat g).toNat default).parent ++
          [⟨-1, Int.ofNat g⟩] := by
      simp only [groupChain]
      split
      · rename_i hcond
        exact absurd hcond (by simp)
      · rfl
    rw [hunfold]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- Injectivity of trailing group units. -/
theorem c8a_unit_group_inj {a g : Nat}
    (h : (⟨-1, (a : Int)⟩ : Elegant.Grid.Architecture.Unit) = ⟨-1, (g : Int)⟩) : a = g := by
  simp only [Elegant.Grid.Architecture.Unit.mk.injEq] at h
  exact by omega

/-- A `divergent` miss means one chain is a prefix of the other. -/
theorem c8a_divergent_none (left right : List Elegant.Grid.Architecture.Unit) (parent : Int)
    (h : divergent left right parent = none) :
    (∃ rest, right = left ++ rest) ∨ (∃ rest, left = right ++ rest) := by
  induction left generalizing right parent with
  | nil => exact Or.inl ⟨right, rfl⟩
  | cons a as ih =>
    cases right with
    | nil => exact Or.inr ⟨a :: as, by simp⟩
    | cons b bs =>
      simp only [divergent] at h
      by_cases heq : a = b
      · rw [ite_eq_left heq] at h
        obtain ⟨rest, hr⟩ | ⟨rest, hr⟩ := ih bs _ h
        · subst heq
          exact Or.inl ⟨rest, by simp only [hr, List.cons_append]⟩
        · subst heq
          exact Or.inr ⟨rest, by simp only [hr, List.cons_append]⟩
      · rw [ite_eq_right heq] at h
        cases h

/-- Membership lifts through one walk step with a known parent link. -/
theorem c8a_walk_step (mboxes : List ModelBox) (mb : ModelBox)
    (hfind : mboxes.find? (fun b => b.id == mb.id) = some mb)
    (hne : mb.parent ≠ "") (F' : Nat) (x : String)
    (hx : x ∈ archAncestors mboxes F' mb.parent) :
    x ∈ archAncestors mboxes (F' + 1) mb.id := by
  have hwalk : archAncestors mboxes (F' + 1) mb.id =
      mb.parent :: archAncestors mboxes F' mb.parent := by
    simp only [archAncestors_succ, hfind, hne, ↓reduceIte]
  rw [hwalk]
  exact List.mem_cons_of_mem _ hx

/-- A nonempty parent is reached in one walk step. -/
theorem c8a_walk_head (mboxes : List ModelBox) (mb : ModelBox)
    (hfind : mboxes.find? (fun b => b.id == mb.id) = some mb)
    (hne : mb.parent ≠ "") (F' : Nat) :
    mb.parent ∈ archAncestors mboxes (F' + 1) mb.id := by
  have hwalk : archAncestors mboxes (F' + 1) mb.id =
      mb.parent :: archAncestors mboxes F' mb.parent := by
    simp only [archAncestors_succ, hfind, hne, ↓reduceIte]
  rw [hwalk]
  exact List.mem_cons_self
theorem c8a_group_anc_mem (groups : List ModelBox)
    (groupInput : List Elegant.Grid.Architecture.Group)
    (mboxes : List ModelBox)
    (hfind : ∀ mb ∈ mboxes, mboxes.find? (fun b => b.id == mb.id) = some mb)
    (hmem : ∀ g, g < groups.length → (groups.getD g default) ∈ mboxes)
    (hglen : groupInput.length = groups.length)
    (hpar : ∀ g, g < groups.length → ∀ s, (groups.getD g default).parent = s →
      (s = "" ∧ (groupInput.getD g default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (groupInput.getD g default).parent = Int.ofNat g'))
    (hord : ∀ k, k < groupInput.length → (groupInput.getD k default).parent < Int.ofNat k) :
    ∀ (k : Nat) (g : Nat), g < groups.length → ∀ a : Nat,
      ⟨-1, (a : Int)⟩ ∈ groupChain groupInput k (Int.ofNat g) →
      a = g ∨ (a < groups.length ∧ ∀ F : Nat, g + 1 ≤ F →
        (groups.getD a default).id ∈ archAncestors mboxes F (groups.getD g default).id) := by
  intro k
  induction k with
  | zero =>
    intro g hg a hm
    simp only [groupChain, List.not_mem_nil] at hm
  | succ k ih =>
    intro g hg a hm
    have hg2 : g < groupInput.length := by omega
    have hunfold : groupChain groupInput (k + 1) (Int.ofNat g) =
        groupChain groupInput k (groupInput.getD g default).parent ++
          [⟨-1, Int.ofNat g⟩] := by
      have hget : groupInput.getD (Int.ofNat g).toNat default =
          groupInput.getD g default := by
        simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
      simp only [groupChain]
      split
      · rename_i hcond
        exact absurd hcond (by simp)
      · rw [hget]
    rw [hunfold] at hm
    rcases List.mem_append.mp hm with hleft | hright
    · rcases hpar g hg (groups.getD g default).parent rfl with
        ⟨hs, hneg⟩ | ⟨g', hg', hne, hsid, hpg⟩
      · have htail : groupChain groupInput k ((groupInput.getD g default).parent) = [] := by
          rw [hneg]
          exact c8a_groupChain_neg _ _ _ (by decide)
        rw [htail] at hleft
        simp only [List.not_mem_nil] at hleft
      · have hmem' : (⟨-1, (a : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
            groupChain groupInput k (Int.ofNat g') := by
          rw [hpg] at hleft
          exact hleft
        have hplt : g' < g := by
          have hlt := hord g hg2
          rw [hpg] at hlt
          exact Int.ofNat_lt.mp hlt
        have hIH := ih g' hg' a hmem'
        rcases hIH with rfl | ⟨halt, hdeep⟩
        · refine Or.inr ⟨hg', fun F hF => ?_⟩
          cases F with
          | zero => omega
          | succ F' =>
            have hHW := c8a_walk_head mboxes (groups.getD g default)
              (hfind _ (hmem _ hg)) hne F'
            rw [← hsid]
            exact hHW
        · refine Or.inr ⟨halt, fun F hF => ?_⟩
          cases F with
          | zero => omega
          | succ F' =>
            have htail := hdeep F' (by omega)
            rw [← hsid] at htail
            exact c8a_walk_step mboxes (groups.getD g default)
              (hfind _ (hmem _ hg)) hne F' _ htail
    · have heq : (⟨-1, (a : Int)⟩ : Elegant.Grid.Architecture.Unit) =
          (⟨-1, (Int.ofNat g : Int)⟩ : Elegant.Grid.Architecture.Unit) :=
        List.mem_singleton.mp hright
      exact Or.inl (c8a_unit_group_inj heq)

/-- Chain membership pushes node ids into the model ancestor walk. -/
theorem c8a_node_anc_mem (groups : List ModelBox) (nodes : List ModelBox)
    (groupInput : List Elegant.Grid.Architecture.Group)
    (nodeInput : List Elegant.Grid.Architecture.Node)
    (L : Nat) (mboxes : List ModelBox)
    (hfind : ∀ mb ∈ mboxes, mboxes.find? (fun b => b.id == mb.id) = some mb)
    (hmemG : ∀ g, g < groups.length → (groups.getD g default) ∈ mboxes)
    (hmemN : ∀ ni, ni < nodes.length → (nodes.getD ni default) ∈ mboxes)
    (hglen : groupInput.length = groups.length)
    (hparG : ∀ g, g < groups.length → ∀ s, (groups.getD g default).parent = s →
      (s = "" ∧ (groupInput.getD g default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (groupInput.getD g default).parent = Int.ofNat g'))
    (hparN : ∀ ni, ni < nodes.length → ∀ s, (nodes.getD ni default).parent = s →
      (s = "" ∧ (nodeInput.getD ni default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (nodeInput.getD ni default).parent = Int.ofNat g'))
    (hord : ∀ k, k < groupInput.length → (groupInput.getD k default).parent < Int.ofNat k)
    (hL : groups.length < L) :
    ∀ (ni : Nat), ni < nodes.length → ∀ (owner : Int),
      (nodeInput.getD ni default).parent = owner → ∀ a : Nat,
      ⟨-1, (a : Int)⟩ ∈
        groupChain groupInput (groupInput.length) owner ++
          [(⟨(ni : Int), (-1 : Int)⟩ : Elegant.Grid.Architecture.Unit)] →
      a < groups.length ∧
        (groups.getD a default).id ∈ archAncestors mboxes L (nodes.getD ni default).id := by
  intro ni hni owner howner a hm
  rcases List.mem_append.mp hm with hleft | hright
  · rcases hparN ni hni (nodes.getD ni default).parent rfl with
      ⟨hs, hown⟩ | ⟨g', hg', hne, hsid, hown⟩
    · have how0 : owner = -1 := by rw [← howner]; exact hown
      rw [how0] at hleft
      have hempty : groupChain groupInput (groupInput.length) (-1 : Int) = [] :=
        c8a_groupChain_neg _ _ _ (by decide)
      rw [hempty] at hleft
      simp only [List.not_mem_nil] at hleft
    · have hown_eq : owner = Int.ofNat g' := by rw [← howner]; exact hown
      rw [hown_eq] at hleft
      have hG := c8a_group_anc_mem groups groupInput mboxes hfind hmemG hglen
        hparG hord _ g' hg' a hleft
      rcases hG with rfl | ⟨halt, hdeep⟩
      · refine ⟨hg', ?_⟩
        cases L with
        | zero => omega
        | succ F' =>
          have hHW := c8a_walk_head mboxes (nodes.getD ni default)
            (hfind _ (hmemN _ hni)) hne F'
          rw [← hsid]
          exact hHW
      · refine ⟨halt, ?_⟩
        cases L with
        | zero => omega
        | succ F' =>
          have htail := hdeep F' (by omega)
          rw [← hsid] at htail
          exact c8a_walk_step mboxes (nodes.getD ni default)
            (hfind _ (hmemN _ hni)) hne F' _ htail
  · have heq := List.mem_singleton.mp hright
    simp only [Elegant.Grid.Architecture.Unit.mk.injEq] at heq
    omega

/-- Dropping `i` elements exposes the `i`-th element. -/
theorem c8a_drop_cons {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l.drop i = l[i]'hi :: l.drop (i + 1) := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => simp at hi
    | cons x xs => rfl
  | succ i ih =>
    cases l with
    | nil => simp at hi
    | cons x xs =>
      have hi' : i < xs.length := by
        have h1 := hi
        simp only [List.length_cons] at h1
        omega
      show List.drop i xs = xs[i]'hi' :: List.drop (i + 1) xs
      exact ih xs hi'

/-- Residual supply for steps 1-3, about the `placeHierarchy` and
`resolveHierarchy` hierarchy loop: the executed build's hierarchy
preconditions (ordered group parents, admitted parent links, positive pitch,
nonnegative padding and line height). Strictly simpler than `Validator.C8a`;
used as the hypothesis of every step lemma below. -/
def c8a_residual_hierarchy (input : Input) (p : Params) (fp : FrameParams) : Prop :=
  (∀ k, k < input.groups.length →
    (input.groups.getD k default).parent < Int.ofNat k) ∧
  (∀ g, g < input.groups.length →
    (input.groups.getD g default).parent = -1 ∨
      ∃ parent, parent < input.groups.length ∧
        (input.groups.getD g default).parent = Int.ofNat parent) ∧
  (∀ parent ∈ input.parents,
    parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g) ∧
  0 < p.pitchX ∧ 0 < p.pitchY ∧ 0 ≤ fp.padding ∧ 0 ≤ fp.lineHeight

/-- Step 1: distinct virtual indices diverge into executed siblings. -/
theorem c8a_step1_siblings (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (hres : c8a_residual_hierarchy input p fp)
    (a b : Nat) (ha : a < (virtualParents input).length)
    (hb : b < (virtualParents input).length) (different : a ≠ b) :
    ∃ owner first second,
      divergent (chainOf input a) (chainOf input b) (-1) =
        some (owner, first, second) ∧
      SiblingsExecuted input p fp fuel owner first second := by
  obtain ⟨ordered, groupParents, parents, px, py, padding, line⟩ := hres
  exact divergent_siblings_executed input p fp fuel ordered groupParents parents
    px py padding line a b ha hb different

/-- Step 2: executed siblings have separated resolved unit spans. -/
theorem c8a_step2_separation (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (hres : c8a_residual_hierarchy input p fp)
    (owner : Int) (first second : Elegant.Grid.Architecture.Unit)
    (siblings : SiblingsExecuted input p fp fuel owner first second) :
    (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
      first).overlaps
      (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
        second) = false := by
  obtain ⟨ordered, _, _, px, py, padding, line⟩ := hres
  exact executed_sibling_final_spans_separated input p fp fuel
    ordered px py padding line owner first second siblings

/-- Step 3 (nodes): every chain member's resolved span contains the terminal tile. -/
theorem c8a_step3_node_contain (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (hres : c8a_residual_hierarchy input p fp)
    (n : Nat) (hn : n < (virtualParents input).length)
    (unit : Elegant.Grid.Architecture.Unit) (member : unit ∈ chainOf input n) :
    (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
      unit).contains
      (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
        (⟨Int.ofNat n, -1⟩ : Elegant.Grid.Architecture.Unit)) := by
  obtain ⟨ordered, _, parents, px, py, padding, line⟩ := hres
  exact chain_unit_contains_node_tile input p fp fuel ordered px py padding line
    parents n hn unit member

/-- Span containment is reflexive. -/
theorem c8a_contains_refl (s : Span) : s.contains s := by
  unfold Span.contains
  omega

/-- Span containment is transitive. -/
theorem c8a_contains_trans (outer middle inner : Span)
    (h1 : outer.contains middle) (h2 : middle.contains inner) :
    outer.contains inner := by
  unfold Span.contains at h1 h2 ⊢
  omega

/-- Step 3 (groups): an ancestor frame contains every descendant frame below it
in its group chain. -/
theorem c8a_step3_group_contain (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (hres : c8a_residual_hierarchy input p fp) :
    ∀ (k g : Nat), g < input.groups.length → ∀ (x : Nat),
      x < input.groups.length →
      (⟨-1, (x : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈ groupChain input.groups k (Int.ofNat g) →
      ((resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD x
        default).contains
        ((resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD g
          default) := by
  intro k
  induction k with
  | zero =>
    intro g _ x _ hmem
    simp only [groupChain, List.not_mem_nil] at hmem
  | succ k ih =>
    intro g hg x hx hmem
    have hget : (input.groups.getD (Int.ofNat g).toNat default) =
        input.groups.getD g default := by
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
    have hunfold : groupChain input.groups (k + 1) (Int.ofNat g) =
        groupChain input.groups k (input.groups.getD g default).parent ++
          [⟨-1, Int.ofNat g⟩] := by
      simp only [groupChain]
      split
      · rename_i hcond
        exact absurd hcond (by simp)
      · rw [hget]
    rw [hunfold] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨ordered, groupParents, _, px, py, padding, line⟩ := hres
      rcases groupParents g hg with hneg | ⟨p', hp', hpg⟩
      · have hempty : groupChain input.groups k
            ((input.groups.getD g default).parent) = [] := by
          rw [hneg]
          exact c8a_groupChain_neg _ _ _ (by decide)
        rw [hempty] at hleft
        simp only [List.not_mem_nil] at hleft
      · rw [hpg] at hleft
        have hIH := ih p' hp' x hx hleft
        have hstep := resolved_group_contains_child_frame input p fp fuel ordered
          px py padding line g p' hg hp' hpg
        exact c8a_contains_trans _ _ _ hIH hstep
    · have heq : (⟨-1, (x : Int)⟩ : Elegant.Grid.Architecture.Unit) = ⟨-1, Int.ofNat g⟩ :=
        List.mem_singleton.mp hright
      have hxg : x = g := by
        simp only [Elegant.Grid.Architecture.Unit.mk.injEq] at heq
        simp only [Int.ofNat_eq_natCast] at heq
        omega
      subst hxg
      exact c8a_contains_refl _

/-- Step 4: containment transports sibling separation to translated rects. -/
theorem c8a_step4_disjoint (outerA outerB innerA innerB : Span)
    (ra rb : Rect) (dx dy : Int)
    (hsep : outerA.overlaps outerB = false)
    (hA : outerA.contains innerA) (hB : outerB.contains innerB)
    (hTA : translateRect dx dy innerA = .ok ra)
    (hTB : translateRect dx dy innerB = .ok rb) :
    Disjoint ra rb := by
  have hsepInner :=
    spansSeparated_of_contains outerA outerB innerA innerB hA hB hsep
  exact translateRect_disjoint_of_spans dx dy innerA innerB ra rb hTA hTB hsepInner

/-- Steps 1-4 composed (node-node case): distinct virtual tiles are separated. -/
theorem c8a_tiles_disjoint_of_residual (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (hres : c8a_residual_hierarchy input p fp)
    (a b : Nat) (ha : a < (virtualParents input).length)
    (hb : b < (virtualParents input).length) (different : a ≠ b) :
    (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
      (⟨Int.ofNat a, -1⟩ : Elegant.Grid.Architecture.Unit)).overlaps
      (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
        (⟨Int.ofNat b, -1⟩ : Elegant.Grid.Architecture.Unit)) = false := by
  obtain ⟨owner, first, second, hdiv, hsib⟩ :=
    c8a_step1_siblings input p fp fuel hres a b ha hb different
  have hsep := c8a_step2_separation input p fp fuel hres owner first second hsib
  have hmem := chainOf_divergent_units input a b owner first second hdiv
  have hA := c8a_step3_node_contain input p fp fuel hres a ha first hmem.2.1
  have hB := c8a_step3_node_contain input p fp fuel hres b hb second hmem.2.2.1
  exact spansSeparated_of_contains _ _ _ _ hA hB hsep

/-- Residual supply for the group case of step 3, about the `groupChain` walk:
a frame contains every group below its own suffix position in a descendant
chain. Used by `c8a_step3_group_frame_of_suffix`; tested by the probe. -/
def c8a_residual_groupSuffix (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) : Prop :=
  ∀ (s g : Nat), s < input.groups.length → g < input.groups.length →
    ∀ (shared rest : List Elegant.Grid.Architecture.Unit),
      groupChain input.groups input.groups.length (Int.ofNat g) =
        shared ++ (⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit) :: rest →
      (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
        (⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit)).contains
        ((resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD g
          default)

/-- Step 3 (group frames at suffix positions): the residual applied. -/
theorem c8a_step3_group_frame_of_suffix (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (hres : c8a_residual_groupSuffix input p fp fuel)
    (s g : Nat) (hs : s < input.groups.length) (hg : g < input.groups.length)
    (shared rest : List Elegant.Grid.Architecture.Unit)
    (hsuf : groupChain input.groups input.groups.length (Int.ofNat g) =
      shared ++ (⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit) :: rest) :
    (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
      (⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit)).contains
      ((resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD g
        default) :=
  hres s g hs hg shared rest hsuf

/-- A successful `parentIndex` lookup admits only the root or an in-range group
index (copy of the private C2 helper). -/
theorem c8a_parentIndex_ok_admitted {groups : List ModelBox} {id : String}
    {p : Int} (h : parentIndex groups id = .ok p) :
    p = -1 ∨ ∃ i, i < groups.length ∧ p = Int.ofNat i := by
  unfold parentIndex at h
  by_cases he : id.isEmpty = true
  · simp only [he, ↓reduceIte, Except.ok.injEq] at h
    exact Or.inl h.symm
  · simp only [he] at h
    cases hf : groups.findIdx? (fun b => b.id == id) with
    | none => rw [hf] at h; simp at h
    | some i =>
        rw [hf] at h
        simp at h
        have hi : i < groups.length :=
          (List.findIdx?_eq_some_iff_findIdx_eq.mp hf).1
        exact Or.inr ⟨i, hi, h.symm⟩

/-- Pointwise form of `mapM` for `getD` lookup (copy of the private C8 helper). -/
theorem c8a_mapM_getD {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (a : α) (b : β) (hi : i < xs.length) :
    f (xs.getD i a) = .ok (ys.getD i b) := by
  have hj : i < ys.length := by
    have hlen := (Elegant.Grid.mapM_ok_pairs _ _ h).1
    omega
  have hpt := mapM_pointwise h i hi hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] at hpt ⊢
  exact hpt

/-- The computed pitch never drops below the base pitch (copies of the private
C2 helpers). -/
theorem c8a_pitch_x_lower (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    p.pitchX ≤ (Grid.Architecture.pitch p nodes edgeLabels).x := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

theorem c8a_pitch_y_lower (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    p.pitchY ≤ (Grid.Architecture.pitch p nodes edgeLabels).y := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

theorem c8a_pitch_top_nonneg (p : Grid.Architecture.GeometryParams)
    (nodes : List Grid.Architecture.Node) (edgeLabels : List Size) :
    0 ≤ (Grid.Architecture.pitch p nodes edgeLabels).top := by
  simp only [Grid.Architecture.pitch]
  split <;> omega

/-- Config-decode nonnegativity (copies of the private CellContracts helpers). -/
theorem c8a_checked_config_integer_nonnegative
    (source : Option (String × ConfigValue)) (n : Int)
    (decoded : (match source with
      | some (_, .integer value) =>
        if 0 ≤ value ∧ value ≤ I32_MAX then some value else none
      | _ => none) = some n) : 0 ≤ n := by
  cases source with
  | none => cases decoded
  | some pair =>
    obtain ⟨key, value⟩ := pair
    cases value with
    | string value => cases decoded
    | boolean value => cases decoded
    | integer value =>
      change (if 0 ≤ value ∧ value ≤ I32_MAX then some value else none) = some n at decoded
      by_cases valid : 0 ≤ value ∧ value ≤ I32_MAX
      · rw [ite_eq_left valid] at decoded
        have same := Option.some.inj decoded
        rw [← same]
        exact valid.1
      · rw [ite_eq_right valid] at decoded
        cases decoded

theorem c8a_decoded_frame_padding_nonnegative
    (m : Model) (profile : Profile) (cell : Bool) (padding : Int)
    (decoded : padding = (match
        (match m.options.config.find? (fun q => q.1 == "padding") with
          | some (_, .integer value) =>
            if 0 ≤ value ∧ value ≤ I32_MAX then some value else none
          | _ => none) with
      | some px => if cell then Int.fdiv (2 * px + 20) 40 else px * 64
      | none => LayoutConst.architecture_padding.get profile)) :
    0 ≤ padding := by
  let value : Option Int :=
    match m.options.config.find? (fun q => q.1 == "padding") with
    | some (_, .integer value) =>
      if 0 ≤ value ∧ value ≤ I32_MAX then some value else none
    | _ => none
  change padding = (match value with
    | some px => if cell then Int.fdiv (2 * px + 20) 40 else px * 64
    | none => LayoutConst.architecture_padding.get profile) at decoded
  cases actual : value with
  | none =>
    rw [actual] at decoded
    rw [decoded]
    change 0 ≤ LayoutConst.architecture_padding.get profile
    cases profile <;> decide
  | some px =>
    have sourceNonnegative := c8a_checked_config_integer_nonnegative
      (m.options.config.find? (fun q => q.1 == "padding")) px actual
    rw [actual] at decoded
    rw [decoded]
    cases cell with
    | false =>
      change 0 ≤ px * 64
      exact Int.mul_nonneg sourceNonnegative (by decide)
    | true =>
      change 0 ≤ Int.fdiv (2 * px + 20) 40
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
      exact Int.ediv_nonneg (by omega) (by decide)

/-- An empty-tested string is the empty string. -/
theorem c8a_isEmpty_eq_empty (s : String) (h : s.isEmpty = true) : s = "" := by
  have hbeq : s.utf8ByteSize == 0 := h
  have h0 : s.utf8ByteSize = 0 := beq_iff_eq.mp hbeq
  exact String.utf8ByteSize_eq_zero_iff.mp h0

/-- A `Level` unit membership with separated absolute rects yields executed
sibling indices (copy of the private CellContracts witness). -/
theorem c8a_level_sibling_witness (l : Level) (first second : Elegant.Grid.Architecture.Unit)
    (left : first ∈ l.units) (right : second ∈ l.units) (different : first ≠ second)
    (separated : ∀ i j, i < l.units.length → j < l.units.length → i ≠ j →
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false) :
    ∃ i j, i < l.units.length ∧ j < l.units.length ∧
      l.units[i]? = some first ∧ l.units[j]? = some second ∧ i ≠ j ∧
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false := by
  obtain ⟨i, leftLookup⟩ := List.mem_iff_getElem?.mp left
  obtain ⟨j, rightLookup⟩ := List.mem_iff_getElem?.mp right
  have hi := (List.getElem?_eq_some_iff.mp leftLookup).choose
  have hj := (List.getElem?_eq_some_iff.mp rightLookup).choose
  have indices : i ≠ j := by
    intro equal
    rw [equal, rightLookup] at leftLookup
    exact different (Option.some.inj leftLookup).symm
  exact ⟨i, j, hi, hj, leftLookup, rightLookup, indices,
    separated i j hi hj indices⟩

/-- A member of a reverse range splits it (copy of the private CellContracts
split). -/
theorem c8a_split_member (indices : List Nat) (g : Nat) (member : g ∈ indices) :
    ∃ before suffix, indices = before ++ g :: suffix := by
  induction indices with
  | nil => simp at member
  | cons a rest ih =>
    rcases List.mem_cons.mp member with same | present
    · subst a
      exact ⟨[], rest, rfl⟩
    · obtain ⟨before, suffix, equal⟩ := ih present
      exact ⟨a :: before, suffix, by simp only [equal, List.cons_append]⟩

/-- A resolved unit span for a group unit is that group's frame. -/
theorem c8a_resolvedUnitSpan_group (p : Params)
    (resolved : Resolved) (u : Elegant.Grid.Architecture.Unit)
    (h : 0 ≤ u.group) :
    resolvedUnitSpan p resolved u = resolved.frames.getD u.group.toNat default := by
  unfold resolvedUnitSpan
  rw [ite_eq_right (by omega : ¬ u.group < 0)]

/-- Any two diverging chains with admitted paths execute as siblings in their
owner level (generalizes `divergent_siblings_executed` beyond virtual indices). -/
theorem c8a_level_siblings_executed (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (hres : c8a_residual_hierarchy input p fp)
    (left right : List Elegant.Grid.Architecture.Unit)
    (leftEnd rightEnd : Int)
    (leftPath : ParentPath input (-1) left leftEnd)
    (rightPath : ParentPath input (-1) right rightEnd)
    (owner : Int) (first second : Elegant.Grid.Architecture.Unit)
    (found : divergent left right (-1) = some (owner, first, second)) :
    SiblingsExecuted input p fp fuel owner first second := by
  obtain ⟨ordered, groupParents, parents, px, py, padding, line⟩ := hres
  have owned := divergent_units_owned input left right (-1) leftEnd rightEnd
    owner first second leftPath rightPath found
  have distinct : first ≠ second :=
    (divergent_common_prefix left right (-1) owner first second found).1
  rcases owned_parent_admitted input groupParents parents owner first owned.1 with
    root | ⟨g, hg, groupOwner⟩
  · subst root
    let before := (List.range input.groups.length).reverse
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    have m1 := owned_unit_in_level input p state.relative (-1) first owned.1
    have m2 := owned_unit_in_level input p state.relative (-1) second owned.2
    refine ⟨before, Or.inl ⟨rfl, rfl⟩, ?_⟩
    apply c8a_level_sibling_witness l first second
    · simpa only [l, arrange_units] using m1
    · simpa only [l, arrange_units] using m2
    · exact distinct
    · exact executed_root_unit_rects_separated input p fp fuel ordered px py padding line
  · subst groupOwner
    obtain ⟨before, suffix, position⟩ := c8a_split_member
      (List.range input.groups.length).reverse g
      (List.mem_reverse.mpr (List.mem_range.mpr hg))
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    have m1 := owned_unit_in_level input p state.relative (Int.ofNat g) first owned.1
    have m2 := owned_unit_in_level input p state.relative (Int.ofNat g) second owned.2
    refine ⟨before, Or.inr ⟨g, suffix, rfl, position⟩, ?_⟩
    apply c8a_level_sibling_witness l first second
    · simpa only [l, arrange_units] using m1
    · simpa only [l, arrange_units] using m2
    · exact distinct
    · exact executed_group_unit_rects_separated input p fp fuel ordered px py
        padding line before suffix g position

theorem c8a_groupChain_mem_node (groups : List Elegant.Grid.Architecture.Group)
    (fuel : Nat) (parent : Int) (u : Elegant.Grid.Architecture.Unit)
    (hmem : u ∈ groupChain groups fuel parent) : u.node = -1 := by
  induction fuel generalizing parent with
  | zero => simp only [groupChain, List.not_mem_nil] at hmem
  | succ k ih =>
    by_cases hneg : parent < 0
    · have hempty := c8a_groupChain_neg groups (k + 1) parent hneg
      rw [hempty] at hmem
      simp only [List.not_mem_nil] at hmem
    · have hunfold : groupChain groups (k + 1) parent =
          groupChain groups k ((groups.getD parent.toNat default).parent) ++
            [⟨-1, parent⟩] := by
        simp only [groupChain]
        rw [ite_eq_right hneg]
      rw [hunfold] at hmem
      rcases List.mem_append.mp hmem with hleft | hright
      · exact ih _ hleft
      · have heq := List.mem_singleton.mp hright
        rw [heq]
/-- Every member of a `groupChain` rooted at an in-range group is in range. -/
theorem c8a_groupChain_mem_bound (groups : List Elegant.Grid.Architecture.Group)
    (ordered : ∀ k, k < groups.length →
      (groups.getD k default).parent < Int.ofNat k)
    (g : Nat) (hg : g < groups.length) (fuel : Nat)
    (u : Elegant.Grid.Architecture.Unit)
    (hmem : u ∈ groupChain groups fuel (Int.ofNat g)) :
    u.group.toNat < groups.length := by
  induction fuel generalizing g with
  | zero => simp only [groupChain, List.not_mem_nil] at hmem
  | succ k ih =>
    have hget : (groups.getD (Int.ofNat g).toNat default) =
        groups.getD g default := by
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
    have hunfold : groupChain groups (k + 1) (Int.ofNat g) =
        groupChain groups k (groups.getD g default).parent ++
          [⟨-1, Int.ofNat g⟩] := by
      simp only [groupChain]
      split
      · rename_i hcond
        exact absurd hcond (by simp)
      · rw [hget]
    rw [hunfold] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · by_cases hneg : (groups.getD g default).parent < 0
      · have hempty : groupChain groups k
            ((groups.getD g default).parent) = [] :=
          c8a_groupChain_neg _ _ _ hneg
        rw [hempty] at hleft
        simp only [List.not_mem_nil] at hleft
      · have hnn : 0 ≤ (groups.getD g default).parent := by omega
        have hge : (groups.getD g default).parent =
            ↑((groups.getD g default).parent.toNat) :=
          (Int.toNat_of_nonneg hnn).symm
        rw [hge] at hleft
        have hlt := ordered g hg
        rw [hge] at hlt
        simp only [Int.ofNat_eq_natCast] at hlt
        have hlt' : (groups.getD g default).parent.toNat < g :=
          Int.ofNat_lt.mp hlt
        have hleft' : u ∈ groupChain groups k
            (Int.ofNat ((groups.getD g default).parent.toNat)) := by
          simp only [Int.ofNat_eq_natCast]
          exact hleft
        have hbound := ih _ (Nat.lt_trans hlt' hg) hleft'
        exact hbound
    · have heq := List.mem_singleton.mp hright
      rw [heq]
      show (Int.ofNat g).toNat < groups.length
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
      exact hg

/-- Gap (a): the executed-build index bundle. Everything the C8a assembly needs
from a successful build: model/input/geometry correspondence, per-box dump
indices with translated rects and parent-index equations, the hierarchy facts,
and the tile-fit and constant facts. Proved as `c8a_dump_box_index`. -/
abbrev c8a_gapA_index (m : Model) (scene : Scene) (capped : Bool)
    (_built : build m = .ok (scene, capped)) : Prop :=
  ∃ (groups nodes : List ModelBox) (groupInput : List Elegant.Grid.Architecture.Group)
    (nodeInput : List Grid.Architecture.Node) (input : Input)
    (pitch : Pitch) (params : Params) (frameParams : FrameParams)
    (placed : Placement) (resolved : Resolved) (geometry : Geometry)
    (dx dy : Int) (frames boxes : List Rect) (dumpBoxes : List Box),
    groups = m.boxes.filter (fun b => b.role == .group) ∧
    nodes = m.boxes.filter (fun b => b.role != .group) ∧
    groupInput.length = groups.length ∧
    nodeInput.length = nodes.length ∧
    input.parents = nodeInput.map (fun n => n.parent) ∧
    input.groups = groupInput ∧
    params.pitchX = pitch.x ∧ params.pitchY = pitch.y ∧
    placed = placeHierarchy input params frameParams
      (LayoutConst.architecture_bfs_cap.get m.profile).toNat ∧
    resolved = resolveHierarchy input params placed ∧
    geometry = Grid.Architecture.geometry (archParams m) pitch nodeInput groupInput resolved ∧
    geometry.frames = resolved.frames ∧
    frames.length = geometry.frames.length ∧
    boxes.length = geometry.boxes.length ∧
    (∀ i, i < frames.length →
      translateRect dx dy (geometry.frames.getD i default) = .ok (frames.getD i default)) ∧
    (∀ i, i < boxes.length →
      translateRect dx dy (geometry.boxes.getD i default) = .ok (boxes.getD i default)) ∧
    scene.layoutDump.boxes = dumpBoxes ∧
    (∀ db ∈ dumpBoxes,
      (∃ gi, gi < groups.length ∧ (groups.getD gi default).id = db.id ∧
        (groups.getD gi default).parent = db.parent ∧
        db.rect = frames.getD gi default ∧ gi < input.groups.length ∧
        (∃ pv, parentIndex groups (groups.getD gi default).parent = .ok pv ∧
          (groupInput.getD gi default).parent = pv) ∧
        translateRect dx dy (geometry.frames.getD gi default) =
          .ok (frames.getD gi default) ∧
        db.role = (groups.getD gi default).role.id) ∨
      (∃ ni, ni < nodes.length ∧ (nodes.getD ni default).id = db.id ∧
        (nodes.getD ni default).parent = db.parent ∧
        db.rect = boxes.getD ni default ∧ ni < input.parents.length ∧
        (∃ pv, parentIndex groups (nodes.getD ni default).parent = .ok pv ∧
          (nodeInput.getD ni default).parent = pv) ∧
        translateRect dx dy (geometry.boxes.getD ni default) =
          .ok (boxes.getD ni default) ∧
        db.role = (nodes.getD ni default).role.id)) ∧
    (∀ g, g < groups.length → ∀ s, (groups.getD g default).parent = s →
      (s = "" ∧ (groupInput.getD g default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (groupInput.getD g default).parent = Int.ofNat g')) ∧
    (∀ ni, ni < nodes.length → ∀ s, (nodes.getD ni default).parent = s →
      (s = "" ∧ (nodeInput.getD ni default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (nodeInput.getD ni default).parent = Int.ofNat g')) ∧
    (∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k) ∧
    (∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ gparent, gparent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat gparent) ∧
    (∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g) ∧
    0 < params.pitchX ∧ 0 < params.pitchY ∧
    0 ≤ frameParams.padding ∧ 0 ≤ frameParams.lineHeight ∧
    (∀ n, n < nodeInput.length →
      nodeTileFits (archParams m) pitch (nodeInput.getD n default) = true) ∧
    (∀ n, n < nodeInput.length →
      (nodeInput.getD n default).junction = true →
        0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2) ∧
    0 ≤ pitch.top ∧ 0 ≤ (archParams m).gutter ∧ 0 ≤ (archParams m).thickness ∧
    m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes

/-- Gap (b): dump-ancestor membership from chain membership, through the landed
model-walk bridge. Proved as `c8a_prefix_not_ancestor`. -/
abbrev c8a_gapB_bridge (m : Model) (groups nodes : List ModelBox)
    (groupInput : List Elegant.Grid.Architecture.Group)
    (nodeInput : List Grid.Architecture.Node) (input : Input) (L : Nat)
    (_hgroups : groups = m.boxes.filter (fun b => b.role == .group))
    (_hnodes : nodes = m.boxes.filter (fun b => b.role != .group))
    (_hglen : groupInput.length = groups.length)
    (_hnlen : nodeInput.length = nodes.length)
    (_hparG : ∀ g, g < groups.length → ∀ s, (groups.getD g default).parent = s →
      (s = "" ∧ (groupInput.getD g default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (groupInput.getD g default).parent = Int.ofNat g'))
    (_hparN : ∀ ni, ni < nodes.length → ∀ s, (nodes.getD ni default).parent = s →
      (s = "" ∧ (nodeInput.getD ni default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (nodeInput.getD ni default).parent = Int.ofNat g'))
    (_hord : ∀ k, k < groupInput.length →
      (groupInput.getD k default).parent < Int.ofNat k)
    (_hinputPar : input.parents = nodeInput.map (fun n => n.parent))
    (_hinputGrp : input.groups = groupInput)
    (_hwf : WellFormed m)
    (frames boxes : List Rect) (dumpBoxes : List Box)
    (_hdumpBoxes : m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes)
    (d : LayoutDump) (_hd : d.boxes = dumpBoxes)
    (_hL : groups.length < L) : Prop :=
  (∀ (ni : Nat) (_hni : ni < nodes.length) (g : Nat) (_hg : g < groups.length)
    (owner : Int) (_howner : (nodeInput.getD ni default).parent = owner),
    (⟨-1, (g : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈ chainOf input ni →
    (groups.getD g default).id ∈ d.ancestors (nodes.getD ni default).id) ∧
  (∀ (g : Nat) (_hg : g < groups.length) (x : Nat) (_hx : x < groups.length),
    x ≠ g →
    (⟨-1, (x : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
      groupChain groupInput (groupInput.length) (Int.ofNat g) →
    (groups.getD x default).id ∈ d.ancestors (groups.getD g default).id)

/-- Appending after `l₁` does not change `getD` lookups inside `l₁`. -/
theorem c8a_getD_append_left {α : Type} (l₁ l₂ : List α) (n : Nat) (d : α)
    (h : n < l₁.length) : (l₁ ++ l₂).getD n d = l₁.getD n d := by
  induction l₁ generalizing n with
  | nil => simp at h
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have h' : n < as.length := by
        simp only [List.length_cons] at h
        omega
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih n h'

/-- A filter never gains elements. -/
theorem c8a_filter_length_le (p : ModelBox → Bool) (l : List ModelBox) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases hb : p b = true
    · simp only [hb, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ ih
    · have hbF : p b = false := by
        cases hpb : p b with
        | true => exact absurd hpb hb
        | false => rfl
      simp only [hbF, ↓reduceIte]
      exact Nat.le_succ_of_le ih

/-- A list element failing the predicate makes the filtered list strictly shorter. -/
theorem c8a_groups_lt_of_node (l : List ModelBox) (x : ModelBox) (hx : x ∈ l)
    (hfail : (x.role == BoxRole.group) = false) :
    (l.filter (fun b => b.role == BoxRole.group)).length < l.length := by
  induction l with
  | nil => simp at hx
  | cons b bs ih =>
    simp only [List.filter_cons, List.length_cons] at ⊢
    by_cases hb : (b.role == BoxRole.group) = true
    · simp only [hb, ↓reduceIte, List.length_cons] at ⊢
      rcases List.mem_cons.mp hx with rfl | hmem
      · rw [hfail] at hb
        cases hb
      · exact Nat.succ_lt_succ (ih hmem)
    · have hbF : (b.role == BoxRole.group) = false := by
        cases hpb : (b.role == BoxRole.group) with
        | true => exact absurd hpb hb
        | false => rfl
      simp only [hbF, ↓reduceIte] at ⊢
      exact Nat.lt_succ_of_le (c8a_filter_length_le _ _)

/-- Gap (b): dump-ancestor membership from executed chain membership, through the
landed model-walk bridge. -/
theorem c8a_prefix_not_ancestor (m : Model) (groups nodes : List ModelBox)
    (groupInput : List Elegant.Grid.Architecture.Group)
    (nodeInput : List Grid.Architecture.Node) (input : Input) (L : Nat)
    (hgroups : groups = m.boxes.filter (fun b => b.role == .group))
    (hnodes : nodes = m.boxes.filter (fun b => b.role != .group))
    (hglen : groupInput.length = groups.length)
    (hnlen : nodeInput.length = nodes.length)
    (hparG : ∀ g, g < groups.length → ∀ s, (groups.getD g default).parent = s →
      (s = "" ∧ (groupInput.getD g default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (groupInput.getD g default).parent = Int.ofNat g'))
    (hparN : ∀ ni, ni < nodes.length → ∀ s, (nodes.getD ni default).parent = s →
      (s = "" ∧ (nodeInput.getD ni default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (nodeInput.getD ni default).parent = Int.ofNat g'))
    (hord : ∀ k, k < groupInput.length →
      (groupInput.getD k default).parent < Int.ofNat k)
    (hinputPar : input.parents = nodeInput.map (fun n => n.parent))
    (hinputGrp : input.groups = groupInput)
    (hwf : WellFormed m)
    (frames boxes : List Rect) (dumpBoxes : List Box)
    (hdumpBoxes : m.boxes.mapM (fun (b : ModelBox) => ((do
      let r ← if b.role == BoxRole.group then
        match groups.findIdx? (fun q => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match nodes.findIdx? (fun q => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure (Box.mk b.id b.role.id r b.parent b.exclusive)) : Except LayoutError Box)) = .ok dumpBoxes)
    (d : LayoutDump) (hd : d.boxes = dumpBoxes)
    (hL : groups.length < L) :
    c8a_gapB_bridge m groups nodes groupInput nodeInput input L hgroups hnodes
      hglen hnlen hparG hparN hord hinputPar hinputGrp hwf frames boxes
      dumpBoxes hdumpBoxes d hd hL := by
  have hnodup : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hfind : ∀ mb ∈ m.boxes, m.boxes.find? (fun b => b.id == mb.id) = some mb :=
    fun mb hmem => c8a_model_find_self m.boxes hnodup mb hmem
  have hmemG : ∀ g, g < groups.length → (groups.getD g default) ∈ m.boxes := by
    intro g hg
    have h1 : (groups.getD g default) ∈ m.boxes.filter (fun b => b.role == .group) := by
      rw [← hgroups]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
        Option.getD_some] using List.getElem_mem hg
    exact (List.mem_filter.mp h1).1
  have hmemN : ∀ ni, ni < nodes.length → (nodes.getD ni default) ∈ m.boxes := by
    intro ni hni
    have h1 : (nodes.getD ni default) ∈ m.boxes.filter (fun b => b.role != .group) := by
      rw [← hnodes]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni,
        Option.getD_some] using List.getElem_mem hni
    exact (List.mem_filter.mp h1).1
  have hgo_eq : ∀ s : String,
      d.ancestors s = archAncestors m.boxes d.boxes.length s := by
    intro s
    exact c8a_ancestors_eq m groups nodes frames boxes dumpBoxes hdumpBoxes hwf d hd
      (d.boxes.length) s
  unfold c8a_gapB_bridge
  refine ⟨?_, ?_⟩
  · intro ni hni g hg owner howner hmem
    have hni2 : ni < nodeInput.length := by rw [hnlen]; exact hni
    have hplen : input.parents.length = nodeInput.length := by
      rw [hinputPar, List.length_map]
    have hlt : ni < input.parents.length := by rw [hplen, hnlen]; exact hni
    have hvp : (virtualParents input).getD ni (-1) = (input.parents.getD ni (-1)) := by
      unfold virtualParents
      exact c8a_getD_append_left _ _ _ _ hlt
    have hpar_get : (input.parents.getD ni (-1)) =
        (nodeInput.getD ni default).parent := by
      have e1 : input.parents[ni]? =
          some ((nodeInput[ni]'hni2).parent) := by
        rw [hinputPar, List.getElem?_map, List.getElem?_eq_getElem hni2,
          Option.map_some]
      have e2 : input.parents.getD ni (-1) = (nodeInput[ni]'hni2).parent := by
        rw [List.getD_eq_getElem?_getD, e1, Option.getD_some]
      have e3 : (nodeInput.getD ni default).parent =
          (nodeInput[ni]'hni2).parent := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni2,
          Option.getD_some]
      rw [e2, e3]
    have hchain : chainOf input ni = groupChain groupInput groupInput.length owner ++
        [(⟨(ni : Int), (-1 : Int)⟩ : Elegant.Grid.Architecture.Unit)] := by
      unfold chainOf
      rw [hinputGrp, hvp, hpar_get, howner]
    have hmem' : (⟨-1, (g : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
        groupChain groupInput groupInput.length owner ++
          [(⟨(ni : Int), (-1 : Int)⟩ : Elegant.Grid.Architecture.Unit)] := by
      have hmemc := hmem
      rw [hchain] at hmemc
      exact hmemc
    have e1 : m.boxes.length = dumpBoxes.length :=
      (Elegant.Grid.mapM_ok_pairs _ _ hdumpBoxes).1
    have e2 : d.boxes.length = dumpBoxes.length := by rw [hd]
    have h1N : (nodes.getD ni default) ∈
        m.boxes.filter (fun b => b.role != .group) := by
      rw [← hnodes]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni,
        Option.getD_some] using List.getElem_mem hni
    have hfail : ((nodes.getD ni default).role == BoxRole.group) = false := by
      have h2 := (List.mem_filter.mp h1N).2
      cases hr : (nodes.getD ni default).role <;> simp_all
    have hLlen : groups.length < d.boxes.length := by
      have hlt_grp : (m.boxes.filter
          (fun b => b.role == BoxRole.group)).length < m.boxes.length :=
        c8a_groups_lt_of_node m.boxes (nodes.getD ni default)
          (hmemN ni hni) hfail
      have e3 : groups.length =
          (m.boxes.filter (fun b => b.role == BoxRole.group)).length := by
        rw [hgroups]
      omega
    have hdeep := (c8a_node_anc_mem groups nodes groupInput nodeInput
      (d.boxes.length) m.boxes hfind hmemG hmemN hglen hparG hparN hord hLlen
      ni hni owner howner g hmem').2
    rw [hgo_eq]
    exact hdeep
  · intro g hg x hx hne hmem
    have hG := c8a_group_anc_mem groups groupInput m.boxes hfind hmemG hglen
      hparG hord (groupInput.length) g hg x hmem
    rcases hG with rfl | ⟨halt, hdeep⟩
    · exact absurd rfl hne
    · have e1 : m.boxes.length = dumpBoxes.length :=
        (Elegant.Grid.mapM_ok_pairs _ _ hdumpBoxes).1
      have e2 : d.boxes.length = dumpBoxes.length := by rw [hd]
      have hle : groups.length ≤ m.boxes.length := by
        have hle0 := c8a_filter_length_le (fun b => b.role == BoxRole.group) m.boxes
        rwa [← hgroups] at hle0
      have hF : g + 1 ≤ d.boxes.length := by omega
      have hmem2 := hdeep (d.boxes.length) hF
      rw [hgo_eq]
      exact hmem2

/-- Gap (c): every ancestor-unrelated pair with a group on the left is disjoint.
Proved as `c8a_group_case` from gaps (a), (b), (d) and the step lemmas. -/
abbrev c8a_gapC_pair (m : Model) (scene : Scene) (capped : Bool)
    (_built : build m = .ok (scene, capped)) : Prop :=
  ∀ (gdb : Box), gdb ∈ scene.layoutDump.boxes → gdb.role = "group" →
    ∀ (bdb : Box), bdb ∈ scene.layoutDump.boxes → bdb.id ≠ gdb.id →
      gdb.id ∉ scene.layoutDump.ancestors bdb.id →
      bdb.id ∉ scene.layoutDump.ancestors gdb.id →
      Disjoint gdb.rect bdb.rect

theorem c8a_geometry_frames_proj (p : GeometryParams) (pitch : Pitch)
    (nodes : List Grid.Architecture.Node)
    (groups : List Elegant.Grid.Architecture.Group) (resolved : Resolved) :
    (Grid.Architecture.geometry p pitch nodes groups resolved).frames =
      resolved.frames := by
  rfl

/-- Gap (a) for a given successful build. -/
theorem c8a_gapA_of_build (m : Model) (scene : Scene) (capped : Bool)
    (hwf : WellFormed m)
    (built : build m = .ok (scene, capped)) :
    c8a_gapA_index m scene capped built := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, p, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := build_success m scene capped built
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hcanvas,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hscene, hcapped⟩
  have htitleLen : titles.length = groups.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ htitles).1.symm
  have hcapLen : captions.length = nodes.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hcaptions).1.symm
  have groupLen : groupInput.length = groups.length := by
    have hgl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have htit := (Elegant.Grid.mapM_ok_pairs _ _ htitles).1
    have hzl : (groups.zip titles).length =
        min groups.length titles.length := by simp only [List.length_zip]
    rw [htit] at hzl
    simp only [Nat.min_self] at hzl
    exact (hgl.symm.trans hzl).trans htit.symm
  have hnodeLen : nodeInput.length = nodes.length := by
    have hc := (Elegant.Grid.mapM_ok_pairs _ _ hcaptions).1
    have hn := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    simp only [List.length_zip] at hn
    omega
  have hinputPar : input.parents = nodeInput.map (fun n => n.parent) := by
    rw [hinput]
  have hinputGrp : input.groups = groupInput := by rw [hinput]
  have hparamsX : params.pitchX = pitch.x := by rw [hparams]
  have hparamsY : params.pitchY = pitch.y := by rw [hparams]
  have hplaced' : placed = placeHierarchy input params frameParams
      (LayoutConst.architecture_bfs_cap.get m.profile).toNat := by
    rw [hplaced, hprofile]


  have hgeomFrames : geometry.frames = resolved.frames := by
    rw [hgeometry]
    exact c8a_geometry_frames_proj p pitch nodeInput groupInput resolved
  have hgeomFramesLen : geometry.frames.length = resolved.frames.length := by
    rw [hgeomFrames]
  have hresLen : resolved.frames.length = input.groups.length := by
    rw [hresolved, hplaced]
    exact (resolveHierarchy_storage_lengths input params frameParams _).2
  have hgeomBoxesLen : geometry.boxes.length = nodes.length := by
    rw [hgeometry]
    simp only [Grid.Architecture.geometry, List.length_map, List.length_zipIdx]
    exact hnodeLen
  have hframesLen : frames.length = geometry.frames.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hframes).1.symm
  have hboxesLen : boxes.length = geometry.boxes.length :=
    (Elegant.Grid.mapM_ok_pairs _ _ hboxes).1.symm
  have htransF : ∀ i, i < frames.length →
      translateRect dx dy (geometry.frames.getD i default) =
        .ok (frames.getD i default) := by
    intro i hi
    have hi' : i < geometry.frames.length := by omega
    exact c8a_mapM_getD hframes i _ _ hi'
  have htransB : ∀ i, i < boxes.length →
      translateRect dx dy (geometry.boxes.getD i default) =
        .ok (boxes.getD i default) := by
    intro i hi
    have hi' : i < geometry.boxes.length := by omega
    exact c8a_mapM_getD hboxes i _ _ hi'
  have hboxEq : scene.layoutDump.boxes = dumpBoxes := by
    rw [hscene]
    rfl
  have hp_eq : p = archParams m := by
    rw [hp]
    simp only [archParams, archIconWidth, archIconHeight,
      GeometryParams.mk.injEq]
    rw [← hprofile, ← hcell]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | rfl
        | exact hiw
        | exact hih
        | exact hlh
        | exact hinset
        | exact hthickness
  have hpitch_eq : pitch = archPitch m nodeInput edgeLines := by
    rw [hpitch, hsizes]
    simp only [archPitch, archLineHeight]
    rw [← hp_eq, ← hprofile, ← hlh]
  have hpxBase : 0 < LayoutConst.architecture_pitch_x.get profile := by
    cases profile <;> decide
  have hpyBase : 0 < LayoutConst.architecture_pitch_y.get profile := by
    cases profile <;> decide

  have hgeometry' : geometry =
      Grid.Architecture.geometry (archParams m) pitch nodeInput groupInput resolved := by
    rw [hgeometry, hp_eq]

  have hpPitchX : p.pitchX = LayoutConst.architecture_pitch_x.get profile := by
    rw [hp]
  have hpPitchY : p.pitchY = LayoutConst.architecture_pitch_y.get profile := by
    rw [hp]
  have hpxpos : 0 < pitch.x := by
    rw [hpitch]
    have hx := c8a_pitch_x_lower p nodeInput sizes
    rw [hpPitchX] at hx
    have hbase : 0 < p.pitchX := by rw [hpPitchX]; exact hpxBase
    omega
  have hpypos : 0 < pitch.y := by
    rw [hpitch]
    have hy := c8a_pitch_y_lower p nodeInput sizes
    rw [hpPitchY] at hy
    have hbase : 0 < p.pitchY := by rw [hpPitchY]; exact hpyBase
    omega
  have hptop : 0 ≤ pitch.top := by
    rw [hpitch]
    exact c8a_pitch_top_nonneg p nodeInput sizes
  have hgut : 0 ≤ p.gutter := by
    rw [hp]
    show 0 ≤ (if cell then (1 : Int) else 0)
    split <;> omega
  have hpth : 0 ≤ p.thickness := by
    rw [hp]
    show 0 ≤ thickness
    rw [hthickness]
    cases profile <;> decide
  rw [hp_eq] at hgut hpth
  rw [← hp_eq, ← hpitch_eq] at hguard
  have hfits : ∀ n, n < nodeInput.length →
      nodeTileFits (archParams m) pitch (nodeInput.getD n default) = true := by
    intro n hn
    have hmem : nodeInput.getD n default ∈ nodeInput := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
        Option.getD_some] using List.getElem_mem hn
    by_cases hfit : nodeTileFits p pitch (nodeInput.getD n default) = true
    · rw [hp_eq] at hfit
      exact hfit
    · have hfalse : nodeTileFits p pitch (nodeInput.getD n default) = false :=
        Bool.eq_false_iff.mpr hfit
      have hany : nodeInput.any (fun n => !(nodeTileFits p pitch n)) = true :=
        List.any_eq_true.mpr ⟨nodeInput.getD n default, hmem, by rw [hfalse]; decide⟩
      exact absurd hany hguard
  have hnodeDec : ∀ n, n < nodeInput.length →
      ((nodeInput.getD n default).junction = true →
        (nodeInput.getD n default).icon.h =
          LayoutConst.architecture_junction_size.get profile) ∧
      ((nodeInput.getD n default).parent = -1 ∨
        ∃ i, i < groups.length ∧
          (nodeInput.getD n default).parent = Int.ofNat i) := by
    intro n hn
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    have hxs : n < (nodes.zip captions).length := by rw [hnl]; exact hn
    have hnn : n < nodes.length := by omega
    have hnc : n < captions.length := by omega
    have hdec := mapM_pointwise hnodeInput n hxs hn
    simp only [List.getElem_zip] at hdec
    cases hpv : parentIndex groups nodes[n].parent with
    | error err =>
        rw [hpv] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok parent =>
        rw [hpv] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hget : nodeInput.getD n default = nodeInput[n] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
            Option.getD_some]
        refine ⟨?_, ?_⟩
        · intro hj
          rw [hget, ← hdec] at hj ⊢
          dsimp only at hj ⊢
          simp only [hj, ↓reduceIte]
        · rw [hget, ← hdec]
          dsimp only
          exact c8a_parentIndex_ok_admitted hpv
  have hjsle : LayoutConst.architecture_junction_size.get profile ≤
      LayoutConst.architecture_pitch_y.get profile := by
    cases profile <;> decide
  have hpy' : p.pitchY ≤ pitch.y := by
    rw [hpitch]
    have hy := c8a_pitch_y_lower p nodeInput sizes
    rw [hpPitchY] at hy
    omega
  have hjq : ∀ n, n < nodeInput.length →
      (nodeInput.getD n default).junction = true →
        0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2 := by
    intro n hn hj
    have hjc := (hnodeDec n hn).1 hj
    rw [hprofile] at hjc
    have hdiff : 0 ≤ pitch.y - (nodeInput.getD n default).icon.h := by
      rw [hjc, ← hprofile]
      omega
    exact Int.fdiv_nonneg hdiff (by decide)
  have groupPar1 : ∀ g, g < groupInput.length → ∃ pv,
      parentIndex groups (groups.getD g default).parent = .ok pv ∧
        (groupInput.getD g default).parent = pv := by
    intro g hg
    have hgg : g < groups.length := by omega
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hgroupInput).1
    have hxs : g < (groups.zip titles).length := by omega
    have hdec := mapM_pointwise hgroupInput g hxs hg
    simp only [List.getElem_zip] at hdec
    cases hpv : parentIndex groups (groups[g]).parent with
    | error e =>
        rw [hpv] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok pv =>
        have hgd : groups[g] = groups.getD g default := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgg,
            Option.getD_some]
        rw [hpv] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hpar := congrArg (fun gr => gr.parent) hdec
        have hgd2 : groupInput[g] = groupInput.getD g default := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
            Option.getD_some]
        rw [hgd] at hpv
        have hpar2 : (groupInput.getD g default).parent = pv := by
          rw [← hgd2]
          exact hpar.symm
        exact ⟨pv, hpv, hpar2⟩
  have nodePar1 : ∀ ni, ni < nodeInput.length → ∃ pv,
      parentIndex groups (nodes.getD ni default).parent = .ok pv ∧
        (nodeInput.getD ni default).parent = pv := by
    intro ni hn
    have hnn : ni < nodes.length := by omega
    have hnl := (Elegant.Grid.mapM_ok_pairs _ _ hnodeInput).1
    have hxs : ni < (nodes.zip captions).length := by omega
    have hdec := mapM_pointwise hnodeInput ni hxs hn
    simp only [List.getElem_zip] at hdec
    cases hpv : parentIndex groups (nodes[ni]).parent with
    | error e =>
        rw [hpv] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        cases hdec
    | ok pv =>
        have hnd : nodes[ni] = nodes.getD ni default := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnn,
            Option.getD_some]
        rw [hpv] at hdec
        dsimp only [pure, Except.pure, Bind.bind, Except.bind] at hdec
        simp only [Except.ok.injEq] at hdec
        have hpar := congrArg (fun nr => nr.parent) hdec
        have hnd2 : nodeInput[ni] = nodeInput.getD ni default := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
            Option.getD_some]
        rw [hnd] at hpv
        have hpar2 : (nodeInput.getD ni default).parent = pv := by
          rw [← hnd2]
          exact hpar.symm
        exact ⟨pv, hpv, hpar2⟩
  have hparG : ∀ g, g < groups.length → ∀ s, (groups.getD g default).parent = s →
      (s = "" ∧ (groupInput.getD g default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (groupInput.getD g default).parent = Int.ofNat g') := by
    intro g hg s hs
    have hg' : g < groupInput.length := by omega
    obtain ⟨pv, hpv, hpeq⟩ := groupPar1 g hg'
    rw [hs] at hpv
    unfold parentIndex at hpv
    by_cases he : s.isEmpty = true
    · simp only [he, ↓reduceIte] at hpv
      have hpv' : pv = -1 := (Except.ok.inj hpv).symm
      refine Or.inl ⟨c8a_isEmpty_eq_empty s he, ?_⟩
      rw [hpeq]
      exact hpv'
    · have heF : s.isEmpty = false := by
        cases heq : s.isEmpty with
        | true => exact absurd heq he
        | false => rfl
      simp only [heF, ↓reduceIte] at hpv
      cases hfi : groups.findIdx? (fun b => b.id == s) with
      | none =>
          simp only [hfi] at hpv
          cases hpv
      | some i =>
          simp only [hfi] at hpv
          have hi : i < groups.length :=
            (List.findIdx?_eq_some_iff_findIdx_eq.mp hfi).1
          have hid : (groups.getD i default).id = s := by
            have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfi).2.1
            have hgd : groups[i] = groups.getD i default := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
                Option.getD_some]
            rw [← hgd]
            simpa using hbeq
          have hne : s ≠ "" := by
            intro hcon
            have htrue : ("").isEmpty = true := by
              show (("".utf8ByteSize) == 0) = true
              rw [String.utf8ByteSize_empty]
              rfl
            rw [hcon] at heF
            rw [htrue] at heF
            cases heF
          refine Or.inr ⟨i, hi, hne, hid.symm, ?_⟩
          have hpvi : pv = Int.ofNat i := by
            have h2 := Except.ok.inj hpv
            simp only [Int.ofNat_eq_natCast] at ⊢
            exact h2.symm
          rw [hpeq]
          exact hpvi
  have hparN : ∀ ni, ni < nodes.length → ∀ s, (nodes.getD ni default).parent = s →
      (s = "" ∧ (nodeInput.getD ni default).parent = -1) ∨
      (∃ g', g' < groups.length ∧ s ≠ "" ∧ s = (groups.getD g' default).id ∧
        (nodeInput.getD ni default).parent = Int.ofNat g') := by
    intro ni hn s hs
    have hn' : ni < nodeInput.length := by omega
    obtain ⟨pv, hpv, hpeq⟩ := nodePar1 ni hn'
    rw [hs] at hpv
    unfold parentIndex at hpv
    by_cases he : s.isEmpty = true
    · simp only [he, ↓reduceIte] at hpv
      have hpv' : pv = -1 := (Except.ok.inj hpv).symm
      refine Or.inl ⟨c8a_isEmpty_eq_empty s he, ?_⟩
      rw [hpeq]
      exact hpv'
    · have heF : s.isEmpty = false := by
        cases heq : s.isEmpty with
        | true => exact absurd heq he
        | false => rfl
      simp only [heF, ↓reduceIte] at hpv
      cases hfi : groups.findIdx? (fun b => b.id == s) with
      | none =>
          simp only [hfi] at hpv
          cases hpv
      | some i =>
          simp only [hfi] at hpv
          have hi : i < groups.length :=
            (List.findIdx?_eq_some_iff_findIdx_eq.mp hfi).1
          have hid : (groups.getD i default).id = s := by
            have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfi).2.1
            have hgd : groups[i] = groups.getD i default := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
                Option.getD_some]
            rw [← hgd]
            simpa using hbeq
          have hne : s ≠ "" := by
            intro hcon
            have htrue : ("").isEmpty = true := by
              show (("".utf8ByteSize) == 0) = true
              rw [String.utf8ByteSize_empty]
              rfl
            rw [hcon] at heF
            rw [htrue] at heF
            cases heF
          refine Or.inr ⟨i, hi, hne, hid.symm, ?_⟩
          have hpvi : pv = Int.ofNat i := by
            have h2 := Except.ok.inj hpv
            simp only [Int.ofNat_eq_natCast] at ⊢
            exact h2.symm
          rw [hpeq]
          exact hpvi
  have hfalse : groupInput.zipIdx.any
      (fun q => decide (q.1.parent ≥ Int.ofNat q.2)) = false := by
    cases hb : groupInput.zipIdx.any
        (fun q => decide (q.1.parent ≥ Int.ofNat q.2)) with
    | true => exact absurd hb hgroupOrder
    | false => rfl
  rw [List.any_eq_false] at hfalse
  have hord : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k := by
    intro k hk
    rw [hinputGrp] at hk ⊢
    have hmem : (groupInput.getD k default, k) ∈ groupInput.zipIdx := by
      have hk' : k < (groupInput.zipIdx (0 : Nat)).length := by
        simp only [List.length_zipIdx]
        exact hk
      have hget : (groupInput.zipIdx (0 : Nat))[k]'hk' =
          (groupInput.getD k default, k) := by
        rw [List.getElem_zipIdx]
        show (groupInput[k]'hk, 0 + k) = _
        simp only [Nat.zero_add]
        congr 1
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
            Option.getD_some]
      rw [← hget]
      exact List.getElem_mem hk'
    have hnp := hfalse _ hmem
    have hff : decide ((groupInput.getD k default).parent ≥ Int.ofNat k) =
        false := by
      cases hb2 : decide
          ((groupInput.getD k default).parent ≥ Int.ofNat k) with
      | true => exact absurd hb2 hnp
      | false => rfl
    have hcon : ¬ (groupInput.getD k default).parent ≥ Int.ofNat k :=
      of_decide_eq_false hff
    omega
  have hgp : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ gparent, gparent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat gparent := by
    intro g hg
    rw [hinputGrp] at hg ⊢
    obtain ⟨pv, hpv, hpeq⟩ := groupPar1 g hg
    rcases c8a_parentIndex_ok_admitted hpv with hneg | ⟨i, hi, heq⟩
    · exact Or.inl (by rw [hpeq]; exact hneg)
    · refine Or.inr ⟨i, ?_, ?_⟩
      · rw [groupLen]
        exact hi
      · rw [hpeq, heq]
  have hpar : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
    intro parent hmem
    rw [hinputPar] at hmem
    obtain ⟨a, hamem, hfa⟩ := List.mem_map.mp hmem
    obtain ⟨ni, hni, heq⟩ := List.mem_iff_getElem.mp hamem
    obtain ⟨pv, hpv, hpeq⟩ := nodePar1 ni hni
    have hfa' : a.parent = parent := hfa
    have hpar_eq : parent = pv := by
      have h1 : nodeInput[ni]'hni = a := heq
      rw [← h1] at hfa'
      have h2 : nodeInput[ni]'hni = nodeInput.getD ni default := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni,
          Option.getD_some]
      rw [h2] at hfa'
      exact hfa'.symm.trans hpeq
    rcases c8a_parentIndex_ok_admitted hpv with hneg | ⟨i, hi, heq2⟩
    · exact Or.inl (by rw [hpar_eq]; exact hneg)
    · refine Or.inr ⟨i, ?_, ?_⟩
      · rw [hinputGrp, groupLen]
        exact hi
      · rw [hpar_eq, heq2]
  have hparamsPosX : 0 < params.pitchX := by rw [hparamsX]; exact hpxpos
  have hparamsPosY : 0 < params.pitchY := by rw [hparamsY]; exact hpypos
  have hpad : 0 ≤ frameParams.padding := by
    have hfp : frameParams =
        (⟨padding, inset, lh, p.badge⟩ : FrameParams) := by rw [hframeParams]
    have hpad0 : 0 ≤ padding :=
      c8a_decoded_frame_padding_nonnegative m profile cell padding hpadding
    rw [hfp] at ⊢
    show 0 ≤ padding
    exact hpad0
  have hline : 0 ≤ frameParams.lineHeight := by
    have hfp : frameParams =
        (⟨padding, inset, lh, p.badge⟩ : FrameParams) := by rw [hframeParams]
    rw [hfp]
    show 0 ≤ lh
    rw [hlh]
    change 0 ≤ LayoutConst.line_h.get profile
    cases profile <;> decide
  have hcorr : ∀ db ∈ dumpBoxes,
      (∃ gi, gi < groups.length ∧ (groups.getD gi default).id = db.id ∧
        (groups.getD gi default).parent = db.parent ∧
        db.rect = frames.getD gi default ∧ gi < input.groups.length ∧
        (∃ pv, parentIndex groups (groups.getD gi default).parent = .ok pv ∧
          (groupInput.getD gi default).parent = pv) ∧
        translateRect dx dy (geometry.frames.getD gi default) =
          .ok (frames.getD gi default) ∧
        db.role = (groups.getD gi default).role.id) ∨
      (∃ ni, ni < nodes.length ∧ (nodes.getD ni default).id = db.id ∧
        (nodes.getD ni default).parent = db.parent ∧
        db.rect = boxes.getD ni default ∧ ni < input.parents.length ∧
        (∃ pv, parentIndex groups (nodes.getD ni default).parent = .ok pv ∧
          (nodeInput.getD ni default).parent = pv) ∧
        translateRect dx dy (geometry.boxes.getD ni default) =
          .ok (boxes.getD ni default) ∧
        db.role = (nodes.getD ni default).role.id) := by
    intro db hdb
    obtain ⟨mb, hmb, hmap⟩ := mapM_output_origin hdumpBoxes hdb
    have hnodupMap : (m.boxes.map (fun b => b.id)).Nodup :=
      Model.boxIds_nodup hwf
    rcases c8a_dump_box_cases groups nodes frames boxes mb db hmap with
      ⟨gi, _, hfind, hgeq⟩ | ⟨ni, _, hfind, hgeq⟩
    · subst hgeq
      have hgi : gi < groups.length :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
      have hgid : (groups.getD gi default).id = mb.id := by
        have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
        have hgd : groups[gi] = groups.getD gi default := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgi,
            Option.getD_some]
        rw [← hgd]
        simpa using hbeq
      have hmemG : groups.getD gi default ∈ m.boxes := by
        have hmem : groups.getD gi default ∈ m.boxes.filter (fun b => b.role == .group) := by
          rw [← hgroups]
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgi,
            Option.getD_some] using List.getElem_mem hgi
        exact (List.mem_filter.mp hmem).1
      have hf1 : m.boxes.find? (fun b => b.id == mb.id) = some mb :=
        c8a_model_find_self m.boxes hnodupMap mb hmb
      have hf2 : m.boxes.find? (fun b => b.id == mb.id) =
          some (groups.getD gi default) := by
        have hbase := c8a_model_find_self m.boxes hnodupMap
          (groups.getD gi default) hmemG
        rw [hgid] at hbase
        exact hbase
      have hmbEq : mb = groups.getD gi default := Option.some.inj (hf1.symm.trans hf2)
      have hgiIn : gi < input.groups.length := by
        rw [hinputGrp, groupLen]
        exact hgi
      have hgiLen : gi < groupInput.length := by
        rw [groupLen]
        exact hgi
      obtain ⟨pv, hpv, hpeq⟩ := groupPar1 gi hgiLen
      have htrans : translateRect dx dy (geometry.frames.getD gi default) =
          .ok (frames.getD gi default) := by
        have hgiF : gi < frames.length := by
          rw [hframesLen, hgeomFramesLen, hresLen]
          exact hgiIn
        exact htransF gi hgiF
      refine Or.inl ⟨gi, hgi, ?_, ?_, rfl, hgiIn, ⟨pv, hpv, hpeq⟩, htrans, ?_⟩
      · rw [hmbEq]
      · rw [hmbEq]
      · rw [hmbEq]
    · subst hgeq
      have hni : ni < nodes.length :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
      have hnid : (nodes.getD ni default).id = mb.id := by
        have hbeq := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
        have hnd : nodes[ni] = nodes.getD ni default := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni,
            Option.getD_some]
        rw [← hnd]
        simpa using hbeq
      have hmemN : nodes.getD ni default ∈ m.boxes := by
        have hmem : nodes.getD ni default ∈ m.boxes.filter (fun b => b.role != .group) := by
          rw [← hnodes]
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni,
            Option.getD_some] using List.getElem_mem hni
        exact (List.mem_filter.mp hmem).1
      have hf1 : m.boxes.find? (fun b => b.id == mb.id) = some mb :=
        c8a_model_find_self m.boxes hnodupMap mb hmb
      have hf2 : m.boxes.find? (fun b => b.id == mb.id) =
          some (nodes.getD ni default) := by
        have hbase := c8a_model_find_self m.boxes hnodupMap
          (nodes.getD ni default) hmemN
        rw [hnid] at hbase
        exact hbase
      have hmbEq : mb = nodes.getD ni default := Option.some.inj (hf1.symm.trans hf2)
      have hniIn : ni < input.parents.length := by
        rw [hinputPar, List.length_map]
        have : ni < nodeInput.length := by omega
        exact this
      have hniLen : ni < nodeInput.length := by omega
      obtain ⟨pv, hpv, hpeq⟩ := nodePar1 ni hniLen
      have htrans : translateRect dx dy (geometry.boxes.getD ni default) =
          .ok (boxes.getD ni default) := by
        have hniF : ni < boxes.length := by omega
        exact htransB ni hniF
      refine Or.inr ⟨ni, hni, ?_, ?_, rfl, hniIn, ⟨pv, hpv, hpeq⟩, htrans, ?_⟩
      · rw [hmbEq]
      · rw [hmbEq]
      · rw [hmbEq]
  refine ⟨groups, nodes, groupInput, nodeInput, input, pitch, params,
    frameParams, placed, resolved, geometry, dx, dy, frames, boxes, dumpBoxes,
    hgroups, hnodes, groupLen, hnodeLen, hinputPar, hinputGrp, hparamsX,
    hparamsY, hplaced', hresolved, hgeometry', hgeomFrames, hframesLen,
    hboxesLen, htransF, htransB, hboxEq, hcorr, hparG, hparN, hord, hgp, hpar,
    hparamsPosX, hparamsPosY, hpad, hline, hfits, hjq, hptop, hgut, hpth, hdumpBoxes⟩

/-- Gap (d): a tile-fitting node box sits inside its pitch tile. Proved as
`c8a_node_rect_in_tile` by copying the C2 `node_box_bounds` proof. -/
abbrev c8a_gapD_tile (p : Grid.Architecture.GeometryParams) (pitch : Grid.Architecture.Pitch)
    (nodeInput : List Grid.Architecture.Node)
    (groupInput : List Elegant.Grid.Architecture.Group) (resolved : Resolved)
    (n : Nat) (_hn : n < nodeInput.length)
    (_pxpos : 0 < pitch.x) (_pypos : 0 < pitch.y) (_g0 : 0 ≤ p.gutter)
    (_pth : 0 ≤ p.thickness)
    (_fits : nodeTileFits p pitch (nodeInput.getD n default) = true)
    (_jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2)
    (_ptop : 0 ≤ pitch.top) : Prop :=
  ((⟨0, 0, pitch.x, pitch.y⟩ : Span).shift
    ((resolved.nodes.getD n default).x * pitch.x)
    ((resolved.nodes.getD n default).y * pitch.y)).contains
    ((Grid.Architecture.geometry p pitch nodeInput groupInput resolved).boxes.getD n default)

/-- Gap (a): the executed-build index bundle, from a successful layout. -/
theorem c8a_dump_box_index (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m)
    (h : layout m = .ok result) :
    ∃ (scene : Scene) (capped : Bool) (built : build m = .ok (scene, capped)),
      c8a_gapA_index m scene capped built := by
  obtain ⟨scene, capped, built, _dump⟩ := public_layout_dump m result h
  exact ⟨scene, capped, built, c8a_gapA_of_build m scene capped hwf built⟩

/-- Copy of the C2 `node_box_bounds` proof under a new name: a tile-fitting node's
dump rectangle satisfies tile-relative `BoxBounds`. -/
theorem c8a_node_box_bounds (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch) (nodeInput : List Grid.Architecture.Node)
    (groupInput : List Grid.Architecture.Group) (resolved : Grid.Architecture.Resolved)
    (n : Nat) (hn : n < nodeInput.length)
    (pxpos : 0 < pitch.x) (pypos : 0 < pitch.y) (g0 : 0 ≤ p.gutter)
    (_pth : 0 ≤ p.thickness)
    (fits : nodeTileFits p pitch (nodeInput.getD n default) = true)
    (jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2)
    (ptop : 0 ≤ pitch.top) :
    RouteClearance.BoxBounds pitch.x pitch.y p.gutter
      (RouteClearance.spanRect
        ((Grid.Architecture.geometry p pitch nodeInput groupInput resolved).boxes.getD n default))
      (resolved.nodes.getD n default).x (resolved.nodes.getD n default).y := by
  have icon := Grid.Architecture.geometry_icon_at p pitch nodeInput groupInput resolved n hn
  have hbox := Grid.Architecture.geometry_box_at p pitch nodeInput groupInput resolved n hn
  rw [icon] at hbox
  simp only [Grid.Architecture.sized] at hbox
  unfold nodeTileFits at fits
  have hright : (resolved.nodes.getD n default).x * pitch.x + pitch.x =
      ((resolved.nodes.getD n default).x + 1) * pitch.x := by
    rw [Int.add_mul, Int.one_mul]
  have hrightY : (resolved.nodes.getD n default).y * pitch.y + pitch.y =
      ((resolved.nodes.getD n default).y + 1) * pitch.y := by
    rw [Int.add_mul, Int.one_mul]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
  obtain ⟨fits1, fits2⟩ := fits
  have hdecomp := Int.mul_fdiv_add_fmod (pitch.x - (nodeInput.getD n default).icon.w) 2
  have hmodnn := Int.fmod_nonneg_of_pos (pitch.x - (nodeInput.getD n default).icon.w)
    (show (0 : Int) < 2 by decide)
  have hmodlt := Int.fmod_lt_of_pos (pitch.x - (nodeInput.getD n default).icon.w)
    (show (0 : Int) < 2 by decide)
  rw [hbox]
  simp only [RouteClearance.spanRect]
  by_cases hj : (nodeInput.getD n default).junction = true
  · have hjq := jq hj
    simp only [hj, ↓reduceIte] at fits2 ⊢
    refine ⟨pxpos, pypos, g0, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · simp only [hj, Bool.false_eq_true, ↓reduceIte] at fits2 ⊢
    refine ⟨pxpos, pypos, g0, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

/-- `BoxBounds` in a pitch tile implies `Span.contains` of the tile span. -/
theorem c8a_boxBounds_contains (px py g : Int) (s : Span) (rect : Rect)
    (cx cy : Int)
    (hrect : rect = RouteClearance.spanRect s)
    (hb : RouteClearance.BoxBounds px py g rect cx cy) :
    ((⟨0, 0, px, py⟩ : Span).shift (cx * px) (cy * py)).contains s := by
  subst hrect
  obtain ⟨_, _, _, x0ge, x1le, y0ge, y1le⟩ := hb
  have ex : (RouteClearance.spanRect s).x = s.x0 := rfl
  have ey : (RouteClearance.spanRect s).y = s.y0 := rfl
  have ew : (RouteClearance.spanRect s).w = s.x1 - s.x0 := rfl
  have eh : (RouteClearance.spanRect s).h = s.y1 - s.y0 := rfl
  simp only [ex, ey, ew, eh] at x0ge x1le y0ge y1le
  have hfacX : (cx + 1) * px = cx * px + px := by rw [Int.add_mul, Int.one_mul]
  have hfacY : (cy + 1) * py = cy * py + py := by rw [Int.add_mul, Int.one_mul]
  rw [hfacX] at x1le
  rw [hfacY] at y1le
  simp only [Span.contains]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 0 + cx * px ≤ s.x0
    omega
  · show s.x1 ≤ px + cx * px
    omega
  · show 0 + cy * py ≤ s.y0
    omega
  · show s.y1 ≤ py + cy * py
    omega

/-- Gap (d): a tile-fitting node box sits inside its pitch tile. -/
theorem c8a_node_rect_in_tile (p : Grid.Architecture.GeometryParams)
    (pitch : Grid.Architecture.Pitch)
    (nodeInput : List Grid.Architecture.Node)
    (groupInput : List Elegant.Grid.Architecture.Group)
    (resolved : Resolved)
    (n : Nat) (hn : n < nodeInput.length)
    (pxpos : 0 < pitch.x) (pypos : 0 < pitch.y) (g0 : 0 ≤ p.gutter)
    (pth : 0 ≤ p.thickness)
    (fits : nodeTileFits p pitch (nodeInput.getD n default) = true)
    (jq : (nodeInput.getD n default).junction = true →
      0 ≤ Int.fdiv (pitch.y - (nodeInput.getD n default).icon.h) 2)
    (ptop : 0 ≤ pitch.top) :
    c8a_gapD_tile p pitch nodeInput groupInput resolved n hn pxpos pypos g0 pth
      fits jq ptop := by
  unfold c8a_gapD_tile
  have hb := c8a_node_box_bounds p pitch nodeInput groupInput resolved n hn
    pxpos pypos g0 pth fits jq ptop
  exact c8a_boxBounds_contains _ _ _ _ _ _ _ rfl hb


/-- Every member of a group chain rooted at `ofNat g` has nonnegative group. -/
theorem c8a_groupChain_nonneg (groups : List Elegant.Grid.Architecture.Group)
    (k : Nat) (g : Nat) (u : Elegant.Grid.Architecture.Unit)
    (hmem : u ∈ groupChain groups k (Int.ofNat g)) : 0 ≤ u.group := by
  induction k generalizing g with
  | zero => simp only [groupChain, List.not_mem_nil] at hmem
  | succ k ih =>
    have hget : (groups.getD (Int.ofNat g).toNat default) =
        groups.getD g default := by
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
    have hunfold : groupChain groups (k + 1) (Int.ofNat g) =
        groupChain groups k (groups.getD g default).parent ++
          [⟨-1, Int.ofNat g⟩] := by
      simp only [groupChain]
      split
      · rename_i hcond
        exact absurd hcond (by simp)
      · rw [hget]
    rw [hunfold] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · by_cases hneg : (groups.getD g default).parent < 0
      · have hempty : groupChain groups k
            ((groups.getD g default).parent) = [] :=
          c8a_groupChain_neg _ _ _ hneg
        rw [hempty] at hleft
        simp only [List.not_mem_nil] at hleft
      · have hnn : 0 ≤ (groups.getD g default).parent := by omega
        have heq : (groups.getD g default).parent =
            Int.ofNat (groups.getD g default).parent.toNat :=
          (Int.toNat_of_nonneg hnn).symm
        rw [heq] at hleft
        exact ih _ hleft
    · have heq : u = (⟨-1, Int.ofNat g⟩ : Elegant.Grid.Architecture.Unit) :=
        List.mem_singleton.mp hright
      rw [heq]
      show (0 : Int) ≤ (g : Int)
      omega

/-- Residual supply for steps 1-3 projected from the executed-build index bundle. -/
theorem c8a_residual_hierarchy_of_gapA (m : Model) (scene : Scene) (capped : Bool)
    (built : build m = .ok (scene, capped))
    (hA : c8a_gapA_index m scene capped built) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      c8a_residual_hierarchy input p fp := by
  obtain ⟨_, _, _, _, input, _, params, frameParams, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hord, hgp, hpar,
      hparamsPosX, hparamsPosY, hpad, hline, _, _, _, _, _, _⟩ := hA
  exact ⟨input, params, frameParams, hord, hgp, hpar,
    hparamsPosX, hparamsPosY, hpad, hline⟩

/-- Residual supply for the group case of step 3, discharged from step 3 itself. -/
theorem c8a_residual_groupSuffix_of_step3 (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (hres : c8a_residual_hierarchy input p fp) :
    c8a_residual_groupSuffix input p fp fuel := by
  intro s g hs hg shared rest hsuf
  have hmem : (⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
      groupChain input.groups input.groups.length (Int.ofNat g) := by
    rw [hsuf]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hcon := c8a_step3_group_contain input p fp fuel hres
    input.groups.length g hg s hs hmem
  have hspan : resolvedUnitSpan p
      (resolveHierarchy input p (placeHierarchy input p fp fuel))
      (⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit) =
      (resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD s
        default := by
    have hnn : (0 : Int) ≤
        ((⟨-1, (s : Int)⟩ : Elegant.Grid.Architecture.Unit).group) := by
      show (0 : Int) ≤ (s : Int)
      omega
    rw [c8a_resolvedUnitSpan_group _ _ _ hnn]
    congr 1
  rw [hspan]
  exact hcon

/-- A group-indexed box is a group-role model box. -/
theorem c8a_mem_groups_role (groups mboxes : List ModelBox)
    (hgroups : groups = mboxes.filter (fun b => b.role == .group))
    (g : Nat) (hg : g < groups.length) :
    (groups.getD g default).role = BoxRole.group := by
  have hmem : (groups.getD g default) ∈ groups := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
      Option.getD_some] using List.getElem_mem hg
  have hmem' : (groups.getD g default) ∈
      mboxes.filter (fun b => b.role == .group) := by
    rw [← hgroups]
    exact hmem
  have hbeq := (List.mem_filter.mp hmem').2
  cases hr : (groups.getD g default).role <;> simp_all

/-- A node-indexed box is a node-role model box. -/
theorem c8a_mem_nodes_role (nodes mboxes : List ModelBox)
    (hnodes : nodes = mboxes.filter (fun b => b.role != .group))
    (ni : Nat) (hni : ni < nodes.length) :
    (nodes.getD ni default).role = BoxRole.node := by
  have hmem : (nodes.getD ni default) ∈ nodes := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hni,
      Option.getD_some] using List.getElem_mem hni
  have hmem' : (nodes.getD ni default) ∈
      mboxes.filter (fun b => b.role != .group) := by
    rw [← hnodes]
    exact hmem
  have hne' := (List.mem_filter.mp hmem').2
  cases hr : (nodes.getD ni default).role <;> simp_all

/-- Gap (c), node side: a group box is disjoint from an ancestor-unrelated node box. -/
theorem c8a_group_case_node (m : Model) (scene : Scene) (capped : Bool)
    (built : build m = .ok (scene, capped)) (hwf : WellFormed m)
    (hA : c8a_gapA_index m scene capped built)
    (gdb bdb : Box)
    (hgdb : gdb ∈ scene.layoutDump.boxes) (hrole : gdb.role = "group")
    (hbdb : bdb ∈ scene.layoutDump.boxes) (hbdbN : bdb.role = "node")
    (h1 : gdb.id ∉ scene.layoutDump.ancestors bdb.id) :
    Disjoint gdb.rect bdb.rect := by
  obtain ⟨groups, nodes, groupInput, nodeInput, input, pitch, params, frameParams,
    placed, resolved, geometry, dx, dy, frames, boxes, dumpBoxes,
    hgroups, hnodes, groupLen, hnodeLen, hinputPar, hinputGrp, hparamsX,
    hparamsY, hplaced', hresolved', hgeometry', hgeomFrames, hframesLen,
    hboxesLen, htransF, htransB, hboxEq, hcorr, hparG, hparN, hord, hgp, hpar,
    hparamsPosX, hparamsPosY, hpad, hline, hfits, hjq, hptop, hgut, hpth,
    hdumpBoxes⟩ := hA
  have hres : c8a_residual_hierarchy input params frameParams :=
    ⟨hord, hgp, hpar, hparamsPosX, hparamsPosY, hpad, hline⟩
  have hord' : ∀ k, k < groupInput.length →
      (groupInput.getD k default).parent < Int.ofNat k := by
    rw [← hinputGrp]
    exact hord
  have hB := c8a_prefix_not_ancestor m groups nodes groupInput nodeInput input
    (groups.length + 1) hgroups hnodes groupLen hnodeLen hparG hparN hord' hinputPar
    hinputGrp hwf frames boxes dumpBoxes hdumpBoxes scene.layoutDump hboxEq
    (Nat.lt_succ_self _)
  obtain ⟨hBnode, hBgroup⟩ := hB
  have hresS := c8a_residual_groupSuffix_of_step3 input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
  have hgdb' : gdb ∈ dumpBoxes := by rw [← hboxEq]; exact hgdb
  have hbdb' : bdb ∈ dumpBoxes := by rw [← hboxEq]; exact hbdb
  rcases hcorr gdb hgdb' with hG | hN
  · obtain ⟨gi, hgi, hidG, _, hrectG, hgiIn, _, htransG, _⟩ := hG
    rcases hcorr bdb hbdb' with hJ | hNj
    · obtain ⟨gj, hgj, _, _, _, _, _, _, hroleJ⟩ := hJ
      exfalso
      have hJrole := c8a_mem_groups_role groups m.boxes hgroups gj hgj
      rw [hJrole] at hroleJ
      have hgid : BoxRole.group.id = "group" := rfl
      rw [hgid, hbdbN] at hroleJ
      exact absurd hroleJ (by decide)
    · obtain ⟨nj, hnj, hidN, _, hrectN, hnjIn, _, htransN, _⟩ := hNj
      have hgiL : gi < groupInput.length := by rw [groupLen]; exact hgi
      have hnj_node : nj < nodeInput.length := by rw [hnodeLen]; exact hnj
      have hnj_parents : nj < input.parents.length := by
        rw [hinputPar, List.length_map]; exact hnj_node
      have hge : input.parents.length ≤ (virtualParents input).length := by
        unfold virtualParents
        simp only [List.length_append]
        omega
      have hnj_vp : nj < (virtualParents input).length := by omega
      have hnm : (⟨-1, (gi : Int)⟩ : Elegant.Grid.Architecture.Unit) ∉
          chainOf input nj := by
        intro hmem
        have howner : (nodeInput.getD nj default).parent =
            (nodeInput.getD nj default).parent := rfl
        have hmemB := hBnode nj hnj gi hgi _ howner hmem
        rw [hidG, hidN] at hmemB
        exact h1 hmemB
      obtain ⟨owner, first, second, hdiv⟩ :
          ∃ owner first second, divergent (chainOf input nj)
            (groupChain input.groups input.groups.length (Int.ofNat gi)) (-1) =
            some (owner, first, second) := by
        cases hdiv : divergent (chainOf input nj)
            (groupChain input.groups input.groups.length (Int.ofNat gi)) (-1) with
        | some v =>
          obtain ⟨o, f, s⟩ := v
          exact ⟨o, f, s, rfl⟩
        | none =>
          exfalso
          have hnn := c8a_divergent_none _ _ _ hdiv
          rcases hnn with ⟨rest, hr⟩ | ⟨rest, hr⟩
          · have hterm_left : (⟨(nj : Int), -1⟩ :
                Elegant.Grid.Architecture.Unit) ∈ chainOf input nj := by
              unfold chainOf
              exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
            have hterm : (⟨(nj : Int), -1⟩ : Elegant.Grid.Architecture.Unit) ∈
                groupChain input.groups input.groups.length (Int.ofNat gi) := by
              rw [hr]
              exact List.mem_append.mpr (Or.inl hterm_left)
            have hcon := c8a_groupChain_mem_node _ _ _ _ hterm
            have hcon' : (nj : Int) = -1 := hcon
            omega
          · have hs0 := c8a_groupChain_self_mem input.groups groupInput.length
              gi hgiL
            have hself : (⟨-1, (gi : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
                groupChain input.groups input.groups.length (Int.ofNat gi) := by
              rw [← hinputGrp] at hs0
              exact hs0
            have hmem2 : (⟨-1, (gi : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
                chainOf input nj := by
              rw [hr]
              exact List.mem_append.mpr (Or.inl hself)
            exact hnm hmem2
      have hleftPath : ParentPath input (-1) (chainOf input nj) (-1) :=
        chainOf_parent_path input hord hgp hpar nj hnj_vp
      have hrightPath : ParentPath input (-1)
          (groupChain input.groups input.groups.length (Int.ofNat gi))
          (Int.ofNat gi) :=
        groupChain_parent_path input hord hgp _ _ (Or.inr ⟨gi, hgiIn, hgiIn, rfl⟩)
      have hsib := c8a_level_siblings_executed input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
        (chainOf input nj)
        (groupChain input.groups input.groups.length (Int.ofNat gi))
        (-1) (Int.ofNat gi) hleftPath hrightPath owner first second hdiv
      have hsep0 := c8a_step2_separation input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
        owner first second hsib
      rw [← hplaced', ← hresolved'] at hsep0
      have hdiv' := divergent_common_prefix (chainOf input nj)
        (groupChain input.groups input.groups.length (Int.ofNat gi))
        (-1) owner first second hdiv
      obtain ⟨_, shared, lr, rr, hleq, hreq, _⟩ := hdiv'
      have hfirst : first ∈ chainOf input nj := by
        rw [hleq]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have hsecond : second ∈
          groupChain input.groups input.groups.length (Int.ofNat gi) := by
        rw [hreq]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have htile_mem := c8a_step3_node_contain input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
        nj hnj_vp first hfirst
      rw [← hplaced', ← hresolved'] at htile_mem
      have htile_eq : resolvedUnitSpan params resolved
          (⟨(nj : Int), -1⟩ : Elegant.Grid.Architecture.Unit) =
          ((⟨0, 0, pitch.x, pitch.y⟩ : Span).shift
            ((resolved.nodes.getD nj default).x * pitch.x)
            ((resolved.nodes.getD nj default).y * pitch.y)) := by
        have hneg : ((⟨(nj : Int), -1⟩ : Elegant.Grid.Architecture.Unit).group) < 0 := by
          show (-1 : Int) < 0
          decide
        unfold resolvedUnitSpan
        simp only [hneg, ↓reduceIte]
        rw [← hparamsX, ← hparamsY]
        simp only [Int.toNat_natCast]
      have hparamsPosX' : 0 < pitch.x := by rw [← hparamsX]; exact hparamsPosX
      have hparamsPosY' : 0 < pitch.y := by rw [← hparamsY]; exact hparamsPosY
      have hD := c8a_node_rect_in_tile (archParams m) pitch nodeInput groupInput
        resolved nj hnj_node hparamsPosX' hparamsPosY' hgut hpth
        (hfits nj hnj_node) (hjq nj hnj_node) hptop
      unfold c8a_gapD_tile at hD
      rw [← hgeometry'] at hD
      have h2' : (resolvedUnitSpan params resolved
          (⟨(nj : Int), -1⟩ : Elegant.Grid.Architecture.Unit)).contains
          (geometry.boxes.getD nj default) := by
        rw [htile_eq]
        exact hD
      have hA_side : (resolvedUnitSpan params resolved first).contains
          (geometry.boxes.getD nj default) :=
        c8a_contains_trans _ _ _ htile_mem h2'
      have hnn2 : 0 ≤ second.group :=
        c8a_groupChain_nonneg _ _ _ _ hsecond
      have hsecond_eq : second =
          (⟨-1, ((second.group.toNat : Nat) : Int)⟩ : Elegant.Grid.Architecture.Unit) := by
        cases second with
        | mk n g =>
          have hn2 : n = (-1 : Int) := c8a_groupChain_mem_node _ _ _ _ hsecond
          have hg2 : ((g.toNat : Nat) : Int) = g :=
            Int.toNat_of_nonneg (c8a_groupChain_nonneg _ _ _ _ hsecond)
          subst hn2
          rw [hg2]
      have hrightEq2 := hreq
      rw [hsecond_eq] at hrightEq2
      have hmemS : second.group.toNat < input.groups.length :=
        c8a_groupChain_mem_bound input.groups hord gi hgiIn _ second hsecond
      have hsuf : groupChain input.groups input.groups.length (Int.ofNat gi) =
          shared ++ (⟨-1, ((second.group.toNat : Nat) : Int)⟩ :
            Elegant.Grid.Architecture.Unit) :: rr :=
        hrightEq2
      have hframe0 := c8a_step3_group_frame_of_suffix input params frameParams
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat
        hresS (second.group.toNat) gi hmemS hgiIn shared rr hsuf
      rw [← hplaced', ← hresolved'] at hframe0
      rw [← hsecond_eq] at hframe0
      rw [← hgeomFrames] at hframe0
      have hdis : Disjoint (boxes.getD nj default) (frames.getD gi default) :=
        c8a_step4_disjoint _ _ _ _ _ _ _ _ hsep0 hA_side hframe0 htransN htransG
      rw [hrectG, hrectN]
      exact (Disjoint.comm _ _).mp hdis
  · obtain ⟨ni, hni, hidN, _, _, _, _, _, hroleN⟩ := hN
    exfalso
    have hNrole := c8a_mem_nodes_role nodes m.boxes hnodes _ hni
    have heq : (nodes.getD ni default).role.id = "group" := by
      rw [← hroleN]
      exact hrole
    rw [hNrole] at heq
    exact absurd heq (by decide)

/-- Gap (c), group side: a group box is disjoint from an ancestor-unrelated group box. -/
theorem c8a_group_case_group (m : Model) (scene : Scene) (capped : Bool)
    (built : build m = .ok (scene, capped)) (hwf : WellFormed m)
    (hA : c8a_gapA_index m scene capped built)
    (gdb bdb : Box)
    (hgdb : gdb ∈ scene.layoutDump.boxes) (hrole : gdb.role = "group")
    (hbdb : bdb ∈ scene.layoutDump.boxes) (hbdbG : bdb.role = "group")
    (hne : bdb.id ≠ gdb.id)
    (h1 : gdb.id ∉ scene.layoutDump.ancestors bdb.id)
    (h2 : bdb.id ∉ scene.layoutDump.ancestors gdb.id) :
    Disjoint gdb.rect bdb.rect := by
  obtain ⟨groups, nodes, groupInput, nodeInput, input, pitch, params, frameParams,
    placed, resolved, geometry, dx, dy, frames, boxes, dumpBoxes,
    hgroups, hnodes, groupLen, hnodeLen, hinputPar, hinputGrp, hparamsX,
    hparamsY, hplaced', hresolved', hgeometry', hgeomFrames, hframesLen,
    hboxesLen, htransF, htransB, hboxEq, hcorr, hparG, hparN, hord, hgp, hpar,
    hparamsPosX, hparamsPosY, hpad, hline, hfits, hjq, hptop, hgut, hpth,
    hdumpBoxes⟩ := hA
  have hres : c8a_residual_hierarchy input params frameParams :=
    ⟨hord, hgp, hpar, hparamsPosX, hparamsPosY, hpad, hline⟩
  have hord' : ∀ k, k < groupInput.length →
      (groupInput.getD k default).parent < Int.ofNat k := by
    rw [← hinputGrp]
    exact hord
  have hB := c8a_prefix_not_ancestor m groups nodes groupInput nodeInput input
    (groups.length + 1) hgroups hnodes groupLen hnodeLen hparG hparN hord' hinputPar
    hinputGrp hwf frames boxes dumpBoxes hdumpBoxes scene.layoutDump hboxEq
    (Nat.lt_succ_self _)
  obtain ⟨hBnode, hBgroup⟩ := hB
  have hresS := c8a_residual_groupSuffix_of_step3 input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
  have hgdb' : gdb ∈ dumpBoxes := by rw [← hboxEq]; exact hgdb
  have hbdb' : bdb ∈ dumpBoxes := by rw [← hboxEq]; exact hbdb
  rcases hcorr gdb hgdb' with hG | hN
  · obtain ⟨gi, hgi, hidG, _, hrectG, hgiIn, _, htransG, _⟩ := hG
    rcases hcorr bdb hbdb' with hJ | hNj
    · obtain ⟨gj, hgj, hidJ, _, hrectJ, hgjIn, _, htransJ, _⟩ := hJ
      have hneij : gi ≠ gj := by
        intro heq
        apply hne
        rw [← hidJ, ← hidG, heq]
      have hnm : (⟨-1, (gi : Int)⟩ : Elegant.Grid.Architecture.Unit) ∉
          groupChain input.groups input.groups.length (Int.ofNat gj) := by
        intro hmem
        rw [hinputGrp] at hmem
        have hmemB := hBgroup gj hgj gi hgi hneij hmem
        rw [hidG, hidJ] at hmemB
        exact h1 hmemB
      have hnm' : (⟨-1, (gj : Int)⟩ : Elegant.Grid.Architecture.Unit) ∉
          groupChain input.groups input.groups.length (Int.ofNat gi) := by
        intro hmem
        rw [hinputGrp] at hmem
        have hmemB := hBgroup gi hgi gj hgj (fun h => hneij h.symm) hmem
        rw [hidG, hidJ] at hmemB
        exact h2 hmemB
      obtain ⟨owner, first, second, hdiv⟩ :
          ∃ owner first second, divergent
            (groupChain input.groups input.groups.length (Int.ofNat gi))
            (groupChain input.groups input.groups.length (Int.ofNat gj)) (-1) =
            some (owner, first, second) := by
        cases hdiv : divergent
            (groupChain input.groups input.groups.length (Int.ofNat gi))
            (groupChain input.groups input.groups.length (Int.ofNat gj)) (-1) with
        | some v =>
          obtain ⟨o, f, s⟩ := v
          exact ⟨o, f, s, rfl⟩
        | none =>
          exfalso
          have hnn := c8a_divergent_none _ _ _ hdiv
          rcases hnn with ⟨rest, hr⟩ | ⟨rest, hr⟩
          · have hself := c8a_groupChain_self_mem input.groups
              input.groups.length gi hgiIn
            have hmem2 : (⟨-1, (gi : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
                groupChain input.groups input.groups.length (Int.ofNat gj) := by
              rw [hr]
              exact List.mem_append.mpr (Or.inl hself)
            exact hnm hmem2
          · have hself := c8a_groupChain_self_mem input.groups
              input.groups.length gj hgjIn
            have hmem2 : (⟨-1, (gj : Int)⟩ : Elegant.Grid.Architecture.Unit) ∈
                groupChain input.groups input.groups.length (Int.ofNat gi) := by
              rw [hr]
              exact List.mem_append.mpr (Or.inl hself)
            exact hnm' hmem2
      have hleftPath : ParentPath input (-1)
          (groupChain input.groups input.groups.length (Int.ofNat gi))
          (Int.ofNat gi) :=
        groupChain_parent_path input hord hgp _ _ (Or.inr ⟨gi, hgiIn, hgiIn, rfl⟩)
      have hrightPath : ParentPath input (-1)
          (groupChain input.groups input.groups.length (Int.ofNat gj))
          (Int.ofNat gj) :=
        groupChain_parent_path input hord hgp _ _ (Or.inr ⟨gj, hgjIn, hgjIn, rfl⟩)
      have hsib := c8a_level_siblings_executed input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
        (groupChain input.groups input.groups.length (Int.ofNat gi))
        (groupChain input.groups input.groups.length (Int.ofNat gj))
        (Int.ofNat gi) (Int.ofNat gj) hleftPath hrightPath owner first second hdiv
      have hsep0 := c8a_step2_separation input params frameParams (LayoutConst.architecture_bfs_cap.get m.profile).toNat hres
        owner first second hsib
      rw [← hplaced', ← hresolved'] at hsep0
      have hdiv' := divergent_common_prefix
        (groupChain input.groups input.groups.length (Int.ofNat gi))
        (groupChain input.groups input.groups.length (Int.ofNat gj))
        (-1) owner first second hdiv
      obtain ⟨_, shared, lr, rr, hleq, hreq, _⟩ := hdiv'
      have hfirst : first ∈
          groupChain input.groups input.groups.length (Int.ofNat gi) := by
        rw [hleq]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have hsecond : second ∈
          groupChain input.groups input.groups.length (Int.ofNat gj) := by
        rw [hreq]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have hmemA : first.group.toNat < input.groups.length :=
        c8a_groupChain_mem_bound input.groups hord gi hgiIn _ first hfirst
      have hfirstEq : first =
          (⟨-1, ((first.group.toNat : Nat) : Int)⟩ : Elegant.Grid.Architecture.Unit) := by
        cases first with
        | mk n g =>
          have hnA : n = (-1 : Int) := c8a_groupChain_mem_node _ _ _ _ hfirst
          have hgA : ((g.toNat : Nat) : Int) = g :=
            Int.toNat_of_nonneg (c8a_groupChain_nonneg _ _ _ _ hfirst)
          subst hnA
          rw [hgA]
      have hleqA := hleq
      rw [hfirstEq] at hleqA
      have hframeA := c8a_step3_group_frame_of_suffix input params frameParams
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat
        hresS (first.group.toNat) gi hmemA hgiIn shared lr hleqA
      rw [← hplaced', ← hresolved'] at hframeA
      rw [← hfirstEq] at hframeA
      rw [← hgeomFrames] at hframeA
      have hmemBnd : second.group.toNat < input.groups.length :=
        c8a_groupChain_mem_bound input.groups hord gj hgjIn _ second hsecond
      have hsecondEq : second =
          (⟨-1, ((second.group.toNat : Nat) : Int)⟩ : Elegant.Grid.Architecture.Unit) := by
        cases second with
        | mk n g =>
          have hnB : n = (-1 : Int) := c8a_groupChain_mem_node _ _ _ _ hsecond
          have hgB : ((g.toNat : Nat) : Int) = g :=
            Int.toNat_of_nonneg (c8a_groupChain_nonneg _ _ _ _ hsecond)
          subst hnB
          rw [hgB]
      have hreqB := hreq
      rw [hsecondEq] at hreqB
      have hframeB := c8a_step3_group_frame_of_suffix input params frameParams
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat
        hresS (second.group.toNat) gj hmemBnd hgjIn shared rr hreqB
      rw [← hplaced', ← hresolved'] at hframeB
      rw [← hsecondEq] at hframeB
      rw [← hgeomFrames] at hframeB
      rw [hrectG, hrectJ]
      exact c8a_step4_disjoint _ _ _ _ _ _ _ _ hsep0 hframeA hframeB htransG htransJ
    · obtain ⟨nj, hnj, hidN, _, _, _, _, _, hroleN⟩ := hNj
      exfalso
      have hNrole := c8a_mem_nodes_role nodes m.boxes hnodes _ hnj
      have heq : (nodes.getD nj default).role.id = "group" := by
        rw [← hroleN]
        exact hbdbG
      rw [hNrole] at heq
      exact absurd heq (by decide)
  · obtain ⟨ni, hni, hidN, _, _, _, _, _, hroleN⟩ := hN
    exfalso
    have hNrole := c8a_mem_nodes_role nodes m.boxes hnodes _ hni
    have heq : (nodes.getD ni default).role.id = "group" := by
      rw [← hroleN]
      exact hrole
    rw [hNrole] at heq
    exact absurd heq (by decide)

/-- Gap (c): every ancestor-unrelated pair with a group on the left is disjoint,
combining the node side and the group side. -/
theorem c8a_group_case (m : Model) (scene : Scene) (capped : Bool)
    (built : build m = .ok (scene, capped)) (hwf : WellFormed m)
    (hA : c8a_gapA_index m scene capped built) :
    c8a_gapC_pair m scene capped built := by
  intro gdb hgdb hroleG bdb hbdb hne h1 h2
  have hA2 : c8a_gapA_index m scene capped built := hA
  obtain ⟨groups, nodes, _, _, _, _, _, _, _, _, _, _, _, _, _, dumpBoxes,
    hgroups, hnodes, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hboxEq, hcorr, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _⟩ := hA
  have hbdb' : bdb ∈ dumpBoxes := by rw [← hboxEq]; exact hbdb
  by_cases hb : bdb.role = "node"
  · exact c8a_group_case_node m scene capped built hwf hA2 gdb bdb hgdb hroleG hbdb hb h1
  · have hbdbG : bdb.role = "group" := by
      rcases hcorr bdb hbdb' with hG | hN
      · obtain ⟨gi, hgi, _, _, _, _, _, _, hroleB⟩ := hG
        have hrB := c8a_mem_groups_role groups m.boxes hgroups gi hgi
        rw [hrB] at hroleB
        have hgid : BoxRole.group.id = "group" := rfl
        rw [hgid] at hroleB
        exact hroleB
      · obtain ⟨ni, hni, _, _, _, _, _, _, hroleB⟩ := hN
        have hrB := c8a_mem_nodes_role nodes m.boxes hnodes ni hni
        rw [hrB] at hroleB
        have hnid : BoxRole.node.id = "node" := rfl
        rw [hnid] at hroleB
        exact absurd hroleB hb
    exact c8a_group_case_group m scene capped built hwf hA2 gdb bdb hgdb hroleG hbdb hbdbG hne h1 h2

/-- Architecture C8a: every group frame is disjoint from every ancestor-unrelated
box, proved from a successful layout of a well-formed, within-limits model. -/
theorem architecture_c8a (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  obtain ⟨scene, capped, built, dump⟩ := public_layout_dump m result h
  rw [dump]
  unfold Validator.C8a
  exact c8a_group_case m scene capped built hwf
    (c8a_gapA_of_build m scene capped hwf built)

end Elegant.Kinds.Architecture
