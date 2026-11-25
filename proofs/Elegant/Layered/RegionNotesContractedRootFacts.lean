import Elegant.Layered.NotesSubInputWellFormedExecuted
import Elegant.Layered.RecursiveC2

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

private def LiveFramedParents (inp : Input) : Prop :=
  ∀ b ∈ inp.boxes, ∀ p ∈ inp.boxes, b.parent ≠ "" → p.id = b.parent →
    p.role = .group ∧ inp.fixedSizes.any (fun fixed => fixed.1 == p.id) = false

private theorem liveFramed_of_framed {inp : Input} (hnd : (inp.boxes.map (·.id)).Nodup)
    (h : framedParents inp = true) : LiveFramedParents inp := by
  intro b hb p hp hn hid
  obtain ⟨other, hother, hoid, hr, hf⟩ := framedParents_parent h hb hn
  have he : other = p := eq_of_mem_id hnd hother hp (hoid.trans hid.symm)
  subst other
  exact ⟨hr, hf⟩

private theorem contractOne_box_nodup (inp : Input) (l : BundleLayout)
    (hnd : (inp.boxes.map (·.id)).Nodup) : ((contractOne inp l).boxes.map (·.id)).Nodup := by
  let keep : ModelBox × Nat → Bool := fun q =>
    !(Compound.inside inp.boxes l.top.id q.1.id || (l.notes.map (·.1.id)).contains q.1.id)
  have heq : (contractOne inp l).boxes.map (·.id) =
      ((inp.boxes.zipIdx.filter keep).map Prod.fst).map ModelBox.id := by
    unfold contractOne
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    change (if q.1.id == l.top.id then { q.1 with role := .node, direction := "" } else q.1).id = q.1.id
    split <;> rfl
  rw [heq]
  exact List.Nodup.sublist ((zipIdx_filter_map_fst_sublist keep inp.boxes).map ModelBox.id) hnd

private theorem contractOne_liveFramed (inp : Input) (l : BundleLayout)
    (hnd : (inp.boxes.map (·.id)).Nodup) (hfr : LiveFramedParents inp) :
    LiveFramedParents (contractOne inp l) := by
  intro b hb p hp hn hid
  simp only [contractOne, List.mem_map, List.mem_filter] at hb hp
  obtain ⟨⟨src, _⟩, ⟨hzip, hkeep⟩, rfl⟩ := hb
  obtain ⟨⟨par, _⟩, ⟨hparZip, _⟩, rfl⟩ := hp
  have hs : src ∈ inp.boxes := List.fst_mem_of_mem_zipIdx hzip
  have hp : par ∈ inp.boxes := List.fst_mem_of_mem_zipIdx hparZip
  have hsrcParent :
      (if src.id == l.top.id then { src with role := .node, direction := "" } else src).parent = src.parent := by
    split <;> rfl
  have hparId :
      (if par.id == l.top.id then { par with role := .node, direction := "" } else par).id = par.id := by
    split <;> rfl
  rw [hsrcParent] at hn
  rw [hsrcParent, hparId] at hid
  have htop : par.id ≠ l.top.id := by
    intro ht
    have hin := inside_of_parent hnd hp hs hid hn
    rw [ht] at hin
    simp [hin] at hkeep
  obtain ⟨hrole, hfixed⟩ := hfr src hs par hp hn hid
  refine ⟨by simp [htop, hrole], ?_⟩
  rw [hparId]
  change ((inp.fixedSizes.filter (·.1 != l.top.id) ++ [(l.top.id, l.footprint.size)]).any
    (fun fixed => fixed.1 == par.id)) = false
  rw [List.any_append]
  have hf : (inp.fixedSizes.filter (·.1 != l.top.id)).any (fun fixed => fixed.1 == par.id) = false :=
    List.any_eq_false.mpr fun q hq => List.any_eq_false.mp hfixed q (List.mem_filter.mp hq).1
  simp [hf, Ne.symm htop]

private theorem contractFold_liveFramed (layouts : List BundleLayout) (inp : Input)
    (hnd : (inp.boxes.map (·.id)).Nodup) (hfr : LiveFramedParents inp) :
    LiveFramedParents (layouts.foldl contractOne inp) := by
  induction layouts generalizing inp with
  | nil => exact hfr
  | cons l rest ih =>
    exact ih (contractOne inp l) (contractOne_box_nodup inp l hnd)
      (contractOne_liveFramed inp l hnd hfr)

private theorem contractFold_box_source (layouts : List BundleLayout) (inp : Input)
    {b : ModelBox} (hb : b ∈ (layouts.foldl contractOne inp).boxes) :
    ∃ src ∈ inp.boxes, src.id = b.id ∧ src.parent = b.parent := by
  induction layouts generalizing inp with
  | nil => exact ⟨b, hb, rfl, rfl⟩
  | cons l rest ih =>
    rw [List.foldl_cons] at hb
    obtain ⟨mid, hm, hid, hpar⟩ := ih _ hb
    obtain ⟨src, hs, hsid, hspar⟩ := contractOne_box_mem inp l mid hm
    exact ⟨src, hs, hsid.trans hid, hspar.trans hpar⟩

namespace ContractedC8a

def rootParent (ids : List String) (parent : String) : String :=
  if parent ∈ ids then parent else ""

@[simp] theorem rootParent_empty (ids : List String) : rootParent ids "" = "" := by
  simp [rootParent]

def rootModelBox (ids : List String) (b : ModelBox) : ModelBox :=
  { b with parent := rootParent ids b.parent }

def rootInput (inp : Input) : Input :=
  { inp with boxes := inp.boxes.map (rootModelBox (inp.boxes.map (·.id))) }

@[simp] theorem rootInput_ids (inp : Input) :
    (rootInput inp).boxes.map (·.id) = inp.boxes.map (·.id) := by
  simp only [rootInput, List.map_map] <;> rfl

private theorem chainTerm_at_live_box {boxes : List ModelBox} {b : ModelBox}
    (hnd : (boxes.map (·.id)).Nodup) (hb : b ∈ boxes) (hne : b.id ≠ "") (n : Nat) :
    chainTerm boxes (n + 1) b.id = chainTerm boxes n b.parent := by
  cases hfind : boxes.findIdx? (fun x => x.id == b.id) with
  | none =>
    have hbad := List.findIdx?_eq_none_iff.mp hfind b hb
    simp at hbad
  | some i =>
    obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    have heq : boxes[i] = b := eq_of_mem_id hnd (List.getElem_mem hlt) hb (beq_iff_eq.mp hmatch)
    rw [chainTerm.eq_3 boxes b.id n hne, hfind]
    simp only [List.getElem?_eq_getElem hlt, heq]

private theorem rooted_chain_of_source {src kept : Input}
    (hsrc : (src.boxes.map (·.id)).Nodup) (hkept : (kept.boxes.map (·.id)).Nodup)
    (htransfer : ∀ b ∈ kept.boxes, ∃ old ∈ src.boxes, old.id = b.id ∧ old.parent = b.parent) :
    ∀ n id, ParentReaches src.boxes n id →
      chainTerm (rootInput kept).boxes n (rootParent (kept.boxes.map (·.id)) id) = true := by
  have hrnd : ((rootInput kept).boxes.map (·.id)).Nodup := by simpa using hkept
  intro n
  induction n with
  | zero =>
    intro id h
    by_cases he : id = ""
    · subst id
      simp only [rootParent_empty, chainTerm.eq_1]
    · rw [ParentReaches.eq_2 _ _ he] at h
      contradiction
  | succ n ih =>
    intro id h
    by_cases he : id = ""
    · subst id
      simp only [rootParent_empty, chainTerm.eq_1]
    by_cases hmem : id ∈ kept.boxes.map (·.id)
    · obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hmem
      obtain ⟨srcB, hs, hsid, hsparent⟩ := htransfer b hb
      rw [ParentReaches.eq_3 _ _ _ he] at h
      obtain ⟨found, hf, hnext⟩ := h
      have htest : (found.id == id) = true :=
        List.find?_some (p := fun b : ModelBox => b.id == id) hf
      have hfound : found.id = id := beq_iff_eq.mp htest
      have hfEq := eq_of_mem_id hsrc (List.mem_of_find?_eq_some hf) hs
        (hfound.trans (hsid.trans hbid).symm)
      let b' := rootModelBox (kept.boxes.map (·.id)) b
      have hb' : b' ∈ (rootInput kept).boxes := List.mem_map_of_mem hb
      have hb'id : b'.id = id := hbid
      have hb'ne : b'.id ≠ "" := fun hn => he (hb'id.symm.trans hn)
      have hstep := chainTerm_at_live_box hrnd hb' hb'ne n
      rw [hb'id] at hstep
      rw [rootParent, ite_eq_left hmem, hstep]
      exact ih b.parent (by rwa [hfEq, hsparent] at hnext)
    · simp only [rootParent, ite_eq_right hmem, chainTerm.eq_1]

private theorem rootInput_framed {inp : Input} (h : LiveFramedParents inp) :
    framedParents (rootInput inp) = true := by
  unfold framedParents
  rw [List.all_eq_true]
  intro b hb
  change b ∈ inp.boxes.map (rootModelBox (inp.boxes.map (·.id))) at hb
  obtain ⟨orig, hOrig, rfl⟩ := List.mem_map.mp hb
  by_cases hn : (rootModelBox (inp.boxes.map (·.id)) orig).parent = ""
  · simp only [hn, beq_self_eq_true, Bool.true_or]
  have hm : orig.parent ∈ inp.boxes.map (·.id) := by
    by_cases hm : orig.parent ∈ inp.boxes.map (·.id)
    · exact hm
    · exact (hn (by simp only [rootModelBox, rootParent, ite_eq_right hm])).elim
  have hpar : (rootModelBox (inp.boxes.map (·.id)) orig).parent = orig.parent := by
    simp only [rootModelBox, rootParent, ite_eq_left hm]
  obtain ⟨p, hp, hid⟩ := List.mem_map.mp hm
  obtain ⟨hrole, hf⟩ := h orig hOrig p hp (fun he => hn (hpar.trans he)) hid
  have ha : (rootInput inp).boxes.any (fun p =>
      p.id == (rootModelBox (inp.boxes.map (·.id)) orig).parent && p.role == .group &&
        !(rootInput inp).fixedSizes.any (fun f => f.1 == p.id)) = true := by
    apply List.any_eq_true.mpr
    refine ⟨rootModelBox (inp.boxes.map (·.id)) p, List.mem_map_of_mem hp, ?_⟩
    change (p.id == (rootModelBox (inp.boxes.map (·.id)) orig).parent &&
      p.role == .group && !inp.fixedSizes.any (fun f => f.1 == p.id)) = true
    rw [hpar, ← hid]
    simp [hrole, hf]
  simp only [ha, Bool.or_true]

theorem contracted_rooted_guards {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids (reindexRegionSets idSets sub) sub opt)
      exactIds fuel inp o res) (hwf : WellFormed (inputModel inp o))
    (hfr : framedParents inp = true) :
    WellFormed (inputModel (rootInput e.contractedInput) o) ∧
      framedParents (rootInput e.contractedInput) = true := by
  have hsrc := (inputFacts_of_wellFormed hwf).nodup
  obtain ⟨hb, hr, hl, hg, howner, hends⟩ := e.contractedInput_wellFormed_fields hwf
  have hpres (b : ModelBox) (h : b ∈ e.contractedInput.boxes) :
      ∃ orig ∈ inp.boxes, orig.id = b.id ∧ orig.parent = b.parent := by
    rw [e.contractedInput_eq] at h
    exact contractFold_box_source e.layouts inp h
  constructor
  · rw [wellFormed_iff]
    have hnd : ((rootInput e.contractedInput).boxes.map (·.id)).Nodup := by
      simpa using hb
    refine ⟨nodup_eraseDups_length _ hnd, nodup_eraseDups_length _ hr,
      nodup_eraseDups_length _ hl, ?_, ?_, ?_, ?_⟩
    · intro b hm
      change b ∈ (rootInput e.contractedInput).boxes at hm
      have hm' : b ∈ e.contractedInput.boxes.map (rootModelBox (e.contractedInput.boxes.map (·.id))) := hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm'
      obtain ⟨orig, horig, _, hp⟩ := hpres old hold
      have ht := ((wellFormed_iff (inputModel inp o)).mp hwf).2.2.2.1 orig horig
      change ParentReaches inp.boxes inp.boxes.length orig.parent at ht
      rw [hp] at ht
      have hterm := rooted_chain_of_source hsrc hb hpres _ _ ht
      apply chainTerm_parentReaches hnd
      exact chainTerm_mono _ _ (chainTerm_depth hterm hm rfl) _ (Nat.sub_le _ _)
    · intro r hm
      simpa only [inputModel, rootInput_ids] using hends r hm
    · intro l hm
      change l.owner ∈ (rootInput e.contractedInput).boxes.map (·.id) ∨
        l.owner ∈ e.contractedInput.routes.map (·.id)
      rw [rootInput_ids]
      exact howner l hm
    · intro b hm hrole
      change b ∈ e.contractedInput.boxes.map (rootModelBox (e.contractedInput.boxes.map (·.id))) at hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
      exact hg old hold hrole
  · apply rootInput_framed
    rw [e.contractedInput_eq]
    exact contractFold_liveFramed e.layouts inp hsrc (liveFramed_of_framed hsrc hfr)

end ContractedC8a
end Elegant.Layered.PipelineImpl
