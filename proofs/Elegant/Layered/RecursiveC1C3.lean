import Elegant.Layered.RecursiveFit
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Chart.TreemapContainmentFacts
import Elegant.Layered.SelectInputWellFormed

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- Boxes the `chainTerm` walk visits, in order, up to `fuel` lookups. -/
def chainWalk (boxes : List ModelBox) : Nat → String → List ModelBox
  | _, "" => []
  | 0, _ => []
  | n + 1, id =>
    match boxes.findIdx? (fun b => b.id == id) with
    | none => []
    | some i =>
      match boxes[i]? with
      | none => []
      | some b => b :: chainWalk boxes n b.parent

theorem chainWalk_nil (boxes : List ModelBox) (n : Nat) :
    chainWalk boxes n "" = [] := chainWalk.eq_1 boxes n

theorem chainWalk_zero {boxes : List ModelBox} {id : String} (hid : id ≠ "") :
    chainWalk boxes 0 id = [] := chainWalk.eq_2 boxes id (fun h => hid h)

theorem chainWalk_succ {boxes : List ModelBox} {id : String} (hid : id ≠ "") (n : Nat) :
    chainWalk boxes n.succ id =
      match boxes.findIdx? (fun b => b.id == id) with
      | none => []
      | some i =>
        match boxes[i]? with
        | none => []
        | some b => b :: chainWalk boxes n b.parent :=
  chainWalk.eq_3 boxes id n (fun h => hid h)

theorem chainWalk_length_le (boxes : List ModelBox) :
    ∀ (n : Nat) (id : String), (chainWalk boxes n id).length ≤ n := by
  intro n
  induction n with
  | zero =>
      intro id
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil]; simp
      · rw [chainWalk_zero hid]; simp
  | succ n ih =>
      intro id
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil]; simp
      · rw [chainWalk_succ hid n]
        split
        · simp
        · split
          · simp
          · rename_i i opt b hb
            simp only [List.length_cons]
            exact Nat.succ_le_succ (ih b.parent)

theorem chainWalk_mem {boxes : List ModelBox} :
    ∀ (n : Nat) (id : String) (b : ModelBox),
      b ∈ chainWalk boxes n id → b ∈ boxes := by
  intro n
  induction n with
  | zero =>
      intro id b hb
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at hb; simp at hb
      · rw [chainWalk_zero hid] at hb; simp at hb
  | succ n ih =>
      intro id b hb
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at hb; simp at hb
      · rw [chainWalk_succ hid n] at hb
        cases hf : boxes.findIdx? (fun b0 => b0.id == id) with
        | none => simp only [hf] at hb; simp at hb
        | some i =>
          simp only [hf] at hb
          cases hg : boxes[i]? with
          | none => simp only [hg] at hb; simp at hb
          | some b0 =>
            simp only [hg, List.mem_cons] at hb
            rcases hb with rfl | htail
            · exact getElem?_mem' hg
            · exact ih _ _ htail

/-- If the walk's last visited box has empty parent, the walk needed exactly
its length in fuel: `chainWalk` at that exact fuel reproduces the walk. -/
theorem chainWalk_fuel_exact (boxes : List ModelBox) :
    ∀ (n : Nat) (id : String) (w : List ModelBox),
      chainWalk boxes n id = w → w.getLast?.map (·.parent) = some "" →
      chainWalk boxes w.length id = w := by
  intro n
  induction n with
  | zero =>
      intro id w hw hg
      by_cases hid : id = ""
      · subst hid
        rw [chainWalk_nil] at hw
        cases hw
        exact absurd hg (by simp)
      · rw [chainWalk_zero hid] at hw
        cases hw
        exact absurd hg (by simp)
  | succ n ih =>
      intro id w hw hg
      by_cases hid : id = ""
      · subst hid
        rw [chainWalk_nil] at hw
        cases hw
        exact absurd hg (by simp)
      · rw [chainWalk_succ hid n] at hw
        cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp only [hf] at hw; cases hw; exact absurd hg (by simp)
        | some i =>
          simp only [hf] at hw
          cases hg2 : boxes[i]? with
          | none => simp only [hg2] at hw; cases hw; exact absurd hg (by simp)
          | some b =>
            simp only [hg2] at hw
            cases hw
            cases hX : chainWalk boxes n b.parent with
            | nil =>
                simp [hX] at hg
                have h1 : chainWalk boxes 1 id = [b] := by
                  rw [chainWalk_succ hid 0]
                  simp only [hf, hg2]
                  simp [hg, chainWalk_nil]
                simpa using h1
            | cons c cs =>
                rw [hX] at hg
                simp only [List.getLast?_cons_cons] at hg
                have hstep := ih b.parent (c :: cs) hX hg
                have h2 : chainWalk boxes ((c :: cs).length + 1) id = b :: c :: cs := by
                  rw [chainWalk_succ hid (c :: cs).length]
                  simp only [hf, hg2]
                  rw [hstep]
                simpa using h2

/-- One more fuel leaves a terminated walk unchanged. -/
theorem chainWalk_succ_stable (boxes : List ModelBox) :
    ∀ (K : Nat) (id : String) (w : List ModelBox),
      chainWalk boxes K id = w → w ≠ [] → w.getLast?.map (·.parent) = some "" →
      chainWalk boxes K.succ id = w := by
  intro K
  induction K with
  | zero =>
      intro id w hw hne hg
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at hw; exact (hne hw.symm).elim
      · rw [chainWalk_zero hid] at hw; exact (hne hw.symm).elim
  | succ j ih =>
      intro id w hw hne hg
      by_cases hid : id = ""
      · subst hid
        rw [chainWalk_nil] at hw
        exact (hne hw.symm).elim
      · rw [chainWalk_succ hid j] at hw
        cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp only [hf] at hw; exact (hne hw.symm).elim
        | some i =>
          simp only [hf] at hw
          cases hg2 : boxes[i]? with
          | none => simp only [hg2] at hw; exact (hne hw.symm).elim
          | some b =>
            simp only [hg2] at hw
            cases hw
            cases hw'' : chainWalk boxes j b.parent with
            | nil =>
                have hbp : b.parent = "" := by
                  rw [hw''] at hg
                  simpa using hg
                rw [chainWalk_succ hid j.succ]
                simp only [hf, hg2]
                rw [hbp]
                simp [chainWalk_nil]
            | cons c cs =>
                have hg' : (Option.map (fun x => x.parent) (c :: cs).getLast?)
                    = some "" := by
                  rw [hw''] at hg
                  simpa using hg
                have hne' : (c :: cs : List ModelBox) ≠ [] := by simp
                have hstep := ih b.parent (c :: cs) hw'' hne' hg'
                rw [chainWalk_succ hid j.succ]
                simp only [hf, hg2]
                rw [hstep]

/-- A terminated nonempty walk is reproduced at every fuel at least its
length. -/
theorem chainWalk_stable_all (boxes : List ModelBox) :
    ∀ (K : Nat) (id : String) (w : List ModelBox), ∀ M : Nat,
      chainWalk boxes M id = w → w ≠ [] → w.getLast?.map (·.parent) = some "" →
      w.length ≤ K → chainWalk boxes K id = w := by
  intro K
  induction K with
  | zero =>
      intro id w M hw hne hg hlen
      have hw0 : w.length = 0 := by omega
      have : w = [] := by
        cases w with
        | nil => rfl
        | cons c cs => simp [List.length_cons] at hw0
      exact absurd this hne
  | succ K ih =>
      intro id w M hw hne hg hlen
      by_cases hle : w.length ≤ K
      · have hstep := ih id w M hw hne hg hle
        exact chainWalk_succ_stable boxes K id w hstep hne hg
      · have heq : w.length = K + 1 := by omega
        have hex := chainWalk_fuel_exact boxes M id w hw hg
        rw [heq] at hex
        exact hex

section DepthLemma
variable {boxes : List ModelBox}

/-- The head of a nonempty walk is the box the start id resolves to. -/
theorem chainWalk_head_id {n : Nat} {id : String} {q : ModelBox} {rest : List ModelBox}
    (h : chainWalk boxes n id = q :: rest) : q.id = id := by
  by_cases hid : id = ""
  · subst hid
    rw [chainWalk_nil] at h
    exact absurd h (by simp)
  · cases n with
    | zero => rw [chainWalk_zero hid] at h; exact absurd h (by simp)
    | succ m =>
        rw [chainWalk_succ hid m] at h
        cases hf : boxes.findIdx? (fun b0 : ModelBox => b0.id == id) with
        | none => simp only [hf] at h; exact absurd h (by simp)
        | some i =>
          simp only [hf] at h
          cases hg : boxes[i]? with
          | none => simp only [hg] at h; exact absurd h (by simp)
          | some b =>
            simp only [hg] at h
            injection h with h
            cases h
            obtain ⟨_, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            rw [List.getElem?_eq_some_iff.mp hg |>.2] at hmatch
            exact beq_iff_eq.mp hmatch

/-- The suffix of a walk from position `a` onwards is the walk from the box
at position `a`. -/
theorem chainWalk_drop {n : Nat} {id : String} {a : Nat} {w : List ModelBox} {q : ModelBox}
    (h : chainWalk boxes n id = w) (ha : w[a]? = some q) :
    chainWalk boxes (n - (a + 1)) q.parent = w.drop (a + 1) := by
  induction n generalizing a id w q with
  | zero =>
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at h; exact absurd ha (by rw [← h]; simp)
      · rw [chainWalk_zero hid] at h; exact absurd ha (by rw [← h]; simp)
  | succ m ih =>
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at h; exact absurd ha (by rw [← h]; simp)
      · rw [chainWalk_succ hid m] at h
        cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp only [hf] at h; exact absurd ha (by rw [← h]; simp)
        | some i =>
          simp only [hf] at h
          cases hg : boxes[i]? with
          | none => simp only [hg] at h; exact absurd ha (by rw [← h]; simp)
          | some b =>
            simp only [hg] at h
            rw [← h] at ha ⊢
            rcases a with _ | a'
            · simp only [List.getElem?_cons_zero] at ha
              have hbq : b = q := Option.some.inj ha
              subst hbq
              show chainWalk boxes (m + 1 - 1) b.parent
                = (b :: chainWalk boxes m b.parent).drop 1
              rw [List.drop_cons (by omega)]
              rfl
            · simp only [List.getElem?_cons_succ] at ha
              show chainWalk boxes (m + 1 - (a' + 1 + 1)) q.parent
                = (b :: chainWalk boxes m b.parent).drop (a' + 1 + 1)
              rw [List.drop_cons (by omega)]
              rw [show m + 1 - (a' + 1 + 1) = m - (a' + 1) from by omega]
              exact ih (a := a') (id := b.parent) rfl ha

/-- The empty parent terminates the walk: no earlier position has it. -/
theorem chainWalk_empty_parent_last {n : Nat} {id : String} {w : List ModelBox} {j : Nat}
    (h : chainWalk boxes n id = w) (hj : j < w.length)
    (hp : w[j].parent = "") : j + 1 = w.length := by
  have hsome : w[j]? = some w[j] := List.getElem?_eq_getElem hj
  have hdrop := chainWalk_drop h hsome
  rw [hp] at hdrop
  rw [chainWalk_nil] at hdrop
  have hdropnil : w.drop (j + 1) = [] := hdrop.symm
  have hle : w.length ≤ j + 1 := by
    have hl : (w.drop (j + 1)).length = w.length - (j + 1) := List.length_drop
    rw [hdropnil, List.length_nil] at hl
    omega
  omega

/-- Two terminated nonempty walks from the same start coincide. -/
theorem chainWalk_det :
    ∀ (M K : Nat) (p : String) (X Y : List ModelBox),
      chainWalk boxes M p = X → X ≠ [] → X.getLast?.map (·.parent) = some "" →
      chainWalk boxes K p = Y → Y ≠ [] → Y.getLast?.map (·.parent) = some "" → X = Y := by
  intro M K p X Y hX hXne hXt hY hYne hYt
  have hXe := chainWalk_fuel_exact boxes M p X hX hXt
  have hYe := chainWalk_fuel_exact boxes K p Y hY hYt
  have hXlen : X.length ≤ Y.length ∨ Y.length ≤ X.length := Nat.le_total _ _
  rcases hXlen with hle | hle
  · have hs := chainWalk_stable_all boxes Y.length p X M hX hXne hXt (by omega)
    rw [hs] at hYe
    exact hYe
  · have hs := chainWalk_stable_all boxes X.length p Y K hY hYne hYt (by omega)
    rw [hs] at hXe
    exact hXe.symm

/-- The last element of a terminated walk has empty parent. -/
theorem chainWalk_last_parent_val :
    ∀ (w : List ModelBox) (c : ModelBox),
      w.getLast? = some c → w.getLast?.map (·.parent) = some "" → c.parent = "" := by
  intro w c hc hg
  cases w with
  | nil => rw [List.getLast?_nil] at hc; exact absurd hc (by simp)
  | cons d ds =>
      cases ds with
      | nil =>
          rw [List.getLast?_singleton] at hc hg
          have := Option.some.inj hc
          subst this
          simpa using hg
      | cons e es =>
          rw [List.getLast?_cons_cons] at hc hg
          exact chainWalk_last_parent_val (e :: es) c hc hg

/-- A terminated walk visits no box twice. -/
theorem chainWalk_nodup :
    ∀ (n : Nat) (id : String) (w : List ModelBox),
      chainWalk boxes n id = w → w.getLast?.map (·.parent) = some "" → w.Nodup := by
  intro n
  induction n with
  | zero =>
      intro id w hw hg
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at hw; cases hw; exact List.nodup_nil
      · rw [chainWalk_zero hid] at hw; cases hw; exact List.nodup_nil
  | succ n ih =>
      intro id w hw hg
      by_cases hid : id = ""
      · subst hid; rw [chainWalk_nil] at hw; cases hw; exact List.nodup_nil
      · rw [chainWalk_succ hid n] at hw
        cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp only [hf] at hw; cases hw; exact List.nodup_nil
        | some i =>
          simp only [hf] at hw
          cases hgo : boxes[i]? with
          | none => simp only [hgo] at hw; cases hw; exact List.nodup_nil
          | some b =>
            simp only [hgo] at hw
            have hwcons : w = b :: chainWalk boxes n b.parent := hw.symm
            cases hTc : chainWalk boxes n b.parent with
            | nil =>
                rw [hwcons, hTc] at hg ⊢
                simp only [List.getLast?_singleton] at hg
                refine List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
            | cons c0 cs0 =>
                have hT : chainWalk boxes n b.parent = c0 :: cs0 := hTc
                have hTne : chainWalk boxes n b.parent ≠ [] := by rw [hTc]; simp
                have hgl := hg
                rw [hwcons] at hgl
                rw [hTc] at hgl
                have hTterm : (c0 :: cs0).getLast?.map (·.parent) = some "" := hgl
                have hTnodup := ih b.parent _ hT hTterm
                rw [hwcons, hTc]
                refine List.nodup_cons.mpr ⟨?_, hTnodup⟩
                intro hbin
                obtain ⟨a, haeq⟩ := (List.mem_iff_getElem? (α := ModelBox)).mp hbin
                have haeq' : (chainWalk boxes n b.parent)[a]? = some b := by
                  rw [hTc]; exact haeq
                obtain ⟨haLT, -⟩ := List.getElem?_eq_some_iff.mp haeq'
                have hdrop := chainWalk_drop hT haeq
                have hdrop' : chainWalk boxes (n - (a + 1)) b.parent =
                    (chainWalk boxes n b.parent).drop (a + 1) := by
                  rw [hTc]
                  exact hdrop
                by_cases hsuf : (chainWalk boxes n b.parent).drop (a + 1) = []
                · -- empty suffix: T[a] is the last box, so b.parent = ""
                  have hlen : a + 1 = (chainWalk boxes n b.parent).length := by
                    have hl : ((chainWalk boxes n b.parent).drop (a + 1)).length =
                        (chainWalk boxes n b.parent).length - (a + 1) :=
                      List.length_drop
                    rw [hsuf, List.length_nil] at hl
                    omega
                  have hlastget : (chainWalk boxes n b.parent).getLast? = some b := by
                    rw [List.getLast?_eq_getElem?, show
                      (chainWalk boxes n b.parent).length - 1 = a from by omega]
                    exact haeq'
                  have hbp : b.parent = "" := by
                    have hlv := chainWalk_last_parent_val (c0 :: cs0) b (by rw [← hTc]; exact hlastget) hTterm
                    exact hlv
                  rw [hbp, chainWalk_nil] at hT
                  exact absurd hT (by simp)
                · -- nonempty suffix: determinism forces suffix = T, length contradiction
                  have hsufne : (chainWalk boxes n b.parent).drop (a + 1) ≠ [] := hsuf
                  have hlt : (chainWalk boxes n b.parent).length > (a + 1) := by
                    by_cases hcon : (chainWalk boxes n b.parent).length ≤ (a + 1)
                    · exfalso
                      apply hsufne
                      have hl : ((chainWalk boxes n b.parent).drop (a + 1)).length =
                          (chainWalk boxes n b.parent).length - (a + 1) := List.length_drop
                      have h0 : (chainWalk boxes n b.parent).length - (a + 1) = 0 := by omega
                      rw [h0] at hl
                      exact List.eq_nil_of_length_eq_zero hl
                    · omega
                  have hsuffT : ((chainWalk boxes n b.parent).drop (a + 1)).getLast?.map
                      (·.parent) = some "" := by
                    rw [List.getLast?_drop, ite_eq_right (by omega), hTc]
                    exact hTterm
                  have hdet : (chainWalk boxes n b.parent).drop (a + 1)
                      = c0 :: cs0 :=
                    chainWalk_det (M := n - (a + 1)) (K := n) (p := b.parent)
                      (X := List.drop (a + 1) (chainWalk boxes n b.parent))
                      (Y := c0 :: cs0) hdrop' hsufne hsuffT hT (by simp) hTterm
                  have hl : ((chainWalk boxes n b.parent).drop (a + 1)).length =
                      (chainWalk boxes n b.parent).length - (a + 1) := List.length_drop
                  rw [hdet] at hl
                  rw [hTc] at hl
                  have hlen2 : (c0 :: cs0).length = (c0 :: cs0).length - (a + 1) := hl
                  rw [hTc] at haLT
                  have hpos : 0 < (c0 :: cs0).length := by omega
                  have hlt2 : (c0 :: cs0).length - (a + 1) < (c0 :: cs0).length :=
                    Nat.sub_lt hpos (by omega)
                  omega

/-- A walk whose last box has empty parent is exactly a successful `chainTerm`. -/
theorem chainTerm_of_chainWalk :
    ∀ (n : Nat) (id : String) (w : List ModelBox),
      chainWalk boxes n id = w → w.getLast?.map (·.parent) = some "" →
      chainTerm boxes n id = true := by
  intro n
  induction n with
  | zero =>
      intro id w hw hg
      by_cases hid : id = ""
      · subst hid; exact chainTerm.eq_1 _ _
      · rw [chainWalk_zero hid] at hw; exact absurd hg (by rw [← hw]; simp)
  | succ n ih =>
      intro id w hw hg
      by_cases hid : id = ""
      · subst hid; exact chainTerm.eq_1 _ _
      · rw [chainWalk_succ hid n] at hw
        cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp only [hf] at hw; exact absurd hg (by rw [← hw]; simp)
        | some i =>
          simp only [hf] at hw
          cases hgo : boxes[i]? with
          | none => simp only [hgo] at hw; exact absurd hg (by rw [← hw]; simp)
          | some b =>
            simp only [hgo] at hw
            have hwcons : w = b :: chainWalk boxes n b.parent := hw.symm
            rw [chainTerm.eq_3 _ _ _ hid]
            simp only [hf, hgo]
            -- tail termination
            have hgl := hg
            rw [hwcons] at hgl
            have hterm : (chainWalk boxes n b.parent).getLast?.map (·.parent) = some "" ∨
                chainWalk boxes n b.parent = [] := by
              cases hTc : chainWalk boxes n b.parent with
              | nil => exact Or.inr rfl
              | cons c0 cs0 =>
                  left
                  have hgl' := hgl
                  rw [hTc] at hgl'
                  rw [List.getLast?_cons_cons] at hgl'
                  exact hgl'
            rcases hterm with hterm | hnil
            · exact ih b.parent _ rfl hterm
            · have hbp : b.parent = "" := by
                rw [hnil] at hgl
                simpa using hgl
              rw [hbp]
              exact chainTerm.eq_1 _ _

/-- A successful `chainTerm` exposes the terminated walk. -/
theorem chainWalk_of_chainTerm :
    ∀ (n : Nat) (id : String),
      chainTerm boxes n id = true →
      id = "" ∨ ∃ w, chainWalk boxes n id = w ∧
        w.getLast?.map (·.parent) = some "" := by
  intro n
  induction n with
  | zero =>
      intro id h
      by_cases hid : id = ""
      · exact Or.inl hid
      · rw [chainTerm.eq_2 _ _ hid] at h; exact absurd h (by simp)
  | succ n ih =>
      intro id h
      by_cases hid : id = ""
      · exact Or.inl hid
      · rw [chainTerm.eq_3 _ _ _ hid] at h
        cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp only [hf] at h; exact absurd h (by simp)
        | some i =>
          simp only [hf] at h
          cases hgo : boxes[i]? with
          | none => simp only [hgo] at h; exact absurd h (by simp)
          | some b =>
            simp only [hgo] at h
            rcases ih b.parent h with hbp | ⟨w2, hw2, hgt2⟩
            · refine Or.inr ⟨[b], ?_, ?_⟩
              · rw [chainWalk_succ hid n]
                simp only [hf, hgo]
                rw [hbp, chainWalk_nil]
              · rw [List.getLast?_singleton]
                simp [hbp]
            · refine Or.inr ⟨b :: w2, ?_, ?_⟩
              · rw [chainWalk_succ hid n]
                simp only [hf, hgo]
                rw [hw2]
              · cases w2 with
                | nil => simp at hgt2
                | cons c cs =>
                    rw [List.getLast?_cons_cons]
                    exact hgt2

/-- Membership counting for a nodup sublist. -/
theorem nodup_length_le_of_subset {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (w s : List α), w.Nodup → (∀ x ∈ w, x ∈ s) → w.length ≤ s.length := by
  intro w
  induction w with
  | nil => intro s _ _; simp
  | cons x xs ih =>
      intro s hnod hsub
      have hxnot : x ∉ xs := (List.nodup_cons.mp hnod).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnod).2
      have hxs_sub : ∀ y ∈ xs, y ∈ s.erase x := by
        intro y hy
        have hys : y ∈ s := hsub y (List.mem_cons_of_mem x hy)
        have hyx : y ≠ x := by
          intro hcon
          exact hxnot (hcon ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hys
      have hxmem : x ∈ s := hsub x List.mem_cons_self
      have hlen := ih (s.erase x) hxs hxs_sub
      have herase : (s.erase x).length = s.length - 1 := List.length_erase_of_mem hxmem
      rw [herase] at hlen
      have hpos : 0 < s.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hxmem)
      simp only [List.length_cons]
      omega

/-- The walk-length bound: a terminated walk from a parent pointer that
starts below `b` never visits `b`, so it fits in `boxes.length - 1` fuel. -/
theorem chainWalk_length_bound {n : Nat} {x : String} {w : List ModelBox}
    (h : chainWalk boxes n x = w) (hg : w.getLast?.map (·.parent) = some "")
    (hx : x ≠ "") (hb : ∃ b ∈ boxes, b.parent = x) :
    w.length ≤ boxes.length - 1 := by
  obtain ⟨b, hbmem, hbpar⟩ := hb
  have hwne : w ≠ [] := by
    intro hcon
    rw [hcon] at hg
    simp at hg
  have hwnodup := chainWalk_nodup n x w h hg
  -- b is not among the walked boxes
  have hbnot : b ∉ w := by
    intro hbin
    obtain ⟨a, haeq⟩ := (List.mem_iff_getElem? (α := ModelBox)).mp hbin
    obtain ⟨haLT, -⟩ := List.getElem?_eq_some_iff.mp haeq
    have hget : w[a] = b := (List.getElem?_eq_some_iff.mp haeq).2
    have hdrop := chainWalk_drop h haeq
    have hparx : w[a].parent = x := by rw [hget]; exact hbpar
    -- hdrop : chainWalk boxes (n - (a+1)) x = w.drop (a+1), and chainWalk boxes n x = w
    by_cases hsuf : w.drop (a + 1) = []
    · -- T[a] is the last box: b.parent = x = ""
      have hlen : a + 1 = w.length := by
        have hl : (w.drop (a + 1)).length = w.length - (a + 1) := List.length_drop
        rw [hsuf, List.length_nil] at hl
        omega
      have hlastget : w.getLast? = some b := by
        rw [List.getLast?_eq_getElem?, show w.length - 1 = a from by omega]
        exact haeq
      have hbp : b.parent = "" := chainWalk_last_parent_val w b hlastget hg
      exact hx (hbpar.symm.trans hbp)
    · have hsufne : w.drop (a + 1) ≠ [] := hsuf
      have hlt : w.length > (a + 1) := by
        by_cases hcon : w.length ≤ (a + 1)
        · exfalso
          apply hsufne
          have hl : (w.drop (a + 1)).length = w.length - (a + 1) := List.length_drop
          have h0 : w.length - (a + 1) = 0 := by omega
          rw [h0] at hl
          exact List.eq_nil_of_length_eq_zero hl
        · omega
      have hsuffT : (w.drop (a + 1)).getLast?.map (·.parent) = some "" := by
        rw [List.getLast?_drop, ite_eq_right (by omega)]
        exact hg
      have hdet : w.drop (a + 1) = w :=
        chainWalk_det (M := n - (a + 1)) (K := n) (p := x) (X := w.drop (a + 1))
          (Y := w) (by rw [hbpar] at hdrop; exact hdrop) hsufne hsuffT h hwne hg
      have hl : (w.drop (a + 1)).length = w.length - (a + 1) := List.length_drop
      rw [hdet] at hl
      have hpos : 0 < w.length := List.length_pos_iff.mpr hwne
      have := Nat.sub_lt hpos (by omega)
      omega
  -- count: w ⊆ boxes.erase b
  have hsub : ∀ e ∈ w, e ∈ boxes.erase b := by
    intro e he
    have heb : e ∈ boxes := chainWalk_mem n x e (by rw [h]; exact he)
    have hne : e ≠ b := by
      intro hcon
      exact hbnot (hcon ▸ he)
    exact (List.mem_erase_of_ne hne).mpr heb
  have hlen := nodup_length_le_of_subset w (boxes.erase b) hwnodup hsub
  have herase := List.length_erase_of_mem hbmem
  rw [herase] at hlen
  have hpos : 0 < boxes.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hbmem)
  omega

/-- Depth bound for `chainTerm`: a successful chain from a parent pointer that
starts below some box terminates within `boxes.length - 1` fuel. -/
theorem chainTerm_depth {n : Nat} {x : String} {b : ModelBox}
    (h : chainTerm boxes n x = true) (hb : b ∈ boxes) (hbx : b.parent = x) :
    chainTerm boxes (boxes.length - 1) x = true := by
  by_cases hx : x = ""
  · subst hx
    exact chainTerm.eq_1 _ _
  · rcases chainWalk_of_chainTerm n x h with hxe | ⟨w, hw, hgt⟩
    · exact absurd hxe hx
    · have hlenBound := chainWalk_length_bound hw hgt hx ⟨b, hb, hbx⟩
      have hK := chainWalk_stable_all boxes (boxes.length - 1) x w n hw
        (by intro hcon; rw [hcon] at hgt; simp at hgt) hgt hlenBound
      exact chainTerm_of_chainWalk (boxes.length - 1) x w hK hgt

end DepthLemma

section ParentClosed

/-- Upward fuel monotonicity of `chainTerm`: more fuel never turns a
terminating parent chain into a failing one. -/
theorem chainTerm_mono {boxes : List ModelBox} :
    ∀ (n : Nat) (id : String), chainTerm boxes n id = true →
      ∀ (m : Nat), n ≤ m → chainTerm boxes m id = true := by
  intro n
  induction n with
  | zero =>
      intro id h m _
      by_cases hid : id = ""
      · subst hid; exact chainTerm.eq_1 _ _
      · rw [chainTerm.eq_2 _ _ hid] at h
        simp at h
  | succ n ih =>
      intro id h m hm
      by_cases hid : id = ""
      · subst hid; exact chainTerm.eq_1 _ _
      · obtain ⟨m', hm'eq⟩ : ∃ m' : Nat, m = m' + 1 := ⟨m - 1, by omega⟩
        subst hm'eq
        rw [chainTerm.eq_3 _ _ _ hid] at h
        cases hf : boxes.findIdx? (fun b0 : ModelBox => b0.id == id) with
        | none => simp only [hf] at h; simp at h
        | some i =>
            simp only [hf] at h
            cases hgo : boxes[i]? with
            | none => simp only [hgo] at h; simp at h
            | some b =>
                simp only [hgo] at h
                rw [chainTerm.eq_3 _ _ _ hid]
                simp only [hf, hgo]
                exact ih b.parent h m' (by omega)

/-- `WellFormed` makes every box parent either empty or resolving inside the
box list. -/
theorem parents_resolve_of_wellFormed {m : Model} (hwf : WellFormed m) :
    ∀ b ∈ m.boxes, b.parent = "" ∨ ∃ p ∈ m.boxes, p.id = b.parent := by
  intro b hb
  exact parent_induction m hwf (fun id => id = "" ∨ ∃ p ∈ m.boxes, p.id = id)
    (Or.inl rfl) (fun b hbmem _ => Or.inr ⟨b, hbmem, rfl⟩) b hb

/-- Under parent resolution and unique ids, `parentChainEnds` success is
`chainTerm` success: the only difference between the two walks is the
missing-box case, which resolution rules out. -/
theorem chainTerm_of_parentChainEnds {boxes : List ModelBox}
    (hnodup : (boxes.map (·.id)).Nodup)
    (hres : ∀ b ∈ boxes, b.parent = "" ∨ ∃ p ∈ boxes, p.id = b.parent) :
    ∀ (fuel : Nat) (id : String),
      Treemap.parentChainEnds boxes fuel id = true →
      (∃ b ∈ boxes, b.parent = id) →
      chainTerm boxes fuel id = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro id h _
      by_cases hid : id = ""
      · subst hid; exact chainTerm.eq_1 _ _
      · rw [Treemap.parentChainEnds.eq_2 boxes id hid] at h
        simp at h
  | succ fuel ih =>
      intro id h hstart
      by_cases hid : id = ""
      · subst hid; exact chainTerm.eq_1 _ _
      · obtain ⟨s, hsmem, hsp⟩ := hstart
        cases hf : boxes.find? (fun b0 : ModelBox => b0.id == id) with
        | none =>
            rcases hres s hsmem with hc0 | ⟨p, hpmem, hpid⟩
            · exact absurd (hsp.symm.trans hc0) hid
            · rw [List.find?_eq_none] at hf
              have hnone := hf p hpmem
              rw [hpid, hsp] at hnone
              simp at hnone
        | some p0 =>
            rw [Treemap.parentChainEnds.eq_3 boxes id fuel hid, hf] at h
            have h0mem : p0 ∈ boxes := List.mem_of_find?_eq_some hf
            have h0id : p0.id = id := by simpa using List.find?_some hf
            have hstep := ih p0.parent h ⟨p0, h0mem, rfl⟩
            rw [chainTerm.eq_3 boxes id fuel hid]
            cases hf2 : boxes.findIdx? (fun b0 : ModelBox => b0.id == id) with
            | none =>
                have hnone := List.findIdx?_eq_none_iff.mp hf2 p0 h0mem
                rw [h0id] at hnone
                simp at hnone
            | some i =>
                obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf2
                have hqi : boxes[i].id = id := beq_iff_eq.mp hmatch
                have hqmem : boxes[i] ∈ boxes := List.getElem_mem hlt
                have hq : boxes[i] = p0 := eq_of_mem_id hnodup hqmem h0mem (hqi.trans h0id.symm)
                simp only [List.getElem?_eq_getElem hlt, hq]
                exact hstep

/-- `InputFacts` of an input whose model is well-formed: unique ids, resolved
parents, and parent chains that terminate within the box list. -/
theorem inputFacts_of_wellFormed {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) : InputFacts inp := by
  have hres := parents_resolve_of_wellFormed (m := inputModel inp o) hwf
  refine ⟨Model.boxIds_nodup hwf, hres, ?_⟩
  intro b hb n hn
  have hpc := Treemap.Containment.wellFormed_parentChainEnds hwf b hb
  have hct := chainTerm_of_parentChainEnds (Model.boxIds_nodup hwf) hres
    (inputModel inp o).boxes.length b.parent hpc ⟨b, hb, rfl⟩
  by_cases hbp : b.parent = ""
  · rw [hbp]; exact chainTerm.eq_1 _ _
  · rcases chainWalk_of_chainTerm _ _ hct with h0 | ⟨w, hwalk, hgt⟩
    · exact absurd h0 hbp
    · have hlenEq : (inputModel inp o).boxes.length = inp.boxes.length := rfl
      have hlenBound := chainWalk_length_bound hwalk hgt hbp ⟨b, hb, rfl⟩
      have hstable := chainWalk_stable_all inp.boxes n b.parent w
        (inputModel inp o).boxes.length hwalk
        (by intro hcon; rw [hcon] at hgt; simp at hgt) hgt (by omega)
      exact chainTerm_of_chainWalk n b.parent w hstable hgt

end ParentClosed

section ParentClosedFinal

/-! ### `InputFacts` transports through `selectInput` -/

/-- `InputFacts` only quantifies over the box list, so it transfers across
record updates that leave `boxes` fixed. -/
theorem inputFacts_congr {p q : Input} (h : p.boxes = q.boxes) (hf : InputFacts p) :
    InputFacts q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← h]; exact hf.nodup
  · intro b hb
    rw [← h] at hb ⊢
    exact hf.parents b hb
  · intro b hb n hn
    rw [← h] at hb hn ⊢
    exact hf.term b hb n hn

/-- The `InputFacts` invariant of a `selectInput` sub-input, from the input's
own facts plus the keep-closure of the selection: kept boxes either root at
the selection root or keep their parent inside the selection. -/
theorem selectInput_facts (inp : Input) (keep : ModelBox → Bool) (root : String)
    (hf : InputFacts inp)
    (hclose : ∀ b ∈ inp.boxes, keep b = true →
      b.parent = "" ∨ (b.parent == root) = true ∨
        ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true) :
    InputFacts (selectInput inp keep root) := by
  refine ⟨?_, ?_, ?_⟩
  · exact selectInput_boxes_nodup keep root hf.nodup
  · intro b hb
    obtain ⟨m, hm, hkm, _, hbpar⟩ := selectInput_box_spec inp keep root hb
    rw [hbpar]
    split
    · exact Or.inl rfl
    · rename_i hneRoot
      rcases hclose m hm hkm with hc0 | hc1 | ⟨q2, hq2, hq2id, hkq2⟩
      · exact Or.inl hc0
      · simp [hneRoot] at hc1
      · obtain ⟨img, himg, himgId, _⟩ := selectInput_box_exists inp keep root hq2 hkq2
        exact Or.inr ⟨img, himg, himgId.trans hq2id⟩
  · intro b hb n hn
    -- termination at the source-length fuel transports to any fuel past the
    -- sub-input's own length: the terminating walk from `b.parent` avoids `b`,
    -- so its length is at most `sel.boxes.length - 1`; `chainWalk_fuel_exact`
    -- runs it at exactly that fuel and `chainTerm_mono` lifts to `n`.
    have hbase := selectInput_chainTerm inp keep root hf hclose
      (inp.boxes.length - 1) (by omega) b hb
    by_cases hx : b.parent = ""
    · rw [hx]; exact chainTerm.eq_1 _ _
    · rcases chainWalk_of_chainTerm (boxes := (selectInput inp keep root).boxes)
        (inp.boxes.length - 1) b.parent hbase with h0 | ⟨w, hw, hgt⟩
      · exact absurd h0 hx
      · have hbound := chainWalk_length_bound hw hgt hx ⟨b, hb, rfl⟩
        have hfuel := chainWalk_fuel_exact (selectInput inp keep root).boxes
          (inp.boxes.length - 1) b.parent w hw hgt
        have htermW := chainTerm_of_chainWalk w.length b.parent w hfuel hgt
        exact chainTerm_mono w.length b.parent htermW n (by omega)

/-- The inside-selection sub-input keeps the `InputFacts` invariant. -/
theorem selectInput_facts_inside (inp : Input) (group : ModelBox) (hf : InputFacts inp) :
    InputFacts (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) :=
  selectInput_facts inp _ group.id hf
    (fun _c hc hkept => keepInside_close (group := group.id) hf hc hkept)

/-- The outside-selection sub-input keeps the `InputFacts` invariant. -/
theorem selectInput_facts_outside (inp : Input) (group : ModelBox) (hf : InputFacts inp) :
    InputFacts (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "") :=
  selectInput_facts inp _ "" hf
    (fun _c hc hkept => keepOutside_close (group := group.id) hf hc hkept)

/-- Every box id of a `selectInput` sub-input is an id of the source input. -/
theorem selectInput_ids_subset (inp : Input) (keep : ModelBox → Bool) (root : String)
    {id : String} (hid : id ∈ (selectInput inp keep root).boxes.map (·.id)) :
    id ∈ inp.boxes.map (·.id) := by
  obtain ⟨sb, hsb, hsbid⟩ := List.mem_map.mp hid
  obtain ⟨m, hm, _, hmid, _⟩ := selectInput_box_spec inp keep root hsb
  exact List.mem_map.mpr ⟨m, hm, hmid.symm.trans hsbid⟩

/-- Membership in a keyed filterMap from a successful lookup: the source
element with a matching key witnesses the result element. -/
theorem filterMap_mem_of_find {α β : Type} (keyA : α → String) (src : List α)
    (keyB : β → String) (items : List β) (a : α) (ha : a ∈ src) (b : β)
    (hfind : items.find? (fun it => keyB it == keyA a) = some b) :
    b ∈ src.filterMap fun m => items.find? (fun it => keyB it == keyA m) :=
  List.mem_filterMap.mpr ⟨a, ha, hfind⟩

/-! ### Parent closure of `expandChild` and `layoutRecursive` -/

/-- Flat layouts keep every scene box's parent inside the scene: scene ids
are exactly the input ids and nonempty input parents resolve to input boxes. -/
theorem layout_parent_closed {inp : Input} {o : Options} {res : FamilyResult}
    (hf : InputFacts inp) (h : layout inp o = .ok res) :
    SceneParentClosed res.scene := by
  intro bb hbb
  obtain ⟨hidsB, _⟩ := layout_ids h
  obtain ⟨sb, hsb, _, hsbpar⟩ := layout_scene_box_parent h bb hbb
  rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
  · rw [hsbpar]; exact Or.inl h0
  · have hqidIn : q.id ∈ res.scene.boxes.map (·.id) := by
      rw [hidsB]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨bb', hbb', hbb'id⟩ := List.mem_map.mp hqidIn
    rw [hsbpar]
    exact Or.inr ⟨bb', hbb', hbb'id.trans hqid⟩

/-- `expandChild` keeps every nonempty parent pointer of the merged scene
inside the merged scene, given parent closure of both source scenes, coverage
of every nonempty source parent pointer by an input id, and a box named
`group.id` in the result. The rewritten child roots resolve to that box;
deeper child boxes and parent boxes resolve through the input-id coverage. -/
theorem expandChild_parent_closed {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int} {parent child result : FamilyResult}
    (hparentClosed : SceneParentClosed parent.scene)
    (hchildClosed : SceneParentClosed child.scene)
    (hchildCover : ∀ q ∈ child.scene.boxes, q.parent ≠ "" →
      q.parent ∈ inp.boxes.map (·.id))
    (hparentCover : ∀ q ∈ parent.scene.boxes, q.parent ≠ "" →
      q.parent ∈ inp.boxes.map (·.id))
    (hgroupRes : ∃ q ∈ result.scene.boxes, q.id = group.id)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    SceneParentClosed result.scene := by
  obtain ⟨_, _metric, _titleLines, _lines, dx, dy, _hframe, _, _, _, _, _, _, hboxes⟩ :=
    expandChild_sources h
  intro bb hbb
  rw [hboxes] at hbb
  obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hbb
  have hbbItems : bb ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hfind
  rcases List.mem_append.mp hbbItems with hbc | hbp
  · -- embedded child box: the parent projection rewrites only empty roots
    obtain ⟨cb, hcbmem, hE⟩ := List.mem_map.mp hbc
    have hproj : bb.parent = (if cb.parent == "" then group.id else cb.parent) := by
      have hpar := congrArg (fun bx : Box => bx.parent) hE
      simpa [embedBox] using hpar.symm
    by_cases hcb0 : cb.parent = ""
    · rw [hproj]
      split
      · rcases hgroupRes with ⟨q, hqmem, hqid⟩
        exact Or.inr ⟨q, hqmem, hqid⟩
      · rename_i hcond
        exact absurd (beq_iff_eq.mpr hcb0) hcond
    · rw [hproj]
      split
      · rename_i hcond
        exact absurd (beq_iff_eq.mp hcond) hcb0
      · rcases hchildClosed cb hcbmem with h0 | ⟨q, hqmem, hqid⟩
        · exact absurd h0 hcb0
        · obtain ⟨model2, hm2, hm2id⟩ := List.mem_map.mp (hchildCover cb hcbmem hcb0)
          cases hF2 : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
              parent.scene.boxes).find? (fun box => box.id == cb.parent) with
          | none =>
              have hnone := List.find?_eq_none.mp hF2 (embedBox group.id dx dy q)
                (List.mem_append_left _ (List.mem_map.mpr ⟨q, hqmem, rfl⟩))
              have hidEq : (embedBox group.id dx dy q).id = cb.parent := by
                simpa [embedBox] using hqid
              rw [hidEq] at hnone
              simp at hnone
          | some f =>
              refine Or.inr ⟨f, ?_, ?_⟩
              · rw [hboxes]
                exact filterMap_mem_of_find (fun m : ModelBox => m.id) inp.boxes
                  (fun bx : Box => bx.id) _ model2 hm2 f (by rw [hm2id]; exact hF2)
              · simpa using List.find?_some hF2
  · -- parent scene box: the parent pointer survives verbatim
    rcases hparentClosed bb hbp with h0 | ⟨q, hqmem, hqid⟩
    · exact Or.inl h0
    · by_cases hne : bb.parent = ""
      · exact Or.inl hne
      · rcases List.mem_map.mp (hparentCover bb hbp hne) with ⟨model2, hm2, hm2id⟩
        cases hF2 : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes).find? (fun box => box.id == bb.parent) with
        | none =>
            have hnone := List.find?_eq_none.mp hF2 q (List.mem_append_right _ hqmem)
            rw [← hqid] at hnone
            simp at hnone
        | some f =>
            refine Or.inr ⟨f, ?_, ?_⟩
            · rw [hboxes]
              exact filterMap_mem_of_find (fun m : ModelBox => m.id) inp.boxes
                (fun bx : Box => bx.id) _ model2 hm2 f (by rw [hm2id]; exact hF2)
            · simpa using List.find?_some hF2

/-- Coverage: every nonempty parent pointer of a result scene box names an
input box id of the laid-out input. -/
theorem layoutRecursive_parent_in_ids :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursive fuel inp o = .ok res →
      ∀ p ∈ res.scene.boxes, p.parent ≠ "" → p.parent ∈ inp.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h p hp hne
      obtain ⟨sb, hsb, _, hsbpar⟩ := layout_scene_box_parent h p hp
      rw [hsbpar] at hne ⊢
      rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
      · exact absurd h0 hne
      · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  | succ fuel ih =>
      intro inp o res hf h p hp hne
      rcases layoutRecursive_succ h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · obtain ⟨sb, hsb, _, hsbpar⟩ := layout_scene_box_parent hlayout p hp
        rw [hsbpar] at hne ⊢
        rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
        · exact absurd h0 hne
        · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      · obtain ⟨_, _metric, _titleLines, _lines, dx, dy, _hframe, _, _, _, _, _, _,
          hboxes⟩ := expandChild_sources hexpand
        rw [hboxes] at hp
        obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hp
        have hfound : p ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hfound with hcb | hpb
        · obtain ⟨cb, hcbmem, hE⟩ := List.mem_map.mp hcb
          have hproj : p.parent = (if cb.parent == "" then group.id else cb.parent) := by
            have hpar := congrArg (fun bx : Box => bx.parent) hE
            simpa [embedBox] using hpar.symm
          by_cases hcb0 : cb.parent = ""
          · rw [hproj]
            split
            · exact List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some hg, rfl⟩
            · rename_i hcond
              exact absurd (beq_iff_eq.mpr hcb0) hcond
          · rw [hproj]
            split
            · rename_i hcond
              exact absurd (beq_iff_eq.mp hcond) hcb0
            · have hchildFacts := selectInput_facts_inside inp group hf
              have hcov := ih _ _ _ hchildFacts hchild cb hcbmem hcb0
              exact selectInput_ids_subset inp
                (fun box => Compound.inside inp.boxes group.id box.id) group.id hcov
        · have hparentFacts : InputFacts { selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) with
              fixedSizes := a, fixedChildren := b, fixedAreas := c } :=
            inputFacts_congr
              (rfl : (selectInput inp
                (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes =
                  { selectInput inp
                    (fun box => !Compound.inside inp.boxes group.id box.id) with
                    fixedSizes := a, fixedChildren := b, fixedAreas := c }.boxes)
              (selectInput_facts_outside inp group hf)
          have hpIn := ih _ _ _ hparentFacts hparent p hpb hne
          exact selectInput_ids_subset inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" hpIn

/-- `layoutRecursive` keeps every nonempty parent pointer of the produced
scene inside that scene. The leaf case is the flat argument; the expansion
case transports the invariant through both `selectInput` sub-inputs and
merges with `expandChild_parent_closed`. -/
theorem layoutRecursive_parent_closed :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursive fuel inp o = .ok res →
      SceneParentClosed res.scene := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h
      exact layout_parent_closed hf h
  | succ fuel ih =>
      intro inp o res hf h
      rcases layoutRecursive_succ h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · exact layout_parent_closed hf hlayout
      · have hchildFacts := selectInput_facts_inside inp group hf
        have hparentFacts : InputFacts { selectInput inp
            (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } :=
          inputFacts_congr
            (rfl : (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes =
                { selectInput inp
                  (fun box => !Compound.inside inp.boxes group.id box.id) with
                  fixedSizes := a, fixedChildren := b, fixedAreas := c }.boxes)
            (selectInput_facts_outside inp group hf)
        have hcc := ih _ _ _ hchildFacts hchild
        have hpc := ih _ _ _ hparentFacts hparent
        have hcoverC : ∀ q ∈ child.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hci := layoutRecursive_parent_in_ids fuel
            (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
              group.id) _ child hchildFacts hchild q hq hne
          exact selectInput_ids_subset inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
        have hcoverP : ∀ q ∈ parent.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hpi := layoutRecursive_parent_in_ids fuel { selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) with
              fixedSizes := a, fixedChildren := b, fixedAreas := c } _ parent
            hparentFacts hparent q hq hne
          exact selectInput_ids_subset inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" hpi
        have hgroupRes : ∃ q ∈ res.scene.boxes, q.id = group.id := by
          obtain ⟨frame, _, _, _, dx, dy, hframe, _, _, _, _, _, _, hboxes⟩ :=
            expandChild_sources hexpand
          have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
          cases hF : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
              parent.scene.boxes).find? (fun box => box.id == group.id) with
          | none =>
              have hnone := List.find?_eq_none.mp hF frame
                (List.mem_append_right _ (List.mem_of_find?_eq_some hframe))
              rw [hframeId] at hnone
              simp at hnone
          | some f =>
              refine ⟨f, ?_, ?_⟩
              · rw [hboxes]
                exact filterMap_mem_of_find (fun m : ModelBox => m.id) inp.boxes
                  (fun bx : Box => bx.id) _ group (List.mem_of_find?_eq_some hg) f hF
              · simpa using List.find?_some hF
        exact expandChild_parent_closed hpc hcc hcoverC hcoverP hgroupRes hexpand

/-- Parent closedness of a successful recursive layout, from the
well-formedness of the original input model alone. -/
theorem layoutRecursive_parent_closed_wellFormed {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) :
    ∀ (fuel : Nat) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res → SceneParentClosed res.scene := by
  intro fuel res h
  exact layoutRecursive_parent_closed fuel inp o res (inputFacts_of_wellFormed hwf) h

/-- Discharge of `ExpandChildC2Step` for an `expandChild` call
`layoutRecursive` performs: the `ExpandChildCallContext` supplies the
well-formedness, group witness, parent-input box list, and the two recursive
successes; `hsub` re-establishes well-formedness of both sub-inputs; and
`layoutRecursive_parent_closed_wellFormed` discharges the scene
parent-closedness the step cannot derive. `hids` stays a premise on the
input: `modelWellFormed` does not reject empty box ids. -/
theorem expandChild_c2_step_of_context
    (hsub : SubInputWellFormedC2)
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {group : ModelBox} {P : Params} {child parent : FamilyResult}
    {titleLines : List Measure.Line} {titleHeight : Int}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    ExpandChildC2Step P inp o group titleHeight parent child res := by
  obtain ⟨hwf, hgroup, hpboxes, hchild, hparent, hexpand⟩ := hctx
  obtain ⟨hchildWf, hparentWf⟩ := hsub inp o group hwf
  have hclosed : SceneParentClosed parent.scene ∧ SceneParentClosed child.scene :=
    ⟨layoutRecursive_parent_closed_wellFormed (hparentWf _ _ _) fuel parent hparent,
     layoutRecursive_parent_closed_wellFormed hchildWf fuel child hchild⟩
  exact expandChild_c2_step_of_recursion (hwf := hwf) (hids := hids)
    (hclosed := hclosed) (hgroup := hgroup) (hpboxes := hpboxes)
    (hchild := hchild) (hparent := hparent) hexpand

/-- The C2 instance of the recursive-lift `hgeo` hypothesis: every
`expandChild` call `layoutRecursive` performs satisfies `ExpandChildC2Step`,
discharged from the `ExpandChildCallContext` the recursion supplies.  This is
the `hgeo` argument `layoutRecursive_c2_of_flat` consumes; `hsub` is the named
premise the flat/seam layer owns, and the nonempty ids arrive per call. -/
theorem hgeo_of_recursion (hsub : SubInputWellFormedC2) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC2Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res _hexpand
    hidsIn hctx
  exact expandChild_c2_step_of_context hsub hidsIn hctx

end ParentClosedFinal
