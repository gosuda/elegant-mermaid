import Elegant.Layered.PipelineFacts
import Elegant.Layered.SizingFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Component coverage for the layered family

`PipelineImpl.components g` partitions the node indices of `g` by the union-find style
labels produced by `labelPass`/`labelsFix`.  This file proves that every node index below
`g.nodes.length` belongs to at least one reported component, provided every edge endpoint
stays below the node count (true for measured graphs, see `measuredGraph_edges_bounded`).
It also exposes the structural facts the scene integration needs:
`measuredGraph_nodes_length_ge`, `sceneExecution_edges_bounded`, and
`sceneExecution_parts_entry` (the exact consequent of the packing coverage premise).
-/

/-! ### Undirected step and depth-bounded connectivity -/

/-- Undirected step along an edge of `edges` whose endpoints are both below `n`. -/
def edgeStep (edges : List Edge) (n a b : Nat) : Prop :=
  ∃ e ∈ edges,
    (a = e.tail ∧ b = e.head ∨ a = e.head ∧ b = e.tail) ∧
    e.tail < n ∧ e.head < n

theorem edgeStep_symm {edges : List Edge} {n a b : Nat} (h : edgeStep edges n a b) :
    edgeStep edges n b a := by
  obtain ⟨e, he, hdir, hta, htb⟩ := h
  refine ⟨e, he, ?_, hta, htb⟩
  rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

/-- Depth-bounded undirected connectivity: `Conn edges n d a b` holds when `b` is reachable
from `a` in at most `d` undirected steps, through nodes below `n`. -/
inductive Conn (edges : List Edge) (n : Nat) : Nat → Nat → Nat → Prop
  | refl (a : Nat) : a < n → Conn edges n 0 a a
  | step {d a b c : Nat} : Conn edges n d a b → edgeStep edges n b c →
      Conn edges n (d + 1) a c

/-- Depth-exact transitivity of `Conn`. -/
theorem conn_trans {edges : List Edge} {n : Nat} (d d' : Nat) (a b : Nat) :
    ∀ c, Conn edges n d a b → Conn edges n d' b c → Conn edges n (d + d') a c := by
  induction d' with
  | zero =>
    intro c h h'
    cases h' with
    | refl x _ => exact h
  | succ d' ih =>
    intro c h h'
    cases h' with
    | step hprev hstep => exact Conn.step (ih _ h hprev) hstep

theorem Conn_symm {edges : List Edge} {n : Nat} :
    ∀ (d a b : Nat), Conn edges n d a b →
      ∃ d', Conn edges n d' b a ∧ d' ≤ d + 1 := by
  intro d
  induction d with
  | zero =>
    intro a b h
    cases h
    exact ⟨0, Conn.refl _ (by assumption), by omega⟩
  | succ d ih =>
    intro a b h
    cases h with
    | step hprev hstep =>
      obtain ⟨e, he, hdir, hbt, hbc⟩ := hstep
      rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        subst h2
        have hcon1 : Conn edges n 1 e.head e.tail :=
          Conn.step (Conn.refl e.head hbc)
            (edgeStep_symm ⟨e, he, Or.inl ⟨rfl, rfl⟩, hbt, hbc⟩)
        obtain ⟨d', hd', hdle⟩ := ih _ _ hprev
        exact ⟨1 + d', conn_trans 1 d' e.head e.tail a hcon1 hd', by omega⟩
      · subst h1
        subst h2
        have hcon1 : Conn edges n 1 e.tail e.head :=
          Conn.step (Conn.refl e.tail hbt)
            (edgeStep_symm ⟨e, he, Or.inr ⟨rfl, rfl⟩, hbt, hbc⟩)
        obtain ⟨d', hd', hdle⟩ := ih _ _ hprev
        exact ⟨1 + d', conn_trans 1 d' e.tail e.head a hcon1 hd', by omega⟩

/-! ### Array primitives for the label fold -/

private theorem get_set!_oob {l : Array Nat} {i v : Nat} (h : l.size ≤ i) :
    (l.set! i v)[i]! = l[i]! := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le h]

private theorem range_getElem! {n x : Nat} (h : x < n) : (Array.range n)[x]! = x := by
  have hx : (Array.range n)[x]? = some x := by
    rw [Array.getElem?_range]
    split
    · rfl
    · exact absurd h (by omega)
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hx]
  rfl

/-- One sequential edge step of `labelPass`, with the runtime `let` reduced away. -/
private def passStep (l : Array Nat) (e : Edge) : Array Nat :=
  (l.set! e.tail (min l[e.tail]! l[e.head]!)).set! e.head (min l[e.tail]! l[e.head]!)

private theorem labelPass_eq (edges : List Edge) (lab : Array Nat) :
    labelPass edges lab = edges.foldl passStep lab := rfl

private theorem passStep_get_eq {l : Array Nat} {e : Edge} {x : Nat}
    (hx : x = e.tail ∨ x = e.head) :
    (passStep l e)[x]! = min l[e.tail]! l[e.head]! := by
  simp only [passStep]
  rcases hx with rfl | rfl
  · by_cases hne : e.head = e.tail
    · rw [hne]
      by_cases hb : e.tail < l.size
      · rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!]; exact hb)]
      · rw [get_set!_oob (by rw [Array.size_set!]; omega), get_set!_oob (by omega)]
        omega
    · by_cases hb : e.tail < l.size
      · rw [Array.getElem!_set!_ne _ _ _ _ hne, Array.getElem!_set!_self _ _ _ hb]
      · rw [Array.getElem!_set!_ne _ _ _ _ hne, get_set!_oob (by omega)]
        have h0 : l[e.tail]! = 0 := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none_iff.mpr (by omega)]
          simp
        omega
  · by_cases hne : e.head = e.tail
    · rw [hne]
      by_cases hb : e.tail < l.size
      · rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!]; exact hb)]
      · rw [get_set!_oob (by rw [Array.size_set!]; omega), get_set!_oob (by omega)]
        omega
    · by_cases hb : e.head < l.size
      · rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!]; exact hb)]
      · rw [get_set!_oob (by rw [Array.size_set!]; omega),
          Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        have h0 : l[e.head]! = 0 := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none_iff.mpr (by omega)]
          simp
        omega

private theorem passStep_get_ne {l : Array Nat} {e : Edge} {x : Nat}
    (hx : x ≠ e.tail) (hx2 : x ≠ e.head) : (passStep l e)[x]! = l[x]! := by
  simp only [passStep]
  rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hx2), Array.getElem!_set!_ne _ _ _ _ (Ne.symm hx)]

private theorem passStep_get_head_le {l : Array Nat} (e : Edge) :
    (passStep l e)[e.head]! ≤ l[e.tail]! := by
  rw [passStep_get_eq (Or.inr rfl)]
  omega

private theorem passStep_get_tail_le {l : Array Nat} (e : Edge) :
    (passStep l e)[e.tail]! ≤ l[e.head]! := by
  rw [passStep_get_eq (Or.inl rfl)]
  omega

private theorem foldl_passStep_le_of_le :
    ∀ (es : List Edge) (l : Array Nat) (c x : Nat), l[x]! ≤ c →
      (es.foldl passStep l)[x]! ≤ c := by
  intro es
  induction es with
  | nil => intro l c x h; exact h
  | cons e es ih =>
    intro l c x h
    rw [List.foldl_cons]
    refine ih (passStep l e) c x ?_
    by_cases hx : x = e.tail
    · subst hx
      rw [passStep_get_eq (Or.inl rfl)]
      omega
    · by_cases hx2 : x = e.head
      · subst hx2
        rw [passStep_get_eq (Or.inr rfl)]
        omega
      · rw [passStep_get_ne hx hx2]
        exact h

private theorem labelPass_le_start {edges : List Edge} (lab : Array Nat) (x : Nat) :
    (labelPass edges lab)[x]! ≤ lab[x]! := by
  rw [labelPass_eq]
  exact foldl_passStep_le_of_le edges lab (lab[x]!) x (Nat.le_refl _)

private theorem foldl_passStep_mem_head_le :
    ∀ (es : List Edge) (e : Edge), e ∈ es → ∀ l : Array Nat,
      (es.foldl passStep l)[e.head]! ≤ l[e.tail]! := by
  intro es
  induction es with
  | nil => intro e he; exact absurd he (by simp)
  | cons a es ih =>
    intro e he l
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with heq | he'
    · subst e
      exact Nat.le_trans (foldl_passStep_le_of_le es (passStep l a) _ a.head
        (Nat.le_refl _)) (passStep_get_head_le a)
    · exact Nat.le_trans (ih e he' (passStep l a))
        (foldl_passStep_le_of_le [a] l (l[e.tail]!) e.tail (Nat.le_refl _))

private theorem foldl_passStep_mem_tail_le :
    ∀ (es : List Edge) (e : Edge), e ∈ es → ∀ l : Array Nat,
      (es.foldl passStep l)[e.tail]! ≤ l[e.head]! := by
  intro es
  induction es with
  | nil => intro e he; exact absurd he (by simp)
  | cons a es ih =>
    intro e he l
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with heq | he'
    · subst e
      exact Nat.le_trans (foldl_passStep_le_of_le es (passStep l a) _ a.tail
        (Nat.le_refl _)) (passStep_get_tail_le a)
    · exact Nat.le_trans (ih e he' (passStep l a))
        (foldl_passStep_le_of_le [a] l (l[e.head]!) e.head (Nat.le_refl _))

private theorem labelPass_edge_head_le {edges : List Edge} {e : Edge} (he : e ∈ edges)
    (lab : Array Nat) : (labelPass edges lab)[e.head]! ≤ lab[e.tail]! := by
  rw [labelPass_eq]
  exact foldl_passStep_mem_head_le edges e he lab

private theorem labelPass_edge_tail_le {edges : List Edge} {e : Edge} (he : e ∈ edges)
    (lab : Array Nat) : (labelPass edges lab)[e.tail]! ≤ lab[e.head]! := by
  rw [labelPass_eq]
  exact foldl_passStep_mem_tail_le edges e he lab

private theorem labelsFix_le {edges : List Edge} :
    ∀ (f : Nat) (lab : Array Nat) (x : Nat), (labelsFix edges f lab)[x]! ≤ lab[x]! := by
  intro f
  induction f with
  | zero => intro lab x; exact Nat.le_refl _
  | succ f ih =>
    intro lab x
    show (labelsFix edges f (labelPass edges lab))[x]! ≤ lab[x]!
    exact Nat.le_trans (ih (labelPass edges lab) x) (labelPass_le_start lab x)

private theorem labelsFix_pass_commute {edges : List Edge} :
    ∀ (f : Nat) (lab : Array Nat),
      labelsFix edges f (labelPass edges lab) = labelPass edges (labelsFix edges f lab) := by
  intro f
  induction f with
  | zero => intro lab; rfl
  | succ f ih =>
    intro lab
    show labelsFix edges f (labelPass edges (labelPass edges lab))
      = labelPass edges (labelsFix edges f (labelPass edges lab))
    rw [ih (labelPass edges lab)]

/-- One pull across the final pass: the head of an edge after `f + 1` passes never exceeds
the tail after `f` passes. -/
private theorem labelsFix_step_pull {edges : List Edge} (lab : Array Nat) {f y x : Nat}
    {e : Edge} (he : e ∈ edges)
    (hmatch : (y = e.tail ∧ x = e.head) ∨ (y = e.head ∧ x = e.tail)) :
    (labelsFix edges (f + 1) lab)[x]! ≤ (labelsFix edges f lab)[y]! := by
  show (labelsFix edges f (labelPass edges lab))[x]! ≤ (labelsFix edges f lab)[y]!
  rw [labelsFix_pass_commute f lab]
  rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact labelPass_edge_head_le he (labelsFix edges f lab)
  · exact labelPass_edge_tail_le he (labelsFix edges f lab)

/-- The upper-bound transport along a `Conn` derivation: every step consumes one pass. -/
private theorem labelPull {edges : List Edge} {n μ : Nat} (lab : Array Nat) :
    ∀ d k x, Conn edges n d μ x →
      (labelsFix edges (k + d) lab)[x]! ≤ (labelsFix edges k lab)[μ]! := by
  intro d
  induction d with
  | zero =>
    intro k x hconn
    cases hconn with
    | refl _ _ => rw [Nat.add_zero]; exact Nat.le_refl _
  | succ d ih =>
    intro k x hconn
    cases hconn with
    | step hprev hstep =>
      obtain ⟨e, he, hdir, hbt, hbx⟩ := hstep
      rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        subst h2
        have hf : k + (d + 1) = k + d + 1 := by omega
        rw [hf]
        refine Nat.le_trans (labelsFix_step_pull lab he (Or.inl ⟨rfl, rfl⟩)) ?_
        exact ih k e.tail hprev
      · subst h1
        subst h2
        have hf : k + (d + 1) = k + d + 1 := by omega
        rw [hf]
        refine Nat.le_trans (labelsFix_step_pull lab he (Or.inr ⟨rfl, rfl⟩)) ?_
        exact ih k e.head hprev

/-! ### Lower bound: labels never drop below the connected minimum -/

private theorem passStep_lower {edges : List Edge} {n v μ : Nat} {l : Array Nat}
    (hbd : ∀ e ∈ edges, e.tail < n ∧ e.head < n)
    (hl : ∀ x, (∃ d, Conn edges n d v x) → x < n → l[x]! ≥ μ)
    (e : Edge) (he : e ∈ edges)
    (x : Nat) (hcx : ∃ d, Conn edges n d v x) (hxn : x < n) :
    (passStep l e)[x]! ≥ μ := by
  obtain ⟨d, hcx'⟩ := hcx
  by_cases hxt : x = e.tail
  · subst hxt
    obtain ⟨htn, hhn⟩ := hbd e he
    have hch : ∃ d', Conn edges n d' v e.head :=
      ⟨d + 1, Conn.step hcx' ⟨e, he, Or.inl ⟨rfl, rfl⟩, htn, hhn⟩⟩
    have h1 := hl e.tail ⟨d, hcx'⟩ htn
    have h2 := hl e.head hch hhn
    rw [passStep_get_eq (Or.inl rfl)]
    omega
  · by_cases hxh : x = e.head
    · subst hxh
      obtain ⟨htn, hhn⟩ := hbd e he
      have hct : ∃ d', Conn edges n d' v e.tail :=
        ⟨d + 1, Conn.step hcx' (edgeStep_symm ⟨e, he, Or.inl ⟨rfl, rfl⟩, htn, hhn⟩)⟩
      have h1 := hl e.tail hct htn
      have h2 := hl e.head ⟨d, hcx'⟩ hhn
      rw [passStep_get_eq (Or.inr rfl)]
      omega
    · rw [passStep_get_ne hxt hxh]
      exact hl x ⟨d, hcx'⟩ hxn

private theorem foldl_passStep_lower {edges : List Edge} {n v μ : Nat}
    (hbd : ∀ e ∈ edges, e.tail < n ∧ e.head < n) :
    ∀ (es : List Edge) (l : Array Nat), (∀ e ∈ es, e ∈ edges) →
      (∀ x, (∃ d, Conn edges n d v x) → x < n → l[x]! ≥ μ) →
      ∀ x, (∃ d, Conn edges n d v x) → x < n → (es.foldl passStep l)[x]! ≥ μ := by
  intro es
  induction es with
  | nil => intro l _ hl x hcx hxn; exact hl x hcx hxn
  | cons e es ih =>
    intro l hmem hl x hcx hxn
    rw [List.foldl_cons]
    exact ih (passStep l e) (fun g hg => hmem g (List.mem_cons_of_mem _ hg))
      (passStep_lower hbd hl e (hmem e List.mem_cons_self)) x hcx hxn

private theorem labelsFix_lower {edges : List Edge} {n v μ : Nat}
    (hbd : ∀ e ∈ edges, e.tail < n ∧ e.head < n)
    (_hμ : ∀ x, (∃ d, Conn edges n d v x) → x < n → μ ≤ x) :
    ∀ (f : Nat) (arr : Array Nat),
      (∀ y, (∃ d, Conn edges n d v y) → y < n → arr[y]! ≥ μ) →
      ∀ (x : Nat), (∃ d, Conn edges n d v x) → x < n →
        (labelsFix edges f arr)[x]! ≥ μ := by
  intro f
  induction f with
  | zero => intro arr hinv x hcx hxn; exact hinv x hcx hxn
  | succ f ih =>
    intro arr hinv x hcx hxn
    have hinv' : ∀ y, (∃ d, Conn edges n d v y) → y < n → (labelPass edges arr)[y]! ≥ μ :=
      foldl_passStep_lower hbd edges arr (fun _ he => he) hinv
    exact ih (labelPass edges arr) hinv' x hcx hxn

/-! ### Least connected node -/

/-- Every nonempty `Nat`-predicate has a least witness (classical; only `Classical.choice`
is used). -/
private theorem exists_least {P : Nat → Prop} (hnonempty : ∃ x, P x) :
    ∃ μ, P μ ∧ ∀ x, P x → μ ≤ x := by
  refine Classical.byContradiction fun hnone => ?_
  have hdesc : ∀ k, P k → ∃ j, P j ∧ j < k := by
    intro k hk
    refine Classical.byContradiction fun hno => ?_
    have hleast : ∀ x, P x → k ≤ x := by
      intro x hx
      refine Classical.byContradiction fun hxlt => ?_
      exact hno ⟨x, hx, by omega⟩
    exact hnone ⟨k, hk, hleast⟩
  have hmain : ∀ N k, k < N → P k → False := by
    intro N
    induction N with
    | zero => intro k hk _; exact absurd hk (Nat.not_lt_zero k)
    | succ N ih =>
      intro k hk hPk
      obtain ⟨j, hj, hjlt⟩ := hdesc k hPk
      exact ih j (by omega) hj
  obtain ⟨x0, hx0⟩ := hnonempty
  exact hmain (x0 + 1) x0 (Nat.lt_succ_self x0) hx0

/-! ### Depth trimming: connectivity within depth at most `n - 1` -/

private theorem conn_split {edges : List Edge} {n : Nat} :
    ∀ (d a b : Nat), Conn edges n d a b → ∀ i, i ≤ d →
      ∃ p, p < n ∧ Conn edges n i a p ∧ Conn edges n (d - i) p b := by
  intro d
  induction d with
  | zero =>
    intro a b h i hi
    cases i with
    | zero =>
      cases h
      exact ⟨_, (by assumption), Conn.refl _ (by assumption),
        Conn.refl _ (by assumption)⟩
    | succ i' => exact absurd hi (by omega)
  | succ d ih =>
    intro a b h i hi
    cases h with
    | step hprev hstep =>
      obtain ⟨e, he, hdir, hbt, hbc⟩ := hstep
      by_cases hic : i ≤ d
      · obtain ⟨p, hplt, hc1, hc2⟩ := ih a _ hprev i hic
        refine ⟨p, hplt, hc1, ?_⟩
        have heq : d + 1 - i = d - i + 1 := by omega
        rw [heq]
        exact Conn.step hc2 ⟨e, he, hdir, hbt, hbc⟩
      · have hie : i = d + 1 := by omega
        subst hie
        refine ⟨b, ?_, Conn.step hprev ⟨e, he, hdir, hbt, hbc⟩, ?_⟩
        · rcases hdir with ⟨_, h2⟩ | ⟨_, h2⟩
          · rw [h2]; exact hbc
          · rw [h2]; exact hbt
        · rw [Nat.sub_self]
          exact Conn.refl b (by
            rcases hdir with ⟨_, h2⟩ | ⟨_, h2⟩
            · rw [h2]; exact hbc
            · rw [h2]; exact hbt)

/-- Pigeonhole for index sequences: `d + 1` values below `n` with `n ≤ d` repeat. -/
private theorem pigeon_repeat :
    ∀ (n d : Nat), n ≤ d → ∀ p : Nat → Nat, (∀ i, i ≤ d → p i < n) →
      ∃ i j, i < j ∧ j ≤ d ∧ p i = p j := by
  intro n
  induction n with
  | zero =>
    intro d _ p pall
    exact absurd (pall 0 (Nat.zero_le d)) (by omega)
  | succ n ih =>
    intro d hle p pall
    by_cases hex : ∃ i, i < d ∧ p i = p d
    · obtain ⟨i, hi, hpi⟩ := hex
      exact ⟨i, d, hi, by omega, hpi⟩
    · obtain ⟨i, j, hij, hjd, heq⟩ :=
        ih (d - 1) (by omega)
          (fun k => if p k < p d then p k else p k - 1)
          (fun k hk => by
            have hpdlt : p d < n + 1 := pall d (by omega)
            have hpklt : p k < n + 1 := pall k (by omega)
            have pne : p k ≠ p d := by
              intro hce
              exact hex ⟨k, by omega, hce⟩
            by_cases hlt : p k < p d
            · have hif : (if p k < p d then p k else p k - 1) = p k := by simp [hlt]
              have hpkn : p k ≠ n := by
                intro hce
                omega
              omega
            · have hif : (if p k < p d then p k else p k - 1) = p k - 1 := by simp [hlt]
              omega)
      refine ⟨i, j, hij, by omega, ?_⟩
      have hine : p i ≠ p d := by
        intro hce
        exact hex ⟨i, by omega, hce⟩
      have hjne : p j ≠ p d := by
        intro hce
        exact hex ⟨j, by omega, hce⟩
      split at heq
      · split at heq
        · exact heq
        · omega
      · split at heq
        · omega
        · omega

/-- Any two nodes connected by a long walk are connected by a walk of depth at most
`n - 1`. -/
private theorem conn_trim {edges : List Edge} {n : Nat} :
    ∀ (d a b : Nat), Conn edges n d a b →
      ∃ e, e ≤ n - 1 ∧ Conn edges n e a b := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro a b h
    by_cases hle : d ≤ n - 1
    · exact ⟨d, hle, h⟩
    · have hdn : n ≤ d := by omega
      have hn : 0 < n := by
        cases h with
        | refl _ ha => omega
        | step hp hs =>
          obtain ⟨e, _, _, ht, _⟩ := hs
          omega
      have hall : ∀ i : Nat,
          ∃ q, q < n ∧ (i ≤ d → Conn edges n i a q ∧ Conn edges n (d - i) q b) := by
        intro i
        by_cases hic : i ≤ d
        · obtain ⟨q, hq1, hq2, hq3⟩ := conn_split d a b h i hic
          exact ⟨q, hq1, fun _ => ⟨hq2, hq3⟩⟩
        · exact ⟨0, hn, fun hi => absurd hi hic⟩
      let p := fun i => Classical.choose (hall i)
      have hpi : ∀ i, p i < n ∧
          (i ≤ d → Conn edges n i a (p i) ∧ Conn edges n (d - i) (p i) b) :=
        fun i => Classical.choose_spec (hall i)
      obtain ⟨i, j, hij, hjd, hij2⟩ :=
        pigeon_repeat n d hdn p (fun i _ => (hpi i).1)
      have hc1 := ((hpi i).2 (by omega)).1
      have hc4 := ((hpi j).2 hjd).2
      rw [← hij2] at hc4
      exact ih (i + (d - j)) (by omega) a b
        (conn_trans i (d - j) a (p i) b hc1 hc4)

/-! ### Component coverage -/

/-- After the full label fold, a node carries the least index of its connected class. -/
private theorem componentLab_least {g : Graph} {v μ : Nat}
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    (hv : v < g.nodes.length) (hμlt : μ < g.nodes.length)
    (hconn : ∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d v μ)
    (hμle : ∀ x, (∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d v x) →
      x < g.nodes.length → μ ≤ x) :
    (componentLab g)[v]! = μ := by
  obtain ⟨E, hE⟩ : ∃ x : List Edge, x = g.edges ++ Compound.constraints g := ⟨_, rfl⟩
  rw [← hE] at hbd hconn hμle
  obtain ⟨d₁, hd₁⟩ := hconn
  obtain ⟨d₂, hd₂le, hd₂⟩ := conn_trim d₁ v μ hd₁
  obtain ⟨d₃, hd₃, hd₃le⟩ := Conn_symm d₂ v μ hd₂
  have hlabdef : (componentLab g)
      = labelsFix E (g.nodes.length + 1) (Array.range g.nodes.length) := by
    rw [hE]
    rfl
  have hLB := labelsFix_lower hbd hμle
  have hinit : ∀ y, (∃ d, Conn E g.nodes.length d v y) →
      y < g.nodes.length → (Array.range g.nodes.length)[y]! ≥ μ := by
    intro y hdconn hy
    rw [range_getElem! hy]
    exact hμle y hdconn hy
  have hLBv : (componentLab g)[v]! ≥ μ := by
    rw [hlabdef]
    exact hLB (g.nodes.length + 1) (Array.range g.nodes.length)
      hinit v ⟨0, Conn.refl v hv⟩ hv
  have hUBv : (componentLab g)[v]! ≤ μ := by
    obtain ⟨k, hk⟩ : ∃ k, g.nodes.length + 1 = k + d₃ :=
      ⟨g.nodes.length + 1 - d₃, by omega⟩
    rw [hlabdef, hk]
    refine Nat.le_trans (labelPull (Array.range g.nodes.length) d₃ k v hd₃) ?_
    have h2 := labelsFix_le (edges := E) k (Array.range g.nodes.length) μ
    rw [range_getElem! hμlt] at h2
    exact h2
  exact Nat.le_antisymm hUBv hLBv

/-- Every node of a bounded graph belongs to a reported component.  The edge-bound premise
`hbd` is discharged for measured graphs by `measuredGraph_edges_bounded`. -/
theorem components_cover {g : Graph} {v : Nat} (hv : v < g.nodes.length)
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length) :
    ∃ comp ∈ components g, v ∈ comp := by
  obtain ⟨μ, hPμ, hμmin⟩ := exists_least
    (P := fun x => x < g.nodes.length ∧
      ∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d v x)
    ⟨v, hv, 0, Conn.refl v hv⟩
  obtain ⟨hμlt, d₁, hd₁⟩ := hPμ
  have hμle : ∀ x, (∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d v x) →
      x < g.nodes.length → μ ≤ x := fun x hd hx => hμmin x ⟨hx, hd⟩
  have hvμ := componentLab_least hbd hv hμlt ⟨d₁, hd₁⟩ hμle
  have hμμ : (componentLab g)[μ]! = μ :=
    componentLab_least hbd hμlt hμlt ⟨0, Conn.refl μ hμlt⟩
      (fun x ⟨d, hd⟩ hx => hμle x ⟨d₁ + d, conn_trans d₁ d v μ x hd₁ hd⟩ hx)
  refine ⟨(List.range g.nodes.length).filter (fun w => (componentLab g)[w]! == μ),
    ?_, mem_componentOf.mpr ⟨hv, hvμ⟩⟩
  rw [components_eq]
  exact List.mem_map.mpr ⟨μ, mem_componentRoots.mpr ⟨hμlt, hμμ⟩, rfl⟩

/-- The two endpoints of a graph or compound-constraint edge lie in one reported component. -/
theorem components_edge_endpoints {g : Graph} {e : Edge}
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    (he : e ∈ g.edges ++ Compound.constraints g) :
    ∃ comp ∈ components g, e.tail ∈ comp ∧ e.head ∈ comp := by
  have htail := (hbd e he).1
  have hhead := (hbd e he).2
  have hstep : edgeStep (g.edges ++ Compound.constraints g) g.nodes.length e.tail e.head :=
    ⟨e, he, Or.inl ⟨rfl, rfl⟩, htail, hhead⟩
  have hconnTH : Conn (g.edges ++ Compound.constraints g) g.nodes.length 1 e.tail e.head :=
    Conn.step (Conn.refl e.tail htail) hstep
  have hconnHT : Conn (g.edges ++ Compound.constraints g) g.nodes.length 1 e.head e.tail :=
    Conn.step (Conn.refl e.head hhead) (edgeStep_symm hstep)
  obtain ⟨μ, hPμ, hμmin⟩ := exists_least
    (P := fun x => x < g.nodes.length ∧
      ∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d e.tail x)
    ⟨e.tail, htail, 0, Conn.refl e.tail htail⟩
  obtain ⟨hμlt, d₁, hd₁⟩ := hPμ
  have hμtail : ∀ x,
      (∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d e.tail x) →
      x < g.nodes.length → μ ≤ x := fun x hd hx => hμmin x ⟨hx, hd⟩
  have hμhead : ∀ x,
      (∃ d, Conn (g.edges ++ Compound.constraints g) g.nodes.length d e.head x) →
      x < g.nodes.length → μ ≤ x := fun x ⟨d, hd⟩ hx =>
    hμtail x ⟨1 + d, conn_trans 1 d e.tail e.head x hconnTH hd⟩ hx
  have hlabTail := componentLab_least hbd htail hμlt ⟨d₁, hd₁⟩ hμtail
  have hlabHead := componentLab_least hbd hhead hμlt
    ⟨1 + d₁, conn_trans 1 d₁ e.head e.tail μ hconnHT hd₁⟩ hμhead
  have hlabμ : (componentLab g)[μ]! = μ :=
    componentLab_least hbd hμlt hμlt ⟨0, Conn.refl μ hμlt⟩
      (fun x ⟨d, hd⟩ hx => hμtail x ⟨d₁ + d, conn_trans d₁ d e.tail μ x hd₁ hd⟩ hx)
  refine ⟨(List.range g.nodes.length).filter (fun w => (componentLab g)[w]! == μ),
    ?_, mem_componentOf.mpr ⟨htail, hlabTail⟩, mem_componentOf.mpr ⟨hhead, hlabHead⟩⟩
  rw [components_eq]
  exact List.mem_map.mpr ⟨μ, mem_componentRoots.mpr ⟨hμlt, hlabμ⟩, rfl⟩

/-! ### Boundedness of measured-graph edges -/

private theorem findIdx?_lt_length {α : Type} {p : α → Bool} :
    ∀ (l : List α) (i : Nat), l.findIdx? p = some i → i < l.length := by
  intro l
  induction l with
  | nil =>
    intro i h
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons x xs ih =>
    intro i h
    rw [List.findIdx?_cons] at h
    split at h
    · simp at h
      subst h
      simp
    · cases hx : xs.findIdx? p with
      | none => rw [hx] at h; simp at h
      | some j =>
        rw [hx] at h
        simp at h
        have hbound := ih j hx
        have hlen : (x :: xs).length = xs.length + 1 := List.length_cons ..
        omega

private theorem edgeOf_tail_head_lt {inp : Input} {r : ModelRoute} {i : Nat} {e : Edge}
    (h : edgeOf inp r i = .ok e) :
    e.tail < inp.boxes.length ∧ e.head < inp.boxes.length := by
  unfold edgeOf at h
  cases h1 : inp.boxes.findIdx? (fun b => b.id == r.fromId) with
  | none => rw [h1] at h; simp at h
  | some a =>
    cases h2 : inp.boxes.findIdx? (fun b => b.id == r.toId) with
    | none => rw [h1, h2] at h; simp at h
    | some b =>
      rw [h1, h2] at h
      simp at h
      cases h
      exact ⟨findIdx?_lt_length inp.boxes a h1,
        findIdx?_lt_length inp.boxes b h2⟩

private theorem graphEdges_mem_bounds (inp : Input) :
    ∀ (rs : List ModelRoute) (k : Nat) (es : List Edge),
      graphEdgesFrom inp k rs = .ok es →
      ∀ e ∈ es, e.tail < inp.boxes.length ∧ e.head < inp.boxes.length := by
  intro rs
  induction rs with
  | nil =>
    intro k es h e he
    simp only [graphEdgesFrom] at h
    simp at h
    subst h
    simp at he
  | cons r rs ih =>
    intro k es h e he
    unfold graphEdgesFrom at h
    obtain ⟨edge, hedge, h⟩ := bind_ok h
    obtain ⟨edges, hedges, h⟩ := bind_ok h
    have hr := Except.ok.inj h
    subst hr
    rcases List.mem_cons.mp he with rfl | he'
    · exact edgeOf_tail_head_lt hedge
    · exact ih (k + 1) edges hedges e he'

private theorem drop_getElem {α : Type} : ∀ (l : List α) (i : Nat) (hi : i < l.length),
    ∃ rest, l.drop i = l[i]'hi :: rest := by
  intro l
  induction l with
  | nil => intro i hi; simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => exact ⟨xs, rfl⟩
    | succ i' =>
      have hi' : i' < xs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      obtain ⟨rest, hrest⟩ := ih i' hi'
      exact ⟨rest, hrest⟩

private theorem group_count_take_lt (boxes : List ModelBox) (i : Nat) (box : ModelBox)
    (hbi : boxes[i]? = some box) (hgrp : box.role = .group) :
    ((boxes.take i).filter (fun b : ModelBox => b.role == .group)).length + 1 ≤
      (boxes.filter (fun b : ModelBox => b.role == .group)).length := by
  have hbox : boxes[i]'((List.getElem?_eq_some_iff.mp hbi).1) = box :=
    (List.getElem?_eq_some_iff.mp hbi).2
  obtain ⟨rest, hdrop⟩ := drop_getElem boxes i (List.getElem?_eq_some_iff.mp hbi).1
  have hrw : (boxes.filter (fun b : ModelBox => b.role == .group)).length =
      ((boxes.take i ++ boxes.drop i).filter
        (fun b : ModelBox => b.role == .group)).length := by
    rw [List.take_append_drop]
  rw [hrw, List.filter_append, hdrop, hbox,
    List.filter_cons_of_pos (by simp [hgrp])]
  simp only [List.length_append, List.length_cons]
  omega

private theorem length_zipIdx_filter_eq {α : Type} (p : α → Bool) (l : List α) :
    (l.zipIdx.filter (fun q : α × Nat => p q.1)).length = (l.filter p).length := by
  have hgen : ∀ (m : List α) (k : Nat),
      ((m.zipIdx k).filter (fun q : α × Nat => p q.1)).map
        (fun q : α × Nat => q.1) = m.filter p := by
    intro m
    induction m with
    | nil => intro k; simp
    | cons x xs ih =>
      intro k
      simp only [List.zipIdx_cons]
      cases hp : p x with
      | true => simp [hp, ih]
      | false => simp [hp, ih]
  rw [← List.length_map (fun q : α × Nat => q.1), hgen l 0]

private theorem endpoint_lt (boxes : List ModelBox) (src : Bool) (i j n : Nat)
    (hi : i < boxes.length)
    (hG : boxes.length +
        (boxes.filter (fun b : ModelBox => b.role == .group)).length = n) :
    Compound.endpoint boxes src i j < n := by
  unfold Compound.endpoint
  by_cases hb1 : boxes[i]? = none
  · rw [hb1]
    exact Nat.lt_of_lt_of_le hi (by omega)
  · obtain ⟨box, hbi⟩ : ∃ box, boxes[i]? = some box := by
      cases hh : boxes[i]? with
      | none => exact absurd hh hb1
      | some box => exact ⟨box, rfl⟩
    rw [hbi]
    cases hbj : boxes[j]? with
    | none =>
      change i < n
      exact Nat.lt_of_lt_of_le hi (by omega)
    | some target =>
      show (if box.role != .group || i == j then i
          else
            let contains := Compound.inside boxes box.id target.id
            if src == contains then i else Compound.bottomIndex boxes i) < n
      split
      · exact Nat.lt_of_lt_of_le hi (by omega)
      · rename_i hcond
        have hgrp : box.role = .group := by
          by_cases hb : box.role = .group
          · exact hb
          · exfalso
            have hne : (box.role != .group) = true := by simp [hb]
            simp [hne] at hcond
        dsimp only
        split
        · exact Nat.lt_of_lt_of_le hi (by omega)
        · have hcount := group_count_take_lt boxes i box hbi hgrp
          unfold Compound.bottomIndex
          omega

theorem constraints_bounded (g : Graph) :
    ∀ e ∈ Compound.constraints g, e.tail < g.nodes.length ∧ e.head < g.nodes.length := by
  have hzlt : ∀ q : Node × Nat, q ∈ g.nodes.zipIdx → q.2 < g.nodes.length := by
    intro q hq
    have hget : g.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
    exact (List.getElem?_eq_some_iff.mp hget).1
  intro e he
  unfold Compound.constraints at he
  dsimp only at he
  obtain ⟨top, htop, hmatch⟩ := List.mem_flatMap.mp he
  have htopz : top ∈ g.nodes.zipIdx := (List.mem_filter.mp htop).1
  have htoplt := hzlt top htopz
  cases hfind : g.nodes.zipIdx.find? (fun q => q.1.border == 2 && q.1.decl == top.1.decl) with
  | none => rw [hfind] at hmatch; cases hmatch
  | some bottom =>
    rw [hfind] at hmatch
    dsimp only at hmatch
    have hbotz : bottom ∈ g.nodes.zipIdx := List.mem_of_find?_eq_some hfind
    have hbotlt := hzlt bottom hbotz
    have hmembers : ∀ member : Node × Nat,
        member ∈ g.nodes.zipIdx.filter
          (fun q => q.1.border == 0 && q.1.clusterPath.contains top.1.decl) →
        member.2 < g.nodes.length := fun member hmem =>
      hzlt member (List.mem_filter.mp hmem).1
    have hchildren : ∀ child : Node × Nat,
        child ∈ ((g.nodes.zipIdx.filter fun q => q.1.border == -2).filter
          fun q => q.1.clusterPath.dropLast == top.1.clusterPath) →
        child.2 < g.nodes.length := fun child hc =>
      hzlt child (List.mem_filter.mp (List.mem_filter.mp hc).1).1
    split at hmatch
    · rcases List.mem_cons.mp hmatch with hcase | hcase
      · rw [hcase]
        exact ⟨htoplt, hbotlt⟩
      · cases hcase
    · rcases List.mem_append.mp hmatch with hleaf | hnested
      · obtain ⟨member, hmem2, hmem3⟩ := List.mem_flatMap.mp hleaf
        have hmlt := hmembers member hmem2
        rcases List.mem_cons.mp hmem3 with hcase | hcase
        · rw [hcase]
          exact ⟨htoplt, hmlt⟩
        · rcases List.mem_cons.mp hcase with hcase | hcase
          · rw [hcase]
            exact ⟨hmlt, hbotlt⟩
          · cases hcase
      · obtain ⟨child, hchildmem, hchildmatch⟩ := List.mem_flatMap.mp hnested
        have hclt := hchildren child hchildmem
        cases hf2 :
            g.nodes.zipIdx.find? (fun q => q.1.border == 2 && q.1.decl == child.1.decl) with
        | none => rw [hf2] at hchildmatch; cases hchildmatch
        | some childBottom =>
          rw [hf2] at hchildmatch
          dsimp only at hchildmatch
          have hcblt :=
            hzlt childBottom (List.mem_of_find?_eq_some hf2)
          rcases List.mem_cons.mp hchildmatch with hcase | hcase
          · rw [hcase]
            exact ⟨htoplt, hclt⟩
          · rcases List.mem_cons.mp hcase with hcase | hcase
            · rw [hcase]
              exact ⟨hcblt, hbotlt⟩
            · cases hcase

/-! ### Measured graph lengths and the scene-execution bridge -/

private theorem mapM_ok_length {err α β : Type} (f : α → Except err β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

theorem measuredGraph_nodes_length_ge {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (h : measuredGraph P inp o lines = .ok g0)
    (hlines : lines.length = inp.boxes.length) :
    inp.boxes.length ≤ g0.nodes.length := by
  unfold measuredGraph at h
  obtain ⟨nodes0, hn0, h⟩ := bind_ok h
  obtain ⟨edges, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  have h0 : nodes0.length = lines.length := by
    simp only [sizedNodes] at hn0
    exact (mapM_ok_length _ _ _ hn0).trans List.length_zipIdx
  have h1 : nodes.length = lines.length := by
    calc nodes.length = ((nodes0.map (orientNode o.direction)).zipIdx).length :=
          mapM_ok_length _ _ _ hnodes
      _ = (nodes0.map (orientNode o.direction)).length := List.length_zipIdx
      _ = nodes0.length := List.length_map ..
      _ = lines.length := h0
  have h2 := Compound.prepare_nodes_length_ge
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun (fixed : String × Size) => fixed.1 == box.id) then
          { box with role := .node }
        else box)
      P.clusterPad
      (lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * P.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      ⟨nodes, edges, P.slot⟩
  change inp.boxes.length ≤ (Compound.prepare _ _ _ ⟨nodes, edges, P.slot⟩).nodes.length
  exact Nat.le_trans (by simpa only [h1, hlines] using Nat.le_refl nodes.length) h2

theorem measuredGraph_edges_bounded {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (h : measuredGraph P inp o lines = .ok g0)
    (hlines : lines.length = inp.boxes.length) :
    ∀ e ∈ g0.edges, e.tail < g0.nodes.length ∧ e.head < g0.nodes.length := by
  unfold measuredGraph at h
  obtain ⟨nodes0, hn0, h⟩ := bind_ok h
  obtain ⟨edges, hes, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  generalize hgm : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun (fixed : String × Size) => fixed.1 == box.id) then
        { box with role := .node }
      else box) = mapped
  have hGlen : mapped.length = inp.boxes.length := by
    rw [← hgm]
    exact List.length_map ..
  have hnodeslen : nodes.length = inp.boxes.length := by
    have h0 : nodes0.length = lines.length := by
      simp only [sizedNodes] at hn0
      exact (mapM_ok_length _ _ _ hn0).trans List.length_zipIdx
    have h1 := mapM_ok_length _ _ _ hnodes
    simpa only [List.length_zipIdx, List.length_map, h0, hlines] using h1
  have hMn : ∀ (b : List ModelBox) (t : List (Int × Int)),
      (Compound.markNodes b P.clusterPad t nodes).length =
        nodes.length + (b.filter (fun bx : ModelBox => bx.role == .group)).length := by
    intro b t
    simp only [Compound.markNodes_length]
    exact congrArg (nodes.length + ·)
      (length_zipIdx_filter_eq (fun bx : ModelBox => bx.role == .group) b)
  intro e he
  unfold Compound.prepare at he
  dsimp only at he
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
  obtain ⟨ht, hh⟩ := graphEdges_mem_bounds inp inp.routes 0 edges hes e₀ he₀
  simp only [Compound.aliasEdge]
  constructor
  · exact endpoint_lt mapped true e₀.tail e₀.head _
      (by rw [hGlen]; exact ht)
      (by simp only [Compound.prepare, hMn, hnodeslen, hGlen])
  · exact endpoint_lt mapped false e₀.head e₀.tail _
      (by rw [hGlen]; exact hh)
      (by simp only [Compound.prepare, hMn, hnodeslen, hGlen])

/-! ### Scene-execution bridge -/

private theorem sceneExecution_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length := mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

theorem sceneExecution_graph_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {i : Nat} (hi : i < inp.boxes.length) :
    i < execution.graph.nodes.length := by
  have h1 := measuredGraph_nodes_length_ge execution.graph_eq
    (sceneExecution_lines_len execution)
  omega

theorem sceneExecution_edges_bounded {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧ e.head < execution.graph.nodes.length := by
  have hlines := sceneExecution_lines_len execution
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact measuredGraph_edges_bounded execution.graph_eq hlines e he
  · exact constraints_bounded execution.graph e he

private theorem componentCandidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (comp.map (fun v => g.nodes.getD v default)).length = comp.length
  exact List.length_map ..

private theorem placeComponent_rects_length (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run cursor labels loops).rects.length = cg.nodes.length := by
  unfold placeComponent
  simp [List.length_map, List.length_range]

private theorem mem_zip_intro {α β : Type} {l : List α} {l' : List β} {i : Nat}
    {a : α} {b : β} (h1 : l[i]? = some a) (h2 : l'[i]? = some b) : (a, b) ∈ l.zip l' := by
  induction l generalizing l' i with
  | nil => rw [List.getElem?_nil] at h1; exact absurd h1 (by simp)
  | cons x xs ih =>
    cases l' with
    | nil => rw [List.getElem?_nil] at h2; exact absurd h2 (by simp)
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at h1 h2
        simp only [Option.some.injEq] at h1 h2
        subst h1
        subst h2
        exact Or.inl ⟨rfl, rfl⟩
      | succ i' =>
        rw [List.getElem?_cons_succ] at h1 h2
        exact Or.inr (ih h1 h2)

/-- The exact consequent of the packing coverage premise: every box index is owned by an
entry of some reported part. -/
theorem sceneExecution_parts_entry {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {i : Nat} (hi : i < inp.boxes.length) :
    ∃ part ∈ execution.componentsAcc.parts,
      ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometry hempty execution.components_eq
  have hin := sceneExecution_graph_len execution hi
  obtain ⟨comp, hcomp, hiv⟩ := components_cover hin (sceneExecution_edges_bounded execution)
  have hmem : comp ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hm]
    exact hcomp
  obtain ⟨part, hpart, hpc⟩ := List.mem_map.mp hmem
  obtain ⟨index, chosen, run, loops, area, _, _, _, _, _, hpartdef⟩ := hall part hpart
  have hrectlen : part.2.rects.length = comp.length := by
    rw [hpartdef]
    change (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects.length = comp.length
    rw [placeComponent_rects_length, componentCandidate_nodes_length, hpc]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hiv
  have hjlt : j < comp.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjrect : j < part.2.rects.length := by rw [hrectlen]; exact hjlt
  refine ⟨part, hpart, (i, part.2.rects[j]'hjrect), ?_, rfl⟩
  apply mem_zip_intro
  · simpa only [hpc] using hj
  · exact List.getElem?_eq_some_iff.mpr ⟨hjrect, rfl⟩

end PipelineImpl
end Layered
end Elegant
