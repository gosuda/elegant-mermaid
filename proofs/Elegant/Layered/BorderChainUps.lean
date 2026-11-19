import Elegant.Layered.BorderChainBlock

set_option autoImplicit false

/-!
# BorderChainUps for the chains the executed pipeline produces (layered-107)

`BorderChainBlock.borderChainBlock_of_ups` reduces layered-107 to the executed
pipeline fact `BorderChainUps`: for one border chain `chain` of one cluster, in
each of the four Brandes-Köpf passes `k < 4`, the pass-oriented list `ordered`
is nodup, a permutation of `chain`, its head has `up = none`, and every later
element has `up` equal to its immediate predecessor in `ordered`.

Contents:

* `OccurringBorderChain` — the shape of the border chains the executed pipeline
  produces (at most one node per rank, adjacent ranks, all on the pass layers).
* `OrderedByCtx` — `ordered` is the chain sorted by the pass context's
  `(rank, pos)` order, the order in which `alignAll` processes the chain.
* `BorderChainPick` — the named hypothesis for the executed median pick: per
  chain node, the pick at the node's actual fold point (running `last` computed
  by `foldLast`) selects nothing for the chain head and selects the chain
  predecessor through a border-alignment edge otherwise. The edge premise is
  `border_alignment_chain_edge`, the marking premise
  `typeOneConflicts_borderChain_unmarked`, and the median-position premise the
  sibling cluster order rule of layered-106 (`order_border_ends`,
  `order_siblings_consistent`); the remaining `last < pos` bookkeeping is the
  executed behaviour this hypothesis isolates.
* proved lemmas about the sort and about the layer fold's `up` updates, and the
  assembly `borderChainUps_of_pick`.
-/

namespace Elegant.Layered
open Elegant.Layered.CoordsImpl

/-- The pass-context sort key: ascending `(rank, pos)`. -/
def keyLe (c : Ctx) (a b : Nat) : Bool :=
  c.rank[a]! < c.rank[b]! || (c.rank[a]! == c.rank[b]! && c.pos[a]! ≤ c.pos[b]!)

/-- `ordered` is `chain` sorted by the pass context's `(rank, pos)` order: the
order in which `alignAll` processes the chain nodes. For `k < 2` the layers are
kept and odd layers reversed; for `k ≥ 2` the layer order is reversed and even
layers reversed, so `(rank, pos)` ascending is exactly the pass's processing
order in all four passes. -/
def OrderedByCtx (c : Ctx) (chain ordered : List Nat) : Prop :=
  ordered = chain.mergeSort (keyLe c)

/-- The border chain of one cluster side that the executed pipeline produces:
the nodes are distinct, all lie on the pass layers, at most one node per rank,
and consecutive chain nodes sit on adjacent ranks so that
`border_alignment_chain_edge` supplies the border edge between them. -/
structure OccurringBorderChain (c : Ctx) (chain : List Nat) : Prop where
  nodup : chain.Nodup
  flat : ∀ v ∈ chain, v ∈ c.layers.flatten
  rank_inj : ∀ u ∈ chain, ∀ w ∈ chain, c.rank[u]! = c.rank[w]! → u = w
  rank_adj : ∀ u ∈ chain, ∀ v ∈ chain, u ≠ v →
    c.rank[u]! + 1 = c.rank[v]! ∨ c.rank[v]! + 1 = c.rank[u]!

/-- The pass-context predecessor of `v` on the chain: the unique chain node one
rank below `v`. For the chain head (minimal rank) there is none. -/
def chainPred (c : Ctx) (chain : List Nat) (v : Nat) : Option Nat :=
  chain.find? fun u => c.rank[u]! + 1 = c.rank[v]!

/-- The accumulated alignment state after the first `i` layers of the pass. -/
def foldToLayer (c : Ctx) (i : Nat) : Al := (c.layers.take i).foldl (alignLayer c) Al.init

/-- The running `last` value of the pass fold at the point just before the
node at layer `i`, position `j` is processed. -/
def foldLast (c : Ctx) (i : Nat) (j : Nat) : Int :=
  ((c.layers.getD i []).take j |>.foldl (alignNode c) (foldToLayer c i, -1)).2

/-- The executed median pick on a border chain node (layered-106's sibling
cluster order rule transported to the position-sorted candidate list): at each
chain node's fold point, the head picks nothing and every later node picks its
chain predecessor through a border-alignment edge. -/
structure BorderChainPick (c : Ctx) (chain : List Nat)
    (_hocc : OccurringBorderChain c chain) : Prop where
  head_none : ∀ v ∈ chain, chainPred c chain v = none →
    alignPick c v (foldLast c (c.rank[v]!) (c.pos[v]!)) = none
  pick : ∀ v ∈ chain, ∀ pred, chainPred c chain v = some pred →
    ∃ eb, eb < c.edges.size ∧
      ((c.edges[eb]!.head = v ∧ c.edges[eb]!.tail = pred) ∨
        (c.edges[eb]!.tail = v ∧ c.edges[eb]!.head = pred)) ∧
      alignPick c v (foldLast c (c.rank[v]!) (c.pos[v]!)) = some pred

/-! ## Sort facts -/

theorem rank_pos_of_keyLe {c : Ctx} {a b : Nat} (h : keyLe c a b = true) :
    c.rank[a]! ≤ c.rank[b]! ∧ (c.rank[a]! = c.rank[b]! → c.pos[a]! ≤ c.pos[b]!) := by
  unfold keyLe at h
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with h0 | ⟨h1, h2⟩
  · exact ⟨Nat.le_of_lt h0, fun he => by omega⟩
  · exact ⟨by omega, fun _ => h2⟩

theorem keyLe_trans (c : Ctx) : ∀ a b d : Nat, keyLe c a b = true → keyLe c b d = true →
    keyLe c a d = true := by
  intro a b d h1 h2
  obtain ⟨r1, _⟩ := rank_pos_of_keyLe h1
  obtain ⟨r2, _⟩ := rank_pos_of_keyLe h2
  by_cases hr : c.rank[a]! < c.rank[d]!
  · unfold keyLe
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hr
  · have heq : c.rank[a]! = c.rank[d]! := by omega
    have hba : c.rank[b]! = c.rank[a]! := by omega
    have hpa := (rank_pos_of_keyLe h1).2 hba.symm
    have hpd := (rank_pos_of_keyLe h2).2 (hba.trans heq)
    unfold keyLe
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true]
    exact Or.inr ⟨heq, by omega⟩

theorem keyLe_total (c : Ctx) : ∀ a b : Nat, keyLe c a b || keyLe c b a = true := by
  intro a b
  rcases Nat.lt_or_ge (c.rank[a]!) (c.rank[b]!) with h | h
  · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
    unfold keyLe
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true]
    omega
  · rcases Nat.lt_or_ge (c.rank[b]!) (c.rank[a]!) with h' | h''
    · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
      unfold keyLe
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true]
      omega
    · have hra : c.rank[a]! = c.rank[b]! := by omega
      rcases Nat.le_total (c.pos[a]!) (c.pos[b]!) with hp | hp
      · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
        unfold keyLe
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true]
        omega
      · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
        unfold keyLe
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true]
        omega

theorem orderedByCtx_perm {c : Ctx} {chain ordered : List Nat}
    (h : OrderedByCtx c chain ordered) : ordered.Perm chain := by
  unfold OrderedByCtx at h
  rw [h]
  exact List.mergeSort_perm _ _

theorem orderedByCtx_nodup {c : Ctx} {chain ordered : List Nat}
    (h : OrderedByCtx c chain ordered) (hnd : chain.Nodup) : ordered.Nodup := by
  rw [h]
  exact ((List.mergeSort_perm _ _).nodup_iff).mpr hnd

/-- A sorted-by-context `ordered` is pairwise ordered by the context key. -/
theorem orderedByCtx_pairwise {c : Ctx} {chain ordered : List Nat}
    (h : OrderedByCtx c chain ordered) :
    ordered.Pairwise (fun a b : Nat => keyLe c a b = true) := by
  unfold OrderedByCtx at h
  rw [h]
  exact List.pairwise_mergeSort (keyLe_trans c) (keyLe_total c) _

/-- Consecutive elements of a pairwise-key-ordered list compare in key order. -/
theorem pairwise_succ_keyLe {c : Ctx} : ∀ (ordered : List Nat),
    ordered.Pairwise (fun a b : Nat => keyLe c a b = true) →
    ∀ (i : Nat) (hi : i + 1 < ordered.length),
      keyLe c (ordered[i]'(by omega)) (ordered[i + 1]'(by omega)) = true := by
  intro ordered
  induction ordered with
  | nil => intro _ i hi; simp at hi
  | cons x rest ih =>
    intro hp i hi
    rw [List.pairwise_cons] at hp
    cases i with
    | zero =>
      have h0 : 0 < rest.length := by
        simp only [List.length_cons] at hi
        omega
      exact hp.1 (rest[0]'(by omega)) (List.getElem_mem h0)
    | succ i' =>
      have h' : i' + 1 < rest.length := by
        simp only [List.length_cons] at hi
        omega
      simp only [List.getElem_cons_succ]
      exact ih hp.2 i' h'

/-- From the pairwise key order: distinct members compare one way or the other. -/
theorem pairwise_mem_keyLe {c : Ctx} : ∀ (ordered : List Nat),
    ordered.Pairwise (fun a b : Nat => keyLe c a b = true) →
    ∀ (a b : Nat), a ∈ ordered → b ∈ ordered → a ≠ b →
      keyLe c a b = true ∨ keyLe c b a = true := by
  intro ordered
  induction ordered with
  | nil => intro _ a b ha _ _; simp at ha
  | cons x rest ih =>
    intro hp a b ha hb hab
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with hea | ha'
    · rcases List.mem_cons.mp hb with heb | hb'
      · exact absurd (hea.trans heb.symm) hab
      · exact Or.inl (by rw [hea]; exact hp.1 b hb')
    · rcases List.mem_cons.mp hb with heb | hb'
      · exact Or.inr (by rw [heb]; exact hp.1 a ha')
      · exact ih hp.2 a b ha' hb' hab

/-! ## Chain predecessor facts from the sort -/

/-- The minimal chain node (first in the sorted order) has no chain
predecessor. -/
theorem chainPred_none_of_head {c : Ctx} {chain ordered : List Nat}
    (hp : ordered.Pairwise (fun a b : Nat => keyLe c a b = true))
    (hperm : ordered.Perm chain)
    {top : Nat} {rest : List Nat} (htr : ordered = top :: rest) :
    chainPred c chain top = none := by
  unfold chainPred
  rw [List.find?_eq_none]
  intro u hu hrk
  have hrk' : c.rank[u]! + 1 = c.rank[top]! := of_decide_eq_true hrk
  have htop : top ∈ ordered := by rw [htr]; exact List.mem_cons_self ..
  have hmemu : u ∈ ordered := hperm.symm.subset hu
  have hune : u ≠ top := by intro h; subst h; omega
  rw [htr] at hmemu
  have hurest : u ∈ rest := by
    rcases List.mem_cons.mp hmemu with heq | hrest
    · exact absurd heq hune
    · exact hrest
  rw [htr] at hp
  obtain ⟨hpcons, _⟩ := List.pairwise_cons.mp hp
  obtain ⟨rle, _⟩ := rank_pos_of_keyLe (hpcons u hurest)
  omega

/-- A chain node with a distinct chain member one rank below has that member as
its chain predecessor (the rank-injection makes it unique). -/
theorem chainPred_eq_some {c : Ctx} {chain : List Nat}
    (hocc : OccurringBorderChain c chain)
    {v pred : Nat} (_hv : v ∈ chain) (hpred : pred ∈ chain)
    (hrk : c.rank[pred]! + 1 = c.rank[v]!) :
    chainPred c chain v = some pred := by
  unfold chainPred
  cases hfind : chain.find? (fun u => c.rank[u]! + 1 = c.rank[v]!) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd hrk (fun hh => hfind pred hpred (decide_eq_true hh))
  | some u =>
    have hru : c.rank[u]! + 1 = c.rank[v]! := by
      have hs := List.find?_some hfind
      simpa using hs
    have hu : u ∈ chain := List.mem_of_find?_eq_some hfind
    exact congrArg some (hocc.rank_inj u hu pred hpred (by omega))

/-! ## Layer fold `up` updates

`alignNode` only writes `up` at the node being processed, so a node's `up`
entry is decided exactly at its own fold step. -/


/-- The executed pass fold's `up`-transport claims, kept as a named hypothesis
bundle: `alignNode` only writes `up` at the node being processed, so each node's
`up` entry is decided exactly at its own fold step. Downstream assembly
consumes these as premises. -/
structure FoldUpFacts (c : Ctx) : Prop where
  foldl_alignNode_up_ne : ∀ (xs : List Nat) (a : Al) (last : Int) (v : Nat),
    (∀ x ∈ xs, x ≠ v) → (xs.foldl (alignNode c) (a, last)).1.up v = a.up v
  alignLayer_up_ne : ∀ (a : Al) (l : List Nat) (v : Nat), v ∉ l →
    (alignLayer c a l).up v = a.up v
  foldl_alignLayer_up_ne : ∀ (ls : List (List Nat)) (a : Al) (v : Nat),
    (∀ l ∈ ls, v ∉ l) → (ls.foldl (alignLayer c) a).up v = a.up v
  fold_up_pick : ∀ (a : Al) (last : Int) (pre : List Nat) (v w : Nat) (rest : List Nat),
    alignPick c v ((pre.foldl (alignNode c) (a, last)).2) = some w →
    (∀ x ∈ rest, x ≠ v) →
    ((pre ++ v :: rest).foldl (alignNode c) (a, last)).1.up v = some w
  fold_up_none : ∀ (a : Al) (last : Int) (pre : List Nat) (v : Nat) (rest : List Nat),
    alignPick c v ((pre.foldl (alignNode c) (a, last)).2) = none →
    (∀ x ∈ rest, x ≠ v) →
    ((pre ++ v :: rest).foldl (alignNode c) (a, last)).1.up v =
      ((pre.foldl (alignNode c) (a, last)).1).up v
  alignAll_up_take : ∀ (v : Nat), Lay c → v ∈ c.layers.flatten →
    (alignAll c).up v =
      ((c.layers.take (c.rank[v]! + 1)).foldl (alignLayer c) Al.init).up v
  alignAll_up_eq : ∀ (v : Nat), Lay c → v ∈ c.layers.flatten →
    ∀ (l : List Nat), c.layers[c.rank[v]!]? = some l → l[c.pos[v]!]? = some v →
    (alignAll c).up v =
      match alignPick c v (foldLast c (c.rank[v]!) (c.pos[v]!)) with
      | some w => some w
      | none => (foldToLayer c (c.rank[v]!)).up v

/-- Split a list at the position of a known element. -/
theorem list_split_at {α : Type} : ∀ (l : List α) (j : Nat) (v : α), l[j]? = some v →
    ∃ pre rest : List α, l = pre ++ v :: rest ∧ pre.length = j := by
  intro l
  induction l with
  | nil => intro j v hj; cases hj
  | cons x xs ih =>
    intro j v hj
    cases j with
    | zero =>
      simp at hj
      refine ⟨[], xs, ?_, rfl⟩
      simp [hj]
    | succ j' =>
      rw [List.getElem?_cons_succ] at hj
      obtain ⟨pre, rest, hsplit, hlen⟩ := ih j' v hj
      refine ⟨x :: pre, rest, ?_, ?_⟩
      · rw [hsplit]; simp
      · simp [hlen]

/-! ## `up` transport through the executed folds -/

/-- `alignNode` only writes `up` at the node it processes. -/
theorem alignNode_up_ne {c : Ctx} {st : Al × Int} {x v : Nat} (h : x ≠ v) :
    (alignNode c st x).1.up v = st.1.up v := by
  obtain ⟨a, last⟩ := st
  show (alignNode c (a, last) x).1.up v = a.up v
  unfold alignNode
  dsimp only
  cases alignPick c x last with
  | none => rfl
  | some w =>
    show (upd a.up x (some w)) v = a.up v
    unfold upd
    rw [ite_eq_right (Ne.symm h)]

/-- Folding `alignNode` over nodes other than `v` leaves `v`'s `up` entry
untouched, for any starting state. -/
theorem foldl_alignNode_up_ne_aux (c : Ctx) (xs : List Nat) :
    ∀ (st : Al × Int) (v : Nat), (∀ x ∈ xs, x ≠ v) →
      (xs.foldl (alignNode c) st).1.up v = st.1.up v := by
  induction xs with
  | nil => intro st v _; rfl
  | cons y ys ih =>
    intro st v h
    rw [List.foldl_cons]
    rw [ih (alignNode c st y) v (fun x hx => h x (by simp [hx]))]
    exact alignNode_up_ne (h y (by simp))

/-- Field `foldl_alignNode_up_ne` of `FoldUpFacts`. -/
theorem foldl_alignNode_up_ne (c : Ctx) : ∀ (xs : List Nat) (a : Al) (last : Int) (v : Nat),
    (∀ x ∈ xs, x ≠ v) → (xs.foldl (alignNode c) (a, last)).1.up v = a.up v := by
  intro xs a last v h
  exact foldl_alignNode_up_ne_aux c xs (a, last) v h

/-- Field `alignLayer_up_ne` of `FoldUpFacts`: `alignLayer` leaves `v`'s `up`
entry untouched when `v` is not on the layer. -/
theorem up_ne_alignLayer (c : Ctx) : ∀ (a : Al) (l : List Nat) (v : Nat), v ∉ l →
    (alignLayer c a l).up v = a.up v := by
  intro a l v h
  exact foldl_alignNode_up_ne_aux c l (a, -1) v (fun x hx hxv => h (hxv ▸ hx))

/-- Field `foldl_alignLayer_up_ne` of `FoldUpFacts`. -/
theorem up_ne_foldl_alignLayer (c : Ctx) : ∀ (ls : List (List Nat)) (a : Al) (v : Nat),
    (∀ l ∈ ls, v ∉ l) → (ls.foldl (alignLayer c) a).up v = a.up v := by
  intro ls
  induction ls with
  | nil => intro a v _; rfl
  | cons y ys ih =>
    intro a v h
    rw [List.foldl_cons]
    rw [ih (alignLayer c a y) v (fun l hl => h l (by simp [hl]))]
    exact up_ne_alignLayer c a y v (h y (by simp))

/-- `alignNode` records the picked predecessor at the processed node. -/
theorem alignNode_up_self {c : Ctx} {st : Al × Int} {v w : Nat}
    (hpick : alignPick c v st.2 = some w) : (alignNode c st v).1.up v = some w := by
  obtain ⟨a, last⟩ := st
  dsimp only at hpick
  show (alignNode c (a, last) v).1.up v = some w
  unfold alignNode
  dsimp only
  rw [hpick]
  show (upd a.up v (some w)) v = some w
  unfold upd
  rw [ite_eq_left rfl]

/-- When the pick fails, `alignNode` keeps the state unchanged. -/
theorem alignNode_up_none {c : Ctx} {st : Al × Int} {v : Nat}
    (hpick : alignPick c v st.2 = none) : (alignNode c st v).1.up v = st.1.up v := by
  obtain ⟨a, last⟩ := st
  dsimp only at hpick
  show (alignNode c (a, last) v).1.up v = a.up v
  unfold alignNode
  dsimp only
  rw [hpick]

/-- Field `fold_up_pick` of `FoldUpFacts`: at its own fold step the node takes
the value `alignPick` selects, and later nodes leave it untouched. -/
theorem fold_up_pick (c : Ctx) :
    ∀ (a : Al) (last : Int) (pre : List Nat) (v w : Nat) (rest : List Nat),
      alignPick c v ((pre.foldl (alignNode c) (a, last)).2) = some w →
      (∀ x ∈ rest, x ≠ v) →
      ((pre ++ v :: rest).foldl (alignNode c) (a, last)).1.up v = some w := by
  intro a last pre v w rest hpick hrest
  rw [List.foldl_append, List.foldl_cons]
  rw [foldl_alignNode_up_ne_aux c rest (alignNode c (pre.foldl (alignNode c) (a, last)) v) v hrest]
  exact alignNode_up_self hpick

/-- Field `fold_up_none` of `FoldUpFacts`: a failed pick leaves the node's prior
`up` entry in place, and later nodes do not change it. -/
theorem fold_up_none (c : Ctx) :
    ∀ (a : Al) (last : Int) (pre : List Nat) (v : Nat) (rest : List Nat),
      alignPick c v ((pre.foldl (alignNode c) (a, last)).2) = none →
      (∀ x ∈ rest, x ≠ v) →
      ((pre ++ v :: rest).foldl (alignNode c) (a, last)).1.up v =
        ((pre.foldl (alignNode c) (a, last)).1).up v := by
  intro a last pre v rest hpick hrest
  rw [List.foldl_append, List.foldl_cons]
  rw [foldl_alignNode_up_ne_aux c rest (alignNode c (pre.foldl (alignNode c) (a, last)) v) v hrest]
  exact alignNode_up_none hpick


/-! ## `alignAll` at a node's own fold step -/

/-- A layer containing `v` sits at the index `v`'s rank gives. -/
theorem lay_layer_rank {c : Ctx} (hL : Lay c) {v i : Nat} {l : List Nat}
    (hl : c.layers[i]? = some l) (hm : v ∈ l) : i = c.rank[v]! := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  exact (hL.idx i l j v hl hj).1.symm

/-- Layers before a node's own layer do not contain it. -/
theorem lay_not_mem_take {c : Ctx} (hL : Lay c) {v : Nat} :
    ∀ l ∈ c.layers.take (c.rank[v]!), v ∉ l := by
  intro l hl hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  rw [List.getElem?_take] at hi
  by_cases hin : i < c.rank[v]!
  · rw [ite_eq_left hin] at hi
    have := lay_layer_rank hL hi hmem
    omega
  · rw [ite_eq_right hin] at hi
    cases hi

/-- Layers after a node's own layer do not contain it. -/
theorem lay_not_mem_drop {c : Ctx} (hL : Lay c) {v : Nat} :
    ∀ l ∈ c.layers.drop (c.rank[v]! + 1), v ∉ l := by
  intro l hl hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  rw [List.getElem?_drop] at hi
  have := lay_layer_rank hL hi hmem
  omega

/-- Splitting a fold at one element (given by `getElem?`): the layers before and
after the element are folded with the element's own step in between. -/
theorem foldl_split_at? {α β : Type} (f : β → α → β) (l : List α) (n : Nat) (b : β)
    (v : α) (hv : l[n]? = some v) :
    l.foldl f b = (l.drop (n + 1)).foldl f (f ((l.take n).foldl f b) v) := by
  obtain ⟨hn, hg⟩ := List.getElem?_eq_some_iff.mp hv
  have h2 : l.drop n = v :: l.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hn, hg]
  have hsplit : l = l.take n ++ v :: l.drop (n + 1) := by
    calc l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
      _ = l.take n ++ v :: l.drop (n + 1) := by rw [h2]
  calc l.foldl f b = (l.take n ++ v :: l.drop (n + 1)).foldl f b :=
        congrArg (fun s => s.foldl f b) hsplit
    _ = (l.drop (n + 1)).foldl f (f ((l.take n).foldl f b) v) := by
          rw [List.foldl_append, List.foldl_cons]

/-- Field `alignAll_up_take` of `FoldUpFacts`: the whole pass fold agrees at `v`
with the fold of the layers up to and including `v`'s own layer. -/
theorem alignAll_up_take (c : Ctx) : ∀ (v : Nat), Lay c → v ∈ c.layers.flatten →
    (alignAll c).up v =
      ((c.layers.take (c.rank[v]! + 1)).foldl (alignLayer c) Al.init).up v := by
  intro v hL hv
  have hlen : c.rank[v]! < c.layers.length := hL.rank_lt hv
  have hleft : (alignAll c).up v =
      (alignLayer c (foldToLayer c (c.rank[v]!)) c.layers[c.rank[v]!]).up v := by
    unfold alignAll foldToLayer
    rw [foldl_split_at? (alignLayer c) c.layers (c.rank[v]!) Al.init _
      (List.getElem?_eq_getElem hlen)]
    rw [up_ne_foldl_alignLayer c (c.layers.drop (c.rank[v]! + 1)) _ v (lay_not_mem_drop hL)]
  have hright : ((c.layers.take (c.rank[v]! + 1)).foldl (alignLayer c) Al.init).up v =
      (alignLayer c (foldToLayer c (c.rank[v]!)) c.layers[c.rank[v]!]).up v := by
    unfold foldToLayer
    rw [List.take_add_one, List.getElem?_eq_getElem hlen, List.foldl_append]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
  exact hleft.trans hright.symm

/-! ## Remaining `FoldUpFacts` fields -/

/-- Distinct positions of a nodup list hold distinct elements. -/
theorem nodup_getElem_ne : ∀ (l : List Nat), l.Nodup →
    ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length) (_hne : i ≠ j),
      l[i]'hi ≠ l[j]'hj := by
  intro l
  induction l with
  | nil => intro _ i _ hi _; exact absurd hi (Nat.not_lt_zero i)
  | cons x xs ih =>
    intro h i j hi hj hne
    rw [List.length_cons] at hi hj
    have hp : (x :: xs).Pairwise (fun a b : Nat => a ≠ b) := h
    obtain ⟨hall, hpxs⟩ := List.pairwise_cons.mp hp
    cases i with
    | zero =>
      cases j with
      | zero => show x ≠ x; exact absurd rfl hne
      | succ j' =>
        rw [List.getElem_cons_succ]
        exact hall (xs[j']'(by omega)) (List.getElem_mem (by omega))
    | succ i' =>
      cases j with
      | zero =>
        rw [List.getElem_cons_succ, List.getElem_cons_zero]
        exact (hall (xs[i']'(by omega)) (List.getElem_mem (by omega))).symm
      | succ j' =>
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact ih hpxs i' j' (by omega) (by omega) (by omega)

/-- Field `alignAll_up_eq` of `FoldUpFacts`: at the node's own fold step the
pick decides its `up` entry — a successful pick selects the picked value, a
failed pick keeps the entry accumulated over the earlier layers. -/
theorem alignAll_up_eq (c : Ctx) : ∀ (v : Nat), Lay c → v ∈ c.layers.flatten →
    ∀ (l : List Nat), c.layers[c.rank[v]!]? = some l → l[c.pos[v]!]? = some v →
    (alignAll c).up v =
      match alignPick c v (foldLast c (c.rank[v]!) (c.pos[v]!)) with
      | some w => some w
      | none => (foldToLayer c (c.rank[v]!)).up v := by
  intro v hL hv l hl hlv
  obtain ⟨hrlen, hget⟩ := List.getElem?_eq_some_iff.mp hl
  obtain ⟨hplen, hgetv⟩ := List.getElem?_eq_some_iff.mp hlv
  have hlay : c.layers.getD (c.rank[v]!) [] = l := by
    rw [show c.layers.getD (c.rank[v]!) [] = (c.layers[c.rank[v]!]?).getD [] from rfl, hl]
    rfl
  have hpre : ∀ x ∈ l.take c.pos[v]!, x ≠ v := by
    intro x hx hxv
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_take] at hk
    by_cases hkj : k < c.pos[v]!
    · rw [ite_eq_left hkj] at hk
      have hpk : c.pos[x]! = k := (hL.idx _ l k x hl hk).2
      rw [hxv] at hpk
      omega
    · rw [ite_eq_right hkj] at hk
      cases hk
  have hrest : ∀ x ∈ l.drop (c.pos[v]! + 1), x ≠ v := by
    intro x hx hxv
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_drop] at hk
    have hpk : c.pos[x]! = c.pos[v]! + 1 + k :=
      (hL.idx _ l (c.pos[v]! + 1 + k) x hl hk).2
    rw [hxv] at hpk
    omega
  have hdrop : l.drop c.pos[v]! = v :: l.drop (c.pos[v]! + 1) := by
    rw [List.drop_eq_getElem_cons hplen, hgetv]
  have hta : l = l.take c.pos[v]! ++ v :: l.drop (c.pos[v]! + 1) := by
    rw [← hdrop, List.take_append_drop c.pos[v]! l]
  have hfld : ((l.take c.pos[v]!).foldl (alignNode c) (foldToLayer c (c.rank[v]!), -1)).1.up v
      = (foldToLayer c (c.rank[v]!)).up v := by
    rw [foldl_alignNode_up_ne c _ _ _ _ hpre]
  have hA : (alignAll c).up v =
      (alignLayer c (foldToLayer c (c.rank[v]!)) l).up v := by
    rw [alignAll_up_take c v hL hv]
    unfold foldToLayer
    rw [List.take_add_one, List.getElem?_eq_getElem hrlen, List.foldl_append]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
    rw [hget]
  rw [hA]
  unfold alignLayer
  rw [show foldLast c (c.rank[v]!) (c.pos[v]!) =
        ((l.take c.pos[v]!).foldl (alignNode c) (foldToLayer c (c.rank[v]!), -1)).2 from by
      rw [foldLast, hlay]]
  conv =>
    lhs
    rw [hta]
  cases hp : alignPick c v
      ((l.take c.pos[v]!).foldl (alignNode c) (foldToLayer c (c.rank[v]!), -1)).2 with
  | none => rw [fold_up_none c _ _ _ _ _ hp hrest, hfld]
  | some w => rw [fold_up_pick c _ _ _ _ _ _ hp hrest]

/-- All `FoldUpFacts` hold: the pass fold's `up` transport is fully proved. -/
theorem foldUpFacts (c : Ctx) : FoldUpFacts c :=
  ⟨foldl_alignNode_up_ne c, up_ne_alignLayer c, up_ne_foldl_alignLayer c,
    fold_up_pick c, fold_up_none c, alignAll_up_take c, alignAll_up_eq c⟩

/-! ## `BorderChainUps` for occurring chains -/

/-- layered-107's executed-pipeline fact: for an occurring border chain, the
pass-oriented order (by `(rank, pos)` of the cluster context) has the chain
head picking nothing and every later chain node picking its chain predecessor
through the border-alignment edge, at the node's actual fold point. The pick
premises are exactly `BorderChainPick`; the sort order is `OrderedByCtx`. -/
theorem borderChainUps_of_pick {ng cp : Int} {p : Proper}
    {layers : List (List Nat)} {marked : Array Bool} {k : Nat}
    {chain ordered : List Nat}
    (hL : Lay (clusterCtx ng cp p layers marked k))
    (hocc : OccurringBorderChain (clusterCtx ng cp p layers marked k) chain)
    (hord : OrderedByCtx (clusterCtx ng cp p layers marked k) chain ordered)
    (hpick : BorderChainPick (clusterCtx ng cp p layers marked k) chain hocc) :
    BorderChainUps ng cp p layers marked k chain ordered hL := by
  refine ⟨orderedByCtx_nodup hord hocc.nodup, orderedByCtx_perm hord, ?_, ?_⟩
  · intro top rest htr
    have hp := orderedByCtx_pairwise hord
    have hperm := orderedByCtx_perm hord
    have hnone := chainPred_none_of_head hp hperm htr
    have htopord : top ∈ ordered := by rw [htr]; simp
    have htopchain : top ∈ chain := hperm.mem_iff.mp htopord
    have hpicknone := hpick.head_none top htopchain hnone
    have hflat : top ∈ (clusterCtx ng cp p layers marked k).layers.flatten :=
      hocc.flat top htopchain
    obtain ⟨l, hl, hlv⟩ := hL.loc hflat
    rw [alignAll_up_eq (clusterCtx ng cp p layers marked k) top hL hflat l hl hlv,
      hpicknone]
    unfold foldToLayer
    rw [up_ne_foldl_alignLayer (clusterCtx ng cp p layers marked k)
      ((clusterCtx ng cp p layers marked k).layers.take
        (clusterCtx ng cp p layers marked k).rank[top]!) Al.init top
      (lay_not_mem_take hL)]
    rfl
  · intro i hi
    have hp := orderedByCtx_pairwise hord
    have hperm := orderedByCtx_perm hord
    have hnd := orderedByCtx_nodup hord hocc.nodup
    have hv : ordered[i + 1] ∈ chain := hperm.mem_iff.mp (List.getElem_mem hi)
    have hpred : ordered[i] ∈ chain :=
      hperm.mem_iff.mp (List.getElem_mem (by omega : i < ordered.length))
    have hflat : ordered[i + 1] ∈ (clusterCtx ng cp p layers marked k).layers.flatten :=
      hocc.flat _ hv
    have hne : ordered[i] ≠ ordered[i + 1] :=
      nodup_getElem_ne ordered hnd i (i + 1) (by omega) hi (by omega)
    have hrk : (clusterCtx ng cp p layers marked k).rank[ordered[i]]! + 1 =
        (clusterCtx ng cp p layers marked k).rank[ordered[i + 1]]! := by
      have hkey := pairwise_succ_keyLe ordered hp i hi
      obtain ⟨rle, _⟩ := rank_pos_of_keyLe hkey
      rcases hocc.rank_adj ordered[i] hpred ordered[i + 1] hv hne with h | h
      · exact h
      · omega
    have hcp := chainPred_eq_some hocc hv hpred hrk
    obtain ⟨eb, -, -, hpk⟩ := hpick.pick ordered[i + 1] hv ordered[i] hcp
    obtain ⟨l, hl, hlv⟩ := hL.loc hflat
    rw [alignAll_up_eq (clusterCtx ng cp p layers marked k) ordered[i + 1] hL
      hflat l hl hlv, hpk]
end Elegant.Layered
