import ElegantGeometry.Basic

set_option autoImplicit false

/-! Graph of the layered family and the cycle phase (spec/layout/layered.md, "Cycle breaking").
`breakCycles` runs a depth-first search from the roots in declaration order, visits out-edges in
declaration order, and reverses an edge when its target is on the search stack. Self-loops stay.
`breakCycles_acyclic` and `breakCycles_edges_perm` prove the result is acyclic and that exactly
the edges whose target finishes after their source are reversed. -/

namespace Elegant
namespace Layered

structure Node where
  decl : Nat
  w : Int
  h : Int
deriving DecidableEq, Repr, Inhabited

structure Edge where
  tail : Nat
  head : Nat
  minLen : Int
  decl : Nat
  reversed : Bool
deriving DecidableEq, Repr, Inhabited

def Edge.reverse (e : Edge) : Edge :=
  { e with tail := e.head, head := e.tail, reversed := !e.reversed }

structure Graph where
  nodes : List Node
  edges : List Edge
  slot : Int
deriving DecidableEq, Repr, Inhabited

def Graph.bound (g : Graph) : Nat :=
  g.edges.foldl (fun m e => max m (max e.tail e.head + 1)) g.nodes.length

def Graph.outEdges (g : Graph) (v : Nat) : List (Edge × Nat) :=
  g.edges.zipIdx.filter (fun p => p.1.tail == v)

structure Dfs where
  stack : List Nat
  order : List Nat
  rev : Nat → Bool

namespace Dfs

def updRev (f : Nat → Bool) (i : Nat) (b : Bool) : Nat → Bool :=
  fun j => if j = i then b else f j

def visitEdge (rec : Nat → Dfs → Dfs) (st : Dfs) (p : Edge × Nat) : Dfs :=
  if p.1.tail = p.1.head then st
  else if p.1.head ∈ st.stack then { st with rev := updRev st.rev p.2 true }
  else if p.1.head ∈ st.order then st
  else rec p.1.head st

def dfs (g : Graph) : Nat → Nat → Dfs → Dfs
  | 0, _, st => st
  | f + 1, v, st =>
    let st1 : Dfs := { st with stack := v :: st.stack }
    let st2 := (g.outEdges v).foldl (visitEdge (dfs g f)) st1
    { st2 with stack := st2.stack.tail, order := v :: st2.order }

def rootStep (g : Graph) (st : Dfs) (v : Nat) : Dfs :=
  if v ∈ st.stack ∨ v ∈ st.order then st else dfs g g.bound v st

def init : Dfs := { stack := [], order := [], rev := fun _ => false }

def runRoots (g : Graph) : Dfs :=
  (List.range g.bound).foldl (rootStep g) Dfs.init

end Dfs

open Dfs

def breakCycles (g : Graph) : Graph :=
  let st := runRoots g
  { g with edges := g.edges.mapIdx (fun i e => if st.rev i then e.reverse else e) }


def Graph.Step (g : Graph) (a b : Nat) : Prop :=
  ∃ e ∈ g.edges, e.tail = a ∧ e.head = b ∧ a ≠ b

def Acyclic (g : Graph) : Prop :=
  ∀ v, ¬ Relation.TransGen (Graph.Step g) v v

def Graph.isBack (g : Graph) (e : Edge) : Prop :=
  e.tail ≠ e.head ∧ (runRoots g).order.idxOf e.head < (runRoots g).order.idxOf e.tail

instance (g : Graph) (e : Edge) : Decidable (g.isBack e) := by
  unfold Graph.isBack
  infer_instance

def Graph.orient (g : Graph) (e : Edge) : Edge :=
  if g.isBack e then e.reverse else e

theorem Graph.foldl_bound_ge (l : List Edge) (acc : Nat) :
    acc ≤ l.foldl (fun m e => max m (max e.tail e.head + 1)) acc ∧
    ∀ e ∈ l, max e.tail e.head + 1 ≤ l.foldl (fun m e => max m (max e.tail e.head + 1)) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max acc (max x.tail x.head + 1))
    refine ⟨by omega, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · exact h2 e he

theorem Graph.endpoints_lt_bound (g : Graph) {e : Edge} (he : e ∈ g.edges) :
    e.tail < g.bound ∧ e.head < g.bound := by
  have := (Graph.foldl_bound_ge g.edges g.nodes.length).2 e he
  unfold Graph.bound
  omega

namespace DfsProof

def Settled (order : List Nat) (b : Bool) (e : Edge) : Prop :=
  (b = true ∧ (e.head ∉ order ∨ order.idxOf e.head < order.idxOf e.tail)) ∨
  (b = false ∧ e.head ∈ order ∧ order.idxOf e.tail < order.idxOf e.head)

structure Inv (g : Graph) (st : Dfs) : Prop where
  stackNodup : st.stack.Nodup
  orderNodup : st.order.Nodup
  disjoint : ∀ x ∈ st.stack, x ∉ st.order
  stackBound : ∀ x ∈ st.stack, x < g.bound
  revTail : ∀ i, st.rev i = true →
    ∃ e, g.edges[i]? = some e ∧ e.tail ≠ e.head ∧ (e.tail ∈ st.stack ∨ e.tail ∈ st.order)
  fin : ∀ i e, g.edges[i]? = some e → e.tail ≠ e.head → e.tail ∈ st.order →
    Settled st.order (st.rev i) e

theorem idxOf_cons_ne {u x : Nat} (h : u ≠ x) (l : List Nat) :
    (u :: l).idxOf x = l.idxOf x + 1 := by
  simp [List.idxOf_cons, h]

theorem settled_cons {order : List Nat} {b : Bool} {e : Edge} (u : Nat) (hu : u ∉ order)
    (ht : e.tail ∈ order) (h : Settled order b e) : Settled (u :: order) b e := by
  have htu : u ≠ e.tail := fun h' => hu (h' ▸ ht)
  have hit : (u :: order).idxOf e.tail = order.idxOf e.tail + 1 := idxOf_cons_ne htu order
  have hpos : 0 < order.idxOf e.tail + 1 := by omega
  rcases h with ⟨hb, h1⟩ | ⟨hb, h1, h2⟩
  · left
    refine ⟨hb, ?_⟩
    by_cases hhu : u = e.head
    · right
      subst hhu
      simp [List.idxOf_cons_self] at *
      omega
    · rcases h1 with h1 | h1
      · left
        simp [h1, Ne.symm hhu]
      · right
        rw [hit, idxOf_cons_ne hhu]
        omega
  · right
    have hhu : u ≠ e.head := fun h' => hu (h' ▸ h1)
    refine ⟨hb, List.mem_cons_of_mem _ h1, ?_⟩
    rw [hit, idxOf_cons_ne hhu]
    omega

theorem inv_init (g : Graph) :
    Inv g { stack := [], order := [], rev := fun _ => false } := by
  refine ⟨by simp, by simp, by simp, by simp, ?_, ?_⟩
  · intro i h
    simp at h
  · intro i e _ _ h
    simp at h


structure Loop (g : Graph) (f : Nat) (u : Nat) (S : List Nat) (st0 : Dfs)
    (pre rest : List (Edge × Nat)) (st : Dfs) : Prop where
  inv : Inv g st
  stack : st.stack = u :: S
  fuel : g.bound ≤ f + (u :: S).length
  restRev : ∀ p ∈ rest, st.rev p.2 = false
  done : ∀ p ∈ pre, p.1.tail ≠ p.1.head →
    (st.rev p.2 = true ∧ p.1.head ∈ st.stack) ∨ (st.rev p.2 = false ∧ p.1.head ∈ st.order)
  suffix : st0.order <:+ st.order
  frame : ∀ i e, g.edges[i]? = some e → (e.tail ∈ S ∨ e.tail ∈ st0.order) →
    st.rev i = st0.rev i

def RecSpec (g : Graph) (f : Nat) (rec : Nat → Dfs → Dfs) : Prop :=
  ∀ v st, Inv g st → v ∉ st.stack → v ∉ st.order → v < g.bound →
    g.bound ≤ f + st.stack.length →
    Inv g (rec v st) ∧ (rec v st).stack = st.stack ∧ st.order <:+ (rec v st).order ∧
    v ∈ (rec v st).order ∧
    ∀ i e, g.edges[i]? = some e → (e.tail ∈ st.stack ∨ e.tail ∈ st.order) →
      (rec v st).rev i = st.rev i

theorem mem_of_getElem?_edges {g : Graph} {i : Nat} {e : Edge} (h : g.edges[i]? = some e) :
    e ∈ g.edges := List.mem_of_getElem? h

theorem loop_step (g : Graph) (f : Nat) (rec : Nat → Dfs → Dfs) (hrec : RecSpec g f rec)
    (u : Nat) (S : List Nat) (st0 : Dfs) (pre ps : List (Edge × Nat)) (p : Edge × Nat) (st : Dfs)
    (hmem : ∀ q ∈ pre ++ p :: ps, q.1.tail = u ∧ g.edges[q.2]? = some q.1)
    (hnd : ((pre ++ p :: ps).map (·.2)).Nodup)
    (hL : Loop g f u S st0 pre (p :: ps) st) :
    Loop g f u S st0 (pre ++ [p]) ps (visitEdge rec st p) := by
  obtain ⟨hpt, hpe⟩ := hmem p (by simp)
  have hinv := hL.inv
  have hstk := hL.stack
  have huS : u ∉ S := by
    have := hinv.stackNodup
    rw [hstk] at this
    exact (List.nodup_cons.mp this).1
  have huo : u ∉ st.order := by
    apply hinv.disjoint
    rw [hstk]; simp
  have hdistinct : ∀ q ∈ pre, q.2 ≠ p.2 := by
    intro q hq h
    have := hnd
    rw [List.map_append, List.nodup_append] at this
    exact this.2.2 q.2 (List.mem_map_of_mem hq) p.2 (by simp) h
  have hdistinct' : ∀ q ∈ ps, q.2 ≠ p.2 := by
    intro q hq h
    have := hnd
    rw [List.map_append, List.nodup_append] at this
    have h3 := this.2.1
    simp only [List.map_cons, List.nodup_cons] at h3
    exact h3.1 (h ▸ List.mem_map_of_mem hq)
  have hrevp : st.rev p.2 = false := hL.restRev p (by simp)
  unfold visitEdge
  split
  next hl =>
    refine ⟨hinv, hstk, hL.fuel, fun q hq => hL.restRev q (by simp [hq]), ?_, hL.suffix, hL.frame⟩
    intro q hq hne
    rcases List.mem_append.mp hq with hq | hq
    · exact hL.done q hq hne
    · simp at hq; subst hq; exact absurd hl hne
  next hl =>
    split
    next hs =>
      refine ⟨⟨hinv.stackNodup, hinv.orderNodup, hinv.disjoint, hinv.stackBound, ?_, ?_⟩,
        hstk, hL.fuel, ?_, ?_, hL.suffix, ?_⟩
      · intro i hi
        simp only [updRev] at hi
        by_cases hip : i = p.2
        · exact ⟨p.1, hip ▸ hpe, hl, Or.inl (by rw [hstk, hpt]; simp)⟩
        · simp only [hip, ↓reduceIte] at hi
          exact hinv.revTail i hi
      · intro i e hie hne hto
        simp only [updRev]
        by_cases hip : i = p.2
        · subst hip
          rw [hpe] at hie
          cases hie
          exact absurd hto (by rw [hpt]; exact hinv.disjoint u (by rw [hstk]; simp))
        · simp only [hip, ↓reduceIte]
          exact hinv.fin i e hie hne hto
      · intro q hq
        simp only [updRev, hdistinct' q hq, ↓reduceIte]
        exact hL.restRev q (by simp [hq])
      · intro q hq hne
        simp only [updRev]
        rcases List.mem_append.mp hq with hq | hq
        · simp only [hdistinct q hq, ↓reduceIte]
          exact hL.done q hq hne
        · simp at hq; subst hq
          left
          exact ⟨by simp, hs⟩
      · intro i e hie hmem'
        simp only [updRev]
        by_cases hip : i = p.2
        · subst hip
          rw [hpe] at hie
          cases hie
          rw [hpt] at hmem'
          rcases hmem' with h | h
          · exact absurd h huS
          · exact absurd (hL.suffix.subset h) huo
        · simp only [hip, ↓reduceIte]
          exact hL.frame i e hie hmem'
    next hs =>
      split
      next ho =>
        refine ⟨hinv, hstk, hL.fuel, fun q hq => hL.restRev q (by simp [hq]), ?_, hL.suffix, hL.frame⟩
        intro q hq hne
        rcases List.mem_append.mp hq with hq | hq
        · exact hL.done q hq hne
        · simp at hq; subst hq
          right
          exact ⟨hrevp, ho⟩
      next ho =>
        have hlt := (g.endpoints_lt_bound (mem_of_getElem?_edges hpe)).2
        have hfuel : g.bound ≤ f + st.stack.length := by
          rw [hstk]; exact hL.fuel
        obtain ⟨hi2, hs2, hsuf2, hmem2, hfr2⟩ := hrec p.1.head st hinv hs ho hlt hfuel
        have htailS : ∀ q ∈ pre ++ p :: ps, q.1.tail ∈ st.stack := by
          intro q hq
          rw [(hmem q hq).1, hstk]; simp
        have hfr : ∀ q ∈ pre ++ p :: ps, (rec p.1.head st).rev q.2 = st.rev q.2 := by
          intro q hq
          exact hfr2 q.2 q.1 (hmem q hq).2 (Or.inl (htailS q hq))
        refine ⟨hi2, by rw [hs2, hstk], hL.fuel, ?_, ?_, hL.suffix.trans hsuf2, ?_⟩
        · intro q hq
          rw [hfr q (by simp [hq])]
          exact hL.restRev q (by simp [hq])
        · intro q hq hne
          rcases List.mem_append.mp hq with hq | hq
          · rw [hfr q (by simp [hq]), hs2]
            rcases hL.done q hq hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr ⟨h1, hsuf2.subset h2⟩
          · simp at hq; subst hq
            right
            exact ⟨by rw [hfr _ (by simp)]; exact hrevp, hmem2⟩
        · intro i e hie hmem'
          have : e.tail ∈ st.stack ∨ e.tail ∈ st.order := by
            rcases hmem' with h | h
            · left; rw [hstk]; simp [h]
            · right; exact hL.suffix.subset h
          rw [hfr2 i e hie this]
          exact hL.frame i e hie hmem'


theorem visit_spec (g : Graph) (f : Nat) (rec : Nat → Dfs → Dfs) (hrec : RecSpec g f rec)
    (u : Nat) (S : List Nat) (st0 : Dfs) (rest : List (Edge × Nat)) :
    ∀ (pre : List (Edge × Nat)) (st : Dfs),
      (∀ q ∈ pre ++ rest, q.1.tail = u ∧ g.edges[q.2]? = some q.1) →
      ((pre ++ rest).map (·.2)).Nodup →
      Loop g f u S st0 pre rest st →
      Loop g f u S st0 (pre ++ rest) [] (rest.foldl (visitEdge rec) st) := by
  induction rest with
  | nil =>
    intro pre st _ _ hL
    simpa using hL
  | cons p ps ih =>
    intro pre st hmem hnd hL
    have hstep := loop_step g f rec hrec u S st0 pre ps p st hmem hnd hL
    have h := ih (pre ++ [p]) (visitEdge rec st p)
      (by simpa using hmem) (by simpa using hnd) hstep
    simpa using h

theorem outEdges_spec (g : Graph) (v : Nat) :
    (∀ q ∈ g.outEdges v, q.1.tail = v ∧ g.edges[q.2]? = some q.1) ∧
    ((g.outEdges v).map (·.2)).Nodup ∧
    ∀ i e, g.edges[i]? = some e → e.tail = v → (e, i) ∈ g.outEdges v := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    unfold Graph.outEdges at hq
    rw [List.mem_filter] at hq
    exact ⟨by simpa using hq.2, List.mem_zipIdx_iff_getElem?.mp hq.1⟩
  · unfold Graph.outEdges
    have hsub := (List.filter_sublist (p := fun p : Edge × Nat => p.1.tail == v)
      (l := g.edges.zipIdx)).map (·.2)
    refine hsub.nodup ?_
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  · intro i e hie het
    unfold Graph.outEdges
    rw [List.mem_filter]
    exact ⟨List.mem_zipIdx_iff_getElem?.mpr hie, by simpa using het⟩

theorem inv_push (g : Graph) (st : Dfs) (v : Nat) (hinv : Inv g st) (hs : v ∉ st.stack)
    (ho : v ∉ st.order) (hb : v < g.bound) :
    Inv g { st with stack := v :: st.stack } := by
  refine ⟨?_, hinv.orderNodup, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨hs, hinv.stackNodup⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hinv.disjoint x hx
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact hinv.stackBound x hx
  · intro i hi
    obtain ⟨e, he, hne, h⟩ := hinv.revTail i hi
    exact ⟨e, he, hne, by rcases h with h | h <;> simp [h]⟩
  · intro i e hie hne hto
    exact hinv.fin i e hie hne hto

theorem stack_length_lt (g : Graph) (st : Dfs) (v : Nat) (hinv : Inv g st) (hs : v ∉ st.stack)
    (hb : v < g.bound) : st.stack.length + 1 ≤ g.bound := by
  have hnd : (v :: st.stack).Nodup := List.nodup_cons.mpr ⟨hs, hinv.stackNodup⟩
  have hsub : (v :: st.stack) ⊆ List.range g.bound := by
    intro x hx
    rw [List.mem_range]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact hinv.stackBound x hx
  have := hnd.length_le_of_subset hsub
  simpa using this

theorem dfs_spec (g : Graph) : ∀ (f : Nat), ∀ v st, Inv g st → v ∉ st.stack → v ∉ st.order →
    v < g.bound → g.bound ≤ f + st.stack.length →
    Inv g (dfs g f v st) ∧ (dfs g f v st).stack = st.stack ∧ st.order <:+ (dfs g f v st).order ∧
    v ∈ (dfs g f v st).order ∧
    ∀ i e, g.edges[i]? = some e → (e.tail ∈ st.stack ∨ e.tail ∈ st.order) →
      (dfs g f v st).rev i = st.rev i := by
  intro f
  induction f with
  | zero =>
    intro v st hinv hs ho hb hf
    have := stack_length_lt g st v hinv hs hb
    omega
  | succ f ih =>
    intro v st hinv hs ho hb hf
    have hrec : RecSpec g f (dfs g f) := fun v st => ih v st
    obtain ⟨hmem, hnd, hall⟩ := outEdges_spec g v
    have hinv1 := inv_push g st v hinv hs ho hb
    have hL : Loop g f v st.stack st [] (g.outEdges v) { st with stack := v :: st.stack } := by
      refine ⟨hinv1, rfl, ?_, ?_, by simp, List.suffix_refl _, fun _ _ _ _ => rfl⟩
      · simp only [List.length_cons]; omega
      · intro p hp
        show st.rev p.2 = false
        cases hr : st.rev p.2 with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨e, he, _, hmemt⟩ := hinv.revTail p.2 hr
          have hpe := (hmem p hp).2
          rw [hpe] at he
          cases he
          rw [(hmem p hp).1] at hmemt
          rcases hmemt with h | h
          · exact hs h
          · exact ho h
    have hv := visit_spec g f (dfs g f) hrec v st.stack st (g.outEdges v) [] _
      (by simpa using hmem) (by simpa using hnd) hL
    simp only [List.nil_append] at hv
    generalize hst2 : List.foldl (visitEdge (dfs g f)) { st with stack := v :: st.stack } (g.outEdges v) = st2 at hv
    have hinv2 := hv.inv
    have hstk2 := hv.stack
    have hvo : v ∉ st2.order := hinv2.disjoint v (by rw [hstk2]; simp)
    have hS : st2.stack.tail = st.stack := by rw [hstk2]; rfl
    have hdef : dfs g (f + 1) v st = { st2 with stack := st2.stack.tail, order := v :: st2.order } := by
      simp only [dfs]
      rw [hst2]
    rw [hdef]
    refine ⟨?_, hS, ?_, by simp, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show st2.stack.tail.Nodup
        rw [hS]; exact hinv.stackNodup
      · exact List.nodup_cons.mpr ⟨hvo, hinv2.orderNodup⟩
      · intro x hx hxo
        have hx' : x ∈ st.stack := by simpa [hS] using hx
        rcases List.mem_cons.mp hxo with rfl | hxo
        · exact hs hx'
        · exact hinv2.disjoint x (by rw [hstk2]; simp [hx']) hxo
      · intro x hx
        have hx' : x ∈ st.stack := by simpa [hS] using hx
        exact hinv.stackBound x hx'
      · intro i hi
        obtain ⟨e, he, hne, h⟩ := hinv2.revTail i hi
        refine ⟨e, he, hne, ?_⟩
        rcases h with h | h
        · rw [hstk2] at h
          rcases List.mem_cons.mp h with h | h
          · right; simp [h]
          · left; show e.tail ∈ st2.stack.tail
            rw [hS]; exact h
        · right; exact List.mem_cons_of_mem _ h
      · intro i e hie hne hto
        show Settled (v :: st2.order) (st2.rev i) e
        by_cases htv : e.tail = v
        · have hmo := hall i e hie htv
          rcases hv.done (e, i) hmo hne with ⟨hr, hh⟩ | ⟨hr, hh⟩
          · have hhv : e.head ≠ v := fun h => hne (htv.trans h.symm)
            have hh' : e.head ∈ st.stack := by
              rw [hstk2] at hh
              rcases List.mem_cons.mp hh with h | h
              · exact absurd h hhv
              · exact h
            have hno : e.head ∉ st2.order := hinv2.disjoint e.head (by rw [hstk2]; simp [hh'])
            left
            refine ⟨hr, Or.inl ?_⟩
            simp [hhv, hno]
          · have hhv : e.head ≠ v := fun h => hvo (h ▸ hh)
            right
            refine ⟨hr, List.mem_cons_of_mem _ hh, ?_⟩
            rw [htv, idxOf_cons_ne (Ne.symm hhv)]
            simp [List.idxOf_cons_self]
        · have ht : e.tail ∈ st2.order := by
            rcases List.mem_cons.mp hto with h | h
            · exact absurd h htv
            · exact h
          exact settled_cons v hvo ht (hinv2.fin i e hie hne ht)
    · exact hv.suffix.trans (List.suffix_cons _ _)
    · intro i e hie hmem'
      exact hv.frame i e hie (by
        rcases hmem' with h | h
        · exact Or.inl h
        · exact Or.inr h)

theorem runRoots_inv (g : Graph) (k : Nat) (hk : k ≤ g.bound) :
    Inv g ((List.range k).foldl (rootStep g) Dfs.init) ∧
    ((List.range k).foldl (rootStep g) Dfs.init).stack = [] ∧
    ∀ x < k, x ∈ ((List.range k).foldl (rootStep g) Dfs.init).order := by
  induction k with
  | zero => exact ⟨inv_init g, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨hinv, hstk, hall⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (rootStep g) Dfs.init = st at hinv hstk hall
    unfold rootStep
    split
    next h =>
      refine ⟨hinv, hstk, ?_⟩
      intro x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · exact hall x hx
      · rcases h with h | h
        · rw [hstk] at h; simp at h
        · exact h
    next h =>
      have hs : k ∉ st.stack := fun h' => h (Or.inl h')
      have ho : k ∉ st.order := fun h' => h (Or.inr h')
      obtain ⟨hi2, hs2, hsuf, hmem, _⟩ :=
        dfs_spec g g.bound k st hinv hs ho (by omega) (by omega)
      refine ⟨hi2, by rw [hs2, hstk], ?_⟩
      intro x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · exact hsuf.subset (hall x hx)
      · exact hmem

theorem runRoots_spec (g : Graph) :
    Inv g (runRoots g) ∧ ∀ x < g.bound, x ∈ (runRoots g).order := by
  have h := runRoots_inv g g.bound (Nat.le_refl _)
  exact ⟨h.1, h.2.2⟩

theorem rev_eq_isBack (g : Graph) {i : Nat} {e : Edge} (hie : g.edges[i]? = some e) :
    (runRoots g).rev i = decide (g.isBack e) := by
  obtain ⟨hinv, hall⟩ := runRoots_spec g
  have hmem := mem_of_getElem?_edges hie
  obtain ⟨hlt, hlh⟩ := g.endpoints_lt_bound hmem
  by_cases hne : e.tail = e.head
  · have h1 : (runRoots g).rev i = false := by
      cases hr : (runRoots g).rev i with
      | false => rfl
      | true =>
        obtain ⟨e', he', hne', _⟩ := hinv.revTail i hr
        rw [hie] at he'
        cases he'
        exact absurd hne hne'
    rw [h1]
    simp [Graph.isBack, hne]
  · have hfin := hinv.fin i e hie hne (hall e.tail hlt)
    rcases hfin with ⟨hr, h1⟩ | ⟨hr, _, h2⟩
    · rw [hr]
      rcases h1 with h1 | h1
      · exact absurd (hall e.head hlh) h1
      · simp [Graph.isBack, hne, h1]
    · rw [hr]
      simp [Graph.isBack]
      omega

end DfsProof

open DfsProof

theorem breakCycles_edges_eq (g : Graph) :
    (breakCycles g).edges = g.edges.map g.orient := by
  unfold breakCycles
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have h3 : i < g.edges.length := by simpa using h2
    have hie : g.edges[i]? = some g.edges[i] := List.getElem?_eq_getElem h3
    simp only [List.getElem_mapIdx, List.getElem_map, Graph.orient]
    rw [rev_eq_isBack g hie]
    simp

theorem breakCycles_edges_perm (g : Graph) :
    List.Perm (breakCycles g).edges
      (g.edges.map (fun e => if g.isBack e then e.reverse else e)) := by
  rw [breakCycles_edges_eq]
  exact List.Perm.refl _

theorem breakCycles_label_increases (g : Graph) {e' : Edge} (he' : e' ∈ (breakCycles g).edges)
    (hne : e'.tail ≠ e'.head) :
    (runRoots g).order.idxOf e'.tail < (runRoots g).order.idxOf e'.head := by
  rw [breakCycles_edges_eq] at he'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  unfold Graph.orient at hne ⊢
  by_cases hb : g.isBack e
  · simp only [hb, ↓reduceIte, Edge.reverse] at hne ⊢
    exact hb.2
  · simp only [hb, ↓reduceIte] at hne ⊢
    obtain ⟨hinv, hall⟩ := runRoots_spec g
    obtain ⟨hlt, hlh⟩ := g.endpoints_lt_bound he
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
    have hie' : g.edges[i]? = some e := by rw [List.getElem?_eq_getElem hi, hie]
    have hfin := hinv.fin i e hie' hne (hall e.tail hlt)
    rcases hfin with ⟨hr, h1⟩ | ⟨hr, _, h2⟩
    · have := rev_eq_isBack g hie'
      rw [hr] at this
      simp at this
      exact absurd this hb
    · exact h2

theorem breakCycles_acyclic (g : Graph) : Acyclic (breakCycles g) := by
  intro v hv
  have key : ∀ a b, Relation.TransGen (Graph.Step (breakCycles g)) a b →
      (runRoots g).order.idxOf a < (runRoots g).order.idxOf b := by
    intro a b h
    induction h with
    | single hab =>
      obtain ⟨e, he, rfl, rfl, hne⟩ := hab
      exact breakCycles_label_increases g he hne
    | tail _ hbc ih =>
      obtain ⟨e, he, rfl, rfl, hne⟩ := hbc
      exact Nat.lt_trans ih (breakCycles_label_increases g he hne)
  have := key v v hv
  omega

end Layered
end Elegant
