import ElegantGeometry.Basic
import Elegant.Layered.Reachability

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
  loopExtent : Nat := 0
  clusterPath : List Nat := []
  border : Int := 0
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

namespace GreedyCycles

def earlier (g : Graph) (a b : Nat) : Bool :=
  let da := (g.nodes[a]?.map Node.decl).getD a
  let db := (g.nodes[b]?.map Node.decl).getD b
  da < db || (da == db && a < b)

def degree (g : Graph) (remaining : List Nat) (v : Nat) (outgoing : Bool) : Nat :=
  (g.edges.filter (fun e => e.tail != e.head && remaining.contains e.tail &&
    remaining.contains e.head && (if outgoing then e.tail == v else e.head == v))).length

def delta (g : Graph) (remaining : List Nat) (v : Nat) : Int :=
  (degree g remaining v true : Int) - (degree g remaining v false : Int)

def firstBy (preferred : Nat → Nat → Bool) : List Nat → Option Nat
  | [] => none
  | v :: vs => some (vs.foldl (fun best next => if preferred next best then next else best) v)

def select (g : Graph) (remaining : List Nat) : Option (Nat × Bool) :=
  match firstBy (earlier g) (remaining.filter (fun v => degree g remaining v true == 0)) with
  | some v => some (v, true)
  | none =>
    match firstBy (earlier g) (remaining.filter (fun v => degree g remaining v false == 0)) with
    | some v => some (v, false)
    | none =>
      (firstBy (fun a b => delta g remaining a > delta g remaining b ||
        (delta g remaining a == delta g remaining b && earlier g a b)) remaining).map
        (fun v => (v, false))

def removeVertices (g : Graph) : Nat → List Nat → List Nat → List Nat → List Nat
  | 0, remaining, left, right => left ++ remaining ++ right
  | fuel + 1, remaining, left, right =>
    match select g remaining with
    | none => left ++ right
    | some (v, sink) =>
      if sink then removeVertices g fuel (remaining.erase v) left (v :: right)
      else removeVertices g fuel (remaining.erase v) (left ++ [v]) right

def ordering (g : Graph) : List Nat :=
  removeVertices g g.bound (List.range g.bound) [] []

def before (order : List Nat) (a b : Nat) : Prop :=
  order.idxOf a < order.idxOf b ∨ (order.idxOf a = order.idxOf b ∧ a < b)

instance (order : List Nat) (a b : Nat) : Decidable (before order a b) := by
  unfold before
  infer_instance

def orient (order : List Nat) (e : Edge) : Edge :=
  if before order e.head e.tail then e.reverse else e

theorem before_trans (order : List Nat) {a b c : Nat}
    (hab : before order a b) (hbc : before order b c) : before order a c := by
  unfold before at *
  omega

theorem orient_increases (order : List Nat) (e : Edge)
    (hne : (orient order e).tail ≠ (orient order e).head) :
    before order (orient order e).tail (orient order e).head := by
  by_cases hb : before order e.head e.tail
  · simp only [orient, hb, ↓reduceIte, Edge.reverse]
  · simp only [orient, hb, ↓reduceIte] at hne ⊢
    unfold before at *
    omega

end GreedyCycles

def breakCyclesGreedy (g : Graph) : Graph :=
  { g with edges := g.edges.map (GreedyCycles.orient (GreedyCycles.ordering g)) }

theorem breakCyclesGreedy_acyclic (g : Graph) : Acyclic (breakCyclesGreedy g) := by
  intro v hv
  have key : ∀ a b, Relation.TransGen (Graph.Step (breakCyclesGreedy g)) a b →
      GreedyCycles.before (GreedyCycles.ordering g) a b := by
    intro a b h
    induction h with
    | single hab =>
      obtain ⟨e, he, rfl, rfl, hne⟩ := hab
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp he
      exact GreedyCycles.orient_increases _ original hne
    | tail _ hbc ih =>
      obtain ⟨e, he, rfl, rfl, hne⟩ := hbc
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp he
      exact GreedyCycles.before_trans _ ih (GreedyCycles.orient_increases _ original hne)
  have := key v v hv
  simp [GreedyCycles.before] at this

theorem breakCyclesGreedy_edges_perm (g : Graph) :
    List.Perm (breakCyclesGreedy g).edges
      (g.edges.map (GreedyCycles.orient (GreedyCycles.ordering g))) :=
  List.Perm.refl _

theorem breakCyclesGreedy_nodes (g : Graph) :
    (breakCyclesGreedy g).nodes = g.nodes := rfl

theorem breakCyclesGreedy_edge_count (g : Graph) :
    (breakCyclesGreedy g).edges.length = g.edges.length := by
  simp [breakCyclesGreedy]

theorem Edge.reverse_identity (e : Edge) :
    e.reverse.decl = e.decl ∧ e.reverse.minLen = e.minLen ∧
    e.reverse.reverse = e := by
  cases e
  simp [Edge.reverse]

theorem breakCyclesGreedy_original_identity (g : Graph) :
    (breakCyclesGreedy g).edges.map (fun e => (e.decl, e.minLen)) =
      g.edges.map (fun e => (e.decl, e.minLen)) := by
  simp only [breakCyclesGreedy, List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]
  unfold GreedyCycles.orient
  split <;> rfl

def Edge.original (e : Edge) : Edge :=
  if e.reversed then { e with tail := e.head, head := e.tail, reversed := false }
  else { e with reversed := false }

theorem Edge.reverse_original (e : Edge) : e.reverse.original = e.original := by
  cases h : e.reversed <;> simp [Edge.reverse, Edge.original, h]

theorem breakCyclesGreedy_semantic_identity (g : Graph) :
    (breakCyclesGreedy g).edges.map Edge.original = g.edges.map Edge.original := by
  simp only [breakCyclesGreedy, List.map_map]
  apply List.map_congr_left
  intro e _
  change (GreedyCycles.orient (GreedyCycles.ordering g) e).original = e.original
  unfold GreedyCycles.orient
  split
  · exact Edge.reverse_original e
  · rfl

namespace ProtectedCycles
abbrev Rel (edges : List Edge) (a b : Nat) : Prop :=
  ∃ e ∈ edges, e.tail = a ∧ e.head = b ∧ a ≠ b
abbrev Path (edges : List Edge) (a b : Nat) : Prop := a = b ∨ Relation.TransGen (Rel edges) a b

theorem path_trans {edges : List Edge} {a b c : Nat}
    (hab : Path edges a b) (hbc : Path edges b c) : Path edges a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (hab.trans hbc)

def bounded (edges : List Edge) (nodes : Nat) : Prop :=
  ∀ e ∈ edges, e.tail < nodes ∧ e.head < nodes

/-- Build declaration-ordered adjacency once per query. Out-of-range endpoints
are omitted; well-formed ranking graphs have none. -/
def adjacency (nodes : Nat) : List Edge → Array (List Nat)
  | [] => Array.replicate nodes []
  | e :: es =>
    let adj := adjacency nodes es
    if e.head < nodes then adj.modify e.tail (fun ns => e.head :: ns) else adj

@[simp] theorem adjacency_size (nodes : Nat) (edges : List Edge) :
    (adjacency nodes edges).size = nodes := by
  induction edges with
  | nil => simp [adjacency]
  | cons e es ih => simp only [adjacency]; split <;> simp [ih]

theorem adjacency_get (nodes : Nat) (edges : List Edge) (a : Nat) (ha : a < nodes) :
    (adjacency nodes edges)[a]'(by simpa using ha) =
      (edges.filter (fun e => e.tail == a && decide (e.head < nodes))).map Edge.head := by
  induction edges with
  | nil => simp [adjacency]
  | cons e es ih =>
    by_cases hh : e.head < nodes
    · by_cases he : e.tail = a
      · subst a
        simp [adjacency, hh, Array.getElem_modify, ih]
      · simp [adjacency, hh, Array.getElem_modify, he, ih]
    · simp [adjacency, hh, ih]

theorem adjacency_mem (nodes : Nat) (edges : List Edge) (a b : Nat) (ha : a < nodes) :
    b ∈ (adjacency nodes edges)[a]! ↔
      ∃ e ∈ edges, e.tail = a ∧ e.head = b ∧ b < nodes := by
  have ha' : a < (adjacency nodes edges).size := by simpa using ha
  simp only [getElem!_pos (adjacency nodes edges) a ha', adjacency_get nodes edges a ha]
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, ht, hh⟩, rfl⟩
    exact ⟨e, he, ht, rfl, hh⟩
  · rintro ⟨e, he, ht, rfl, hh⟩
    exact ⟨e, ⟨he, ht, hh⟩, rfl⟩

theorem adjacency_bounded (nodes : Nat) (edges : List Edge) :
    ∀ a, a < (adjacency nodes edges).size →
      ∀ b ∈ (adjacency nodes edges)[a]!, b < (adjacency nodes edges).size := by
  intro a ha b hb
  have ha' : a < nodes := by simpa using ha
  obtain ⟨e, _, _, _, hh⟩ := (adjacency_mem nodes edges a b ha').mp hb
  simpa using hh

theorem adjacency_path_sound (nodes : Nat) (edges : List Edge) {a b : Nat}
    (h : Relation.TransGen (fun x y => y ∈ (adjacency nodes edges)[x]!) a b) :
    Path edges a b := by
  have step : ∀ x y, y ∈ (adjacency nodes edges)[x]! → Path edges x y := by
    intro x y hxy
    by_cases hx : x < nodes
    · obtain ⟨e, he, ht, hh, _⟩ := (adjacency_mem nodes edges x y hx).mp hxy
      by_cases hself : x = y
      · exact Or.inl hself
      · exact Or.inr (.single ⟨e, he, ht, hh, hself⟩)
    · have hx' : ¬ x < (adjacency nodes edges).size := by simpa using hx
      have hempty : (adjacency nodes edges)[x]! = ([] : List Nat) := by
        rw [getElem!_neg (adjacency nodes edges) x hx']
        rfl
      simp [hempty] at hxy
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact path_trans ih (step _ _ h)

theorem adjacency_path_complete (nodes : Nat) (edges : List Edge)
    (hb : bounded edges nodes) {a b : Nat}
    (h : Relation.TransGen (Rel edges) a b) :
    Relation.TransGen (fun x y => y ∈ (adjacency nodes edges)[x]!) a b := by
  induction h with
  | single h =>
    obtain ⟨e, he, rfl, rfl, _⟩ := h
    exact .single ((adjacency_mem nodes edges _ _ (hb e he).1).mpr
      ⟨e, he, rfl, rfl, (hb e he).2⟩)
  | tail _ h ih =>
    obtain ⟨e, he, ht, hh, _⟩ := h
    exact .tail ih ((adjacency_mem nodes edges _ _ (ht ▸ (hb e he).1)).mpr
      ⟨e, he, ht, hh, hh ▸ (hb e he).2⟩)
end ProtectedCycles

namespace ProtectedCycles
def acyclicEdges (edges : List Edge) : Prop := ∀ v, ¬ Relation.TransGen (Rel edges) v v

theorem append_edge_cases (edges : List Edge) (edge : Edge) {a b : Nat}
    (h : Rel (edges ++ [edge]) a b) :
    Rel edges a b ∨ (a = edge.tail ∧ b = edge.head ∧ a ≠ b) := by
  obtain ⟨e, he, ht, hh, hne⟩ := h
  rcases List.mem_append.mp he with he | he
  · exact Or.inl ⟨e, he, ht, hh, hne⟩
  · simp only [List.mem_singleton] at he
    subst e
    exact Or.inr ⟨ht.symm, hh.symm, hne⟩

theorem insert_path_cases (edges : List Edge) (edge : Edge)
    (hback : ¬ Path edges edge.head edge.tail) {a b : Nat}
    (h : Relation.TransGen (Rel (edges ++ [edge])) a b) :
    Relation.TransGen (Rel edges) a b ∨
      (Path edges a edge.tail ∧ Path edges edge.head b) := by
  induction h with
  | single hab =>
    rcases append_edge_cases edges edge hab with hab | ⟨rfl, rfl, _⟩
    · exact Or.inl (.single hab)
    · exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
  | @tail b c hab hbc ih =>
    rcases append_edge_cases edges edge hbc with hbc | ⟨rfl, rfl, _⟩
    · rcases ih with ih | ⟨ha, hb⟩
      · exact Or.inl (.tail ih hbc)
      · exact Or.inr ⟨ha, path_trans hb (Or.inr (.single hbc))⟩
    · rcases ih with ih | ⟨ha, hb⟩
      · exact Or.inr ⟨Or.inr ih, Or.inl rfl⟩
      · exact False.elim (hback hb)

theorem append_acyclic (edges : List Edge) (edge : Edge)
    (ha : acyclicEdges edges) (hback : ¬ Path edges edge.head edge.tail) :
    acyclicEdges (edges ++ [edge]) := by
  intro v h
  rcases insert_path_cases edges edge hback h with h | ⟨hv, hv'⟩
  · exact ha v h
  · exact hback (path_trans hv' hv)

theorem opposite_unreachable (edges : List Edge) (ha : acyclicEdges edges)
    (edge : Edge) (hne : edge.tail ≠ edge.head)
    (hback : Path edges edge.head edge.tail) : ¬ Path edges edge.tail edge.head := by
  intro hforward
  rcases hback with hback | hback
  · exact hne hback.symm
  rcases hforward with hforward | hforward
  · exact hne hforward
  · exact ha edge.tail (hforward.trans hback)
end ProtectedCycles

namespace ProtectedCycles

def reachable (edges : List Edge) (nodes : Nat) (source target : Nat) : Bool :=
  if source = target then true
  else if source < nodes ∧ target < nodes then
    Reachability.search (adjacency nodes edges) source target
  else false

def orient (nodes : Nat) (accepted : List Edge) (edge : Edge) : Edge :=
  if edge.tail = edge.head then edge
  else if reachable accepted nodes edge.head edge.tail then edge.reverse
  else edge

def insertSemantic (nodes : Nat) : List Edge → List Edge → List Edge
  | _, [] => []
  | accepted, edge :: rest =>
    let chosen := orient nodes accepted edge
    let next := if edge.tail = edge.head then accepted else accepted ++ [chosen]
    chosen :: insertSemantic nodes next rest

def breakWithHierarchy (g : Graph) (hierarchy : List Edge) : Graph :=
  { g with edges := insertSemantic g.nodes.length hierarchy g.edges }

theorem orient_original (nodes : Nat) (accepted : List Edge) (edge : Edge) :
    (orient nodes accepted edge).original = edge.original := by
  unfold orient
  split
  · rfl
  · split
    · exact Edge.reverse_original edge
    · rfl

theorem insertSemantic_identity (nodes : Nat) (semantic : List Edge) :
    ∀ accepted, (insertSemantic nodes accepted semantic).map Edge.original =
      semantic.map Edge.original := by
  induction semantic with
  | nil => intro accepted; rfl
  | cons edge rest ih =>
    intro accepted
    simp only [insertSemantic, List.map_cons, orient_original]
    rw [ih]

theorem semantic_identity (g : Graph) (hierarchy : List Edge) :
    (breakWithHierarchy g hierarchy).edges.map Edge.original = g.edges.map Edge.original :=
  insertSemantic_identity g.nodes.length g.edges hierarchy

theorem semantic_multiset (g : Graph) (hierarchy : List Edge) :
    List.Perm ((breakWithHierarchy g hierarchy).edges.map Edge.original)
      (g.edges.map Edge.original) := by
  rw [semantic_identity]

theorem alias_equivalent_preserved (nodes : Nat) (accepted : List Edge) (edge : Edge)
    (halias : edge.tail = edge.head) :
    insertSemantic nodes accepted [edge] = [edge] := by
  simp [insertSemantic, orient, halias]

theorem alias_equivalent_cons (nodes : Nat) (accepted : List Edge) (edge : Edge)
    (rest : List Edge) (halias : edge.tail = edge.head) :
    insertSemantic nodes accepted (edge :: rest) =
      edge :: insertSemantic nodes accepted rest := by
  simp [insertSemantic, orient, halias]

theorem zero_length_alias_preserved (nodes : Nat) (accepted : List Edge) (edge : Edge)
    (rest : List Edge) (halias : edge.tail = edge.head) (_hzero : edge.minLen = 0) :
    insertSemantic nodes accepted (edge :: rest) =
      edge :: insertSemantic nodes accepted rest :=
  alias_equivalent_cons nodes accepted edge rest halias

theorem insertSemantic_length (nodes : Nat) (semantic : List Edge) :
    ∀ accepted, (insertSemantic nodes accepted semantic).length = semantic.length := by
  induction semantic with
  | nil => intro accepted; rfl
  | cons edge rest ih =>
    intro accepted
    simp only [insertSemantic, List.length_cons]
    rw [ih]

theorem semantic_count (g : Graph) (hierarchy : List Edge) :
    (breakWithHierarchy g hierarchy).edges.length = g.edges.length :=
  insertSemantic_length g.nodes.length g.edges hierarchy

theorem nodes_preserved (g : Graph) (hierarchy : List Edge) :
    (breakWithHierarchy g hierarchy).nodes = g.nodes := rfl

end ProtectedCycles

end Layered
end Elegant

namespace Elegant.Layered
namespace ProtectedCycles

theorem reachable_sound (edges : List Edge) (nodes a b : Nat)
    (h : reachable edges nodes a b = true) : Path edges a b := by
  unfold reachable at h
  split at h
  next he => exact Or.inl he
  next he =>
    split at h
    next hb =>
      have hs : a < (adjacency nodes edges).size := by simpa using hb.1
      have ht : b < (adjacency nodes edges).size := by simpa using hb.2
      rcases (Reachability.search_iff (adjacency nodes edges)
        (adjacency_bounded nodes edges) a b hs ht).mp h with heq | hp
      · exact Or.inl heq
      · exact adjacency_path_sound nodes edges hp
    next hb => contradiction

theorem path_endpoints (edges : List Edge) (nodes : Nat) (hb : bounded edges nodes)
    {a b : Nat} (h : Relation.TransGen (Rel edges) a b) : a < nodes ∧ b < nodes := by
  induction h with
  | single h =>
    obtain ⟨e, he, ht, hh, _⟩ := h
    exact ⟨ht ▸ (hb e he).1, hh ▸ (hb e he).2⟩
  | tail _ h ih =>
    obtain ⟨e, he, _, hh, _⟩ := h
    exact ⟨ih.1, hh ▸ (hb e he).2⟩

theorem reachable_complete (edges : List Edge) (nodes : Nat) (hb : bounded edges nodes)
    {a b : Nat} (h : Path edges a b) : reachable edges nodes a b = true := by
  rcases h with rfl | hp
  · simp [reachable]
  · have he := path_endpoints edges nodes hb hp
    by_cases hab : a = b
    · simp [reachable, hab]
    · simp only [reachable, hab, ↓reduceIte, he, and_self]
      apply (Reachability.search_iff (adjacency nodes edges)
        (adjacency_bounded nodes edges) a b (by simpa using he.1)
        (by simpa using he.2)).mpr
      exact Or.inr (adjacency_path_complete nodes edges hb hp)

theorem orient_acyclic (nodes : Nat) (accepted : List Edge) (edge : Edge)
    (ha : acyclicEdges accepted) (hb : bounded accepted nodes)
    (hne : edge.tail ≠ edge.head) :
    acyclicEdges (accepted ++ [orient nodes accepted edge]) := by
  unfold orient
  simp only [hne, ↓reduceIte]
  split
  next h =>
    apply append_acyclic accepted edge.reverse ha
    change ¬ Path accepted edge.tail edge.head
    exact opposite_unreachable accepted ha edge hne (reachable_sound accepted nodes _ _ h)
  next h =>
    apply append_acyclic accepted edge ha
    intro hp
    exact h (reachable_complete accepted nodes hb hp)

theorem orient_bounded (nodes : Nat) (accepted : List Edge) (edge : Edge)
    (he : edge.tail < nodes ∧ edge.head < nodes) :
    (orient nodes accepted edge).tail < nodes ∧ (orient nodes accepted edge).head < nodes := by
  unfold orient
  split
  · exact he
  · split
    · exact ⟨he.2, he.1⟩
    · exact he

theorem bounded_append (nodes : Nat) (accepted : List Edge) (edge : Edge)
    (hb : bounded accepted nodes) (he : edge.tail < nodes ∧ edge.head < nodes) :
    bounded (accepted ++ [edge]) nodes := by
  intro e he'
  rcases List.mem_append.mp he' with he' | he'
  · exact hb e he'
  · simp only [List.mem_singleton] at he'
    subst e
    exact he

theorem rel_mono {xs ys : List Edge} (hsub : xs ⊆ ys) {a b : Nat}
    (h : Rel xs a b) : Rel ys a b := by
  obtain ⟨e, he, ht, hh, hne⟩ := h
  exact ⟨e, hsub he, ht, hh, hne⟩

theorem acyclic_mono {xs ys : List Edge} (hsub : xs ⊆ ys) (ha : acyclicEdges ys) :
    acyclicEdges xs := by
  have lift : ∀ a b, Relation.TransGen (Rel xs) a b → Relation.TransGen (Rel ys) a b := by
    intro a b h
    induction h with
    | single h => exact .single (rel_mono hsub h)
    | tail _ h ih => exact .tail ih (rel_mono hsub h)
  intro v h
  exact ha v (lift v v h)

end ProtectedCycles

namespace ProtectedCycles

theorem acyclic_rel_mono {xs ys : List Edge}
    (hsub : ∀ a b, Rel xs a b → Rel ys a b) (ha : acyclicEdges ys) : acyclicEdges xs := by
  have lift : ∀ a b, Relation.TransGen (Rel xs) a b → Relation.TransGen (Rel ys) a b := by
    intro a b h
    induction h with
    | single h => exact .single (hsub _ _ h)
    | tail _ h ih => exact .tail ih (hsub _ _ h)
  intro v h
  exact ha v (lift v v h)

theorem insertSemantic_acyclic (nodes : Nat) (semantic : List Edge)
    (hs : bounded semantic nodes) : ∀ accepted,
    bounded accepted nodes → acyclicEdges accepted →
    acyclicEdges (accepted ++ insertSemantic nodes accepted semantic) := by
  induction semantic with
  | nil => intro accepted _ ha; simpa [insertSemantic] using ha
  | cons edge rest ih =>
    intro accepted hb ha
    have he : edge.tail < nodes ∧ edge.head < nodes := hs edge (by simp)
    have hr : bounded rest nodes := fun e h => hs e (by simp [h])
    by_cases hself : edge.tail = edge.head
    · have hi := ih hr accepted hb ha
      simp only [insertSemantic, orient, hself, ↓reduceIte]
      apply acyclic_rel_mono (ys := accepted ++ insertSemantic nodes accepted rest) _ hi
      intro a b h
      obtain ⟨e, hm, ht, hh, hne⟩ := h
      refine ⟨e, ?_, ht, hh, hne⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact False.elim (hne (ht.symm.trans (hself.trans hh)))
        · exact List.mem_append_right _ hm
    · have hb' := bounded_append nodes accepted (orient nodes accepted edge) hb
        (orient_bounded nodes accepted edge he)
      have ha' := orient_acyclic nodes accepted edge ha hb hself
      have hi := ih hr (accepted ++ [orient nodes accepted edge]) hb' ha'
      simpa only [insertSemantic, hself, ↓reduceIte, List.append_assoc,
        List.singleton_append] using hi

theorem breakWithHierarchy_acyclic (g : Graph) (hierarchy : List Edge)
    (hg : bounded g.edges g.nodes.length) (hh : bounded hierarchy g.nodes.length)
    (ha : acyclicEdges hierarchy) : Acyclic (breakWithHierarchy g hierarchy) := by
  have hi := insertSemantic_acyclic g.nodes.length g.edges hg hierarchy hh ha
  exact acyclic_mono (fun _ h => List.mem_append_right hierarchy h) hi

end ProtectedCycles

end Elegant.Layered

namespace Elegant.Layered
theorem Edge.original_decl (e : Edge) : e.original.decl = e.decl := by
  unfold Edge.original
  split <;> rfl
theorem Edge.original_minLen (e : Edge) : e.original.minLen = e.minLen := by
  unfold Edge.original
  split <;> rfl
theorem breakCyclesGreedy_semantic_multiset (g : Graph) :
    List.Perm ((breakCyclesGreedy g).edges.map Edge.original) (g.edges.map Edge.original) := by
  rw [breakCyclesGreedy_semantic_identity]
namespace ProtectedCycles
theorem semantic_declarations (g : Graph) (hierarchy : List Edge) :
    (breakWithHierarchy g hierarchy).edges.map Edge.decl = g.edges.map Edge.decl := by
  have h := congrArg (List.map Edge.decl) (semantic_identity g hierarchy)
  simpa only [List.map_map, Function.comp_def, Edge.original_decl] using h
end ProtectedCycles
end Elegant.Layered
