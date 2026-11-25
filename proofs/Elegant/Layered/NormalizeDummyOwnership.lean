import Elegant.Layered.Pipeline

set_option autoImplicit false

namespace Elegant.Layered.DummyOwnership

open NormalizeImpl (appendChain chainNode chainOf chainOf_getElem? chainOf_length dummyNodes
  normalizeEdge normalizeEdge_chains_length normalizeLoop)

private structure Ownership (originalCount : Nat) (p : Proper) : Prop where
  originalBound : originalCount ≤ p.nodes.length
  dummyKey : ∀ {v nd}, p.nodes[v]? = some nd → nd.dummy = true →
    originalCount ≤ v ∧ nd.node.border = 0 ∧ ∃ k, nd.edge = some k
  lookupChain : ∀ {v k}, originalCount ≤ v →
    (v ∈ (p.chains[k]?).getD [] ↔ (p.nodes[v]?).bind ProperNode.edge = some k)

private theorem chainOf_mem_new {n a b start span v : Nat}
    (ha : a < n) (hb : b < n) (hv : n ≤ v) :
    v ∈ chainOf a b start span ↔ start ≤ v ∧ v < start + (span - 1) := by
  constructor
  · intro hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
    have hbound := (List.getElem?_eq_some_iff.mp hj).1
    rw [chainOf_length] at hbound
    have hval := Option.some.inj
      ((chainOf_getElem? a b start span j (by omega)).symm.trans hj)
    by_cases hzero : j = 0
    · simp only [chainNode, ite_eq_left hzero] at hval
      omega
    by_cases hlast : j = span
    · simp only [chainNode, ite_eq_right hzero, ite_eq_left hlast] at hval
      omega
    simp only [chainNode, ite_eq_right hzero, ite_eq_right hlast] at hval
    omega
  · rintro ⟨hlower, hupper⟩
    have hpos : v - start + 1 ≠ 0 := by omega
    have hspan : v - start + 1 < span := by omega
    have hval : start + (v - start + 1 - 1) = v := by omega
    refine List.mem_iff_getElem?.mpr ⟨v - start + 1, ?_⟩
    rw [chainOf_getElem? a b start span _ (Nat.le_of_lt hspan), chainNode,
      ite_eq_right hpos, ite_eq_right (Nat.ne_of_lt hspan), hval]

private theorem mem_chain_append {chains : List (List Nat)} {ch : List Nat} {v k : Nat} :
    v ∈ ((chains ++ [ch])[k]?).getD [] ↔
      v ∈ (chains[k]?).getD [] ∨ (k = chains.length ∧ v ∈ ch) := by
  by_cases hk : k < chains.length
  · simp [List.getElem?_append_left hk, Nat.ne_of_lt hk]
  have hge : chains.length ≤ k := by omega
  have hnone : chains[k]? = none := List.getElem?_eq_none hge
  rw [List.getElem?_append_right hge, hnone, List.getElem?_singleton]
  by_cases heq : k = chains.length
  · simp [heq]
  have hsub : k - chains.length ≠ 0 := by omega
  simp [heq, hsub]

private theorem append_ownership {n span : Nat} {slot : Int} {e : Edge}
    {p q : Proper} {ch : List Nat} (hp : Ownership n p)
    (hnodes : q.nodes = p.nodes ++ dummyNodes e p.chains.length slot span)
    (hchains : q.chains = p.chains ++ [ch])
    (hsegment : ∀ {v}, n ≤ v → (v ∈ ch ↔ p.nodes.length ≤ v ∧
      v < p.nodes.length + (span - 1))) : Ownership n q := by
  let made : ProperNode := ⟨{ decl := e.decl, w := slot, h := 0 }, true,
    some p.chains.length, false⟩
  have hold {v : Nat} (hv : v < p.nodes.length) : q.nodes[v]? = p.nodes[v]? := by
    rw [hnodes, List.getElem?_append_left hv]
  have hfresh {v : Nat} (hv : p.nodes.length ≤ v) :
      q.nodes[v]? = if v < p.nodes.length + (span - 1) then some made else none := by
    rw [hnodes, List.getElem?_append_right hv]
    have htest : v - p.nodes.length < span - 1 ↔ v < p.nodes.length + (span - 1) := by omega
    simp only [dummyNodes, List.getElem?_replicate, htest, made]
  refine ⟨?_, ?_, ?_⟩
  · rw [hnodes, List.length_append]
    exact Nat.le_trans hp.originalBound (Nat.le_add_right _ _)
  · intro v nd hnd hd
    by_cases hv : v < p.nodes.length
    · exact hp.dummyKey ((hold hv).symm.trans hnd) hd
    have hge : p.nodes.length ≤ v := by omega
    rw [hfresh hge] at hnd
    split at hnd
    · have heq : made = nd := Option.some.inj hnd
      subst nd
      exact ⟨Nat.le_trans hp.originalBound hge, rfl, p.chains.length, rfl⟩
    · simp at hnd
  · intro v k hvn
    rw [hchains, mem_chain_append, hsegment hvn]
    by_cases hv : v < p.nodes.length
    · have hnge : ¬ p.nodes.length ≤ v := by omega
      rw [hold hv, hp.lookupChain hvn]
      simp [hnge]
    have hge : p.nodes.length ≤ v := by omega
    have hnone : p.nodes[v]? = none := List.getElem?_eq_none hge
    have hnot : v ∉ (p.chains[k]?).getD [] := by
      rw [hp.lookupChain hvn, hnone]
      simp
    rw [hfresh hge]
    by_cases hin : v < p.nodes.length + (span - 1)
    · rw [ite_eq_left hin]
      change _ ↔ some p.chains.length = some k
      constructor
      · rintro (hm | ⟨heq, _⟩)
        · exact False.elim (hnot hm)
        · exact congrArg some heq.symm
      · intro heq
        exact Or.inr ⟨(Option.some.inj heq).symm, hge, hin⟩
    · simp [hnot, hin]

private theorem step_ownership {slot : Int} {n : Nat} {e : Edge} {p q : Proper}
    (hp : Ownership n p) (ha : e.tail < n) (hb : e.head < n)
    (h : normalizeEdge slot p e p.chains.length = .ok q) : Ownership n q := by
  unfold normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst q
    refine append_ownership (slot := slot) (span := 1) (e := e) (ch := []) hp ?_ rfl ?_
    · simp [dummyNodes]
    · intro v _
      change v ∈ ([] : List Nat) ↔ p.nodes.length ≤ v ∧ v < p.nodes.length
      simp only [List.not_mem_nil, false_iff]
      omega
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst q
        let span := (rk p.rank e.head - rk p.rank e.tail).toNat
        exact append_ownership (slot := slot) (e := e) (span := span)
          (ch := chainOf e.tail e.head p.nodes.length span) hp rfl rfl
          (fun {_} hv => chainOf_mem_new ha hb hv)

private theorem loop_ownership {slot : Int} {n : Nat} :
    ∀ (edges : List Edge) (p q : Proper),
      (∀ e ∈ edges, e.tail < n ∧ e.head < n) → Ownership n p →
      normalizeLoop slot (edges.zipIdx p.chains.length) p = .ok q → Ownership n q := by
  intro edges
  induction edges with
  | nil =>
    intro p q _ hp h
    simp only [List.zipIdx_nil, normalizeLoop, Except.ok.injEq] at h
    subst q
    exact hp
  | cons e rest ih =>
    intro p q hb hp h
    rw [List.zipIdx_cons] at h
    simp only [normalizeLoop] at h
    split at h
    · simp at h
    · next nextP hstep =>
      have hlen := normalizeEdge_chains_length hstep
      rw [← hlen] at h
      have he := hb e List.mem_cons_self
      exact ih nextP q (fun other hm => hb other (List.mem_cons_of_mem _ hm))
        (step_ownership hp he.1 he.2 hstep) h

private theorem normalize_ownership {g : Graph} {ranks : List Int} {p : Proper}
    (h : normalize g ranks = .ok p) : Ownership g.nodes.length p := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · next slot _ =>
    split at h
    · next hg =>
      have hb : ∀ e ∈ g.edges, e.tail < g.nodes.length ∧ e.head < g.nodes.length := by
        intro e he
        have hw := RankImpl.wellformed_spec hg.1 e he
        exact ⟨hw.1, hw.2.1⟩
      let initial : Proper :=
        { nodes := g.nodes.map fun n => ⟨n, false, none, false⟩
          edges := [], rank := ranks, chains := [] }
      change normalizeLoop slot (g.edges.zipIdx initial.chains.length) initial = .ok p at h
      refine loop_ownership g.edges initial p hb ⟨by simp [initial], ?_, ?_⟩ h
      · intro v nd hnd hd
        cases hv : g.nodes[v]? with
        | none => simp [initial, List.getElem?_map, hv] at hnd
        | some src =>
          have heq : (⟨src, false, none, false⟩ : ProperNode) = nd := by
            simpa only [initial, List.getElem?_map, hv, Option.map_some, Option.some.injEq]
              using hnd
          subst nd
          cases hd
      · intro v k hv
        have hnone : g.nodes[v]? = none := List.getElem?_eq_none hv
        simp [initial, List.getElem?_map, hnone]
    · simp at h

theorem normalize_dummy_chain_iff {g : Graph} {ranks : List Int} {p : Proper}
    (h : normalize g ranks = .ok p) {v k : Nat} {nd : ProperNode}
    (hv : p.nodes[v]? = some nd) (hd : nd.dummy = true) :
    v ∈ (p.chains[k]?).getD [] ↔ nd.edge = some k := by
  have hp := normalize_ownership h
  have hm := hp.lookupChain (v := v) (k := k) (hp.dummyKey hv hd).1
  simpa only [hv, Option.bind_some] using hm

private theorem chain_of_key {g : Graph} {ranks : List Int} {p : Proper}
    (h : normalize g ranks = .ok p) {v k : Nat} {nd : ProperNode}
    (hv : p.nodes[v]? = some nd) (hd : nd.dummy = true) (hkey : nd.edge = some k) :
    ∃ ch, p.chains[k]? = some ch ∧ v ∈ ch := by
  have hm := (normalize_dummy_chain_iff h hv hd).mpr hkey
  cases hch : p.chains[k]? with
  | none => simp [hch] at hm
  | some ch => exact ⟨ch, rfl, by simpa only [hch, Option.getD_some] using hm⟩

private theorem chain_endpoints {g : Graph} {ranks : List Int} {p : Proper}
    (h : normalize g ranks = .ok p) {v k : Nat} {e : Edge} {ch : List Nat}
    (he : g.edges[k]? = some e) (hc : p.chains[k]? = some ch) (hm : v ∈ ch) :
    e.tail ≠ e.head ∧ ch.head? = some e.tail ∧ ch.getLast? = some e.head := by
  have hf := (Elegant.Layered.normalize_ok h).2.2 k (List.getElem?_eq_some_iff.mp he).1 e he
  by_cases hloop : e.tail = e.head
  · simp only [NormalizeImpl.ChainFact, ite_eq_left hloop] at hf
    have hempty := hf.2
    have hnil := Option.some.inj (hc.symm.trans hempty)
    simp [hnil] at hm
  · simp only [NormalizeImpl.ChainFact, ite_eq_right hloop] at hf
    obtain ⟨actual, hactual, _, hhead, hlast, _⟩ := hf.2
    have heq : actual = ch := Option.some.inj (hactual.symm.trans hc)
    subst actual
    exact ⟨hloop, hhead, hlast⟩

theorem normalize_dummy_owner {g : Graph} {ranks : List Int} {p : Proper}
    (h : normalize g ranks = .ok p) {v : Nat} {nd : ProperNode}
    (hv : p.nodes[v]? = some nd) (hd : nd.dummy = true) :
    g.nodes.length ≤ v ∧ v < p.nodes.length ∧ nd.node.border = 0 ∧
      ∃ k e ch, k < g.edges.length ∧ nd.edge = some k ∧ g.edges[k]? = some e ∧
        p.chains[k]? = some ch ∧ v ∈ ch ∧ e.tail ≠ e.head := by
  obtain ⟨hlo, hborder, k, hk⟩ := (normalize_ownership h).dummyKey hv hd
  obtain ⟨ch, hc, hm⟩ := chain_of_key h hv hd hk
  have hlt := (List.getElem?_eq_some_iff.mp hc).1
  rw [Elegant.Layered.normalize_chains_length h] at hlt
  have he : g.edges[k]? = some (g.edges[k]'hlt) := List.getElem?_eq_getElem hlt
  exact ⟨hlo, (List.getElem?_eq_some_iff.mp hv).1, hborder, k, g.edges[k], ch, hlt,
    hk, he, hc, hm, (chain_endpoints h he hc hm).1⟩

theorem normalized_dummy_nodePath {g : Graph} {ranks : List Int} {p q : Proper}
    (h : normalize g ranks = .ok p) (hchains : q.chains = p.chains)
    {v k : Nat} {nd current : ProperNode} {e : Edge}
    (hv : p.nodes[v]? = some nd) (hd : nd.dummy = true) (hkey : nd.edge = some k)
    (hqv : q.nodes[v]? = some current) (hqd : current.dummy = true)
    (he : g.edges[k]? = some e) :
    OrderImpl.nodePath q v = OrderImpl.commonPath
      ((q.nodes.getD e.tail default).node.clusterPath)
      ((q.nodes.getD e.head default).node.clusterPath) := by
  obtain ⟨ch, hc, hm⟩ := chain_of_key h hv hd hkey
  obtain ⟨_, hhead, hlast⟩ := chain_endpoints h he hc hm
  have hfind : p.chains.find? (fun c => c.contains v) = some ch := by
    cases hfound : p.chains.find? (fun c => c.contains v) with
    | none =>
      have hmiss := List.find?_eq_none.mp hfound ch (List.mem_of_getElem? hc)
      exact False.elim (hmiss (List.contains_iff_mem.mpr hm))
    | some selected =>
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hfound)
      have hmem : v ∈ selected := List.contains_iff_mem.mp
        (List.find?_some (p := fun c : List Nat => c.contains v) hfound)
      have hkey' : nd.edge = some j := (normalize_dummy_chain_iff h hv hd).mp
        (by simpa only [hj, Option.getD_some] using hmem)
      have hjk : j = k := Option.some.inj (hkey'.symm.trans hkey)
      subst j
      exact congrArg some (Option.some.inj (hj.symm.trans hc))
  unfold OrderImpl.nodePath
  simp only [List.getD_eq_getElem?_getD, hqv, Option.getD_some, hqd, Bool.not_true,
    Bool.false_eq_true, ite_false, hchains, hfind, List.headD_eq_head?_getD,
    List.getLastD_eq_getLast?, hhead, hlast]

theorem materialize_normalized_dummy_path {g : Graph} {ranks : List Int} {p q : Proper}
    (h : normalize g ranks = .ok p) (hchains : q.chains = p.chains)
    {v k : Nat} {nd current : ProperNode} {e : Edge}
    (hv : p.nodes[v]? = some nd) (hd : nd.dummy = true) (hkey : nd.edge = some k)
    (hqv : q.nodes[v]? = some current) (hqd : current.dummy = true)
    (he : g.edges[k]? = some e) :
    (PipelineImpl.materializeDummyPaths q).nodes[v]? =
      some { current with
        node := { current.node with
          clusterPath := OrderImpl.commonPath
            ((q.nodes.getD e.tail default).node.clusterPath)
            ((q.nodes.getD e.head default).node.clusterPath) } } := by
  have hpath := normalized_dummy_nodePath h hchains hv hd hkey hqv hqd he
  simp only [PipelineImpl.materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
    hqv, Option.map_some, Nat.zero_add, hqd, ↓reduceIte, hpath]

#print axioms normalize_dummy_chain_iff
#print axioms normalize_dummy_owner
#print axioms materialize_normalized_dummy_path
#print axioms normalized_dummy_nodePath

end Elegant.Layered.DummyOwnership
