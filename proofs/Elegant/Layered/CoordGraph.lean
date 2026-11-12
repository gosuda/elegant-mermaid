import Elegant.Layered.Pipeline
import Elegant.Layered.Metadata

/-!
Facts about the coordinate graph of one component run: the origin of its nodes, the proxy
placement of frame anchors, and the coordinate facts consumed by the route proofs.
-/

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

theorem bind_ok' {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Node keys of a proper graph relative to the compound source graph: real nodes keep the
border and cluster path of their source node; dummies are plain. -/
def NodeKeys (cg : Graph) (q : Proper) : Prop :=
  ∀ (v : Nat) (nd : ProperNode), q.nodes[v]? = some nd →
    (∃ n, cg.nodes[v]? = some n ∧ nd.dummy = false ∧ nd.node.border = n.border ∧
      nd.node.clusterPath = n.clusterPath) ∨
    (nd.dummy = true ∧ nd.node.border = 0 ∧ nd.node.clusterPath = [])

theorem nodeKeys_append_dummies {cg : Graph} {q : Proper} (hI : NodeKeys cg q)
    (extra : List ProperNode) (hx : ∀ n ∈ extra, n.dummy = true ∧ n.node.border = 0 ∧
      n.node.clusterPath = []) (r : List Int) (ch : List (List Nat)) (es : List ProperEdge) :
    NodeKeys cg { nodes := q.nodes ++ extra, edges := es, rank := r, chains := ch } := by
  intro v nd hv
  dsimp only at hv
  by_cases hlt : v < q.nodes.length
  · rw [List.getElem?_append_left hlt] at hv
    exact hI v nd hv
  · rw [List.getElem?_append_right (by omega)] at hv
    right
    exact hx nd (List.mem_of_getElem? hv)

theorem normalizeEdge_keys {cg : Graph} {slot : Int} {q q' : Proper} {e : Edge} {idx : Nat}
    (hI : NodeKeys cg q) (h : NormalizeImpl.normalizeEdge slot q e idx = .ok q') :
    NodeKeys cg q' := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hI
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        unfold NormalizeImpl.appendChain
        apply nodeKeys_append_dummies hI
        intro n hn
        unfold NormalizeImpl.dummyNodes at hn
        obtain ⟨_, rfl⟩ := List.eq_of_mem_replicate hn
        exact ⟨rfl, rfl, rfl⟩

theorem normalizeLoop_keys {cg : Graph} {slot : Int} :
    ∀ (l : List (Edge × Nat)) (q q' : Proper), NodeKeys cg q →
      NormalizeImpl.normalizeLoop slot l q = .ok q' → NodeKeys cg q'
  | [], q, q', hI, h => by
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hI
  | x :: xs, q, q', hI, h => by
    obtain ⟨e, i⟩ := x
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      exact normalizeLoop_keys xs q1 q' (normalizeEdge_keys hI h1) h

theorem normalize_keys {g : Graph} {rank : List Int} {p : Proper}
    (h : NormalizeImpl.normalize g rank = .ok p) : NodeKeys g p := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · next slot hs =>
    split at h
    · refine normalizeLoop_keys _ _ _ ?_ h
      intro v nd hv
      dsimp only at hv
      cases hg : g.nodes[v]? with
      | none => simp [List.getElem?_map, hg] at hv
      | some n =>
        simp only [List.getElem?_map, hg, Option.map_some, Option.some.injEq] at hv
        subst hv
        exact Or.inl ⟨n, rfl, rfl, rfl, rfl⟩
    · simp at h

theorem addLabelNode_keys {cg g : Graph} {p p' : Proper} {label : EdgeLabelSize}
    (hI : NodeKeys cg p) (h : Labels.addLabelNode g p label = .ok p') : NodeKeys cg p' := by
  unfold Labels.addLabelNode at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp only [Except.ok.injEq] at h
          subst h
          exact hI
        · dsimp only at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · next q hq =>
              split at h
              · simp at h
              · next nd hnd =>
                simp only [Except.ok.injEq] at h
                subst h
                intro v nd' hv'
                dsimp only at hv'
                by_cases hvq : q.2 = v
                · subst hvq
                  rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hnd).1] at hv'
                  have hnd' := Option.some.inj hv'
                  subst hnd'
                  rcases hI q.2 nd hnd with h1 | h1
                  · exact Or.inl h1
                  · exact Or.inr h1
                · rw [List.getElem?_set_ne hvq] at hv'
                  exact hI v nd' hv'

theorem addLabelNodes_keys {cg g : Graph} :
    ∀ (labels : List EdgeLabelSize) (p p' : Proper), NodeKeys cg p →
      Labels.addLabelNodes g p labels = .ok p' → NodeKeys cg p'
  | [], p, p', hI, h => by
    simp only [Labels.addLabelNodes, Except.ok.injEq] at h
    subst h
    exact hI
  | label :: rest, p, p', hI, h => by
    simp only [Labels.addLabelNodes] at h
    cases he : Labels.addLabelNode g p label with
    | error e => simp [he, bind, Except.bind] at h
    | ok q =>
      simp only [he, bind, Except.bind] at h
      exact addLabelNodes_keys rest q p' (addLabelNode_keys hI he) h

/-! second block: origin of the coordinate-graph nodes -/

/-- Index-aligned border-`-2` nodes copied by `titleReservations`. -/
def titleNodes (p : Proper) : List (ProperNode × Nat) :=
  p.nodes.zipIdx.filter fun q => q.1.node.border == -2

theorem titleNodes_snd_nodup (p : Proper) : ((titleNodes p).map (·.2)).Nodup := by
  unfold titleNodes
  refine List.Nodup.sublist ((List.filter_sublist).map _) ?_
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

theorem titleNodes_spec {p : Proper} {i : Nat} {q : ProperNode × Nat}
    (h : (titleNodes p)[i]? = some q) : p.nodes[q.2]? = some q.1 ∧ q.1.node.border = -2 := by
  unfold titleNodes at h
  have hm := List.mem_of_getElem? h
  obtain ⟨hmem, hb⟩ := List.mem_filter.mp hm
  refine ⟨?_, by simpa using hb⟩
  exact List.mem_zipIdx_iff_getElem?.mp hmem

def titleF (node : ProperNode) : ProperNode :=
  if node.node.border == -2 || node.node.border == 2 then
    { node with node := { node.node with w := 0, h := 0 } } else node

def copyF (q : ProperNode × Nat) : ProperNode :=
  { q.1 with node := { q.1.node with border := 3, loopExtent := 0 } }

def clearF (node : ProperNode) : ProperNode :=
  if node.node.border == -2 || node.node.border == 2 then
    { node with node := { node.node with loopExtent := 0 } } else node

theorem titleReservations_nodes (p : Proper) :
    (titleReservations p).nodes = p.nodes.map titleF ++ (titleNodes p).map copyF := rfl

theorem clearProxyExtents_nodes (p : Proper) :
    (clearProxyExtents p).nodes = p.nodes.map clearF := rfl

theorem titleF_keys (n : ProperNode) :
    (titleF n).dummy = n.dummy ∧ (titleF n).node.border = n.node.border ∧
      (titleF n).node.clusterPath = n.node.clusterPath ∧
      ((n.node.border = -2 ∨ n.node.border = 2) → (titleF n).node.h = 0) := by
  unfold titleF
  by_cases hc : (n.node.border == -2 || n.node.border == 2) = true
  · simp [hc]
  · have hb : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by simpa using hc
    simp [hc, hb]

theorem clearF_keys (n : ProperNode) :
    (clearF n).dummy = n.dummy ∧ (clearF n).node.border = n.node.border ∧
      (clearF n).node.clusterPath = n.node.clusterPath ∧ (clearF n).node.h = n.node.h := by
  unfold clearF
  by_cases hc : (n.node.border == -2 || n.node.border == 2) = true
  · simp [hc]
  · simp [hc]

def ExtraInv (p s : Proper) : Prop :=
  ∃ extra : List ProperNode, s.nodes = p.nodes ++ extra ∧
    ∀ n ∈ extra, n.dummy = false ∧ (n.node.border = -1 ∨ n.node.border = 1)

theorem addClusterBorders_extra (p : Proper) (bw : Int) :
    ∃ extra : List ProperNode, (OrderImpl.addClusterBorders p bw).nodes = p.nodes ++ extra ∧
      ∀ n ∈ extra, n.dummy = false ∧ (n.node.border = -1 ∨ n.node.border = 1) := by
  unfold OrderImpl.addClusterBorders
  apply OrderImpl.foldl_inv (ExtraInv p) _ _ p ⟨[], by simp, by simp⟩
  intro out hout q _
  dsimp only
  split
  · exact hout
  · apply OrderImpl.foldl_inv (ExtraInv p) _ _ out hout
    intro state hstate offset _
    obtain ⟨extra, hx, hall⟩ := hstate
    let nl : ProperNode := ⟨{ decl := q.1.node.decl, w := bw, h := 0, clusterPath := q.1.node.clusterPath, border := -1 }, false, none⟩
    let nr : ProperNode := ⟨{ decl := q.1.node.decl, w := bw, h := 0, loopExtent := q.1.node.loopExtent, clusterPath := q.1.node.clusterPath, border := 1 }, false, none⟩
    refine ⟨extra ++ [nl, nr], ?_, ?_⟩
    · simp [hx, List.append_assoc, nl, nr]
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hall n hn
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl
        · exact ⟨rfl, Or.inl rfl⟩
        · exact ⟨rfl, Or.inr rfl⟩

theorem sizeProperPorts_key (P : Params) (p : Proper) (v : Nat) :
    ((sizeProperPorts P p).nodes[v]?).map
        (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) =
      (p.nodes[v]?).map (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) := by
  cases hv : p.nodes[v]? with
  | none => simp [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hv]
  | some nd =>
    simp only [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
    by_cases hc : (nd.dummy || nd.node.border != 0) = true
    · simp [hc]
    · simp [hc]

theorem sizeProperPorts_length (P : Params) (p : Proper) :
    (sizeProperPorts P p).nodes.length = p.nodes.length := by
  simp [sizeProperPorts]

/-- Classification of the nodes of the bordered graph by origin. -/
theorem coordinateGraph0_lookup (P : Params) (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat), (titleNodes (sizeProperPorts P p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra (titleReservations (sizeProperPorts P p))
    P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := sizeProperPorts_length P p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPorts P p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPorts P p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPorts P p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPorts_key P p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPorts P p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    exact ⟨by rw [c1]; exact e1, by rw [c2]; exact e2⟩

theorem materialize_lookup (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (materializeDummyPaths p).nodes[v]? = some nd) :
    ∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.h = m.node.h ∧ (m.dummy = false → nd = m) := by
  unfold materializeDummyPaths at h
  simp only [List.getElem?_map, List.getElem?_zipIdx] at h
  cases hp : p.nodes[v]? with
  | none => simp [hp] at h
  | some m =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    refine ⟨m, rfl, ?_⟩
    by_cases hd : m.dummy = true
    · simp only [hd, ↓reduceIte] at h
      subst h
      exact ⟨hd.symm, rfl, rfl, fun h' => by rw [hd] at h'; exact absurd h' (by decide)⟩
    · have hd' : m.dummy = false := by simpa using hd
      simp only [hd', Bool.false_eq_true, ↓reduceIte] at h
      subst h
      exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem materialize_exists (p : Proper) {v : Nat} {m : ProperNode} (h : p.nodes[v]? = some m) :
    ∃ nd, (materializeDummyPaths p).nodes[v]? = some nd ∧ nd.dummy = m.dummy := by
  unfold materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, h, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  split <;> simp_all

/-- Classification of the nodes of the coordinate graph by origin. -/
theorem coordinateGraph_lookup (P : Params) (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraph P p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat), (titleNodes (sizeProperPorts P p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraph at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases coordinateGraph0_lookup P p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

theorem nodup_map_inj_aux {α : Type} (f : α → Nat) {l : List α} (hn : (l.map f).Nodup) {a b : Nat}
    {x y : α} (ha : l[a]? = some x) (hb : l[b]? = some y) (h : f x = f y) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨hai, hax⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hbi, hbx⟩ := List.getElem?_eq_some_iff.mp hb
  have hpa := List.pairwise_iff_getElem.mp hn
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hpa a b (by simpa using hai) (by simpa using hbi) hlt
    simp [hax, hbx, h] at this
  · have := hpa b a (by simpa using hbi) (by simpa using hai) hlt
    simp [hax, hbx, h] at this

/-! third block: properties of the coordinate graph -/

open RouteImpl in
/-- Source-graph shape: border-`-2` anchors have unique cluster paths and no node has border 3. -/
def CgShape (cg : Graph) : Prop :=
  (∀ (a b : Nat) (na nb : Node), cg.nodes[a]? = some na → cg.nodes[b]? = some nb →
    na.border = -2 → nb.border = -2 → na.clusterPath = nb.clusterPath → a = b) ∧
  ∀ n ∈ cg.nodes, n.border ≠ 3

theorem labeled_topUnique {cg : Graph} {q : Proper} (hK : NodeKeys cg q) (hS : CgShape cg)
    {a b : Nat} {na nb : ProperNode} (ha : q.nodes[a]? = some na) (hb : q.nodes[b]? = some nb)
    (h1 : na.node.border = -2) (h2 : nb.node.border = -2)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  rcases hK a na ha with ⟨n1, hn1, _, hb1, hp1⟩ | ⟨_, hb1, _⟩
  · rcases hK b nb hb with ⟨n2, hn2, _, hb2, hp2⟩ | ⟨_, hb2, _⟩
    · exact hS.1 a b n1 n2 hn1 hn2 (by rw [← hb1]; exact h1) (by rw [← hb2]; exact h2)
        (by rw [← hp1, ← hp2]; exact hp)
    · rw [hb2] at h2; exact absurd h2 (by decide)
  · rw [hb1] at h1; exact absurd h1 (by decide)

theorem pc_plain {cg : Graph} {P : Params} {labeled : Proper} (hK : NodeKeys cg labeled)
    {v : Nat} {nd : ProperNode} (h : (coordinateGraph P labeled).nodes[v]? = some nd)
    (hd : nd.dummy = true) : nd.node.border = 0 := by
  rcases coordinateGraph_lookup P labeled h with ⟨m, hm, h1, h2, _, _⟩ | ⟨h1, _⟩ | ⟨i, q, hq, _, h1, h2, _⟩
  · rcases hK v m hm with ⟨n, _, hmd, _, _⟩ | ⟨_, hb, _⟩
    · rw [h1] at hd; rw [hmd] at hd; exact absurd hd (by decide)
    · rw [h2, hb]
  · rw [h1] at hd; exact absurd hd (by decide)
  · obtain ⟨hs, hb⟩ := titleNodes_spec hq
    have hk := sizeProperPorts_key P labeled q.2
    rw [hs] at hk
    cases hp : labeled.nodes[q.2]? with
    | none => simp [hp] at hk
    | some mp =>
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hk1, hk2, _⟩ := hk
      rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
      · rw [h1, hk1, hmd] at hd; exact absurd hd (by decide)
      · rw [hk2] at hb
        rw [hb'] at hb
        exact absurd hb (by decide)

theorem pc_frame_flat {P : Params} {labeled : Proper}
    {v : Nat} {nd : ProperNode} (h : (coordinateGraph P labeled).nodes[v]? = some nd)
    (hb : nd.node.border = -2 ∨ nd.node.border = 2) : nd.node.h = 0 := by
  rcases coordinateGraph_lookup P labeled h with ⟨m, hm, _, _, _, hf⟩ | ⟨_, h1⟩ | ⟨i, q, hq, _, _, h1, _⟩
  · exact hf hb
  · omega
  · omega

theorem pc_title_unique {cg : Graph} {P : Params} {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraph P labeled).nodes[a]? = some na)
    (hb : (coordinateGraph P labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  -- a border-3 node of the coordinate graph is a title copy
  have key : ∀ {v : Nat} {nd : ProperNode}, (coordinateGraph P labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat), (titleNodes (sizeProperPorts P labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases coordinateGraph_lookup P labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPorts_key P labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPorts_key P labeled qi.2
  have kJ := sizeProperPorts_key P labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi) (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

/-! fourth block: proxy placement -/

theorem mapM_getElem? {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ (i : Nat) (a : α), xs[i]? = some a →
        ∃ b, f a = .ok b ∧ ys[i]? = some b := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have hy : [] = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst ys
    exact ⟨rfl, fun i a ha => by simp at ha⟩
  | cons a xs ih =>
    intro ys h
    cases ha : f a with
    | error e => simp [List.mapM_cons, ha, bind, Except.bind] at h
    | ok b =>
      cases ht : xs.mapM f with
      | error e => simp [List.mapM_cons, ha, ht, bind, Except.bind] at h
      | ok bs =>
        have hy : b :: bs = ys := by
          have h' : (Except.ok (b :: bs) : Except LayoutError (List β)) = .ok ys := by
            simpa [List.mapM_cons, ha, ht, bind, Except.bind, pure, Except.pure] using h
          exact Except.ok.inj h'
        subst ys
        obtain ⟨hl, hi⟩ := ih bs ht
        refine ⟨by simp [hl], ?_⟩
        intro i x hx
        cases i with
        | zero =>
          simp at hx
          subst hx
          exact ⟨b, ha, rfl⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact hi i x hx

theorem proxyWidths_rel {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) :
    q.edges = p.edges ∧ q.rank = p.rank ∧ q.nodes.length = p.nodes.length ∧
      xs'.length = p.nodes.length ∧
      (∀ (v : Nat) (nd : ProperNode), p.nodes[v]? = some nd →
        ∃ nd', q.nodes[v]? = some nd' ∧ nd'.dummy = nd.dummy ∧
          nd'.node.border = nd.node.border ∧ nd'.node.h = nd.node.h) ∧
      (∀ (v : Nat) (nd : ProperNode), p.nodes[v]? = some nd →
        ¬ (nd.node.border = -2 ∨ nd.node.border = 2) →
        q.nodes[v]? = some nd ∧ xs'[v]? = some (xs.getD v 0)) := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, h⟩ := bind_ok' h
  have h : (Except.ok _ : Except LayoutError (Proper × List Int)) = Except.ok (q, xs') := h
  have h := Except.ok.inj h
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hu
  have hq : q = { p with nodes := updated.map (·.1) } := (Prod.mk.inj h).1.symm
  have hx : xs' = updated.map (·.2) := (Prod.mk.inj h).2.symm
  subst hq hx
  have hlen' : updated.length = p.nodes.length := by simpa using hlen
  refine ⟨rfl, rfl, by simp [hlen'], by simp [hlen'], ?_, ?_⟩
  · intro v nd hv
    obtain ⟨b, hb1, hb2⟩ := hidx v (nd, v) (by simp [List.getElem?_zipIdx, hv])
    refine ⟨b.1, by simp [List.getElem?_map, hb2], ?_⟩
    dsimp only at hb1
    by_cases hcond : (nd.node.border == -2 || nd.node.border == 2) = true
    · simp only [hcond, ↓reduceIte] at hb1
      cases hl : nd.node.clusterPath.getLast? with
      | none => simp [hl] at hb1
      | some owner =>
        simp only [hl] at hb1
        obtain ⟨span, hspan, hb1⟩ := bind_ok' hb1
        obtain ⟨w, hw, hb1⟩ := bind_ok' hb1
        by_cases hw0 : w < 0
        · simp only [hw0, ↓reduceIte] at hb1
          simp [bind, Except.bind] at hb1
        simp only [hw0, ↓reduceIte] at hb1
        obtain ⟨c, hc, hb1⟩ := bind_ok' hb1
        have hb1 : (Except.ok _ : Except LayoutError (ProperNode × Int)) = Except.ok b := hb1
        have hb1 := Except.ok.inj hb1
        subst hb1
        exact ⟨rfl, rfl, rfl⟩
    · simp only [hcond] at hb1
      have hb1 : (Except.ok (nd, xs.getD v 0) : Except LayoutError (ProperNode × Int)) =
          Except.ok b := hb1
      have hb1 := Except.ok.inj hb1
      subst hb1
      exact ⟨rfl, rfl, rfl⟩
  · intro v nd hv hb
    obtain ⟨b, hb1, hb2⟩ := hidx v (nd, v) (by simp [List.getElem?_zipIdx, hv])
    dsimp only at hb1
    have hcond : ¬ (nd.node.border == -2 || nd.node.border == 2) = true := by simpa using hb
    simp only [hcond] at hb1
    have hb1 : (Except.ok (nd, xs.getD v 0) : Except LayoutError (ProperNode × Int)) =
        Except.ok b := hb1
    have hb1 := Except.ok.inj hb1
    subst hb1
    exact ⟨by simp [List.getElem?_map, hb2], by simp [List.getElem?_map, hb2]⟩

theorem nodeH_proxy {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) (v : Nat) :
    RouteImpl.nodeH q v = RouteImpl.nodeH p v := by
  obtain ⟨_, _, hlen, _, h1, _⟩ := proxyWidths_rel h
  unfold RouteImpl.nodeH
  cases hp : p.nodes[v]? with
  | none =>
    have : q.nodes[v]? = none := by
      rw [List.getElem?_eq_none_iff] at hp ⊢
      omega
    rw [this]
  | some nd =>
    obtain ⟨nd', hq, _, _, hh⟩ := h1 v nd hp
    rw [hq]
    exact hh

theorem layerHeight_proxy {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) (l : List Nat) :
    RouteImpl.layerHeight q l = RouteImpl.layerHeight p l := by
  have hf : RouteImpl.nodeH q = RouteImpl.nodeH p := funext (nodeH_proxy h)
  simp only [RouteImpl.layerHeight, hf]

theorem proxyYs_getD (p : Proper) (layers : List (List Nat)) (top cy : List Int) {v : Nat}
    {nd : ProperNode} (hnd : p.nodes[v]? = some nd) (hv : v < cy.length) :
    (proxyYs p layers top cy).getD v 0 =
      if nd.node.border == -2 then top.getD (rk p.rank v).toNat 0
      else if nd.node.border == 2 then top.getD (rk p.rank v).toNat 0 +
        CoordsImpl.layerHeight p (layers.getD (rk p.rank v).toNat [])
      else cy.getD v 0 := by
  unfold proxyYs
  have hget : cy[v]? = some cy[v] := List.getElem?_eq_getElem hv
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, hget,
    Option.map_some, Option.getD_some, Nat.zero_add, hnd]

theorem topsFrom_head (rg sl : Int) :
    ∀ (ss hs : List Int) (t : Int), ss.length + 1 = hs.length →
      (CoordsImpl.topsFrom rg sl t hs ss).getD 0 0 = t
  | [], [_], t, _ => by simp [CoordsImpl.topsFrom]
  | [], [], t, h => by simp at h
  | [], _ :: _ :: _, t, h => by simp at h
  | _ :: _, [], t, h => by simp at h
  | _ :: _, _ :: _, t, _ => by simp [CoordsImpl.topsFrom]

theorem topsFrom_step (rg sl : Int) :
    ∀ (ss hs : List Int) (t : Int) (k : Nat), ss.length + 1 = hs.length → k + 1 < hs.length →
      (CoordsImpl.topsFrom rg sl t hs ss).getD (k + 1) 0 =
        (CoordsImpl.topsFrom rg sl t hs ss).getD k 0 + hs.getD k 0 + rg + sl * ss.getD k 0 := by
  intro ss
  induction ss with
  | nil =>
    intro hs t k h1 h2
    simp at h1
    omega
  | cons s ss ih =>
    intro hs t k h1 h2
    cases hs with
    | nil => simp at h1
    | cons h hs =>
      cases hs with
      | nil => simp at h1
      | cons h2' hs' =>
        have hlen : ss.length + 1 = (h2' :: hs').length := by simpa using h1
        have e : CoordsImpl.topsFrom rg sl t (h :: h2' :: hs') (s :: ss) =
            t :: CoordsImpl.topsFrom rg sl (t + h + rg + sl * s) (h2' :: hs') ss := rfl
        rw [e]
        cases k with
        | zero =>
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          rw [topsFrom_head rg sl ss (h2' :: hs') _ hlen]
        | succ k' =>
          simp only [List.getD_cons_succ]
          exact ih (h2' :: hs') _ k' hlen (by simpa using h2)

/-! fifth block: assembling the coordinate facts of the executed run -/

theorem isTop_iff {q : Proper} {v : Nat} {n : ProperNode} (h : q.nodes[v]? = some n) :
    RouteImpl.IsTop q v ↔ n.dummy = false ∧ n.node.border = -2 := by
  unfold RouteImpl.IsTop RouteImpl.frameKind
  rw [h]
  cases hd : n.dummy <;> simp [hd]

theorem isBottom_iff {q : Proper} {v : Nat} {n : ProperNode} (h : q.nodes[v]? = some n) :
    RouteImpl.IsBottom q v ↔ n.dummy = false ∧ n.node.border = 2 := by
  unfold RouteImpl.IsBottom RouteImpl.frameKind
  rw [h]
  cases hd : n.dummy <;> simp [hd]

theorem isFrame_iff {q : Proper} {v : Nat} {n : ProperNode} (h : q.nodes[v]? = some n) :
    RouteImpl.IsFrame q v ↔ n.dummy = false ∧ (n.node.border = -2 ∨ n.node.border = 2) := by
  unfold RouteImpl.IsFrame
  rw [isTop_iff h, isBottom_iff h]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

theorem not_isFrame_of_none {q : Proper} {v : Nat} (h : q.nodes[v]? = none) :
    ¬ RouteImpl.IsFrame q v := by
  unfold RouteImpl.IsFrame RouteImpl.IsTop RouteImpl.IsBottom RouteImpl.frameKind
  rw [h]
  simp

/-- Frame clearance: left/right borders and members of a frame row keep clear of the frame
proxy. Open obligation until the order phase proves the border end positions. -/
def FrameClearance (p : Proper) (layers : List (List Nat)) (x : List Int) : Prop :=
  (∀ layer ∈ layers, ∀ t v : Nat, t ∈ layer → v ∈ layer → RouteImpl.IsTop p t → v ≠ t →
    ¬ RouteImpl.IsFrame p v → 0 < RouteImpl.nodeH p v →
    RouteImpl.leftOf p x v + RouteImpl.nodeW p v ≤ RouteImpl.leftOf p x t ∨
      RouteImpl.leftOf p x t ≤ RouteImpl.leftOf p x v) ∧
  (∀ layer ∈ layers, ∀ t v : Nat, t ∈ layer → v ∈ layer → RouteImpl.IsBottom p t →
    v ≠ t → ¬ RouteImpl.IsFrame p v → 0 < RouteImpl.nodeH p v →
    RouteImpl.leftOf p x t + RouteImpl.nodeW p t ≤ RouteImpl.leftOf p x v ∨
      RouteImpl.leftOf p x v + RouteImpl.nodeW p v ≤ RouteImpl.leftOf p x t)

theorem coordFacts_of_parts {P : Params} (hP : P.Valid) {cg : Graph} {labeled pc q0 q : Proper}
    {layers : List (List Nat)} {cx xs cy top ys : List Int} {lr : RouteImpl.LaneRouting}
    {reversed : List Bool} {widths : List Int}
    (hK : NodeKeys cg labeled) (hS : CgShape cg) (hpc : coordinateGraph P labeled = pc)
    (hq : OrderImpl.dropSynthetic q0 = q)
    (hx : crossCoordsClusterWith P.nodeGap P.clusterPad pc layers = .ok cx)
    (hprox : proxyWidths pc cx = .ok (q0, xs))
    (hr : RouteImpl.routeWithLanes P.slot q layers xs reversed widths = .ok lr)
    (hy : rankCoordsWith P.rankGap P.slot pc layers (lr.routing.gaps.map (·.slots)) =
      .ok (cy, top))
    (hys : proxyYs pc layers top cy = ys)
    (hclear : FrameClearance q layers xs) :
    RouteImpl.CoordFacts q layers xs ys top lr.routing
      (min P.nodeGap P.clusterPad) P.rankGap P.slot := by
  obtain ⟨hg, hrg, hs, hh⟩ := hP
  obtain ⟨hn1, hcp, _, _, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hx
  obtain ⟨hrE, hrR, hlen, hxlen, hP1, hP2⟩ := proxyWidths_rel hprox
  have hlay := (RouteImpl.routeWithLanes_geometry hr).1
  obtain ⟨_, _, hmem, hcov, _⟩ := RouteImpl.layersOk_spec hlay
  obtain ⟨_, _, hylen, _, _, htop, hyvv⟩ := CoordsImpl.rankCoordsWith_spec hy
  have hqn : q.nodes = q0.nodes := by rw [← hq]; rfl
  have hqr : q.rank = pc.rank := by rw [← hq]; exact hrR
  have plain : ∀ {v : Nat} {nd : ProperNode}, pc.nodes[v]? = some nd → nd.dummy = true →
      nd.node.border = 0 := fun {v nd} h hd => pc_plain hK (by rw [hpc]; exact h) hd
  have fflat : ∀ {v : Nat} {nd : ProperNode}, pc.nodes[v]? = some nd →
      (nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0 :=
    fun {v nd} h hb => pc_frame_flat (by rw [hpc]; exact h) hb
  have tuniq : ∀ {a b : Nat} {na nb : ProperNode}, pc.nodes[a]? = some na →
      pc.nodes[b]? = some nb → na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b :=
    fun {a b na nb} ha hb h1 h2 hp =>
      pc_title_unique hK hS (by rw [hpc]; exact ha) (by rw [hpc]; exact hb) h1 h2 hp
  -- every node of q comes from a node of pc
  have hq_pc : ∀ (v : Nat) (nd' : ProperNode), q.nodes[v]? = some nd' →
      ∃ nd, pc.nodes[v]? = some nd ∧ nd'.dummy = nd.dummy ∧
        nd'.node.border = nd.node.border ∧ nd'.node.h = nd.node.h := by
    intro v nd' h'
    have hv : v < q0.nodes.length := by
      have := (List.getElem?_eq_some_iff.mp h').1
      rw [hqn] at this
      exact this
    have hv' : v < pc.nodes.length := by omega
    obtain ⟨nd, hnd⟩ : ∃ nd, pc.nodes[v]? = some nd := ⟨pc.nodes[v], List.getElem?_eq_getElem hv'⟩
    obtain ⟨nd2, h2, d2, b2, hh2⟩ := hP1 v nd hnd
    rw [hqn] at h'
    rw [h2] at h'
    have := Option.some.inj h'
    subst this
    exact ⟨nd, hnd, d2, b2, hh2⟩
  have hpc_q : ∀ (v : Nat) (nd : ProperNode), pc.nodes[v]? = some nd →
      ∃ nd', q.nodes[v]? = some nd' ∧ nd'.dummy = nd.dummy ∧
        nd'.node.border = nd.node.border ∧ nd'.node.h = nd.node.h := by
    intro v nd hnd
    obtain ⟨nd', h2, d2, b2, hh2⟩ := hP1 v nd hnd
    exact ⟨nd', by rw [hqn]; exact h2, d2, b2, hh2⟩
  have hnodeHq : ∀ v, RouteImpl.nodeH q v = RouteImpl.nodeH q0 v := by
    intro v; unfold RouteImpl.nodeH; rw [hqn]
  have hnodeH : ∀ v, RouteImpl.nodeH q v = RouteImpl.nodeH pc v := fun v =>
    (hnodeHq v).trans (nodeH_proxy hprox v)
  have hnotframe : ∀ (v : Nat) (pa : ProperNode), pc.nodes[v]? = some pa →
      ¬ RouteImpl.IsFrame q v → pa.node.border ≠ -2 ∧ pa.node.border ≠ 2 := by
    intro v pa hpa hnf
    obtain ⟨qa, hqa, hd, hb, _⟩ := hpc_q v pa hpa
    rw [isFrame_iff hqa] at hnf
    refine ⟨fun hb2 => hnf ⟨?_, Or.inl (by rw [hb]; exact hb2)⟩,
      fun hb2 => hnf ⟨?_, Or.inr (by rw [hb]; exact hb2)⟩⟩ <;>
    · rw [hd]
      cases hdm : pa.dummy
      · rfl
      · have := plain hpa hdm
        omega
  have hcylen : cy.length = pc.nodes.length := by rw [hyvv]; simp
  have hflat : ∀ v, RouteImpl.IsFrame q v → RouteImpl.nodeH q v = 0 := by
    intro v hv
    cases hqv : q.nodes[v]? with
    | none => exact absurd hv (not_isFrame_of_none hqv)
    | some qa =>
      rw [isFrame_iff hqv] at hv
      obtain ⟨pa, hpa, hd, hb, hhh⟩ := hq_pc v qa hqv
      have hf := fflat hpa (by rw [← hb]; exact hv.2)
      have : RouteImpl.nodeH q v = qa.node.h := by simp [RouteImpl.nodeH, hqv]
      rw [this, hhh, hf]
  have hLH : ∀ l, RouteImpl.layerHeight q l = CoordsImpl.layerHeight pc l := fun l =>
    by
    have hf : RouteImpl.nodeH q = RouteImpl.nodeH pc := funext hnodeH
    simp only [RouteImpl.layerHeight, hf]; rfl
  refine ⟨by omega, by omega, hs, hh, ?_, hflat, ?_, hclear.1, hclear.2, ?_, ?_⟩
  · intro layer hl i j a b hij ha hb hna hnb _
    have hLa : a ∈ layer := List.mem_of_getElem? ha
    have hLb : b ∈ layer := List.mem_of_getElem? hb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl
    have hav : a < pc.nodes.length := by
      have h1 := (hmem k layer hk a hLa).1
      rw [hqn] at h1
      omega
    have hbv : b < pc.nodes.length := by
      have h1 := (hmem k layer hk b hLb).1
      rw [hqn] at h1
      omega
    obtain ⟨pa, hpa⟩ : ∃ pa, pc.nodes[a]? = some pa := ⟨_, List.getElem?_eq_getElem hav⟩
    obtain ⟨pb, hpb⟩ : ∃ pb, pc.nodes[b]? = some pb := ⟨_, List.getElem?_eq_getElem hbv⟩
    obtain ⟨a1, a2⟩ := hnotframe a pa hpa hna
    obtain ⟨b1, b2⟩ := hnotframe b pb hpb hnb
    have hsep := CoordsImpl.cluster_all_pairs_separated hx
      (fun a b na nb ha hb h1 h2 hp => tuniq ha hb h1 h2 hp)
      layer hl i j a b pa pb hij ha hb hpa hpb a1 a2 b1 b2
    obtain ⟨hqa, hxa⟩ := hP2 a pa hpa (by omega)
    obtain ⟨hqb, hxb⟩ := hP2 b pb hpb (by omega)
    have hqa' : q.nodes[a]? = some pa := by rw [hqn]; exact hqa
    have hqb' : q.nodes[b]? = some pb := by rw [hqn]; exact hqb
    have hwa : RouteImpl.nodeW q a = RouteImpl.nodeW pc a := by
      simp only [RouteImpl.nodeW, hqa', hpa]
    have hwb : RouteImpl.nodeW q b = RouteImpl.nodeW pc b := by
      simp only [RouteImpl.nodeW, hqb', hpb]
    have hxa' : RouteImpl.xAt xs a = cx.getD a 0 := by
      simp [RouteImpl.xAt, List.getD_eq_getElem?_getD, hxa]
    have hxb' : RouteImpl.xAt xs b = cx.getD b 0 := by
      simp [RouteImpl.xAt, List.getD_eq_getElem?_getD, hxb]
    have hga : RouteImpl.nodeW pc a ≤ CoordsImpl.nodeW pc a := CoordsImpl.nodeW_ge_width pc a
    have hgb : RouteImpl.nodeW pc b ≤ CoordsImpl.nodeW pc b := CoordsImpl.nodeW_ge_width pc b
    unfold CoordsImpl.coordSep at hsep
    unfold RouteImpl.coordSep
    rw [hxa', hxb', hwa, hwb]
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  · intro k l v hkl hv hTop
    obtain ⟨hvn, hrk⟩ := hmem k l hkl v hv
    obtain ⟨qa, hqa⟩ : ∃ qa, q.nodes[v]? = some qa := ⟨_, List.getElem?_eq_getElem hvn⟩
    obtain ⟨pa, hpa, hd, hb, hhh⟩ := hq_pc v qa hqa
    have hT := (isTop_iff hqa).mp hTop
    have hpb : pa.node.border = -2 := by rw [← hb]; exact hT.2
    have hv' : v < cy.length := by
      rw [hcylen]
      have := hvn
      rw [hqn] at this
      omega
    rw [hqr] at hrk
    have hyv : RouteImpl.yAt ys v = top.getD k 0 := by
      rw [← hys]
      unfold RouteImpl.yAt
      rw [proxyYs_getD pc layers top cy hpa hv']
      simp [hpb, hrk]
    rw [hyv, hflat v (Or.inl hTop)]
    omega
  · intro k l v hkl hv hvn hrk
    obtain ⟨qa, hqa⟩ : ∃ qa, q.nodes[v]? = some qa := ⟨_, List.getElem?_eq_getElem hvn⟩
    obtain ⟨pa, hpa, hd, hb, hhh⟩ := hq_pc v qa hqa
    have hvn' : v < pc.nodes.length := by
      have := hvn
      rw [hqn] at this
      omega
    have hv' : v < cy.length := by rw [hcylen]; exact hvn'
    have hrk' : rk pc.rank v = (k : Int) := by rw [← hqr]; exact hrk
    have hLH' := hLH l
    rw [hnodeH v, hLH']
    have hnn : 0 ≤ CoordsImpl.layerHeight pc l := by rw [← hLH']; exact RouteImpl.layerHeight_nonneg q l
    by_cases h2 : pa.node.border = -2
    · have hyv : RouteImpl.yAt ys v = top.getD k 0 := by
        rw [← hys]
        unfold RouteImpl.yAt
        rw [proxyYs_getD pc layers top cy hpa hv']
        simp [h2, hrk']
      have hz : RouteImpl.nodeH pc v = 0 := by
        have : RouteImpl.nodeH pc v = pa.node.h := by simp [RouteImpl.nodeH, hpa]
        rw [this]; exact fflat hpa (Or.inl h2)
      rw [hyv, hz]
      omega
    · by_cases h3 : pa.node.border = 2
      · have hyv : RouteImpl.yAt ys v = top.getD k 0 + CoordsImpl.layerHeight pc l := by
          rw [← hys]
          unfold RouteImpl.yAt
          rw [proxyYs_getD pc layers top cy hpa hv']
          have hb2 : (pa.node.border == -2) = false := by simpa using h2
          have hb3 : (pa.node.border == 2) = true := by simpa using h3
          simp [hb2, hb3, hrk', List.getD_eq_getElem?_getD, hkl]
        have hz : RouteImpl.nodeH pc v = 0 := by
          have : RouteImpl.nodeH pc v = pa.node.h := by simp [RouteImpl.nodeH, hpa]
          rw [this]; exact fflat hpa (Or.inr h3)
        rw [hyv, hz]
        omega
      · have hyv : RouteImpl.yAt ys v = cy.getD v 0 := by
          rw [← hys]
          unfold RouteImpl.yAt
          rw [proxyYs_getD pc layers top cy hpa hv']
          have hb2 : (pa.node.border == -2) = false := by simpa using h2
          have hb3 : (pa.node.border == 2) = false := by simpa using h3
          simp [hb2, hb3]
        have hb := CoordsImpl.rankAxis_node_in_band hy hkl hv hvn' hrk'
        rw [hyv]
        exact hb
  · intro k l hkl hk
    obtain ⟨_, _, _, _, hgl, _, _⟩ := RouteImpl.routeWithLanes_geometry hr
    subst htop
    have hk' : k < lr.routing.gaps.length := by omega
    have hh : (layers.map (CoordsImpl.layerHeight pc)).getD k 0 = CoordsImpl.layerHeight pc l := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hkl]
    have hs' : (lr.routing.gaps.map (·.slots)).getD k 0 = (lr.routing.gaps.getD k default).slots := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk']
    rw [topsFrom_step P.rankGap P.slot (lr.routing.gaps.map (·.slots))
      (layers.map (CoordsImpl.layerHeight pc)) 0 k (by simp; omega) (by simpa using hk), hh, hs',
      hLH l]

end PipelineImpl
end Layered
end Elegant
