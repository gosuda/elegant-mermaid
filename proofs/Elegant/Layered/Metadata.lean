import Elegant.Layered.Route
import Elegant.Layered.Order

namespace Elegant.Layered.Metadata

open RouteImpl

theorem mapM_projection {α β γ : Type}
    (f : α → Except LayoutError β) (keyA : α → γ) (keyB : β → γ)
    (hf : ∀ a b, f a = .ok b → keyB b = keyA a)
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) :
    ys.map keyB = xs.map keyA := by
  induction xs generalizing ys with
  | nil =>
    have hy : [] = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst ys
    rfl
  | cons a xs ih =>
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
        simp only [List.map_cons, hf a b ha, ih ht]

/-- Existing entries retain their dummy flag; newly appended entries need not
have a corresponding lookup in the input graph. -/
def NodeMetadata (p q : Proper) : Prop :=
  ∀ (v : Nat) (nd : ProperNode), p.nodes[v]? = some nd →
    ∃ nd' : ProperNode, q.nodes[v]? = some nd' ∧ nd'.dummy = nd.dummy

theorem lookup_append {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) (ys : List α) : (xs ++ ys)[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a xs ih =>
    cases i with
    | zero => simpa using h
    | succ i => exact ih (by simpa using h)

theorem nodeMetadata_trans {p q r : Proper}
    (hpq : NodeMetadata p q) (hqr : NodeMetadata q r) : NodeMetadata p r := by
  intro v nd hn
  obtain ⟨nd', hn', hd'⟩ := hpq v nd hn
  obtain ⟨nd'', hn'', hd''⟩ := hqr v nd' hn'
  exact ⟨nd'', hn'', hd''.trans hd'⟩

theorem nodeMetadata_map_append {p q : Proper} (f : ProperNode → ProperNode)
    (hf : ∀ n, (f n).dummy = n.dummy) (extra : List ProperNode)
    (hn : q.nodes = p.nodes.map f ++ extra) : NodeMetadata p q := by
  intro v nd hv
  have hm : (p.nodes.map f)[v]? = some (f nd) := by
    simp [hv]
  exact ⟨f nd, hn ▸ lookup_append hm extra, hf nd⟩

theorem nodeMetadata_map {p q : Proper} (f : ProperNode → ProperNode)
    (hf : ∀ n, (f n).dummy = n.dummy)
    (hn : q.nodes = p.nodes.map f) : NodeMetadata p q := by
  apply nodeMetadata_map_append f hf []
  simpa using hn

theorem nodeMetadata_borderExtension {p q : Proper}
    (h : OrderImpl.BorderExtension p q) : NodeMetadata p q := by
  obtain ⟨_, _, extra, hn, _⟩ := h
  intro v nd hv
  exact ⟨nd, hn ▸ lookup_append hv extra, rfl⟩

theorem nodeMetadata_of_lookup_maps {p q : Proper}
    (h : ∀ v : Nat, (q.nodes[v]?).map ProperNode.dummy =
      (p.nodes[v]?).map ProperNode.dummy) :
    NodeMetadata p q := by
  intro v nd hn
  have hm := h v
  rw [hn] at hm
  cases hq : q.nodes[v]? with
  | none => simp [hq] at hm
  | some nd' =>
    exact ⟨nd', rfl, by simpa [hq] using hm⟩

theorem nodeMetadata_of_dummy_list_eq {p q : Proper}
    (h : q.nodes.map ProperNode.dummy = p.nodes.map ProperNode.dummy) :
    NodeMetadata p q := by
  apply nodeMetadata_of_lookup_maps
  intro v
  have hv := congrArg (fun ns : List Bool => ns[v]?) h
  simpa using hv

theorem properShape_transfer {p q : Proper}
    (he : q.edges = p.edges) (hd : NodeMetadata p q)
    (h : ProperShape p) : ProperShape q := by
  intro o
  have ho : edgesOf q o = edgesOf p o := by simp [edgesOf, edgeAt, he]
  rw [ho]
  apply chainRel_mono (l := edgesOf p o) _ (h o)
  intro i j hij
  obtain ⟨hi, hj, hh, nd, hn, hnd⟩ := hij
  obtain ⟨nd', hn', hd'⟩ := hd _ nd hn
  exact ⟨by simpa [he] using hi, by simpa [he] using hj,
    by simpa [edgeAt, he] using hh, nd',
    by simpa [edgeAt, he] using hn', hd'.trans hnd⟩

theorem properShape_borderExtension {p q : Proper}
    (h : OrderImpl.BorderExtension p q) (clean : ∀ e ∈ p.edges, e.synthetic = false)
    (hs : ProperShape p) : ProperShape (OrderImpl.dropSynthetic q) := by
  have hm : NodeMetadata p q := nodeMetadata_borderExtension h
  exact properShape_transfer (OrderImpl.dropSynthetic_edges_of_extension h clean) hm hs

/-- Declaration provenance depends only on the unchanged proper edges. -/
theorem edges_metadata {p q : Proper} {gedges : List Edge}
    (he : q.edges = p.edges)
    (h : ∀ e ∈ p.edges, ∃ ge, gedges[e.original]? = some ge ∧ e.decl = ge.decl) :
    ∀ e ∈ q.edges, ∃ ge, gedges[e.original]? = some ge ∧ e.decl = ge.decl := by
  simpa only [he] using h

/-- Gap declarations transfer when the ranks of original edge tails are
unchanged. No restriction is imposed on ranks of appended border nodes. -/
theorem gapDeclsDistinct_transfer {p q : Proper}
    (he : q.edges = p.edges)
    (hr : ∀ i, i < p.edges.length →
      rk q.rank (edgeAt p i).tail = rk p.rank (edgeAt p i).tail)
    (h : GapDeclsDistinct p) : GapDeclsDistinct q := by
  intro i j hi hj hg hd
  have hi' : i < p.edges.length := by simpa [he] using hi
  have hj' : j < p.edges.length := by simpa [he] using hj
  apply h i j hi' hj'
  · have hgi : gapOf q i = gapOf p i := by
      unfold gapOf
      simpa only [edgeAt, he] using congrArg Int.toNat (hr i hi')
    have hgj : gapOf q j = gapOf p j := by
      unfold gapOf
      simpa only [edgeAt, he] using congrArg Int.toNat (hr j hj')
    exact hgi.symm.trans (hg.trans hgj)
  · simpa [edgeAt, he] using hd

end Elegant.Layered.Metadata
