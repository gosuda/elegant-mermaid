import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.Order

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl
/-- Entries of `commonPath` come from its first argument. -/
theorem commonPath_mem_first {a b : List Nat} {elem : Nat} :
    elem ∈ OrderImpl.commonPath a b → elem ∈ a := by
  induction a generalizing b with
  | nil =>
    intro h
    simp [OrderImpl.commonPath] at h
  | cons x xs ih =>
    cases b with
    | nil =>
      intro h
      simp [OrderImpl.commonPath] at h
    | cons y ys =>
      intro h
      have hc : OrderImpl.commonPath (x :: xs) (y :: ys) =
          if x = y then x :: OrderImpl.commonPath xs ys else [] := rfl
      rw [hc] at h
      by_cases heq : x = y
      · simp only [heq, ↓reduceIte] at h
        rcases List.mem_cons.mp h with heq2 | hm
        · exact List.mem_cons.mpr (Or.inl (heq2.trans heq.symm))
        · exact List.mem_cons_of_mem _ (ih hm)
      · simp only [heq, ↓reduceIte] at h
        exact absurd h (by simp)

/-- `normalizeEdge` never rewrites the existing prefix. -/
theorem normalizeEdge_prefix {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p')
    {v : Nat} (hv : v < p.nodes.length) :
    p'.nodes[v]? = p.nodes[v]? := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        unfold NormalizeImpl.appendChain
        simp only
        rw [List.getElem?_append_left hv]

/-- Length never shrinks across `normalizeEdge`. -/
theorem normalizeEdge_length_le {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') :
    p.nodes.length ≤ p'.nodes.length := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact Nat.le_refl _
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        unfold NormalizeImpl.appendChain
        simp only [List.length_append]
        exact Nat.le_add_right _ _

/-- `normalizeLoop` never rewrites the existing prefix. -/
theorem normalizeLoop_prefix {slot : Int} {l : List (Edge × Nat)} {q q' : Proper}
    (h : NormalizeImpl.normalizeLoop slot l q = .ok q')
    {v : Nat} (hv : v < q.nodes.length) :
    q'.nodes[v]? = q.nodes[v]? := by
  induction l generalizing q with
  | nil =>
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    rfl
  | cons hd rest ih =>
    obtain ⟨e, idx⟩ := hd
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      have hle := normalizeEdge_length_le h1
      have hpre := normalizeEdge_prefix h1 hv
      have hv1 : v < q1.nodes.length := by omega
      have hrest := ih h hv1
      rw [hrest, hpre]

/-- Normalization keeps every original node record on its index. -/
theorem normalize_decl_prefix {g : Graph} {rank : List Int} {p : Proper}
    (h : NormalizeImpl.normalize g rank = .ok p)
    {v : Nat} {n : Node} (hn : g.nodes[v]? = some n) :
    ∃ pn : ProperNode, p.nodes[v]? = some pn ∧ pn.node.decl = n.decl ∧
      pn.dummy = false ∧ pn.node.clusterPath = n.clusterPath ∧
      pn.node.border = n.border := by
  have hv : v < g.nodes.length := (List.getElem?_eq_some_iff.mp hn).1
  unfold NormalizeImpl.normalize at h
  split at h
  · exact absurd h (by simp)
  · next slot _ =>
    split at h
    · next _ =>
      have hlen : v < (g.nodes.map (fun nd => (⟨nd, false, none, false⟩ : ProperNode))).length := by
        simpa using hv
      have hpre : p.nodes[v]? =
          ((g.nodes.map (fun nd => (⟨nd, false, none, false⟩ : ProperNode))))[v]? :=
        normalizeLoop_prefix h hlen
      have hinit : ((g.nodes.map (fun nd => (⟨nd, false, none, false⟩ : ProperNode))))[v]? =
          some (⟨n, false, none, false⟩ : ProperNode) := by
        simp only [List.getElem?_map, hn, Option.map_some]
      rw [hpre, hinit] at ⊢
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd h (by simp)

/-- A single label insertion keeps every node declaration on its index. -/
theorem addLabelNode_decl {g : Graph} {p p' : Proper} {label : EdgeLabelSize}
    (h : Labels.addLabelNode g p label = .ok p')
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ nd' : ProperNode, p'.nodes[v]? = some nd' ∧ nd'.node.decl = nd.node.decl ∧
      nd'.dummy = nd.dummy ∧ nd'.node.clusterPath = nd.node.clusterPath ∧
      nd'.node.border = nd.node.border := by
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
          exact ⟨_, hv, rfl, rfl, rfl, rfl⟩
        · dsimp only at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · next q hq =>
              split at h
              · simp at h
              · next nd0 hnd =>
                simp only [Except.ok.injEq] at h
                subst h
                by_cases hvq : q.2 = v
                · subst hvq
                  rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hnd).1]
                  have hndEq : nd = nd0 := Option.some.inj (hv.symm.trans hnd)
                  subst hndEq
                  refine ⟨_, rfl, rfl, rfl, rfl, rfl⟩
                · rw [List.getElem?_set_ne hvq]
                  exact ⟨_, hv, rfl, rfl, rfl, rfl⟩

/-- Label insertion over a list keeps every node declaration on its index. -/
theorem addLabelNodes_decl {g : Graph} :
    ∀ (labels : List EdgeLabelSize) (p p' : Proper),
      Labels.addLabelNodes g p labels = .ok p' →
      ∀ {v : Nat} {nd : ProperNode}, p.nodes[v]? = some nd →
        ∃ nd' : ProperNode, p'.nodes[v]? = some nd' ∧ nd'.node.decl = nd.node.decl ∧
          nd'.dummy = nd.dummy ∧ nd'.node.clusterPath = nd.node.clusterPath ∧
          nd'.node.border = nd.node.border
  | [], p, _, h, _, _, hv => by
    simp only [Labels.addLabelNodes, Except.ok.injEq] at h
    subst h
    exact ⟨_, hv, rfl, rfl, rfl, rfl⟩
  | label :: rest, p, p', h, _, _, hv => by
    simp only [Labels.addLabelNodes] at h
    cases he : Labels.addLabelNode g p label with
    | error e =>
      simp only [he, bind, Except.bind] at h
      exact absurd h (by simp)
    | ok q =>
      simp only [he, bind, Except.bind] at h
      obtain ⟨mid, hmid, hdecl, hdum, hpath, hbord⟩ := addLabelNode_decl he hv
      obtain ⟨nd', hnd', hdecl2, hdum2, hpath2, hbord2⟩ :=
        addLabelNodes_decl rest q _ h hmid
      exact ⟨nd', hnd', hdecl2.trans hdecl, hdum2.trans hdum,
        hpath2.trans hpath, hbord2.trans hbord⟩

/-- `sizeProperPorts` keeps declarations, dummy flags, borders and paths. -/
theorem sizeProperPorts_decl {P : Params} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (sizeProperPorts P p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  simp only [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hv,
    Option.map_some] at ⊢
  by_cases hc : (nd.dummy || nd.node.border != 0) = true
  · simp only [hc, ↓reduceIte] at ⊢
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · have hcF : (nd.dummy || nd.node.border != 0) = false := by simpa using hc
    simp [hcF]

/-- `titleF` keeps declarations, dummy flags, borders and paths. -/
theorem titleF_decl {n : ProperNode} :
    (titleF n).node.decl = n.node.decl ∧ (titleF n).dummy = n.dummy ∧
      (titleF n).node.border = n.node.border ∧
      (titleF n).node.clusterPath = n.node.clusterPath := by
  unfold titleF
  by_cases hc : (n.node.border == -2 || n.node.border == 2) = true
  · simp [hc]
  · simp [hc]

/-- `titleReservations` keeps every prefix declaration and path. -/
theorem titleReservations_decl {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (titleReservations p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  have hvlt : v < p.nodes.length := (List.getElem?_eq_some_iff.mp hv).1
  have hmap : ((p.nodes.map titleF)[v]?) = some (titleF nd) := by
    simp only [List.getElem?_map, hv, Option.map_some]
  have happ : ((p.nodes.map titleF ++ (titleNodes p).map copyF)[v]?) = some (titleF nd) := by
    rw [List.getElem?_append_left (by simpa using hvlt)]
    exact hmap
  rw [← titleReservations_nodes] at happ
  obtain ⟨hd, hdum, hbord, hpath⟩ := titleF_decl (n := nd)
  exact ⟨_, happ, hd, hdum, hbord, hpath⟩

/-- `addClusterBorders` keeps every prefix declaration and path. -/
theorem addClusterBorders_decl {p : Proper} {w : Int}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (OrderImpl.addClusterBorders p w).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  obtain ⟨extra, hx, _⟩ := addClusterBorders_extra p w
  have hvlt : v < p.nodes.length := (List.getElem?_eq_some_iff.mp hv).1
  have happ : ((p.nodes ++ extra)[v]?) = some nd := by
    rw [List.getElem?_append_left hvlt]
    exact hv
  rw [← hx] at happ
  exact ⟨_, happ, rfl, rfl, rfl, rfl⟩

/-- `clearF` keeps declarations, dummy flags, borders and paths. -/
theorem clearF_decl {n : ProperNode} :
    (clearF n).node.decl = n.node.decl ∧ (clearF n).dummy = n.dummy ∧
      (clearF n).node.border = n.node.border ∧
      (clearF n).node.clusterPath = n.node.clusterPath ∧
      (clearF n).node.h = n.node.h := by
  unfold clearF
  by_cases hc : (n.node.border == -2 || n.node.border == 2) = true
  · simp [hc]
  · simp [hc]

/-- `clearProxyExtents` keeps declarations, dummy flags, borders and paths. -/
theorem clearProxyExtents_decl {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (clearProxyExtents p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  simp only [clearProxyExtents, List.getElem?_map, hv,
    Option.map_some]
  obtain ⟨hd, hdum, hbord, hpath, _⟩ := clearF_decl (n := nd)
  exact ⟨_, rfl, hd, hdum, hbord, hpath⟩

/-- `materializeDummyPaths` keeps declarations, dummy flags and borders. -/
theorem materialize_decl {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (materializeDummyPaths p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border := by
  unfold materializeDummyPaths at ⊢
  simp only [List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some] at ⊢
  by_cases hd : nd.dummy = true
  · simp only [hd, ↓reduceIte] at ⊢
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  · have hdF : nd.dummy = false := by simpa using hd
    simp only [hdF, Bool.false_eq_true, ↓reduceIte] at ⊢
    exact ⟨_, rfl, rfl, hdF, rfl⟩

/-- `proxyWidths` keeps declarations, dummy flags, borders and paths. -/
theorem proxyWidths_decl_path {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) {v : Nat} {nd : ProperNode}
    (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, q.nodes[v]? = some qn ∧ qn.node.decl = nd.node.decl ∧
      qn.dummy = nd.dummy ∧ qn.node.border = nd.node.border ∧
      qn.node.clusterPath = nd.node.clusterPath := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, hok⟩ := bind_ok h
  obtain ⟨_, hidx⟩ := mapM_getElem? _ _ _ hu
  have hqeq : q = { p with nodes := updated.map (·.1) } :=
    (Prod.mk.inj (Except.ok.inj hok)).1.symm
  have hmem : (p.nodes.zipIdx)[v]? = some (nd, v) := by
    simp [List.getElem?_zipIdx, hv]
  obtain ⟨b, hb1, hb2⟩ := hidx v (nd, v) hmem
  have hqn : q.nodes[v]? = some b.1 := by
    have h0 : (updated.map (·.1))[v]? = some b.1 := by
      simp only [List.getElem?_map, hb2, Option.map_some]
    have h1 : ({ p with nodes := updated.map (·.1) } : Proper).nodes[v]? =
        some b.1 := h0
    rwa [← hqeq] at h1
  have hAll : b.1.node.decl = nd.node.decl ∧ b.1.dummy = nd.dummy ∧
      b.1.node.border = nd.node.border ∧
      b.1.node.clusterPath = nd.node.clusterPath := by
    dsimp only at hb1
    by_cases hcond : (nd.node.border == -2 || nd.node.border == 2) = true
    · simp only [hcond, ↓reduceIte] at hb1
      cases hl : nd.node.clusterPath.getLast? with
      | none => simp [hl] at hb1
      | some owner =>
        simp only [hl] at hb1
        obtain ⟨_, _, hb1⟩ := bind_ok hb1
        obtain ⟨w, _, hb1⟩ := bind_ok hb1
        by_cases hw0 : w < 0
        · simp only [hw0, ↓reduceIte] at hb1
          simp [bind, Except.bind] at hb1
        · simp only [hw0, ↓reduceIte] at hb1
          obtain ⟨_, _, hb1⟩ := bind_ok hb1
          have hb1' : (Except.ok _ : Except LayoutError (ProperNode × Int)) =
              Except.ok b := hb1
          have hb1'' := Except.ok.inj hb1'
          subst hb1''
          exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [hcond] at hb1
      have hb1' : (Except.ok (nd, xs.getD v 0) : Except LayoutError (ProperNode × Int)) =
          Except.ok b := hb1
      have hb1'' := Except.ok.inj hb1'
      subst hb1''
      exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hd, hdum, hbord, hpath⟩ := hAll
  exact ⟨b.1, hqn, hd, hdum, hbord, hpath⟩

/-- `dropSynthetic` keeps all node records. -/
theorem dropSynthetic_decl {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (OrderImpl.dropSynthetic p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  simp only [OrderImpl.dropSynthetic_nodes, hv] at ⊢
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- The coordinate graph keeps every prefix declaration and path. -/
theorem coordinateGraph_decl_prefix {P : Params} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (coordinateGraph P p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧
      (nd.dummy = false → qn.node.clusterPath = nd.node.clusterPath) := by
  unfold coordinateGraph at ⊢
  obtain ⟨s1, hs1, hdecl1, hdum1, hbord1, hpath1⟩ := sizeProperPorts_decl hv
  obtain ⟨t1, ht1, hdecl2, hdum2, hbord2, hpath2⟩ := titleReservations_decl hs1
  obtain ⟨c1, hc1, hdecl3, hdum3, hbord3, hpath3⟩ :=
    addClusterBorders_decl (w := P.clusterBorderW) ht1
  obtain ⟨e1, he1, hdecl4, hdum4, hbord4, hpath4⟩ := clearProxyExtents_decl hc1
  obtain ⟨m1, hm1, hdecl5, hdum5, hbord5⟩ := materialize_decl he1
  refine ⟨m1, hm1, ?_, ?_, ?_, ?_⟩
  · exact hdecl5.trans (hdecl4.trans (hdecl3.trans (hdecl2.trans hdecl1)))
  · exact hdum5.trans (hdum4.trans (hdum3.trans (hdum2.trans hdum1)))
  · exact hbord5.trans (hbord4.trans (hbord3.trans (hbord2.trans hbord1)))
  · intro hnd
    have he1dum : e1.dummy = false := by
      have h1 : s1.dummy = nd.dummy := hdum1
      have h2 : t1.dummy = s1.dummy := hdum2
      have h3 : c1.dummy = t1.dummy := hdum3
      have h4 : e1.dummy = c1.dummy := hdum4
      rw [h4, h3, h2, h1, hnd]
    have hme : m1.node.clusterPath = e1.node.clusterPath := by
      have hlookup : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[v]? =
        some e1 := he1
      unfold materializeDummyPaths at hm1
      simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
        Option.map_some] at hm1
      have hF : e1.dummy = false := he1dum
      simp only [hF, Bool.false_eq_true, ↓reduceIte] at hm1
      have heq := Option.some.inj hm1
      rw [heq]
    rw [hme, hpath4, hpath3, hpath2, hpath1]

/-- Every original candidate node survives the run with its declaration. -/
theorem runDeclOfCandidate {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {n : Node} (hn : cg.nodes[v]? = some n) :
    ∃ out : ProperNode, run.proper.nodes[v]? = some out ∧ out.node.decl = n.decl := by
  obtain ⟨_, p0, labeled, q0, hn0, hl0, hcoord, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨pn0, hpn0, hdecl0, _, _, _⟩ := normalize_decl_prefix hn0 hn
  obtain ⟨pn1, hpn1, hdecl1, _, _, _⟩ := addLabelNodes_decl _ _ _ hl0 hpn0
  obtain ⟨pn2, hpn2, hdecl2, _, _, _⟩ := coordinateGraph_decl_prefix (P := P) hpn1
  have hpn2c : run.coordinateProper.nodes[v]? = some pn2 := by
    rw [← hcoord]
    exact hpn2
  obtain ⟨pn3, hpn3, hdecl3, _, _, _⟩ := proxyWidths_decl_path hproxy hpn2c
  have hpn3q : q0.nodes[v]? = some pn3 := hpn3
  obtain ⟨pn4, hpn4, hdecl4, _, _, _⟩ := dropSynthetic_decl (p := q0) hpn3q
  have hpn4r : run.proper.nodes[v]? = some pn4 := by
    rw [← hdrop]
    exact hpn4
  exact ⟨pn4, hpn4r, hdecl4.trans (hdecl3.trans (hdecl2.trans (hdecl1.trans hdecl0)))⟩

/-- Run-phase residual R1 with the target body inlined (no broken import):
proper node declarations follow candidate declarations. -/
theorem properDeclPreservedCore {inp : Input} {o : Options} {res : FamilyResult} :
    ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      ∀ (v : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
        ∃ out : ProperNode, run.proper.nodes[v]? = some out ∧ out.node.decl = node.decl := by
  intro execution comp candidate run hcomp hrun v node hnode
  obtain ⟨out, hout, hdecl⟩ := runDeclOfCandidate hrun hnode
  exact ⟨out, hout, hdecl⟩
/-- Ancestor indices of a parent id are group boxes. -/
theorem ancestors_mem_group_aux {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    : ∀ (fuel : Nat) (id : String),
      (∃ c ∈ inp.boxes, c.parent = id) → id ≠ "" →
      ∀ {k : Nat}, k ∈ Compound.ancestors inp.boxes fuel id →
        ∀ {b : ModelBox}, inp.boxes[k]? = some b → b.role = .group := by
  intro fuel
  induction fuel with
  | zero =>
    intro id _ _ k hmem b _
    simp [Compound.ancestors] at hmem
  | succ fuel ih =>
    intro id hchild hne k hmem b hb
    by_cases hid : id = ""
    · subst hid
      simp [Compound.ancestors] at hmem
    · cases hfi : inp.boxes.findIdx? (fun bx => bx.id == id) with
      | none =>
        have hempty : Compound.ancestors inp.boxes (fuel + 1) id = [] := by
          simp [Compound.ancestors, hfi]
        rw [hempty] at hmem
        simp at hmem
      | some i =>
        obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
        have hbi : inp.boxes[i]? = some (inp.boxes[i]'hi) :=
          List.getElem?_eq_getElem hi
        have hbxeq : (inp.boxes[i]'hi).id = id := beq_iff_eq.mp hmatch
        have hanc : Compound.ancestors inp.boxes (fuel + 1) id =
            Compound.ancestors inp.boxes fuel (inp.boxes[i]'hi).parent ++ [i] := by
          simp [Compound.ancestors, hfi, hbi]
        rw [hanc] at hmem
        rcases List.mem_append.mp hmem with hleft | hright
        · by_cases hpar : (inp.boxes[i]'hi).parent = ""
          · have hempty : Compound.ancestors inp.boxes fuel (inp.boxes[i]'hi).parent = [] := by
              cases fuel with
              | zero => simp [Compound.ancestors]
              | succ _ => simp [Compound.ancestors, hpar]
            rw [hempty] at hleft
            simp at hleft
          · exact ih (inp.boxes[i]'hi).parent
              ⟨inp.boxes[i]'hi, List.mem_of_getElem? hbi, rfl⟩ hpar hleft hb
        · have hki : k = i := by simpa using hright
          rw [hki] at hb
          have hbbx : b = (inp.boxes[i]'hi) := Option.some.inj (hb.symm.trans hbi)
          subst hbbx
          obtain ⟨c, hcmem, hceq⟩ := hchild
          have hcne : c.parent ≠ "" := by rw [hceq]; exact hne
          obtain ⟨g, hgmem, hgid, hgroup, _⟩ :=
            framedParents_parent hframed hcmem hcne
          have hids := Model.boxIds_nodup hwf
          simp only [inputModel] at hids
          obtain ⟨j, hgj⟩ := List.mem_iff_getElem?.mp hgmem
          have hgjid : (inp.boxes.map (fun bx => bx.id))[j]? = some g.id := by
            simp [List.getElem?_map, hgj]
          have hbiid : (inp.boxes.map (fun bx => bx.id))[i]? = some g.id := by
            simp only [List.getElem?_map, hbi, Option.map_some]
            rw [hbxeq, ← hceq, ← hgid]
          obtain ⟨hilt, he1⟩ := List.getElem?_eq_some_iff.mp hbiid
          obtain ⟨hjlt, he2⟩ := List.getElem?_eq_some_iff.mp hgjid
          have hij : i = j := hids.eq_of_getElem_eq hilt hjlt (he1.trans he2.symm)
          have hbxg : (inp.boxes[i]'hi) = g := by
            have : inp.boxes[i]? = inp.boxes[j]? := by rw [hij]
            simpa [hbi, hgj] using this
          rw [hbxg]
          exact hgroup

/-- Entries of `Compound.path` index group boxes. -/
theorem path_mem_group {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {box : ModelBox} (hmem : box ∈ inp.boxes)
    {k : Nat} (hk : k ∈ Compound.path inp.boxes box)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  unfold Compound.path at hk
  by_cases hpar : box.parent = ""
  · rw [hpar] at hk
    have hempty : Compound.ancestors inp.boxes inp.boxes.length "" = [] := by
      cases hlen : inp.boxes.length with
      | zero => simp [Compound.ancestors]
      | succ n => simp [Compound.ancestors]
    rw [hempty] at hk
    simp at hk
  · exact ancestors_mem_group_aux hwf hframed inp.boxes.length box.parent
      ⟨box, hmem, rfl⟩ hpar hk hb

/-- Measured-graph nodes carry group-indexed paths. -/
theorem measured_nodes_path_group {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {v : Nat} {nd : Node} (hn : execution.graph.nodes[v]? = some nd)
    {k : Nat} (hk : k ∈ nd.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  obtain ⟨nodes, edges, titles, hprepared, hlenNodes, _⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have h2 := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa using h2
  have hnodesLen : nodes.length = inp.boxes.length := by
    rw [hlenNodes, hlinesLen]
  have hmapped : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).length = inp.boxes.length := by
    simp
  by_cases hv : v < nodes.length
  · have hsrc : ∃ box : ModelBox, inp.boxes[v]? = some box := by
      have : v < inp.boxes.length := by omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨box, hbox⟩ := hsrc
    have hmappedBox : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[v]? =
        some (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) := by
      simp [List.getElem?_map, hbox]
    by_cases hgroup : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        ({ box with role := .node } : ModelBox) else box).role = .group
    · have hrec := Compound.prepare_group_title_record _ execution.params.clusterPad titles
        { nodes := nodes, edges := edges, slot := execution.params.slot }
        hv hmappedBox hgroup
      rw [← hprepared] at hrec
      have heq := Option.some.inj (hn.symm.trans hrec)
      have hpath : nd.clusterPath =
          Compound.path _ _ ++ [v] := congrArg Node.clusterPath heq
      rw [hpath] at hk
      rcases List.mem_append.mp hk with hmem | hmem
      · have hpathEq := (fixedSizes_path_index inp hbox).2.2
        rw [hpathEq] at hmem
        exact path_mem_group hwf hframed (List.mem_of_getElem? hbox) hmem hb
      · have hkv : k = v := by simpa using hmem
        subst hkv
        have hb_box : b = box := Option.some.inj (hb.symm.trans hbox)
        rw [hb_box]
        have horig : box.role = .group := by
          by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
          · simp [hf] at hgroup
          · simp [hf] at hgroup
            exact hgroup
        exact horig
    · have hrec := Compound.prepare_plain_node_record _ execution.params.clusterPad titles
        { nodes := nodes, edges := edges, slot := execution.params.slot }
        hv hmappedBox (by simpa using hgroup)
      rw [← hprepared] at hrec
      have heq := Option.some.inj (hn.symm.trans hrec)
      have hpath : nd.clusterPath = Compound.path _ _ := congrArg Node.clusterPath heq
      rw [hpath] at hk
      have hpathEq := (fixedSizes_path_index inp hbox).2.2
      rw [hpathEq] at hk
      exact path_mem_group hwf hframed (List.mem_of_getElem? hbox) hk hb
  · have hbot := Compound.prepare_bottom_of_index _ execution.params.clusterPad titles
      { nodes := nodes, edges := edges, slot := execution.params.slot } v
      (by show nodes.length ≤ v; omega) (by rw [← hprepared]; exact hn)
    obtain ⟨_, _, _, hlt, box, hbsrc, hrole, hpath⟩ := hbot
    rw [hpath] at hk
    rcases List.mem_append.mp hk with hmem | hmem
    · have hboxmem : box ∈ (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b) := List.mem_of_getElem? hbsrc
      obtain ⟨orig, horigmem, horigEq⟩ : ∃ orig ∈ inp.boxes,
          (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
            ({ orig with role := .node } : ModelBox) else orig) = box := by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hboxmem
        simp only [List.getElem?_map] at hi
        obtain ⟨orig, horig, heq⟩ := Option.map_eq_some_iff.mp hi
        exact ⟨orig, List.mem_of_getElem? horig, heq⟩
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp horigmem
      have h := (fixedSizes_path_index inp hm).2.2
      simp only [horigEq] at h
      rw [h] at hmem
      exact path_mem_group hwf hframed horigmem hmem hb
    · have hkv : k = nd.decl := by simpa using hmem
      subst hkv
      obtain ⟨orig, horig, horigEq⟩ : ∃ orig, inp.boxes[nd.decl]? = some orig ∧
          (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
            ({ orig with role := .node } : ModelBox) else orig) = box := by
        simp only [List.getElem?_map] at hbsrc
        obtain ⟨orig, horig, heq⟩ := Option.map_eq_some_iff.mp hbsrc
        exact ⟨orig, horig, heq⟩
      have horigGroup : orig.role = .group := by
        by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) = true
        · simp only [hf] at horigEq
          rw [← horigEq] at hrole
          simp at hrole
        · simp only [hf] at horigEq
          rw [← horigEq] at hrole
          exact hrole
      have hbOrig : b = orig := Option.some.inj (hb.symm.trans horig)
      rw [hbOrig]
      exact horigGroup

/-- Candidate nodes inherit group-indexed paths from the measured graph. -/
theorem candidate_nodes_path_group {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {v : Nat} {nd : Node}
    (hn : (componentCandidate execution.graph comp candidate).nodes[v]? = some nd)
    {k : Nat} (hk : k ∈ nd.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hrec : (componentCandidate execution.graph comp candidate).nodes =
      comp.map fun w => execution.graph.nodes.getD w default := by
    simp [componentCandidate_nodes, componentGraph]
  have hlen : (componentCandidate execution.graph comp candidate).nodes.length =
      comp.length := by rw [hrec, List.length_map]
  have hvlt : v < comp.length := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hcompv : comp[v]? = some (comp[v]'hvlt) := List.getElem?_eq_getElem hvlt
  have hmap : ((comp.map fun w => execution.graph.nodes.getD w default)[v]?) =
      some ((execution.graph.nodes.getD (comp[v]'hvlt) default)) := by
    simp [List.getElem?_map, hcompv]
  rw [← hrec] at hmap
  have hndEq : nd = execution.graph.nodes.getD (comp[v]'hvlt) default :=
    Option.some.inj (hn.symm.trans hmap)
  by_cases hkey : comp[v]'hvlt < execution.graph.nodes.length
  · have hgn : execution.graph.nodes[comp[v]'hvlt]? =
        some (execution.graph.nodes[comp[v]'hvlt]'hkey) :=
      List.getElem?_eq_getElem hkey
    have hgetD : execution.graph.nodes.getD (comp[v]'hvlt) default =
        execution.graph.nodes[comp[v]'hvlt]'hkey := by
      simp [List.getD_eq_getElem?_getD, hgn]
    rw [hndEq, hgetD] at hk
    exact measured_nodes_path_group hwf hframed execution hgn hk hb
  · have hle : execution.graph.nodes.length ≤ comp[v]'hvlt := by omega
    have hgetD : execution.graph.nodes.getD (comp[v]'hvlt) default = default := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rw [hndEq, hgetD] at hk
    have hdef : (default : Node).clusterPath = [] := rfl
    rw [hdef] at hk
    simp at hk

/-- `NodeKeys` transports group-indexed paths from the candidate. -/
theorem nodeKeys_path_group {inp : Input} {cg : Graph}
    (hbase : ∀ (v : Nat) (n : Node), cg.nodes[v]? = some n →
      ∀ (k : Nat), k ∈ n.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {q : Proper} (hkeys : NodeKeys cg q)
    {i : Nat} {pn : ProperNode} (hn : q.nodes[i]? = some pn)
    {k : Nat} (hk : k ∈ pn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  rcases hkeys i pn hn with ⟨n, hcg, _, _, hpath⟩ | ⟨_, _, hpath⟩
  · rw [hpath] at hk
    exact hbase i n hcg k hk b hb
  · simp [hpath] at hk

/-- Labeled nodes carry group-indexed paths. -/
theorem labeled_nodes_path_group {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {cg : Graph}
    (hcg : cg = componentCandidate execution.graph comp candidate)
    {ranks : List Int} {p0 labeled : Proper}
    (hn0 : NormalizeImpl.normalize cg ranks = .ok p0)
    (hl0 : Labels.addLabelNodes cg p0 (componentLabels cg execution.measured) = .ok labeled)
    {i : Nat} {pn : ProperNode} (hn : labeled.nodes[i]? = some pn)
    {k : Nat} (hk : k ∈ pn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  subst hcg
  have hbase : ∀ (v : Nat) (n : Node),
      (componentCandidate execution.graph comp candidate).nodes[v]? = some n →
      ∀ (k : Nat), k ∈ n.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group := by
    intro v n hn k hk b hb
    exact candidate_nodes_path_group hwf hframed execution hcomp hn hk hb
  have hkeys0 := normalize_keys hn0
  have hkeys := addLabelNodes_keys _ _ _ hkeys0 hl0
  exact nodeKeys_path_group hbase hkeys hn hk hb

/-- Title copies reuse existing paths. -/
theorem titleReservations_extra_path {p : Proper}
    {i : Nat} {pn : ProperNode} (hn : (titleReservations p).nodes[i]? = some pn)
    (hpref : p.nodes.length ≤ i) :
    ∃ m : Nat, ∃ md : ProperNode, p.nodes[m]? = some md ∧
      pn.node.clusterPath = md.node.clusterPath := by
  rw [titleReservations_nodes] at hn
  rw [List.getElem?_append_right (by simp only [List.length_map]; exact hpref)] at hn
  have hmem : pn ∈ (titleNodes p).map copyF := List.mem_of_getElem? hn
  obtain ⟨r, hr, hreq⟩ := List.mem_map.mp hmem
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hr
  have hrnode := titleNodes_spec hm
  obtain ⟨hlookup, _⟩ := hrnode
  refine ⟨r.2, r.1, hlookup, by simp [copyF, ← hreq]⟩

/-- `sizeProperPorts` preserves group-indexed paths for all nodes. -/
theorem sizeProperPorts_all_groups {inp : Input} {P : Params} {p : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {i : Nat} {qn : ProperNode} (hn : (sizeProperPorts P p).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hlen : (sizeProperPorts P p).nodes.length = p.nodes.length := by
    simp [sizeProperPorts]
  have hvlt : i < p.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hlookup : p.nodes[i]? = some (p.nodes[i]'hvlt) :=
    List.getElem?_eq_getElem hvlt
  obtain ⟨qn', hqn', hdecl, hdum, hbord, hpath⟩ :=
    sizeProperPorts_decl (p := p) (P := P) hlookup
  have heq := Option.some.inj (hn.symm.trans hqn')
  subst heq
  rw [hpath] at hk
  exact hAll i _ hlookup k hk b hb

/-- `titleReservations` preserves group-indexed paths (prefix and copies). -/
theorem titleReservations_all_groups {inp : Input} {p : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {i : Nat} {qn : ProperNode} (hn : (titleReservations p).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  by_cases hpref : i < p.nodes.length
  · have hlookup : p.nodes[i]? = some (p.nodes[i]'hpref) :=
      List.getElem?_eq_getElem hpref
    obtain ⟨qn', hqn', _, _, _, hpath⟩ := titleReservations_decl hlookup
    have heq := Option.some.inj (hn.symm.trans hqn')
    subst heq
    rw [hpath] at hk
    exact hAll i _ hlookup k hk b hb
  · have hle : p.nodes.length ≤ i := by omega
    obtain ⟨m, md, hm, hpathEq⟩ := titleReservations_extra_path hn hle
    rw [hpathEq] at hk
    exact hAll m md hm k hk b hb

/-- Residual (coordinate extras, one stage): border-extra paths come from labeled
paths. True since extras copy anchor paths. -/
def AddClusterBordersExtraGroups (labeled : Proper) (w : Int) : Prop :=
  ∀ {i : Nat} {nd : ProperNode},
    (OrderImpl.addClusterBorders labeled w).nodes[i]? = some nd →
    ∀ {k : Nat}, k ∈ nd.node.clusterPath →
      ∃ m : Nat, ∃ md : ProperNode, labeled.nodes[m]? = some md ∧ k ∈ md.node.clusterPath

/-- Every border-construction node comes from the source or an anchor path. -/
theorem addClusterBordersExtraGroups_all {labeled : Proper} {w : Int} :
    AddClusterBordersExtraGroups labeled w := by
  unfold AddClusterBordersExtraGroups
  intro i nd hn k hk
  have hmem : nd ∈ (OrderImpl.addClusterBorders labeled w).nodes :=
    List.mem_of_getElem? hn
  rcases addClusterBorders_node_origin labeled w nd hmem with horig | ⟨top, htopmem, bottom, _, hpath⟩
  · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp horig
    exact ⟨m, _, hm, hk⟩
  · obtain ⟨hmemTop, _⟩ := List.mem_filter.mp htopmem
    have hlookup := List.mem_zipIdx_iff_getElem?.mp hmemTop
    exact ⟨top.2, top.1, hlookup, by simpa [hpath] using hk⟩

/-- `addClusterBorders` preserves group-indexed paths via the extras residual. -/
theorem addClusterBorders_all_groups {inp : Input} {p : Proper} {w : Int}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    (hextra : AddClusterBordersExtraGroups p w)
    {i : Nat} {qn : ProperNode}
    (hn : (OrderImpl.addClusterBorders p w).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  unfold AddClusterBordersExtraGroups at hextra
  by_cases hpref : i < p.nodes.length
  · have hlookup : p.nodes[i]? = some (p.nodes[i]'hpref) :=
      List.getElem?_eq_getElem hpref
    obtain ⟨qn', hqn', _, _, _, hpath⟩ := addClusterBorders_decl hlookup
    have heq := Option.some.inj (hn.symm.trans hqn')
    subst heq
    rw [hpath] at hk
    exact hAll i _ hlookup k hk b hb
  · obtain ⟨m, md, hm, hmem⟩ := hextra hn hk
    exact hAll m md hm k hmem b hb

/-- `clearProxyExtents` preserves group-indexed paths for all nodes. -/
theorem clearProxyExtents_all_groups {inp : Input} {p : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {i : Nat} {qn : ProperNode}
    (hn : (clearProxyExtents p).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hvlt : i < p.nodes.length := by
    have hlen : (clearProxyExtents p).nodes.length = p.nodes.length := by
      simp [clearProxyExtents]
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hlookup : p.nodes[i]? = some (p.nodes[i]'hvlt) :=
    List.getElem?_eq_getElem hvlt
  obtain ⟨qn', hqn', _, _, _, hpath⟩ := clearProxyExtents_decl hlookup
  have heq := Option.some.inj (hn.symm.trans hqn')
  subst heq
  rw [hpath] at hk
  exact hAll i _ hlookup k hk b hb

/-- `materializeDummyPaths` preserves group-indexed paths via `nodePath`. -/
theorem materialize_all_groups {inp : Input} {p : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {i : Nat} {qn : ProperNode}
    (hn : (materializeDummyPaths p).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hvlt : i < p.nodes.length := by
    have hlen : (materializeDummyPaths p).nodes.length = p.nodes.length := by
      simp [materializeDummyPaths]
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hlookup : p.nodes[i]? = some (p.nodes[i]'hvlt) :=
    List.getElem?_eq_getElem hvlt
  by_cases hd : (p.nodes[i]'hvlt).dummy = true
  · have hpathEq : qn.node.clusterPath = OrderImpl.nodePath p i := by
      unfold materializeDummyPaths at hn
      simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
        Option.map_some] at hn
      have hnd := Option.some.inj hn
      simp only [hd, ↓reduceIte] at hnd
      have hcl := congrArg Node.clusterPath (congrArg ProperNode.node hnd)
      simpa using hcl.symm
    rw [hpathEq] at hk
    have hget : p.nodes.getD i default = p.nodes[i]'hvlt := by
      simp [List.getD_eq_getElem?_getD, hlookup]
    unfold OrderImpl.nodePath at hk
    have hcond : ((!true : Bool) = true) = False := by decide
    simp only [hget, hd, hcond] at hk
    cases hfind : p.chains.find? (fun chain => chain.contains i) with
    | none =>
      simp only [hfind] at hk
      simp at hk
    | some chain =>
      simp only [hfind] at hk
      have hmem := commonPath_mem_first hk
      cases hhead : p.nodes[(chain.headD i)]? with
      | none =>
        have hgetD : p.nodes.getD (chain.headD i) default = (default : ProperNode) := by
          simp only [List.getD_eq_getElem?_getD, hhead, Option.getD_none]
        rw [hgetD] at hmem
        have hdef : (default : ProperNode).node.clusterPath = [] := rfl
        rw [hdef] at hmem
        simp at hmem
      | some hdNode =>
        have hgetD : p.nodes.getD (chain.headD i) default = hdNode := by
          simp only [List.getD_eq_getElem?_getD, hhead, Option.getD_some]
        rw [hgetD] at hmem
        exact hAll _ hdNode hhead k hmem b hb
  · have hF : (p.nodes[i]'hvlt).dummy = false := by simpa using hd
    have hsame : qn = (p.nodes[i]'hvlt) := by
      unfold materializeDummyPaths at hn
      simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
        Option.map_some] at hn
      simp only [hF, Bool.false_eq_true, ↓reduceIte] at hn
      exact (Option.some.inj hn).symm
    subst hsame
    exact hAll i _ hlookup k hk b hb

/-- `proxyWidths` preserves group-indexed paths for all nodes. -/
theorem proxyWidths_all_groups {inp : Input} {p q : Proper} {xs xs' : List Int}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    (h : proxyWidths p xs = .ok (q, xs'))
    {i : Nat} {qn : ProperNode} (hn : q.nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hvlt : i < p.nodes.length := by
    have hlen := (proxyWidths_rel h).2.2.1
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hlookup : p.nodes[i]? = some (p.nodes[i]'hvlt) :=
    List.getElem?_eq_getElem hvlt
  obtain ⟨qn', hqn', _, _, _, hpath⟩ := proxyWidths_decl_path h hlookup
  have heq := Option.some.inj (hn.symm.trans hqn')
  subst heq
  rw [hpath] at hk
  exact hAll i _ hlookup k hk b hb

/-- `dropSynthetic` preserves group-indexed paths. -/
theorem dropSynthetic_all_groups {inp : Input} {p : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {i : Nat} {qn : ProperNode} (hn : (OrderImpl.dropSynthetic p).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  simp only [OrderImpl.dropSynthetic_nodes] at hn
  exact hAll i qn hn k hk b hb

/-- Coordinate graph preserves group-indexed paths using the extras residual. -/
theorem coordinate_all_groups {inp : Input} {P : Params} {labeled : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), labeled.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    (hextra : AddClusterBordersExtraGroups
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)
    {i : Nat} {qn : ProperNode}
    (hn : (coordinateGraph P labeled).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  unfold coordinateGraph at hn
  have hsize : ∀ (i : Nat) (pn : ProperNode),
      (sizeProperPorts P labeled).nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => sizeProperPorts_all_groups hAll hn hk hb
  have htitle : ∀ (i : Nat) (pn : ProperNode),
      (titleReservations (sizeProperPorts P labeled)).nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => titleReservations_all_groups hsize hn hk hb
  have hadd : ∀ (i : Nat) (pn : ProperNode),
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => addClusterBorders_all_groups htitle hextra hn hk hb
  have hclear : ∀ (i : Nat) (pn : ProperNode),
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[i]? =
        some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => clearProxyExtents_all_groups hadd hn hk hb
  have hmat : ∀ (i : Nat) (pn : ProperNode),
      (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW))).nodes[i]? =
        some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => materialize_all_groups hclear hn hk hb
  exact hmat i qn hn k hk b hb

/-- Run-level cluster-path provenance with the target body inlined (no broken
import): every run-proper path entry is a group box. -/
theorem runClusterPathGroupMembersCore
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      ∀ (i : Nat) (nd : ProperNode),
        run.proper.nodes[i]? = some nd →
        ∀ k ∈ nd.node.clusterPath, ∀ b,
          inp.boxes[k]? = some b → b.role = .group := by
  intro execution comp candidate run hcomp hrun i nd hn k hk b hb
  obtain ⟨_, p0, labeled, q0, hn0, hl0, hcoord, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlabeledAll : ∀ (j : Nat) (pn : ProperNode), labeled.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    exact labeled_nodes_path_group hwf hframed execution hcomp rfl hn0 hl0 hjn hm hbb
  have hextra : AddClusterBordersExtraGroups
      (titleReservations (sizeProperPorts execution.params labeled))
      execution.params.clusterBorderW :=
    addClusterBordersExtraGroups_all
  have hcoordAll : ∀ (j : Nat) (pn : ProperNode),
      (coordinateGraph execution.params labeled).nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    exact coordinate_all_groups hlabeledAll hextra hjn hm hbb
  have hcoordAllRun : ∀ (j : Nat) (pn : ProperNode),
      run.coordinateProper.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    have hjn' : (coordinateGraph execution.params labeled).nodes[j]? = some pn := by
      rw [hcoord]
      exact hjn
    exact hcoordAll j pn hjn' m hm bb hbb
  have hproxyAll : ∀ (j : Nat) (pn : ProperNode), q0.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    exact proxyWidths_all_groups hcoordAllRun hproxy hjn hm hbb
  have hdropAll : ∀ (j : Nat) (pn : ProperNode), run.proper.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    have hqn : (OrderImpl.dropSynthetic q0).nodes[j]? = some pn := by
      rw [hdrop]
      exact hjn
    exact dropSynthetic_all_groups hproxyAll hqn hm hbb
  exact hdropAll i nd hn k hk b hb
end PipelineImpl
end Layered
end Elegant
