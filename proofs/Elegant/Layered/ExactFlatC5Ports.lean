import Elegant.Layered.ExactFlatC5
import Elegant.Layered.BracketInsideStructuralFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C5 ports row.

Proves `x_tailPort_holds`: the exact counterpart of `GroupTailPortOnYs`
(`GroupTailPortProof.lean`). For a successful `componentRunX` whose
chain-tail endpoint is a `border = 2` bottom marker, the route's tail point
is the flat port `⟨px, run.ys v⟩` with `px` inside the marker's box span.

The port x-coordinate comes from `portCoord`, which places port `j` of `n`
at `x - w/2 + fdiv ((j+1) * w) (n+1)`; `portCoord_bounds` (`Route.lean`)
already proves this lies in `[x - w/2, x + w/2]` for `0 ≤ j < n` and
`0 ≤ w`, and `route_endpoints_on_ports` lifts that into the box span for
every run, exact or plain. `sizeProperPortsX` keeps exact widths and widens
the others exactly as the plain `sizeProperPorts` does, so only the
coordinate-graph classification and the zero-height transfer need exact
replays; every other obligation is graph-agnostic and reused directly.

Target theorems:
- `theorem x_tailPort_holds (exactIds : List String) : X_TailPort exactIds`
  (proved here).
- `theorem x_selfRoutes_holds (exactIds : List String) : X_SelfRoutes exactIds`
  (open; see final report).
- `theorem x_chosenPart_holds (exactIds : List String) : X_ChosenPart exactIds`
  (open; see final report).
-/

/-- Every nonempty list of naturals has a `getLast?` witness (copy of the
private `edgesOf_getLast` of `GroupTailPortProof.lean`). -/
private theorem X_tailEdgesOf_getLast (l : List Nat) (hne : l ≠ []) :
    ∃ last, l.getLast? = some last := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    cases rest with
    | nil => exact ⟨a, rfl⟩
    | cons b rest' =>
      obtain ⟨last, hlast⟩ := ih (by simp)
      exact ⟨last, by simpa only [List.getLast?_cons_cons] using hlast⟩

/-- `sizeProperPortsX` preserves the node count (copy of the private
`X_sized_length` of `ExactFlatC2.lean`). -/
private theorem X_tailSized_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  unfold sizeProperPortsX
  simp

/-- Exact bordered-graph node classification (copy of the private
`X_coordinateGraph0_lookup` of `ExactFlatC2.lean`). -/
private theorem X_tailCoord0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := X_tailSized_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
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
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification (copy of the private
`X_coordinateGraph_lookup` of `ExactFlatC2.lean`). -/
private theorem X_tailCoord_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases X_tailCoord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
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

/-- A `±1` coordinate node at a recorded `border = 2` position has zero
height (copy of the private `coord_side_height_of_record` of
`GroupTailPortProof.lean`, with `sizeProperPortsX` in place of
`sizeProperPorts`). -/
private theorem X_tailCoord_side_height
    {P : Params} {exact : List Nat} {_cg : Graph} {labeled : Proper}
    {v : Nat} {n : Node} (hnBorder : n.border = 2)
    (hlab : labeled.nodes[v]? = some ⟨n, false, none, false⟩)
    {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hside : nd.node.border = -1 ∨ nd.node.border = 1) :
    nd.node.h = 0 := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, _, hb, hh, _⟩ := materialize_lookup _ h
  rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
  obtain ⟨m2, hm2, rfl⟩ := hm1
  obtain ⟨_, c2, _, c4⟩ := clearF_keys m2
  rw [hh, c4]
  have hmb : m2.node.border = nd.node.border := c2.symm.trans hb.symm
  have hm2side : m2.node.border = -1 ∨ m2.node.border = 1 := by
    rw [hmb]; exact hside
  obtain ⟨extra, hx, hall⟩ :=
    addClusterBorders_extra_height
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  rw [hx] at hm2
  by_cases hvt : v < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length
  · exfalso
    rw [List.getElem?_append_left hvt] at hm2
    rw [titleReservations_nodes] at hm2
    have hlenS : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length :=
      X_tailSized_length P exact labeled
    have hlenA : ((sizeProperPortsX P exact labeled).nodes.map titleF).length =
        labeled.nodes.length := by
      simp only [List.length_map, hlenS]
    by_cases hvl : v < labeled.nodes.length
    · rw [List.getElem?_append_left (by rw [hlenA]; exact hvl)] at hm2
      rw [List.getElem?_map] at hm2
      cases hsm : (sizeProperPortsX P exact labeled).nodes[v]? with
      | none => rw [hsm] at hm2; simp at hm2
      | some ms =>
          rw [hsm, Option.map_some] at hm2
          have hm2def : titleF ms = m2 := Option.some.inj hm2
          have hmsBorder : (titleF ms).node.border = ms.node.border :=
            (titleF_keys ms).2.1
          rw [← hm2def, hmsBorder] at hm2side
          obtain ⟨m, hlm⟩ : ∃ m, labeled.nodes[v]? = some m :=
            ⟨labeled.nodes[v], List.getElem?_eq_getElem hvl⟩
          have hkey := sizeProperPortsX_key P exact labeled v
          rw [hsm, hlm, Option.map_some, Option.map_some] at hkey
          have hborderEq : ms.node.border = m.node.border :=
            congrArg (fun t => t.2.1) (Option.some.inj hkey)
          have hmEq : m = ⟨n, false, none, false⟩ :=
            Option.some.inj (hlm.symm.trans hlab)
          have hmBorder : m.node.border = 2 := by
            rw [hmEq]; exact hnBorder
          omega
    · rw [List.getElem?_append_right (by rw [hlenA]; omega)] at hm2
      rw [hlenA] at hm2
      rw [List.getElem?_map] at hm2
      cases hsq : (titleNodes (sizeProperPortsX P exact labeled))[v - labeled.nodes.length]? with
      | none => rw [hsq] at hm2; simp at hm2
      | some q =>
          rw [hsq, Option.map_some] at hm2
          have hm2def : copyF q = m2 := Option.some.inj hm2
          rw [← hm2def] at hm2side
          have hc3 : ((copyF q).node.border : Int) = 3 := rfl
          omega
  · rw [List.getElem?_append_right (by omega)] at hm2
    exact (hall m2 (List.mem_of_getElem? hm2)).2.2

/-- A `border = 2` graph node executes as a non-top frame node of zero
height (copy of the private `tailBottomFacts` of `GroupTailPortProof.lean`,
with `componentRunX_spec` and the exact coordinate classification in place
of the plain ones). -/
private theorem X_tailBottomFacts
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hb : (cg.nodes.getD v default).border = 2) :
    RouteImpl.frameKind run.proper v ≠ -2 ∧ RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨_, _, labeled, q0, hn, hlabels, hcoord, _, _, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hget : ∃ n : Node, cg.nodes[v]? = some n ∧ n.border = 2 := by
    cases hnode : cg.nodes[v]? with
    | none =>
      simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_none] at hb
      exact absurd hb (by decide)
    | some n =>
      simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some] at hb
      exact ⟨n, rfl, hb⟩
  obtain ⟨n, hnGet, hnBorder⟩ := hget
  have hlab : labeled.nodes[v]? = some ⟨n, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels (normalize_node_record hn hnGet) rfl
  have hlen : v < labeled.nodes.length :=
    (List.getElem?_eq_some_iff.mp hlab).1
  have hrel := proxyWidths_rel hprox
  have hqn : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq_pc : ∀ (w : Nat) (nd' : ProperNode), run.proper.nodes[w]? = some nd' →
      ∃ nd, run.coordinateProper.nodes[w]? = some nd ∧ nd'.dummy = nd.dummy ∧
        nd'.node.border = nd.node.border ∧ nd'.node.h = nd.node.h := by
    intro w nd' h'
    have hw : w < q0.nodes.length := by
      have := (List.getElem?_eq_some_iff.mp h').1
      rw [hqn] at this
      exact this
    have hw' : w < run.coordinateProper.nodes.length := by
      have hlenEq : q0.nodes.length = run.coordinateProper.nodes.length := hrel.2.2.1
      omega
    obtain ⟨nd, hnd⟩ : ∃ nd, run.coordinateProper.nodes[w]? = some nd :=
      ⟨run.coordinateProper.nodes[w], List.getElem?_eq_getElem hw'⟩
    obtain ⟨nd2, h2, d2, b2, hh2⟩ := hrel.2.2.2.2.1 w nd hnd
    rw [hqn] at h'
    rw [h2] at h'
    have hEq := Option.some.inj h'
    subst hEq
    exact ⟨nd, hnd, d2, b2, hh2⟩
  cases hproper : run.proper.nodes[v]? with
  | none =>
    refine ⟨?_, ?_⟩
    · have hfk0 : RouteImpl.frameKind run.proper v = 0 := by
        simp [RouteImpl.frameKind, hproper]
      omega
    · simp [RouteImpl.nodeH, hproper]
  | some qa =>
    obtain ⟨pa, hpa, hdum, hbor, hh⟩ := hq_pc v qa hproper
    have hC : (coordinateGraphX P exact labeled).nodes[v]? = some pa := by
      rw [hcoord]; exact hpa
    rcases X_tailCoord_lookup P exact labeled hC with
      ⟨m, hm, hdumC, hborC, _, hh0⟩ | ⟨hdF, hbS⟩ | ⟨_, _, _, hvLen, _, _, _⟩
    · have hmEq : m = ⟨n, false, none, false⟩ :=
        Option.some.inj (hm.symm.trans hlab)
      have hpaDummy : pa.dummy = false := by rw [hdumC, hmEq]
      have hpaBorder : pa.node.border = 2 := by rw [hborC, hmEq]; exact hnBorder
      have hhZero : pa.node.h = 0 := hh0 (Or.inr hpaBorder)
      have hqaDummy : qa.dummy = false := hdum.trans hpaDummy
      have hqaBorder : qa.node.border = 2 := hbor.trans hpaBorder
      have hqaH : qa.node.h = pa.node.h := hh
      have hfk2 : RouteImpl.frameKind run.proper v = 2 :=
        (isBottom_iff hproper).mpr ⟨hqaDummy, hqaBorder⟩
      refine ⟨?_, ?_⟩
      · rw [hfk2]; decide
      · have hnhEq : RouteImpl.nodeH run.proper v = qa.node.h := by
          simp [RouteImpl.nodeH, hproper]
        rw [hnhEq, hqaH, hhZero]
    · have hhZero : pa.node.h = 0 :=
        X_tailCoord_side_height (_cg := cg) hnBorder hlab hC hbS
      have hqaDummy : qa.dummy = false := hdum.trans hdF
      have hqaBorder : qa.node.border = -1 ∨ qa.node.border = 1 := by
        rw [hbor]; exact hbS
      refine ⟨?_, ?_⟩
      · have hfkEq : RouteImpl.frameKind run.proper v = qa.node.border := by
          simp [RouteImpl.frameKind, hproper, hqaDummy]
        rw [hfkEq]
        rcases hqaBorder with h1 | h1 <;> omega
      · have hnhEq : RouteImpl.nodeH run.proper v = qa.node.h := by
          simp [RouteImpl.nodeH, hproper]
        rw [hnhEq, hh, hhZero]
    · exfalso
      omega

/-- The executed tail port of a `border = 2` bottom-marker endpoint is the
flat port `⟨px, run.ys v⟩`: both stored tail port forms of
`route_endpoints_on_ports` place the tail-side point at
`boxRect.y + boxRect.h`, and the executed exact node has zero height with
`boxRect.y = run.ys v` (exact counterpart of `groupTailPortOnYs`). -/
theorem x_tailPort_holds (exactIds : List String) : X_TailPort exactIds := by
  unfold X_TailPort
  intro P inp cg run labels orderOptions hrun i hi first hfirst hb
  obtain ⟨rt, hrt, horiginal, _⟩ := componentRunX_route_of_index hrun hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, hroutes⟩ :=
    componentRunX_spec hrun
  have hne : RouteImpl.edgesOf run.proper i ≠ [] := by
    intro hnil
    rw [hnil] at hfirst
    simp at hfirst
  obtain ⟨last, hlast⟩ := X_tailEdgesOf_getLast _ hne
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    rw [horiginal]; exact hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    rw [horiginal]; exact hlast
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  obtain ⟨hfk, hnh⟩ := X_tailBottomFacts hrun hb
  obtain ⟨px, _, _, _, hpx0, hpx1, _, _, hend⟩ :=
    route_endpoints_on_ports hrouting hroutes rt hm first last hfirst' hlast'
  rw [horiginal] at hend
  have hhEq : (RouteImpl.boxRect run.proper run.xs run.ys
      (RouteImpl.edgeAt run.proper first).tail).y +
      (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).h =
      run.ys.getD (RouteImpl.edgeAt run.proper first).tail 0 := by
    simp only [RouteImpl.boxRect, RouteImpl.yAt]
    rw [hnh]
    exact Int.add_zero _
  refine ⟨rt, px, hrt, hpx0, hpx1, ?_, ?_⟩
  · intro hrev
    rw [ite_eq_left hrev] at hend
    obtain ⟨-, htail⟩ := hend
    rw [hhEq] at htail
    exact htail
  · intro hcon
    have hnc : ¬((cg.edges.map (·.reversed)).getD i false = true) := by
      rw [hcon]; decide
    rw [ite_eq_right hnc] at hend
    obtain ⟨hhead, -⟩ := hend
    rw [ite_eq_right hfk] at hhead
    rw [hhEq] at hhead
    exact hhead

end PipelineImpl
end Layered
end Elegant
