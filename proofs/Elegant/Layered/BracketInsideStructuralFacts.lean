import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BottomClearanceInside

set_option autoImplicit false

/-!
# Structural seams: side-border height and plain non-dummy borders

Two of the six graph-level clauses of `BracketInsidePremises`
(`FrameClearanceSeam.lean`) hold for every measured graph, in the form
`bracket_inside_rank_below_bottom` consumes them:

* `sideTitleHeightZero` — side borders (`±1`) of an executed component run
  have zero height.  The `±1` nodes are exactly the appended pairs of
  `OrderImpl.addClusterBorders`, whose node records are created with `h := 0`;
  no node of the bordered input carries a `±1` border (a non-dummy `NodeKeys`
  entry copies the measured graph's marker border `0`/`-2`/`2`, a dummy entry
  carries `0`, and an appended title copy carries `3`), and
  `clearProxyExtents`/`materializeDummyPaths` preserve node height.
  Border-`3` title copies are not claimed: they keep the anchor's title
  height.
* `nonDummyBorderPlain` — a non-dummy, non-proxy node of positive height has
  border `0` or `3`: by `coordinateGraph_lookup` its border is the source
  node's border (a marker border `0`/`-2`/`2`, and the proxies are excluded
  by hypothesis), a side border `±1` (excluded by the first theorem, since
  such nodes have zero height), or a title copy's `3`.
-/

namespace Elegant.Layered.PipelineImpl

/-! ### The appended border pairs of `addClusterBorders` have zero height -/

/-- The strengthened form of `addClusterBorders_extra`: the appended border
pairs are non-dummy side borders `±1` with zero height, exactly as the fold
of `OrderImpl.addClusterBorders` constructs them. -/
theorem addClusterBorders_extra_height (p : Proper) (bw : Int) :
    ∃ extra : List ProperNode, (OrderImpl.addClusterBorders p bw).nodes = p.nodes ++ extra ∧
      ∀ n ∈ extra, n.dummy = false ∧ (n.node.border = -1 ∨ n.node.border = 1) ∧
        n.node.h = 0 := by
  unfold OrderImpl.addClusterBorders
  apply OrderImpl.foldl_inv
    (fun s => ∃ extra : List ProperNode, s.nodes = p.nodes ++ extra ∧
      ∀ n ∈ extra, n.dummy = false ∧ (n.node.border = -1 ∨ n.node.border = 1) ∧
        n.node.h = 0) _ _ p ⟨[], by simp, by simp⟩
  intro out hout q _
  dsimp only
  split
  · exact hout
  · apply OrderImpl.foldl_inv
      (fun s => ∃ extra : List ProperNode, s.nodes = p.nodes ++ extra ∧
        ∀ n ∈ extra, n.dummy = false ∧ (n.node.border = -1 ∨ n.node.border = 1) ∧
          n.node.h = 0) _ _ out hout
    intro state hstate offset _
    obtain ⟨extra, hx, hall⟩ := hstate
    let nl : ProperNode := ⟨{ decl := q.1.node.decl, w := bw, h := 0, clusterPath := q.1.node.clusterPath, border := -1 }, false, none, false⟩
    let nr : ProperNode := ⟨{ decl := q.1.node.decl, w := bw, h := 0, loopExtent := q.1.node.loopExtent, clusterPath := q.1.node.clusterPath, border := 1 }, false, none, false⟩
    refine ⟨extra ++ [nl, nr], ?_, ?_⟩
    · simp [hx, List.append_assoc, nl, nr]
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hall n hn
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl
        · exact ⟨rfl, Or.inl rfl, rfl⟩
        · exact ⟨rfl, Or.inr rfl, rfl⟩

/-! ### Side borders of the coordinate graph have zero height -/

/-- A `±1` node of the coordinate graph of a labeled run source has zero
height: `±1` borders exist only among the appended `addClusterBorders` pairs
(whose `h` is `0` by construction), because every source node carries a
marker border (`0`/`-2`/`2`, dummy or not) or a title copy's `3`.  The
`clearProxyExtents` and `materializeDummyPaths` wrappers preserve node
height. -/
theorem coordinateGraph_side_height {P : Params} {cg : Graph} {labeled : Proper}
    (hkeys : NodeKeys cg labeled)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = 0 ∨ node.border = -2 ∨ node.border = 2)
    {v : Nat} {nd : ProperNode}
    (h : (coordinateGraph P labeled).nodes[v]? = some nd)
    (hside : nd.node.border = -1 ∨ nd.node.border = 1) :
    nd.node.h = 0 := by
  unfold coordinateGraph at h
  obtain ⟨m1, hm1, _, hb, hh, _⟩ := materialize_lookup _ h
  rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
  obtain ⟨m2, hm2, rfl⟩ := hm1
  obtain ⟨_, c2, _, c4⟩ := clearF_keys m2
  rw [hh, c4]
  have hmb : m2.node.border = nd.node.border := c2.symm.trans hb.symm
  have hm2side : m2.node.border = -1 ∨ m2.node.border = 1 := by
    rw [hmb]; exact hside
  obtain ⟨extra, hx, hall⟩ :=
    addClusterBorders_extra_height (titleReservations (sizeProperPorts P labeled))
      P.clusterBorderW
  rw [hx] at hm2
  by_cases hvt : v < (titleReservations (sizeProperPorts P labeled)).nodes.length
  · exfalso
    rw [List.getElem?_append_left hvt] at hm2
    rw [titleReservations_nodes] at hm2
    have hlenS : (sizeProperPorts P labeled).nodes.length = labeled.nodes.length :=
      sizeProperPorts_length P labeled
    have hlenA : ((sizeProperPorts P labeled).nodes.map titleF).length =
        labeled.nodes.length := by
      simp only [List.length_map, hlenS]
    by_cases hvl : v < labeled.nodes.length
    · rw [List.getElem?_append_left (by rw [hlenA]; exact hvl)] at hm2
      rw [List.getElem?_map] at hm2
      cases hsm : (sizeProperPorts P labeled).nodes[v]? with
      | none => rw [hsm] at hm2; simp at hm2
      | some ms =>
          rw [hsm, Option.map_some] at hm2
          have hm2def : titleF ms = m2 := Option.some.inj hm2
          have hmsBorder : (titleF ms).node.border = ms.node.border :=
            (titleF_keys ms).2.1
          rw [← hm2def, hmsBorder] at hm2side
          obtain ⟨m, hlm⟩ : ∃ m, labeled.nodes[v]? = some m :=
            ⟨labeled.nodes[v], List.getElem?_eq_getElem hvl⟩
          have hkey := sizeProperPorts_key P labeled v
          rw [hsm, hlm, Option.map_some, Option.map_some] at hkey
          have hborderEq : ms.node.border = m.node.border := by
            have htuple := Option.some.inj hkey
            injection htuple with _ hpair
            injection hpair with hb _
          rcases hkeys v m hlm with ⟨n, hn, _, hnb, _⟩ | ⟨_, hmb0, _⟩
          · have hmarks := hmarkers v n hn
            omega
          · omega
    · rw [List.getElem?_append_right (by rw [hlenA]; omega)] at hm2
      rw [hlenA] at hm2
      rw [List.getElem?_map] at hm2
      cases hsq : (titleNodes (sizeProperPorts P labeled))[v - labeled.nodes.length]? with
      | none => rw [hsq] at hm2; simp at hm2
      | some q =>
          rw [hsq, Option.map_some] at hm2
          have hm2def : copyF q = m2 := Option.some.inj hm2
          rw [← hm2def] at hm2side
          have hc3 : ((copyF q).node.border : Int) = 3 := rfl
          omega
  · rw [List.getElem?_append_right (by omega)] at hm2
    exact (hall m2 (List.mem_of_getElem? hm2)).2.2

/-! ### The two seams -/

theorem sideTitleHeightZero_of_measuredGraph {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) :
    sideTitleHeightZero P graph := by
  intro comp _hcomp candidate run labels orderOptions hrun v hv
  obtain ⟨labeled, hcoord, hkeys, _, _⟩ := componentRun_coordinate_source_alignment hrun
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      node.border = 0 ∨ node.border = -2 ∨ node.border = 2 :=
    fun _ _ hnode => (componentCandidate_marker_shape hgraph hnode).1
  cases hvg : run.coordinateProper.nodes[v]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hvg, Option.getD_none] at hv
      have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
      omega
  | some nd =>
      have hndD : run.coordinateProper.nodes.getD v default = nd := by
        simp [List.getD_eq_getElem?_getD, hvg]
      rw [hndD] at hv
      obtain ⟨hrecord, _⟩ := componentRun_border_record hrun hvg hv
      unfold RouteImpl.nodeH
      rw [hrecord]
      rw [← hcoord] at hvg
      exact coordinateGraph_side_height hkeys hmarkers hvg hv

theorem nonDummyBorderPlain_of_measuredGraph {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) :
    nonDummyBorderPlain P graph := by
  intro comp hcomp candidate run labels orderOptions hrun v hdummy hnotm2 hnot2 hheight
  cases hvg : run.coordinateProper.nodes[v]? with
  | none =>
      left
      rw [List.getD_eq_getElem?_getD, hvg, Option.getD_none]
      rfl
  | some nd =>
      have hndD : run.coordinateProper.nodes.getD v default = nd := by
        simp [List.getD_eq_getElem?_getD, hvg]
      rw [hndD] at hdummy hnotm2 hnot2
      rw [hndD]
      obtain ⟨labeled, hcoord, hkeys, _, _⟩ := componentRun_coordinate_source_alignment hrun
      rw [← hcoord] at hvg
      rcases coordinateGraph_lookup P labeled hvg with
        ⟨m, hm, hdum, hbor, _, _⟩ | ⟨_, hdB⟩ | ⟨_, _, _, _, _, hb3, _⟩
      · rcases hkeys v m hm with ⟨n, hn, _, hnb, _⟩ | ⟨hmd, _, _⟩
        · left
          have hmarks := (componentCandidate_marker_shape hgraph hn).1
          have hchain : nd.node.border = n.border := hbor.trans hnb
          omega
        · rw [hdum, hmd] at hdummy; simp at hdummy
      · exfalso
        have hz : RouteImpl.nodeH run.proper v = 0 :=
          sideTitleHeightZero_of_measuredGraph hgraph comp hcomp candidate run labels
            orderOptions hrun v (by rw [hndD]; exact hdB)
        exact absurd hz hheight
      · right
        exact hb3

end Elegant.Layered.PipelineImpl
