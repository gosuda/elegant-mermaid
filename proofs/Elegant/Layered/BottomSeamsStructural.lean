import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BottomClearanceInside

/-!
Structural seams of `bracket_inside_rank_below_bottom`
(`BottomClearanceInside.bracket_inside_rank_below_bottom`).

This unit discharges `sidePathEq`: side borders (`±1`) of a coordinate graph of a
successful component run carry the full cluster path of their group's bottom
proxy and are non-dummy.

The three sibling seams named in the same def block are FALSE on the executed
pipeline and are reported instead of proved (executed counterexample probes are
in `/tmp/bss-witness.lean`, receipts in the worker report):

* `sideTitleHeightZero` and `nonDummyBorderPlain` fail on border-`3` title
  copies: `titleReservations` resets `w`/`h` only on the border-`±2` entries of
  the mapped list, while the appended border-`3` copies keep the anchor's
  measured height, which `Compound.markNodes` sets to
  `title height + cluster_pad ≥ 1`.  No later phase zeroes that height.
* `dummyWidthZero` fails on chain dummies: `NormalizeImpl.dummyNodes` stores
  `w = slot`, and the family `slot` is `768` (cell) resp. `1` (vector), so
  `RouteImpl.nodeW` of a dummy is nonzero.
-/

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

/-! ### Side borders carry the anchor path -/

private theorem addClusterBorders_side_dummy {p : Proper} {bw : Int}
    (hready : OrderImpl.BorderConstructionReady p) {nd : ProperNode}
    (hmem : nd ∈ (OrderImpl.addClusterBorders p bw).nodes)
    (hs : nd.node.border = -1 ∨ nd.node.border = 1) : nd.dummy = false := by
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra p bw
  rw [hx] at hmem
  rcases List.mem_append.mp hmem with hp | he
  · rcases hs with hs1 | hs2
    · exact absurd hs1 (hready.1 nd hp).1
    · exact absurd hs2 (hready.1 nd hp).2
  · exact (hall nd he).1

/-- A side border (`±1`) of the coordinate graph is an emitted border pair: it is
non-dummy and carries the cluster path of a border-`-2` node of the source.
`t` is the `addClusterBorders` input (`titleReservations (sizeProperPorts P p)`). -/
private theorem coordinateGraph_side_path {P : Params} {p t : Proper}
    (ht : t = titleReservations (sizeProperPorts P p))
    (hready : OrderImpl.BorderConstructionReady t)
    {v : Nat} {nd : ProperNode}
    (h : (coordinateGraph P p).nodes[v]? = some nd)
    (hs : nd.node.border = -1 ∨ nd.node.border = 1) :
    nd.dummy = false ∧
    ∃ m : ProperNode, m ∈ t.nodes ∧ m.node.border = -2 ∧
      nd.node.clusterPath = m.node.clusterPath := by
  unfold coordinateGraph at h
  rw [← ht] at h
  obtain ⟨m1, hm1, _, hb1, heq1⟩ := materialize_lookup _ h
  have hm1d : m1.dummy = false := by
    by_cases hc : m1.dummy = true
    · exfalso
      rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
      obtain ⟨m2, hm2get, heq2⟩ := hm1
      have cm2 := clearF_keys m2
      have hm2b : m2.node.border = -1 ∨ m2.node.border = 1 := by
        rw [← cm2.2.1, heq2, ← hb1]; exact hs
      have hm2mem : m2 ∈ (OrderImpl.addClusterBorders t P.clusterBorderW).nodes :=
        List.mem_of_getElem? hm2get
      have hdummy : m2.dummy = false :=
        addClusterBorders_side_dummy hready hm2mem hm2b
      have hnd2 : m1.dummy = false := by
        rw [← heq2, cm2.1]; exact hdummy
      rw [hnd2] at hc
      exact absurd hc (by decide)
    · exact by simpa using hc
  rw [← heq1.2 hm1d] at hm1
  rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
  obtain ⟨m2, hm2, heq2⟩ := hm1
  have cm2 := clearF_keys m2
  rw [heq2] at cm2
  have hm2b : m2.node.border = -1 ∨ m2.node.border = 1 := by
    rw [← cm2.2.1]; exact hs
  have hm2mem : m2 ∈ (OrderImpl.addClusterBorders t P.clusterBorderW).nodes :=
    List.mem_of_getElem? hm2
  have hndF : nd.dummy = false := by
    rw [cm2.1]; exact addClusterBorders_side_dummy hready hm2mem hm2b
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source t P.clusterBorderW hready hm2mem hm2b
  obtain ⟨tmem, hcond⟩ := List.mem_filter.mp htop
  have hget : t.nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp tmem
  refine ⟨hndF, top.1, List.mem_of_getElem? hget, ?_, cm2.2.2.1.trans hpath⟩
  simpa using hcond

/-! ### The `sidePathEq` seam -/

/-- `sidePathEq P graph` for every measured graph: side borders (`±1`) sharing
their proxy's path tail carry the proxy's full cluster path and are non-dummy. -/
theorem sidePathEq_of_measuredGraph {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) :
    sidePathEq P graph := by
  intro comp hcomp candidate run labels orderOptions hrun x y hx hy hlast
  obtain ⟨labeled, hcoord, hkeys, haligned, _⟩ :=
    componentRun_coordinate_source_alignment hrun
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun _ _ hnode => componentCandidate_marker_shape hgraph hnode
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)) :=
    titled_border_ready hkeys hshape hmarkers haligned
  obtain ⟨xd, hx'⟩ : ∃ n, run.coordinateProper.nodes[x]? = some n := by
    cases hxg : run.coordinateProper.nodes[x]? with
    | none =>
        rw [List.getD_eq_getElem?_getD, hxg, Option.getD_none] at hx
        have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
        omega
    | some n => exact ⟨n, rfl⟩
  obtain ⟨yd, hy'⟩ : ∃ n, run.coordinateProper.nodes[y]? = some n := by
    cases hyg : run.coordinateProper.nodes[y]? with
    | none =>
        rw [List.getD_eq_getElem?_getD, hyg, Option.getD_none] at hy
        have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
        rcases hy with hyv | hyv <;> omega
    | some n => exact ⟨n, rfl⟩
  have hxdD : run.coordinateProper.nodes.getD x default = xd := by
    simp [List.getD_eq_getElem?_getD, hx']
  have hydD : run.coordinateProper.nodes.getD y default = yd := by
    simp [List.getD_eq_getElem?_getD, hy']
  have hxdBorder : xd.node.border = 2 := by rw [← hxdD]; exact hx
  have hydBorder : yd.node.border = -1 ∨ yd.node.border = 1 := by
    rw [← hydD]; exact hy
  rw [← hcoord] at hx' hy'
  rcases coordinateGraph_lookup P labeled hx' with
    ⟨m, hm, _, hmb, hmpath, _⟩ | ⟨_, hbx⟩ | ⟨_, _, _, _, _, hb3, _⟩
  · have hmb2 : m.node.border = 2 := by rw [← hmb]; exact hxdBorder
    rcases hkeys x m hm with ⟨n, hn, hreal, hnb, hnp⟩ | ⟨_, hbd, _⟩
    · have hnB : n.border = 2 := by rw [← hnb]; exact hmb2
      obtain ⟨_, _, hgraphX⟩ := componentCandidate_nonplain_source hn (by omega)
      obtain ⟨box, hbox, _, hpathB, _, _⟩ :=
        measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hgraphX) hnB
      have hxLast : xd.node.clusterPath.getLast? = some n.decl := by
        rw [hmpath hreal, hnp, hpathB, List.getLast?_append]; simp
      rcases coordinateGraph_lookup P labeled hy' with
        ⟨m2, hm2, _, hmb2', _, _⟩ | ⟨ydF, hby⟩ | ⟨_, _, _, _, _, hb3', _⟩
      · rcases hkeys y m2 hm2 with ⟨n2, hn2, _, hnb2, _⟩ | ⟨_, hbd2, _⟩
        · have hcase := (hmarkers y n2 hn2).1
          have hnbB : n2.border = -1 ∨ n2.border = 1 := by
            rw [← hnb2, ← hmb2']; exact hydBorder
          rcases hcase with hz | hz | hz <;> rcases hnbB with hb1 | hb2 <;> omega
        · rw [hbd2] at hmb2'; omega
      · obtain ⟨_, tn, htMem, htB, htPath⟩ :=
            coordinateGraph_side_path (t := titleReservations
              (sizeProperPorts P labeled)) rfl hready hy' hby
        obtain ⟨tidx, htidx⟩ := List.mem_iff_getElem?.mp htMem
        rcases titled_node_origin hkeys htidx with
          ⟨orig2, horig2, _, hbb, hpp⟩ | ⟨_, htb2⟩
        · have horigB : orig2.node.border = -2 := by rw [← hbb]; exact htB
          rcases hkeys tidx orig2 horig2 with ⟨n3, hn3, _, hnb3, hnp3⟩ |
            ⟨_, hb0, _⟩
          · have hnB3 : n3.border = -2 := by rw [← hnb3]; exact horigB
            obtain ⟨_, _, hgraphY⟩ :=
              componentCandidate_nonplain_source hn3 (by omega)
            obtain ⟨_, box3, hbox3, _, hpath3⟩ :=
              measuredGraph_group_origin hgraph hgraphY hnB3
            have hyLast : yd.node.clusterPath.getLast? = some n3.decl := by
              rw [htPath, hpp, hnp3, hpath3, List.getLast?_append]; simp
            rw [hxdD, hydD, hxLast, hyLast] at hlast
            have hdeclEq : n.decl = n3.decl := Option.some.inj hlast
            rw [hdeclEq] at hbox
            have hboxEq : box = box3 := Option.some.inj (hbox.symm.trans hbox3)
            rw [hydD, hxdD, htPath, hpp, hnp3, hpath3, ← hdeclEq, ← hboxEq,
              hmpath hreal, hnp, hpathB]
            exact ⟨rfl, ydF⟩
          · exfalso
            rw [hb0] at horigB
            omega
        · exfalso
          rw [htb2] at htB
          omega
      · omega
    · rw [hbd] at hmb2; omega
  · rcases hbx with hb | hb
    · rw [hb] at hxdBorder; omega
    · rw [hb] at hxdBorder; omega
  · rw [hb3] at hxdBorder; omega

end Elegant.Layered.PipelineImpl
