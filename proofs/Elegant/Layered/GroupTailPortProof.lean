import Elegant.Layered.FlatGroupEndpointsProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SizingFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.BracketInsideStructuralFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Group tail port fact

`GroupTailPortOnYs` is the executed tail-port row of the flat group-endpoint
seam: for a successful `componentRun` whose chain-tail endpoint is a
`border = 2` bottom marker, the emitted route's tail-side point is the flat
port `⟨px, run.ys v⟩` with `px` inside the marker's box span.
The proper marker is not a top marker, so `tailPortY` selects the physical
bottom. The labeled prefix, coordinate classification, and proxy-width
transfer also give zero executed height, so that bottom equals `run.ys v`. -/

/-- Every nonempty list of naturals has a `getLast?` witness. -/
private theorem edgesOf_getLast (l : List Nat) (hne : l ≠ []) :
    ∃ last, l.getLast? = some last := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    cases rest with
    | nil => exact ⟨a, rfl⟩
    | cons b rest' =>
      obtain ⟨last, hlast⟩ := ih (by simp)
      exact ⟨last, by simpa only [List.getLast?_cons_cons] using hlast⟩

/-- A `±1` coordinate node at a recorded `border = 2` position has zero
height.  This is the `coordinateGraph_side_height` argument with the concrete
labeled record in place of the marker-shape hypothesis: the side node is
either an appended border pair (zero height by construction) or sits below
the titled prefix, where the sized record forces its border to the recorded
`2`, contradicting `±1`. -/
private theorem coord_side_height_of_record
    {P : Params} {_cg : Graph} {labeled : Proper}
    {v : Nat} {n : Node} (hnBorder : n.border = 2)
    (hlab : labeled.nodes[v]? = some ⟨n, false, none, false⟩)
    {nd : ProperNode} (h : (coordinateGraph P labeled).nodes[v]? = some nd)
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

/-- A `border = 2` graph node executes as a non-top frame node of zero
height: the labeled prefix record fixes the coordinate node to the mapped
source (ruling out side and title copies), and the proxy-width transfer
carries dummy, border, and height to the proper node. -/
private theorem tailBottomFacts
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} (hb : (cg.nodes.getD v default).border = 2) :
    RouteImpl.frameKind run.proper v ≠ -2 ∧ RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨_, _, labeled, q0, hn, hlabels, hcoord, _, _, hprox, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
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
    have hC : (coordinateGraph P labeled).nodes[v]? = some pa := by
      rw [hcoord]; exact hpa
    rcases coordinateGraph_lookup P labeled hC with
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
        coord_side_height_of_record (_cg := cg) hnBorder hlab hC hbS
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

/-- The executed bottom-marker tail port is flat in both route directions. -/
theorem groupTailPortOnYs : GroupTailPortOnYs := by
  unfold GroupTailPortOnYs
  intro _P cg run _labels _orderOptions hrun i hi first hfirst hb
  obtain ⟨rt, hrt, horiginal, _⟩ := componentRun_route_of_index hrun hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, _, _, hroutes⟩ :=
    componentRun_spec hrun
  have hne : RouteImpl.edgesOf run.proper i ≠ [] := by
    intro hnil
    rw [hnil] at hfirst
    simp at hfirst
  obtain ⟨last, hlast⟩ := edgesOf_getLast _ hne
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    rw [horiginal]; exact hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    rw [horiginal]; exact hlast
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  obtain ⟨hfk, hnh⟩ := tailBottomFacts hrun hb
  obtain ⟨px, _, _, _, hpx0, hpx1, _, _, hend⟩ :=
    route_endpoints_on_ports hrouting hroutes rt hm first last hfirst' hlast'
  rw [horiginal] at hend
  have hport : RouteImpl.tailPortY run.proper run.ys (RouteImpl.edgeAt run.proper first).tail =
      run.ys.getD (RouteImpl.edgeAt run.proper first).tail 0 := by
    rw [RouteImpl.tailPortY, ite_eq_right hfk, hnh, Int.add_zero, RouteImpl.yAt]
  refine ⟨rt, px, hrt, hpx0, hpx1, ?_, ?_⟩
  · intro hrev
    rw [ite_eq_left hrev] at hend
    obtain ⟨-, htail⟩ := hend
    change rt.points.getLast? = some
      ⟨px, RouteImpl.tailPortY run.proper run.ys (RouteImpl.edgeAt run.proper first).tail⟩ at htail
    rw [hport] at htail
    exact htail
  · intro hcon
    have hnc : ¬((cg.edges.map (·.reversed)).getD i false = true) := by
      rw [hcon]; decide
    rw [ite_eq_right hnc] at hend
    obtain ⟨hhead, -⟩ := hend
    change rt.points.head? = some
      ⟨px, RouteImpl.tailPortY run.proper run.ys (RouteImpl.edgeAt run.proper first).tail⟩ at hhead
    rw [hport] at hhead
    exact hhead

end Elegant.Layered.PipelineImpl
