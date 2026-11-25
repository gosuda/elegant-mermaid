import Elegant.Layered.LoopExtentReservationProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Order

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Group-top loop-extent marker copy for executed plain runs

Route: sizing (`loopSizes`, `Loops.extent`) fixes the group top's stored
extent (`lmc_cg_node_loopExtent`, candidate-level copy of the `tsep`
equation); `sizeProperPorts` leaves `-2` nodes untouched,
`titleReservations` (`titleF`) zeroes only dimensions, `addClusterBorders`
copies the anchor extent onto the right border marker (`Order.lean:175`,
`borderRight`), and `clearProxyExtents` (`clearF`) clears only `-2`/`2`
proxies, so the border-`1` marker keeps the extent through
`materializeDummyPaths` into the executed `coordinateProper` record. The
composition discharges `LoopResMarkerCopy` and hence the `hext_all` premise
of `loopFootprintTopSeparation_holds`.
-/

/-- Local copy of the private `ler_candidate_nodes_length`. -/
private theorem lmc_candidate_nodes_length (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (componentGraph g comp).nodes.length = _
  unfold componentGraph
  dsimp only
  rw [List.length_map]

/-- Local copy of the private `ler_slot`. -/
private theorem lmc_slot (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- Local copy of the private `ler_lines_len`. -/
private theorem lmc_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Local copy of the private `ler_extent_nonneg`. -/
private theorem lmc_extent_nonneg {slot : Int} (hs : 0 ≤ slot)
    {sizes : List LoopLabel} (hw : ∀ l ∈ sizes, 0 ≤ l.width) :
    0 ≤ Loops.extent slot sizes := by
  have hsum : ∀ (xs : List Int) (z : Int), 0 ≤ z → (∀ x ∈ xs, 0 ≤ x) →
      0 ≤ xs.foldl (· + ·) z := by
    intro xs
    induction xs with
    | nil => intro z hz h; simpa using hz
    | cons y ys ih =>
      intro z hz h
      simp only [List.foldl_cons]
      have hy : 0 ≤ y := h y (List.mem_cons.mpr (Or.inl rfl))
      have hys : ∀ x ∈ ys, 0 ≤ x :=
        fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      exact ih (z + y) (by omega) hys
  unfold Loops.extent
  apply hsum _ 0 (by omega)
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨l, idx⟩ := p
  have hl : sizes[idx]? = some l :=
    List.mem_zipIdx_iff_getElem?.mp hp
  have h1 : 0 ≤ slot * ((idx : Int) + 2) :=
    Int.mul_nonneg hs (by omega)
  have h2 := hw l (List.mem_of_getElem? hl)
  simpa using Int.add_nonneg h1 h2

/-- Local copy of the private `tsep_graph_node_loopExtent`: an executed graph
node stores the exact loop extent of its own loop sizes. -/
private theorem lmc_graph_node_loopExtent {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) {m : Nat}
    (hm : m < e.lines.length) {gnode : Node}
    (hg : e.graph.nodes[m]? = some gnode) :
    gnode.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
  have hlines : e.lines.length = inp.boxes.length := lmc_lines_len e
  have hmB : m < inp.boxes.length := by rw [← hlines]; exact hm
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[m]? = some box :=
    ⟨_, List.getElem?_eq_getElem hmB⟩
  have hgE := e.graph_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := bind_ok' hgE
  obtain ⟨edges, _, hgE⟩ := bind_ok' hgE
  obtain ⟨metric, hmM, hgE⟩ := bind_ok' hgE
  obtain ⟨labels, hlL, hgE⟩ := bind_ok' hgE
  obtain ⟨nodes, hnodes, hgE⟩ := bind_ok' hgE
  have hprepare := (Except.ok.inj hgE).symm
  let raw : Graph := { nodes := nodes, edges := edges, slot := e.params.slot }
  change e.graph = Compound.prepare _ e.params.clusterPad _ raw at hprepare
  have hemetric : metric = e.metric := Except.ok.inj (hmM.symm.trans e.metric_eq)
  subst hemetric
  have helabels : labels = e.measured :=
    Except.ok.inj (hlL.symm.trans e.measured_eq)
  subst helabels
  have hslotG : e.graph.slot = e.params.slot := by rw [hprepare]; exact rfl
  have hslotnn : 0 ≤ e.params.slot := by
    have hvalid := checkedParams_valid e.checked
    have h1 : 1 ≤ e.params.slot := hvalid.2.2.1
    omega
  have hwidths : ∀ l ∈ loopSizes edges e.measured m e.params.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hextnn : 0 ≤ Loops.extent e.params.slot
      (loopSizes edges e.measured m e.params.slot) :=
    lmc_extent_nonneg hslotnn hwidths
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, _, hbefore⟩ :=
    hinit m (e.lines[m], m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hm,
        Option.map_some, Nat.zero_add])
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed m (orientNode o.direction before, m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have hloop : after.loopExtent =
      (Loops.extent e.params.slot
        (loopSizes edges e.measured m e.params.slot)).toNat := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == box.id) = true
    · obtain ⟨entry, hfindE⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == box.id) = some entry := by
        cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
        | none =>
          obtain ⟨e2, hmF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf e2 hmF) (by rw [hid]; decide)
        | some e2 => exact ⟨e2, rfl⟩
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
        hfixed
      simp [hbox, hfindE, hany] at hstep
      split at hstep
      · cases hstep
      · split at hstep
        · cases hstep
        · have he := Except.ok.inj hstep
          subst after
          rfl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hfindN : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
        List.find?_eq_none.mpr (List.any_eq_false.mp hfixedF)
      by_cases hrole : box.role = .group
      · simp [hbox, hfindN, hrole, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
      · have hroleN : box.role = .node := by
          match h : box.role with
          | .node => rfl
          | .group => exact absurd h hrole
        simp [hbox, hfindN, hroleN, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
  have hinodes : m < nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hget : nodes[m]'hinodes = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hraw : raw.nodes[m]? = some after := by
    simpa only [raw, List.getElem?_eq_getElem hinodes] using congrArg some hget
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := e.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * e.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  have hprepEq : e.graph = Compound.prepare boxes e.params.clusterPad titles raw :=
    hprepare
  have hbound : m < boxes.length := by
    simpa only [boxes, List.length_map] using hmB
  have hpe := prepare_loopSizes_preserved boxes e.params.clusterPad titles raw m
    hbound e.measured e.params.slot
  have heg : (Compound.prepare boxes e.params.clusterPad titles raw).edges =
      e.graph.edges := by
    rw [hprepEq]
  rw [heg] at hpe
  have hrawE : raw.edges = edges := rfl
  have hsizeq : loopSizes edges e.measured m e.params.slot =
      loopSizes e.graph.edges e.measured m e.graph.slot := by
    rw [hrawE] at hpe
    rw [← hpe, hslotG]
  have hloopG : after.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
    rw [hloop, hsizeq, hslotG]
  have hclose : gnode.loopExtent = after.loopExtent →
      gnode.loopExtent = (Loops.extent e.graph.slot
        (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
    intro hll
    rw [hll, hloopG]
  by_cases hrole : box.role = .group
  · by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := Compound.prepare_group_title_record boxes e.params.clusterPad
        titles raw hinodes hboxM hrole
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = (raw.nodes[m]'hinodes).loopExtent := by
        rw [h2]
      have hRl : (raw.nodes[m]'hinodes).loopExtent = after.loopExtent := by
        simp only [raw, hget]
      exact hclose (hloopR.trans hRl)
  · have hroleN : box.role = .node := by
      match h : box.role with
      | .node => rfl
      | .group => exact absurd h hrole
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hboxM hroleN
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR

/-- Local copy of the private `tsep_cg_node_loopExtent`: a candidate group-top
node stores the exact loop extent of its own loop sizes. -/
private theorem lmc_cg_node_loopExtent {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) (comp : List Nat)
    (candidate v : Nat) {nodeV : Node}
    (hcomp : comp ∈ components e.graph)
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2) :
    nodeV.loopExtent = (Loops.extent (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot)).toNat := by
  have hlen : (componentCandidate e.graph comp candidate).nodes.length =
      comp.length :=
    lmc_candidate_nodes_length _ _ _
  have hvcomp : v < comp.length := by rw [← hlen]; exact hvlen
  obtain ⟨u, huv, hnodeU⟩ :=
    componentCandidate_nonplain_source hnodeV (by omega : nodeV.border ≠ 0)
  obtain ⟨hdeclEq, _, hbox, _, _⟩ :=
    measuredGraph_group_origin e.graph_eq hnodeU hvtop
  have huLines : u < e.lines.length := by
    have h1 : nodeV.decl < inp.boxes.length := by
      have hmem := (List.getElem?_eq_some_iff.mp hbox).1
      simpa only [List.length_map] using hmem
    have h2 : e.lines.length = inp.boxes.length := lmc_lines_len e
    omega
  have hextU := lmc_graph_node_loopExtent e huLines hnodeU
  have hslot : (componentCandidate e.graph comp candidate).slot = e.graph.slot := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hnd : comp.Nodup := components_nodup e.graph comp hcomp
  have hloop := componentCandidate_loopSizes_preserved e.graph comp hnd candidate
    v hvcomp e.measured (componentCandidate e.graph comp candidate).slot
  have hcompv : comp[v]'hvcomp = u := by
    have h1 : comp[v]? = some (comp[v]'hvcomp) := List.getElem?_eq_getElem hvcomp
    exact Option.some.inj (h1.symm.trans huv)
  rw [hcompv] at hloop
  rw [hextU, ← hslot, ← hloop]

/-- Local copy of the private `tsep_top_getLast`: a candidate `-2` node ends
its cluster path in its declaration. -/
private theorem lmc_top_getLast {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hb : uNode.border = -2) :
    uNode.clusterPath.getLast? = some uNode.decl := by
  obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hu (by omega)
  obtain ⟨_, _, _, _, hpath⟩ := measuredGraph_group_origin hgraph hsource hb
  rw [hpath]
  simp

/-- Emitted border markers carry their anchor's cluster path, and a border-`1`
marker carries its anchor's loop extent. Strengthens
`addClusterBorders_node_origin` with the copied extent. -/
private theorem lmc_node_origin_loop (source : Proper) (width : Int) :
    ∀ node ∈ (OrderImpl.addClusterBorders source width).nodes,
      node ∈ source.nodes ∨
      ∃ top ∈ source.nodes.zipIdx.filter (fun entry => entry.1.node.border == -2),
        ∃ bottom : ProperNode × Nat,
          (source.nodes.zipIdx.find? fun entry =>
            entry.1.node.border == 2 &&
              entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
          node.node.clusterPath = top.1.node.clusterPath ∧
          (node.node.border = 1 → node.node.loopExtent = top.1.node.loopExtent) := by
  let anchors := source.nodes.zipIdx.filter fun entry => entry.1.node.border == -2
  let evidence := fun emitted : ProperNode =>
    ∃ top ∈ anchors, ∃ bottom : ProperNode × Nat,
      (source.nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      emitted.node.clusterPath = top.1.node.clusterPath ∧
      (emitted.node.border = 1 → emitted.node.loopExtent = top.1.node.loopExtent)
  rw [OrderImpl.addClusterBorders_eq]
  apply OrderImpl.foldl_inv
    (fun current : Proper => ∀ emitted ∈ current.nodes,
      emitted ∈ source.nodes ∨ evidence emitted)
  · intro emitted he
    exact Or.inl he
  · intro current hcurrent top htop
    unfold OrderImpl.borderStep
    split
    · exact hcurrent
    · rename_i bottomIndex hbottomIndex
      obtain ⟨bottom, hbottom, _⟩ := Option.map_eq_some_iff.mp hbottomIndex
      apply OrderImpl.foldl_inv
        (fun state : Proper => ∀ emitted ∈ state.nodes,
          emitted ∈ source.nodes ∨ evidence emitted)
      · exact hcurrent
      · intro state hstate offset _
        intro emitted he
        change emitted ∈ state.nodes ++
          [OrderImpl.borderLeft top width, OrderImpl.borderRight top width] at he
        rcases List.mem_append.mp he with hold | hnew
        · exact hstate emitted hold
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
          rcases hnew with rfl | rfl
          · exact Or.inr ⟨top, htop, bottom, hbottom, rfl,
              fun h => by simp [OrderImpl.borderLeft] at h⟩
          · exact Or.inr ⟨top, htop, bottom, hbottom, rfl, fun _ => rfl⟩

/-- The residual `LoopResMarkerCopy`: in an executed run, every border-`1`
marker filed under a looping group top carries at least the top's loop
extent. Transport: the top's stored extent (sizing) survives `sizeProperPorts`
and `titleReservations`, is copied onto the right marker by
`addClusterBorders`, and survives `clearProxyExtents` (which clears only
`-2`/`2` proxies) and `materializeDummyPaths` into the executed record. -/
theorem loopResMarkerCopy_holds {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v m : Nat} {nodeV : Node} {mk : ProperNode}
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB : nodeV.border = -2)
    (hcoord : run.coordinateProper.nodes[m]? = some mk)
    (hb1 : mk.node.border = 1)
    (hlast : mk.node.clusterPath.getLast? = some nodeV.decl) :
    (mk.node.loopExtent : Int) ≥ Loops.extent (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot) := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hlab : labeled.nodes[v]? = some (⟨nodeV, false, none, false⟩ : ProperNode) :=
    hrecords v nodeV hnodeV
  have htitled : (titleReservations (sizeProperPorts e.params labeled)).nodes[v]? =
      some (titleF (⟨nodeV, false, none, false⟩ : ProperNode)) :=
    titled_marker_record hlab (Or.inl hvB)
  have htitleBorder :
      (titleF (⟨nodeV, false, none, false⟩ : ProperNode)).node.border = -2 :=
    (titleF_keys _).2.1.trans hvB
  have htitleLoop :
      (titleF (⟨nodeV, false, none, false⟩ : ProperNode)).node.loopExtent =
        nodeV.loopExtent := by
    simp [titleF, hvB]
  have hco : (coordinateGraph e.params labeled).nodes[m]? = some mk := by
    rw [hc]; exact hcoord
  have horiginal : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts e.params labeled))
      e.params.clusterBorderW).nodes[m]? = some mk :=
    coordinateGraph_side_original hready hco (Or.inr hb1)
  have hmem : mk ∈ (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts e.params labeled))
      e.params.clusterBorderW).nodes :=
    List.mem_of_getElem? horiginal
  rcases lmc_node_origin_loop _ _ _ hmem with hmemT | ⟨top, htopmem, bottom, hbottom, hpath, hloopEq⟩
  · exact ((hready.1 mk hmemT).2 hb1).elim
  · obtain ⟨hmemZip, hcond⟩ := List.mem_filter.mp htopmem
    have htopLookup :
        (titleReservations (sizeProperPorts e.params labeled)).nodes[top.2]? =
          some top.1 :=
      List.mem_zipIdx_iff_getElem?.mp hmemZip
    have htopBorder : top.1.node.border = -2 := by simpa using hcond
    have htopLast : top.1.node.clusterPath.getLast? = some nodeV.decl := by
      rw [← hpath]; exact hlast
    have htitleLast :
        (titleF (⟨nodeV, false, none, false⟩ : ProperNode)).node.clusterPath.getLast? =
          some nodeV.decl := by
      have htp := lmc_top_getLast e.graph_eq hnodeV hvB
      have hke := (titleF_keys (⟨nodeV, false, none, false⟩ : ProperNode)).2.2.1
      rw [hke]; exact htp
    have howner : top.1.node.clusterPath.getLast? =
        (titleF (⟨nodeV, false, none, false⟩ : ProperNode)).node.clusterPath.getLast? := by
      rw [htopLast, htitleLast]
    have hindex : top.2 = v :=
      titled_group_owner_unique e.graph_eq hcomp hk hrecords htopLookup htitled
        htopBorder htitleBorder howner
    have htopEq : top.1 = titleF (⟨nodeV, false, none, false⟩ : ProperNode) := by
      have h : (titleReservations (sizeProperPorts e.params labeled)).nodes[top.2]? =
          some (titleF (⟨nodeV, false, none, false⟩ : ProperNode)) := by
        rw [hindex]; exact htitled
      exact Option.some.inj (htopLookup.symm.trans h)
    have hmkLoop : mk.node.loopExtent = nodeV.loopExtent := by
      have h1 := hloopEq hb1
      rw [htopEq, htitleLoop] at h1
      exact h1
    have hvlen : v < (componentCandidate e.graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp hnodeV).1
    have heq := lmc_cg_node_loopExtent e comp candidate v hcomp hvlen hnodeV hvB
    have hcslot : (componentCandidate e.graph comp candidate).slot = e.graph.slot :=
      lmc_slot e.graph comp candidate
    have hslotpos : 1 ≤ (componentCandidate e.graph comp candidate).slot := by
      rw [hcslot]
      have hG : e.graph.slot = e.params.slot := by
        have hlines : e.lines.length = inp.boxes.length := lmc_lines_len e
        have hgE := e.graph_eq
        unfold measuredGraph at hgE
        obtain ⟨initial, _, hgE⟩ := bind_ok' hgE
        obtain ⟨edges, _, hgE⟩ := bind_ok' hgE
        obtain ⟨metric, hmM, hgE⟩ := bind_ok' hgE
        obtain ⟨labels, hlL, hgE⟩ := bind_ok' hgE
        obtain ⟨nodes, hnodes, hgE⟩ := bind_ok' hgE
        have hprepare := (Except.ok.inj hgE).symm
        change e.graph = Compound.prepare _ e.params.clusterPad _ _ at hprepare
        rw [hprepare]
        exact rfl
      rw [hG]
      exact (checkedParams_valid e.checked).2.2.1
    have hslotnn : 0 ≤ (componentCandidate e.graph comp candidate).slot := by omega
    have hwidths : ∀ l ∈ loopSizes (componentCandidate e.graph comp candidate).edges
        e.measured v (componentCandidate e.graph comp candidate).slot, 0 ≤ l.width := by
      intro l hl
      obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
      rw [stackSize_width_eq]
      exact Labels.stackWidth_nonneg _
    have hextnn : 0 ≤ Loops.extent (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) :=
      lmc_extent_nonneg hslotnn hwidths
    rw [hmkLoop, heq, Int.toNat_of_nonneg hextnn]
    exact Int.le_refl _
/-- Corollary in the exact form of the `hext_all` premise of
`loopFootprintTopSeparation_holds`. -/
theorem loopFootprintTop_hext_all {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v m : Nat) (nodeV : Node) (mk : ProperNode)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB : nodeV.border = -2)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      oo = .ok run)
    (hcoord : run.coordinateProper.nodes[m]? = some mk)
    (hb1 : mk.node.border = 1)
    (hlast : mk.node.clusterPath.getLast? = some nodeV.decl) :
    (mk.node.loopExtent : Int) ≥ Loops.extent
      (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot) :=
  loopResMarkerCopy_holds e comp candidate oo run hcomp hrun hnodeV hvB hcoord hb1 hlast

end PipelineImpl
end Layered
end Elegant
