import Elegant.Layered.LoopFootprintBeyondProperProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.Labels
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.Route
import Elegant.Layered.CgShape
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.Compound

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Local copy of the private general `bind_ok`. -/
private theorem plain_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => simp [hx, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Except.bind] using h⟩

/-- Local re-proof of `ComponentCoverage.componentCandidate_nodes_length`. -/
private theorem plain_candidate_nodes_length (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Local copy of the private `componentCandidate_slot_general`. -/
private theorem plain_slot (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- Local copy of the private `lines_len_general`. -/
private theorem plain_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Loop extents are nonnegative for nonnegative slots. -/
private theorem plain_extent_nonneg {slot : Int} (hs : 0 ≤ slot)
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

/-- Local copy of the private `graph_node_loopExtent_general`: an executed
graph node stores the exact loop extent of its own loop sizes. -/
private theorem plain_graph_node_loopExtent {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) {m : Nat}
    (hm : m < e.lines.length) {gnode : Node}
    (hg : e.graph.nodes[m]? = some gnode) :
    gnode.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
  have hlines : e.lines.length = inp.boxes.length := plain_lines_len e
  have hmB : m < inp.boxes.length := by rw [← hlines]; exact hm
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[m]? = some box :=
    ⟨_, List.getElem?_eq_getElem hmB⟩
  have hgE := e.graph_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := plain_bind_ok hgE
  obtain ⟨edges, _, hgE⟩ := plain_bind_ok hgE
  obtain ⟨metric, hmM, hgE⟩ := plain_bind_ok hgE
  obtain ⟨labels, hlL, hgE⟩ := plain_bind_ok hgE
  obtain ⟨nodes, hnodes, hgE⟩ := plain_bind_ok hgE
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
    plain_extent_nonneg hslotnn hwidths
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

/-- `coordinateGraph` preserves the loop extent of a plain anchor. Prefixed
copy of the private `coordinateGraph_loopExtent_general`. -/
private theorem plain_coordinateGraph_loopExtent {P : Params} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraph P p).nodes[i]? = some out ∧
      out.node.loopExtent = nd.node.loopExtent := by
  obtain ⟨sized, hs, hb', hle⟩ :
      ∃ sized, (sizeProperPorts P p).nodes[i]? = some sized ∧
        sized.node.border = 0 ∧ sized.node.loopExtent = nd.node.loopExtent := by
    unfold sizeProperPorts
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, hb, rfl⟩
    · refine ⟨_, rfl, hb, rfl⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPorts P p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[i]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · refine ⟨_, rfl, ?_⟩
    show sized.node.loopExtent = nd.node.loopExtent
    exact hle
  · exact ⟨_, rfl, hle⟩

/-- Plain owner loop-extent reservation: the coordinate width at `v` covers the
footprint extent. Prefixed copy of the `hLvGe` block in
`separation_plain_pair_general`. -/
private theorem plain_loopExtent_ge {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v : Nat} {nodeV : Node}
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB0 : nodeV.border = 0)
    {actualV : ProperNode}
    (hcoordV : run.coordinateProper.nodes[v]? = some actualV) :
    (actualV.node.loopExtent : Int) ≥
      Loops.extent (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) := by
  have hslotpos := executed_candidate_slot_pos e comp candidate
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
    plain_extent_nonneg hslotnn hwidths
  by_cases hnil : loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot = []
  · have hExt0 : Loops.extent (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) = 0 := by
      simp [hnil, Loops.extent]
    rw [hExt0]
    exact Int.natCast_nonneg _
  · have hvl : v < comp.length := by
      have hlen : (componentCandidate e.graph comp candidate).nodes.length =
          comp.length := plain_candidate_nodes_length _ _ _
      omega
    have hget : comp.getD v 0 = comp[v]'hvl := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvl,
        Option.getD_some]
    have hlines : e.lines.length = inp.boxes.length := plain_lines_len e
    have hmlin : comp.getD v 0 < e.lines.length := by
      by_cases hcon : comp.getD v 0 < e.lines.length
      · exact hcon
      · have hge : inp.boxes.length ≤ comp.getD v 0 := by omega
        have hn := components_nodup e.graph comp hcomp
        have hpres := componentCandidate_loopSizes_preserved e.graph comp hn
          candidate v hvl e.measured
          (componentCandidate e.graph comp candidate).slot
        have hcslot : (componentCandidate e.graph comp candidate).slot =
            e.graph.slot := plain_slot e.graph comp candidate
        have hm_eq : comp[v]'hvl = comp.getD v 0 := by rw [hget]
        have hcc : (componentCandidate e.graph comp candidate).nodes =
            comp.map fun key => e.graph.nodes.getD key default := by
          rw [componentCandidate_nodes]
          unfold componentGraph
          rfl
        have h1 : (comp.map fun key => e.graph.nodes.getD key default)[v]? =
            some nodeV := by
          rw [← hcc]; exact hnodeV
        rw [List.getElem?_map] at h1
        have h2 : comp[v]? = some (comp.getD v 0) := by
          have h3 := List.getElem?_eq_getElem hvl
          rwa [← hget] at h3
        rw [h2, Option.map_some] at h1
        have hgv : e.graph.nodes.getD (comp.getD v 0) default = nodeV :=
          Option.some.inj h1
        obtain ⟨pnodes, pedges, ptitles, hprep, hplen, _hzero⟩ :=
          measuredGraph_prepared_source e.graph_eq
        have hrawlen : pnodes.length = inp.boxes.length := by
          rw [hplen, hlines]
        by_cases hmgraph : comp.getD v 0 < e.graph.nodes.length
        · have hsome : e.graph.nodes[comp.getD v 0]? = some nodeV := by
            have hg1 : e.graph.nodes[comp.getD v 0]? =
                some (e.graph.nodes[comp.getD v 0]'hmgraph) :=
              List.getElem?_eq_getElem hmgraph
            have hgetd : e.graph.nodes.getD (comp.getD v 0) default =
                e.graph.nodes[comp.getD v 0]'hmgraph := by
              rw [List.getD_eq_getElem?_getD, hg1, Option.getD_some]
            have heq : e.graph.nodes[comp.getD v 0]'hmgraph = nodeV := by
              rw [← hgetd, hgv]
            rw [heq] at hg1
            exact hg1
          have hj : pnodes.length ≤ comp.getD v 0 := by omega
          rw [hprep] at hsome
          have hbot := (Compound.prepare_bottom_of_index _ _ _ _ (comp.getD v 0) hj hsome).1
          rw [hvB0] at hbot
          exact absurd hbot (by decide)
        · have hemptyG : loopEdges e.graph.edges (comp.getD v 0) = [] := by
            apply Classical.byContradiction
            intro hne
            obtain ⟨ed, hmem⟩ : ∃ ed, ed ∈ loopEdges e.graph.edges (comp.getD v 0) := by
              cases h : loopEdges e.graph.edges (comp.getD v 0) with
              | nil => exact absurd h hne
              | cons e _ => exact ⟨e, List.mem_cons.mpr (Or.inl rfl)⟩
            have hpair := List.mem_filter.mp (by simpa only [loopEdges] using hmem)
            obtain ⟨hedges, hflt⟩ := hpair
            have hflt' : (ed.tail == comp.getD v 0 && ed.head == comp.getD v 0) = true :=
              hflt
            rw [Bool.and_eq_true] at hflt'
            have hTailEq : ed.tail = comp.getD v 0 := beq_iff_eq.mp hflt'.1
            have hbd := sceneExecution_edges_bounded e
            have hbnd := hbd ed (List.mem_append_left _ hedges)
            omega
          have hSizesG : loopSizes e.graph.edges e.measured (comp.getD v 0)
              e.graph.slot = [] := by
            simp only [loopSizes, hemptyG, List.map_nil]
          have hEq : loopSizes (componentCandidate e.graph comp candidate).edges
              e.measured v (componentCandidate e.graph comp candidate).slot =
              loopSizes e.graph.edges e.measured (comp[v]'hvl) e.graph.slot := by
            rw [hpres, hm_eq, hcslot]
          have hemptyC : loopSizes (componentCandidate e.graph comp candidate).edges
              e.measured v (componentCandidate e.graph comp candidate).slot = [] := by
            rw [hEq, hm_eq, hSizesG]
          exact absurd hemptyC hnil
    have hgnlen : comp.getD v 0 < e.graph.nodes.length := by
      have h1 := measuredGraph_nodes_length_ge e.graph_eq hlines
      omega
    obtain ⟨gnodeM, hgm⟩ : ∃ g, e.graph.nodes[comp.getD v 0]? = some g :=
      ⟨_, List.getElem?_eq_getElem hgnlen⟩
    have hloopM := plain_graph_node_loopExtent e hmlin hgm
    have hcslot : (componentCandidate e.graph comp candidate).slot =
        e.graph.slot := plain_slot e.graph comp candidate
    have hn := components_nodup e.graph comp hcomp
    have hpres := componentCandidate_loopSizes_preserved e.graph comp hn
      candidate v hvl e.measured
      (componentCandidate e.graph comp candidate).slot
    have hcc : (componentCandidate e.graph comp candidate).nodes =
        comp.map fun key => e.graph.nodes.getD key default := by
      rw [componentCandidate_nodes]
      unfold componentGraph
      rfl
    have h1 : (comp.map fun key => e.graph.nodes.getD key default)[v]? =
        some nodeV := by
      rw [← hcc]; exact hnodeV
    rw [List.getElem?_map] at h1
    have h2 : comp[v]? = some (comp.getD v 0) := by
      have h3 := List.getElem?_eq_getElem hvl
      rwa [← hget] at h3
    rw [h2, Option.map_some] at h1
    have h3 : e.graph.nodes.getD (comp.getD v 0) default = nodeV :=
      Option.some.inj h1
    have e1 : e.graph.nodes.getD (comp.getD v 0) default = gnodeM := by
      rw [List.getD_eq_getElem?_getD, hgm]
      rfl
    have hnodeVloop : nodeV.loopExtent = gnodeM.loopExtent := by rw [← h3, e1]
    obtain ⟨_, labeled, _, hcoordinate, _, _, hrecords, _⟩ :=
      componentRun_prepared_titled_source e.graph_eq hcomp hrun
    have hlabV := hrecords v nodeV hnodeV
    obtain ⟨outV, houtV, hloopV⟩ := plain_coordinateGraph_loopExtent hlabV
      (by simpa using hvB0)
    rw [hcoordinate] at houtV
    have houtVeq : outV = actualV :=
      Option.some.inj (houtV.symm.trans hcoordV)
    have hLvEq : ((actualV.node.loopExtent : Int)) =
        Loops.extent (componentCandidate e.graph comp candidate).slot
          (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
            (componentCandidate e.graph comp candidate).slot) := by
      have h1 : actualV.node.loopExtent = nodeV.loopExtent := by
        rw [← houtVeq]; exact hloopV
      rw [h1, hnodeVloop, hloopM, ← hcslot, hget, ← hpres]
      exact Int.toNat_of_nonneg hextnn
    omega

/-- Beyond-range coordinate nodes are never group proxies: title copies are
`border = 3`, side markers `±1`, normalize dummies plain `0`. -/
private theorem plain_b_nonproxy {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {b : Nat}
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    (_hlt : b < run.proper.nodes.length)
    {actualB : ProperNode}
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB) :
    ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) := by
  obtain ⟨_, labeled, _, hcoordinate, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hlookup : (coordinateGraph e.params labeled).nodes[b]? = some actualB := by
    rw [hcoordinate]; exact hcoordB
  rcases coordinateGraph_lookup e.params labeled hlookup with hreal | hrest
  · obtain ⟨m, hm, _, hborder, _, _⟩ := hreal
    rcases hkeys b m hm with hcg | hdummy
    · obtain ⟨n, hcgmem, _, _, _⟩ := hcg
      have hnone : (componentCandidate e.graph comp candidate).nodes[b]? = none :=
        List.getElem?_eq_none (by omega)
      rw [hnone] at hcgmem
      exact absurd hcgmem (by simp)
    · obtain ⟨_, hborder0, _⟩ := hdummy
      have hb0 : actualB.node.border = 0 := hborder.trans hborder0
      intro hcon
      omega
  · rcases hrest with hside | htitle
    · obtain ⟨_, h12⟩ := hside
      intro hcon
      rcases h12 with h1 | h1 <;> omega
    · obtain ⟨_, _, _, _, _, hborder3, _⟩ := htitle
      intro hcon
      omega

-- Y equality for a nonproxy sliver from its border inequality.
private theorem plain_ys_eq_nonproxy {p : Proper} {layers : List (List Nat)}
    {top cy : List Int} {v : Nat} {nd : ProperNode}
    (hnd : p.nodes[v]? = some nd) (hv : v < cy.length)
    (hne : ¬ (nd.node.border = -2 ∨ nd.node.border = 2)) :
    (proxyYs p layers top cy).getD v 0 = cy.getD v 0 := by
  rw [proxyYs_getD _ _ _ _ hnd hv]
  have e1 : (nd.node.border == -2) = false := by
    cases h : (nd.node.border == -2) with
    | true => exact absurd (Or.inl (beq_iff_eq.mp h)) hne
    | false => rfl
  have e2 : (nd.node.border == 2) = false := by
    cases h : (nd.node.border == 2) with
    | true => exact absurd (Or.inr (beq_iff_eq.mp h)) hne
    | false => rfl
  simp [e1, e2]
/-- Different-rank branch: disjoint bands give y separation. -/
private theorem plain_y_branch {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v b : Nat} {nodeV : Node} {rV rB : Nat}
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    (hlt : b < run.proper.nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB0 : nodeV.border = 0)
    (hrkV : rk run.proper.rank v = (rV : Int))
    (hrkB : rk run.proper.rank b = (rB : Int))
    (hne : rV ≠ rB) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hcovered := componentRun_original_nodes_covered hrun
  have huP : v < run.proper.nodes.length := hcovered v hvlen
  have hvP : b < run.proper.nodes.length := hlt
  have hfp : loopFootprint (componentCandidate e.graph comp candidate) run e.measured v =
      ⟨(frameRect default (componentCandidate e.graph comp candidate) run v).x +
        (frameRect default (componentCandidate e.graph comp candidate) run v).w,
       (frameRect default (componentCandidate e.graph comp candidate) run v).y,
       Loops.extent (componentCandidate e.graph comp candidate).slot
         (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
           (componentCandidate e.graph comp candidate).slot),
       (frameRect default (componentCandidate e.graph comp candidate) run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨actualV, hcoordV, hpropV, _, hbV0', _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeV hvB0
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeV : frameRect default (componentCandidate e.graph comp candidate) run v =
      nodeRect (componentCandidate e.graph comp candidate) run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hvB0]
    rfl
  have hrectV : nodeRect (componentCandidate e.graph comp candidate) run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute,
      _hlanes, hry, hys, hroutes⟩ := componentRun_spec hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : v < run.coordinateProper.nodes.length := by omega
  have hvC : b < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV
  have hrkCoordB : rk run.coordinateProper.rank b = (rB : Int) := by
    rw [← hranks]; exact hrkB
  obtain ⟨_, _, _, _, _, _, hy⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hy]; simp
  have huCy : v < run.coordinateYs.length := by omega
  have hvCy : b < run.coordinateYs.length := by omega
  have hysEqV : run.ys.getD v 0 = run.coordinateYs.getD v 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordV huCy, hbV0']
    rfl
  obtain ⟨actualB, hcoordB⟩ : ∃ nd, run.coordinateProper.nodes[b]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hvC⟩
  have hBneB : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) :=
    plain_b_nonproxy e comp candidate orderOptions run hcomp hrun hle hlt hcoordB
  obtain ⟨hproperB, _hxsB⟩ := componentRun_nonproxy_record hrun hcoordB hBneB
  have hysEqB : run.ys.getD b 0 = run.coordinateYs.getD b 0 := by
    rw [← hys]
    exact plain_ys_eq_nonproxy hcoordB hvCy hBneB
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lV, hlyV0, hvIn, _hrkNNV⟩ := hcov v huP
  obtain ⟨lB, hlyB0, hbIn, _hrkNNB⟩ := hcov b hvP
  have hlyV' : run.layers[rV]? = some lV := by
    have htoNatV : (rk run.proper.rank v).toNat = rV := by
      rw [hrkV]; simp
    rw [← htoNatV]; exact hlyV0
  have hlyB' : run.layers[rB]? = some lB := by
    have htoNatB : (rk run.proper.rank b).toNat = rB := by
      rw [hrkB]; simp
    rw [← htoNatB]; exact hlyB0
  have hbandV := CoordsImpl.rankAxis_node_in_band hry hlyV' hvIn huC hrkCoordV
  have hbandB := CoordsImpl.rankAxis_node_in_band hry hlyB' hbIn hvC hrkCoordB
  have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
    simp [CoordsImpl.nodeH, hcoordV]
  have hnodeHB : CoordsImpl.nodeH run.coordinateProper b = actualB.node.h := by
    simp [CoordsImpl.nodeH, hcoordB]
  rw [hnodeHV] at hbandV
  rw [hnodeHB] at hbandB
  have hnoneB : (componentCandidate e.graph comp candidate).nodes[b]? = none :=
    List.getElem?_eq_none (by omega)
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      default := by
    rw [List.getD_eq_getElem?_getD, hnoneB, Option.getD_none]
  have hcond : (default : Node).border != -2 := by decide
  have hframeB : frameRect default (componentCandidate e.graph comp candidate) run b =
      nodeRect (componentCandidate e.graph comp candidate) run b := by
    unfold frameRect
    dsimp only
    rw [hgetB]
    simp only [hcond, ↓reduceIte]
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      ⟨run.xs.getD b 0 - Int.fdiv actualB.node.w 2, run.ys.getD b 0,
        actualB.node.w, actualB.node.h⟩ := by
    simp [nodeRect, hproperB]
  rcases Nat.lt_or_gt_of_ne hne with hltR | hgtR
  · have hbands := CoordsImpl.rankAxis_bands_disjoint hry rV rB lV lB hltR hlyV' hlyB'
    unfold LoopFootprintSeparation
    rw [hfp, hframeV, hrectV, hframeB, hrectB]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · have hbands := CoordsImpl.rankAxis_bands_disjoint hry rB rV lB lV hgtR hlyB' hlyV'
    unfold LoopFootprintSeparation
    rw [hfp, hframeV, hrectV, hframeB, hrectB]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

/-- Same-rank branch: ordered Coords intervals with the reserved loop extent
give x separation. Needs no alignment fact. -/
private theorem plain_x_branch {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v b : Nat} {nodeV : Node} {rV rB : Nat}
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    (hlt : b < run.proper.nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB0 : nodeV.border = 0)
    (hrkV : rk run.proper.rank v = (rV : Int))
    (hrkB : rk run.proper.rank b = (rB : Int))
    (heq : rV = rB) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hcovered := componentRun_original_nodes_covered hrun
  have huP : v < run.proper.nodes.length := hcovered v hvlen
  have hvP : b < run.proper.nodes.length := hlt
  have hfp : loopFootprint (componentCandidate e.graph comp candidate) run e.measured v =
      ⟨(frameRect default (componentCandidate e.graph comp candidate) run v).x +
        (frameRect default (componentCandidate e.graph comp candidate) run v).w,
       (frameRect default (componentCandidate e.graph comp candidate) run v).y,
       Loops.extent (componentCandidate e.graph comp candidate).slot
         (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
           (componentCandidate e.graph comp candidate).slot),
       (frameRect default (componentCandidate e.graph comp candidate) run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨actualV, hcoordV, hpropV, _, hbV0', _, _, _, hxsV⟩ :=
    componentRun_original_plain_record hrun hnodeV hvB0
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeV : frameRect default (componentCandidate e.graph comp candidate) run v =
      nodeRect (componentCandidate e.graph comp candidate) run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hvB0]
    rfl
  have hrectV : nodeRect (componentCandidate e.graph comp candidate) run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoordSpec, hord, hcross, hproxy, hdrop,
      hroute, _hlanes, hry, hys, hroutes⟩ := componentRun_spec hrun
  obtain ⟨ord, _hordOk, _hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : v < run.coordinateProper.nodes.length := by omega
  have hvC : b < run.coordinateProper.nodes.length := by omega
  obtain ⟨actualB, hcoordB⟩ : ∃ nd, run.coordinateProper.nodes[b]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hvC⟩
  have hBneB : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) :=
    plain_b_nonproxy e comp candidate orderOptions run hcomp hrun hle hlt hcoordB
  obtain ⟨hproperB, hxsB⟩ := componentRun_nonproxy_record hrun hcoordB hBneB
  have hnoneB : (componentCandidate e.graph comp candidate).nodes[b]? = none :=
    List.getElem?_eq_none (by omega)
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      default := by
    rw [List.getD_eq_getElem?_getD, hnoneB, Option.getD_none]
  have hcond : (default : Node).border != -2 := by decide
  have hframeB : frameRect default (componentCandidate e.graph comp candidate) run b =
      nodeRect (componentCandidate e.graph comp candidate) run b := by
    unfold frameRect
    dsimp only
    rw [hgetB]
    simp only [hcond, ↓reduceIte]
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      ⟨run.xs.getD b 0 - Int.fdiv actualB.node.w 2, run.ys.getD b 0,
        actualB.node.w, actualB.node.h⟩ := by
    simp [nodeRect, hproperB]
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lV, hlyV0, hvIn, _⟩ := hcov v huP
  obtain ⟨lB, hlyB0, hbIn, _⟩ := hcov b hvP
  have hlyV' : run.layers[rV]? = some lV := by
    have htoNatV : (rk run.proper.rank v).toNat = rV := by
      rw [hrkV]; simp
    rw [← htoNatV]; exact hlyV0
  have hlyB' : run.layers[rB]? = some lB := by
    have htoNatB : (rk run.proper.rank b).toNat = rB := by
      rw [hrkB]; simp
    rw [← htoNatB]; exact hlyB0
  rw [heq] at hlyV'
  have hlBVeq : lB = lV := Option.some.inj (hlyB'.symm.trans hlyV')
  rw [hlBVeq] at hbIn
  obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp hvIn
  obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hbIn
  have hneVB : v ≠ b := by omega
  have hnePV : pu ≠ pv := by
    intro heq'
    subst heq'
    exact hneVB (Option.some.inj (hpu.symm.trans hpv))
  have hlayerMem : lV ∈ run.layers := by
    obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyV'
    rw [← hmemEq]
    exact List.getElem_mem hmemLT
  have hfbV : ¬ (actualV.node.border = -2 ∨ actualV.node.border = 2) := by
    simp [hbV0']
  obtain ⟨_, _, _, hcoordinate, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hshape := componentCandidate_shape (components_nodup e.graph comp hcomp)
    (measuredGraph_shape e.graph_eq) candidate
  have huniq : ∀ (u w : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[w]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = w := by
    intro u w left right hleft hright hleftBorder hrightBorder hpath
    apply pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hleft)
      (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
  have hLvGe : ((actualV.node.loopExtent : Int)) ≥
      Loops.extent (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) :=
    plain_loopExtent_ge e comp candidate orderOptions run hcomp hrun hvlen hnodeV hvB0
      hcoordV
  have hLwNN : (0 : Int) ≤ ((actualB.node.loopExtent : Int)) :=
    Int.natCast_nonneg _
  have hWvNN : (0 : Int) ≤ actualV.node.w := by
    have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
    have hsizesNN := hcs.2.2.2.1
    exact (sizesNonneg_lookup hsizesNN v actualV hcoordV).1
  have hgap : 1 ≤ min e.params.nodeGap e.params.clusterPad := by
    have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
    omega
  have hVne1 : actualV.node.border ≠ -2 := by simp [hbV0']
  have hVne2 : actualV.node.border ≠ 2 := by simp [hbV0']
  have hBne1 : actualB.node.border ≠ -2 := fun h => hBneB (Or.inl h)
  have hBne2 : actualB.node.border ≠ 2 := fun h => hBneB (Or.inr h)
  rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
  · have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq lV hlayerMem
      pu pv v b actualV actualB hplt hpu hpv hcoordV hcoordB
      hVne1 hVne2 hBne1 hBne2
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordV, hcoordB] at hsep
    unfold LoopFootprintSeparation
    rw [hfp, hframeV, hrectV, hframeB, hrectB]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  · have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq lV hlayerMem
      pv pu b v actualB actualV hpgt hpv hpu hcoordB hcoordV
      hBne1 hBne2 hVne1 hVne2
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordV, hcoordB] at hsep
    unfold LoopFootprintSeparation
    rw [hfp, hframeV, hrectV, hframeB, hrectB]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega

theorem plainSliverResidual_holds {inp : Input} {o : Options} {res : FamilyResult} :
    PlainSliverResidual inp o res := by
  intro e comp candidate run orderOptions v b hcomp hrun hv hle hlt hv0
  obtain ⟨nodeV, hnodeV⟩ : ∃ n, (componentCandidate e.graph comp candidate).nodes[v]? =
      some n := ⟨_, List.getElem?_eq_getElem hv⟩
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hvB0 : nodeV.border = 0 := by
    rw [← hgetV]
    exact hv0
  have hcovered := componentRun_original_nodes_covered hrun
  have huP : v < run.proper.nodes.length := hcovered v hv
  have hvP : b < run.proper.nodes.length := hlt
  obtain ⟨_, _, _, _, _, _, _, hord, _, _, _, hroute, _hlanes, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, _⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨_, _, _, hrkNNV⟩ := hcov v huP
  obtain ⟨_, _, _, hrkNNB⟩ := hcov b hvP
  have hrkV : rk run.proper.rank v = (((rk run.proper.rank v).toNat) : Int) :=
    (Int.toNat_of_nonneg hrkNNV).symm
  have hrkB : rk run.proper.rank b = (((rk run.proper.rank b).toNat) : Int) :=
    (Int.toNat_of_nonneg hrkNNB).symm
  by_cases heq : (rk run.proper.rank v).toNat = (rk run.proper.rank b).toNat
  · exact plain_x_branch e comp candidate orderOptions run hcomp hrun hv hle hlt
      hnodeV hvB0 hrkV hrkB heq
  · exact plain_y_branch e comp candidate orderOptions run hcomp hrun hv hle hlt
      hnodeV hvB0 hrkV hrkB heq

end PipelineImpl
end Layered
end Elegant
