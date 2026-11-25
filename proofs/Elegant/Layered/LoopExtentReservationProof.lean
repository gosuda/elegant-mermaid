import Elegant.Layered.LoopFootprintBeyondProperProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.Loops
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.Labels
import Elegant.Layered.SceneBounds
import Elegant.Layered.SizingFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.Route
import Elegant.Layered.CgShape
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.Compound
import Elegant.Layered.Order
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.LoopFootprintGroupHullProof
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.StrictMemberFrameProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Shared loop-extent reservation core for executed component runs

The coordinate stage reserves the loop extent to the right of a looping node
or group: `CoordsImpl.nodeW = w + 2 * loopExtent` (`Coords.lean:40`) and the
separation constraint `coordSep` between consecutive nodes of a layer
(`Coords.lean:56`), closed through `cluster_all_pairs_separated` against the
executed `crossCoordsClusterWith` assignment. The footprint of a plain looping
node therefore ends left of every same-layer node placed right of it; the
right edge of the footprint is the frame right plus the loop extent
(`loopFootprint`), and the reservation covers exactly that extent.

Truth (all executed, 0 violations; `wip/Probe/LoopResCoreProbe.lean`, the nine
`LoopHullCoverTProbe` inputs plus plain-owner/sibling configurations: every
same-layer node right of a plain looping node starts at or right of the
footprint's right edge; margins grow with the sibling gap).

Route: sizing (`loopSizes`, `Loops.extent`, `ler_graph_node_loopExtent`),
cluster borders (right marker copies the group top's `loopExtent`,
`Order.lean:175`/`Order.lean:3684`), coordinates (`nodeW`, `coordSep`,
`cluster_all_pairs_separated`), frames (`frameRect`, `nodeRect`,
`Labels.rectAt`).

Status: the plain-owner same-layer reservation is proved below
(`loopRes_sameLayer_holds`, rect form, plus the frame-form corollary
`loopRes_sameLayer_frame_holds`). The group-top facts remain as named
single-inequality Props with executed probe evidence:
`LoopResMarkerCopy` (the right marker carries the top's extent) and
`LoopResTopReservation` (the top's footprint ends left of nodes right of its
right marker). The foreign-hull right-neighbor cover is proved through
`LoopResNeighborDisjointProof.loopHullRightNeighborCover_Disj_holds`. -/


/-- Residual: a group-top right marker carries at least the top's loop
extent. Same shape as the `hext_all` premise of
`loopFootprintTopSeparation_holds`. Probe: `BeyondTopSliverTProbe` marker
checks on wide group loops (markers track the top extent on every candidate).
Open: transport the sizing-phase top extent through `titleReservations`,
`addClusterBorders` (copy at `Order.lean:175`), `clearProxyExtents`, and the
executed `componentRun` records to the marker's `loopExtent`. -/
def LoopResMarkerCopy (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (v m : Nat) (nodeV : Node) (mk : ProperNode),
    cg.nodes[v]? = some nodeV → nodeV.border = -2 →
    run.coordinateProper.nodes[m]? = some mk →
    mk.node.border = 1 →
    mk.node.clusterPath.getLast? = some nodeV.decl →
    (mk.node.loopExtent : Int) ≥ Loops.extent cg.slot
      (loopSizes cg.edges labels v cg.slot)

/-- Residual: a group-top footprint ends left of nodes right of its right
marker. Same conclusion shape as the `hright` premise of
`loopFootprintTopSeparation_holds` and the `hgap` premise
(`TopSliverRightGapBt`) of `topLoopsSliverResidual_holds`, with the marker
and layer position made explicit. Probe: `BeyondTopSliverTProbe` (48
firings, zero violations) and the `LoopHullCoverTProbe` group-loop inputs.
Open: combine `LoopResMarkerCopy` with the marker-span alignment
(`SideMarkerSpanAligned`) and the ordered-intervals separation between the
marker and `b`, then fit the top frame inside the marker span. -/
def LoopResTopReservation (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (v mR b : Nat) (nodeV : Node) (nR actualB : ProperNode),
    cg.nodes[v]? = some nodeV → nodeV.border = -2 →
    run.coordinateProper.nodes[mR]? = some nR →
    nR.node.border = 1 →
    nR.node.clusterPath.getLast? = some nodeV.decl →
    ((nR.node.loopExtent : Int) ≥ Loops.extent cg.slot
      (loopSizes cg.edges labels v cg.slot)) →
    SideMarkerSpanAligned →
    run.coordinateProper.nodes[b]? = some actualB →
    ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) →
    run.proper.nodes[b]? = some actualB →
    run.xs.getD b 0 = run.coordinateXs.getD b 0 →
    ∀ (layer : List Nat), layer ∈ run.layers →
      ∀ (j iv : Nat), layer[j]? = some mR → layer[iv]? = some b → j < iv →
      (loopFootprint cg run labels v).x +
        (loopFootprint cg run labels v).w ≤
        (frameRect P cg run b).x

/-- Local copy of the private `bind_ok`. -/
private theorem ler_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => simp [hx, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Except.bind] using h⟩

/-- Local re-proof of `ComponentCoverage.componentCandidate_nodes_length`. -/
private theorem ler_candidate_nodes_length (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Local copy of the private `componentCandidate_slot`. -/
private theorem ler_slot (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- Local copy of the private `lines_len`. -/
private theorem ler_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Loop extents are nonnegative for nonnegative slots. -/
private theorem ler_extent_nonneg {slot : Int} (hs : 0 ≤ slot)
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

/-- Sizing-phase loop extent: an executed graph node stores the exact loop
extent of its own loop sizes. Local copy of the private
`graph_node_loopExtent_eq`. -/
private theorem ler_graph_node_loopExtent {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) {m : Nat}
    (hm : m < e.lines.length) {gnode : Node}
    (hg : e.graph.nodes[m]? = some gnode) :
    gnode.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
  have hlines : e.lines.length = inp.boxes.length := ler_lines_len e
  have hmB : m < inp.boxes.length := by rw [← hlines]; exact hm
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[m]? = some box :=
    ⟨_, List.getElem?_eq_getElem hmB⟩
  have hgE := e.graph_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := ler_bind_ok hgE
  obtain ⟨edges, _, hgE⟩ := ler_bind_ok hgE
  obtain ⟨metric, hmM, hgE⟩ := ler_bind_ok hgE
  obtain ⟨labels, hlL, hgE⟩ := ler_bind_ok hgE
  obtain ⟨nodes, hnodes, hgE⟩ := ler_bind_ok hgE
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
    ler_extent_nonneg hslotnn hwidths
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

/-- `coordinateGraph` preserves the loop extent of a plain anchor. Local copy
of the private `coordinateGraph_loopExtent`. -/
private theorem ler_coordinateGraph_loopExtent {P : Params} {p : Proper}
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

/-- Plain owner loop-extent lower bound: the executed coordinate width at `v`
covers the footprint extent. Local copy of the private `plain_loopExtent_ge`. -/
private theorem ler_loopExtent_ge {inp : Input} {o : Options} {res : FamilyResult}
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
  have hcslot : (componentCandidate e.graph comp candidate).slot =
      e.graph.slot := ler_slot e.graph comp candidate
  have hslotpos : 1 ≤ (componentCandidate e.graph comp candidate).slot := by
    rw [hcslot]
    have hG : e.graph.slot = e.params.slot := by
      have hlines : e.lines.length = inp.boxes.length := ler_lines_len e
      have hgE := e.graph_eq
      unfold measuredGraph at hgE
      obtain ⟨initial, _, hgE⟩ := ler_bind_ok hgE
      obtain ⟨edges, _, hgE⟩ := ler_bind_ok hgE
      obtain ⟨metric, hmM, hgE⟩ := ler_bind_ok hgE
      obtain ⟨labels, hlL, hgE⟩ := ler_bind_ok hgE
      obtain ⟨nodes, hnodes, hgE⟩ := ler_bind_ok hgE
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
    ler_extent_nonneg hslotnn hwidths
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
          comp.length := ler_candidate_nodes_length _ _ _
      omega
    have hget : comp.getD v 0 = comp[v]'hvl := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvl,
        Option.getD_some]
    have hlines : e.lines.length = inp.boxes.length := ler_lines_len e
    have hmlin : comp.getD v 0 < e.lines.length := by
      by_cases hcon : comp.getD v 0 < e.lines.length
      · exact hcon
      · have hge : inp.boxes.length ≤ comp.getD v 0 := by omega
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
          have hbot := (Compound.prepare_bottom_of_index _ _ _ _ _ hj hsome).1
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
          have hm_eq : comp[v]'hvl = comp.getD v 0 := by rw [hget]
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
    have hloopM := ler_graph_node_loopExtent e hmlin hgm
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
    obtain ⟨_, labeled, _, hcoordinate, hkeys, _, hrecords, _⟩ :=
      componentRun_prepared_titled_source e.graph_eq hcomp hrun
    have hlabV := hrecords v nodeV hnodeV
    obtain ⟨outV, houtV, hloopV⟩ := ler_coordinateGraph_loopExtent hlabV
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

/-- Shared core (plain owner, same layer, rect form): in an executed run, the
footprint of a plain looping node ends left of the placed rectangle of every
same-layer node positioned right of it. The loop extent is covered by the
owner's coordinate width (`CoordsImpl.nodeW`), so the gap holds for markers
and beyond-range slivers as well as plain nodes. -/
theorem loopRes_sameLayer_holds {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v b : Nat} {nodeV : Node}
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB0 : nodeV.border = 0)
    {actualV actualB : ProperNode}
    (hcoordV : run.coordinateProper.nodes[v]? = some actualV)
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2))
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hxsB : run.xs.getD b 0 = run.coordinateXs.getD b 0)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {pu pv : Nat} (hpu : layer[pu]? = some v) (hpv : layer[pv]? = some b)
    (hlt : pu < pv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
      (Labels.rectAt run.proper run.xs run.ys b).x := by
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hfp : loopFootprint (componentCandidate e.graph comp candidate) run e.measured v = ⟨(frameRect default (componentCandidate e.graph comp candidate) run v).x + (frameRect default (componentCandidate e.graph comp candidate) run v).w, (frameRect default (componentCandidate e.graph comp candidate) run v).y, Loops.extent (componentCandidate e.graph comp candidate).slot (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v (componentCandidate e.graph comp candidate).slot), (frameRect default (componentCandidate e.graph comp candidate) run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨actualV', hcoordV', hpropV, _, hbV0', _, _, _, hxsV⟩ :=
    componentRun_original_plain_record hrun hnodeV hvB0
  have hcoordVeq : actualV = actualV' :=
    Option.some.inj (hcoordV.symm.trans hcoordV')
  subst hcoordVeq
  have hxsV' : run.xs.getD v 0 = run.coordinateXs.getD v 0 := hxsV.2
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeV : frameRect default (componentCandidate e.graph comp candidate) run v =
      nodeRect (componentCandidate e.graph comp candidate) run v :=
    frameRect_of_border_zero hgetV hvB0
  have hrectV : nodeRect (componentCandidate e.graph comp candidate) run v = ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0, actualV.node.w, actualV.node.h⟩ := by
    rw [nodeRect_of_record hpropV]
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hpropV]
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoordSpec, hord, hcross, hproxy, hdrop,
      hroute, hlanes, hry, hys, hroutes⟩ := componentRun_spec hrun
  obtain ⟨_, _, _, hcoordinate, hkeys, _, hrecords, _⟩ :=
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
  have hlayerMem : layer ∈ run.layers := hlayer
  have hfbV : ¬ (actualV.node.border = -2 ∨ actualV.node.border = 2) := by
    simp [hbV0']
  have hBne1 : actualB.node.border ≠ -2 := fun h => hbne (Or.inl h)
  have hBne2 : actualB.node.border ≠ 2 := fun h => hbne (Or.inr h)
  have hVne1 : actualV.node.border ≠ -2 := by simp [hbV0']
  have hVne2 : actualV.node.border ≠ 2 := by simp [hbV0']
  have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq layer hlayerMem
    pu pv v b actualV actualB hlt hpu hpv hcoordV hcoordB
    hVne1 hVne2 hBne1 hBne2
  simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordV, hcoordB] at hsep
  have hLvGe : ((actualV.node.loopExtent : Int)) ≥
      Loops.extent (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) :=
    ler_loopExtent_ge e comp candidate orderOptions run hcomp hrun hvlen hnodeV hvB0
      hcoordV
  have hLwNN : (0 : Int) ≤ ((actualB.node.loopExtent : Int)) :=
    Int.natCast_nonneg _
  have hWvNN : (0 : Int) ≤ actualV.node.w := by
    have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
    have hsizesNN := hcs.2.2.2.1
    exact (sizesNonneg_lookup hsizesNN v actualV hcoordV).1
  have hWbNN : (0 : Int) ≤ actualB.node.w := by
    have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
    have hsizesNN := hcs.2.2.2.1
    exact (sizesNonneg_lookup hsizesNN b actualB hcoordB).1
  have hgap : 1 ≤ min e.params.nodeGap e.params.clusterPad := by
    have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
    omega
  have hrectB : (Labels.rectAt run.proper run.xs run.ys b).x =
      run.xs.getD b 0 - Int.fdiv actualB.node.w 2 := by
    simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
      hproperB]
  have hNWvNN : 0 ≤ actualV.node.w + 2 * (actualV.node.loopExtent : Int) := by
    have hnn := Int.natCast_nonneg actualV.node.loopExtent
    omega
  have hNWbNN : 0 ≤ actualB.node.w + 2 * (actualB.node.loopExtent : Int) := by
    have hnn := Int.natCast_nonneg actualB.node.loopExtent
    omega
  rw [hfp]
  dsimp only
  rw [hframeV, hrectV]
  dsimp only
  rw [hxsV', hrectB, hxsB]
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
  omega

/-- Frame-form corollary: the same reservation against the node frame. The
caller supplies the frame equation for `b` (plain nodes via
`frameRect_of_border_zero`, beyond-range slivers by unfolding `frameRect`
on the default node). -/
theorem loopRes_sameLayer_frame_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v b : Nat} {nodeV : Node}
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvB0 : nodeV.border = 0)
    {actualV actualB : ProperNode}
    (hcoordV : run.coordinateProper.nodes[v]? = some actualV)
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2))
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hxsB : run.xs.getD b 0 = run.coordinateXs.getD b 0)
    (hframeB : frameRect default (componentCandidate e.graph comp candidate) run b =
      nodeRect (componentCandidate e.graph comp candidate) run b)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {pu pv : Nat} (hpu : layer[pu]? = some v) (hpv : layer[pv]? = some b)
    (hlt : pu < pv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
      (frameRect default (componentCandidate e.graph comp candidate) run b).x := by
  have hcore := loopRes_sameLayer_holds e comp candidate orderOptions run hcomp hrun
    hvlen hnodeV hvB0 hcoordV hcoordB hbne hproperB hxsB hlayer hpu hpv hlt
  have heq : (Labels.rectAt run.proper run.xs run.ys b).x =
      (frameRect default (componentCandidate e.graph comp candidate) run b).x := by
    rw [hframeB, nodeRect_of_record hproperB, rectAt_eq]
  rw [← heq]
  exact hcore


/-- Plain-owner ancestor-hull right cover: the ancestor right-gap for plain looping
nodes. The ancestor's right border marker in the owner's layer sits right of
the owner (executed bracket), carries a positive width (`1 ≤ clusterBorderW`),
and its rect achieves no more than the hull's right edge. -/
theorem loopRes_plainExtentGap_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) (hmem : np.decl ∈ nt.clusterPath) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w <
      ((frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos).w) -
      ((frameRect execution.params
          (componentCandidate execution.graph comp candidate) run t).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run t).w) := by
  have _hframed := hframed
  have _hne := hne
  have hinside : nt.clusterPath.contains np.decl = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hmem
  obtain ⟨actual, ord, left, right, hordOk, hordLayers, hcoordM, hproperM, _,
      _, _, hxM, hleftRec, hrightRec, hbracket⟩ :=
    execution.component_member_bracket hwf hcomp hrun hnp hgrp hnt htB hinside
  obtain ⟨li, mi, ri, hli, hmi, hri, hbefore, hafter⟩ := hbracket.positions
  have hlayer : ord.layers.getD (OrderImpl.lay run.coordinateProper t) [] ∈
      run.layers := by
    rw [← hordLayers]
    exact hbracket.layer_mem
  have hcoordR := hrightRec
  have hborderR : (OrderImpl.borderRight
      (titleF ⟨np, false, none, false⟩, t) execution.params.clusterBorderW).node.border
      = 1 := rfl
  have hneR : ¬ ((OrderImpl.borderRight
      (titleF ⟨np, false, none, false⟩, t)
      execution.params.clusterBorderW).node.border = -2 ∨
      (OrderImpl.borderRight
      (titleF ⟨np, false, none, false⟩, t)
      execution.params.clusterBorderW).node.border = 2) := by
    rw [hborderR]
    decide
  obtain ⟨hproperR, hxsR⟩ :=
    componentRun_nonproxy_record hrun hcoordR hneR
  have hcore := loopRes_sameLayer_holds (v := t) (b := right) execution comp
    candidate orderOptions run hcomp hrun
    ((List.getElem?_eq_some_iff.mp hnt).1) hnt htB hcoordM hcoordR hneR hproperR
    hxsR hlayer hmi hri hafter
  have hlast : (OrderImpl.borderRight
      (titleF ⟨np, false, none, false⟩, t)
      execution.params.clusterBorderW).node.clusterPath.getLast? = some np.decl := by
    have hpath : (OrderImpl.borderRight
        (titleF ⟨np, false, none, false⟩, t)
        execution.params.clusterBorderW).node.clusterPath = np.clusterPath := by
      simp [OrderImpl.borderRight, titleF, hgrp]
    rw [hpath]
    obtain ⟨key, hkey, hsource⟩ :=
      componentCandidate_nonplain_source hnp (by omega)
    obtain ⟨_, _, _, _, hpathNp⟩ :=
      measuredGraph_group_origin (lines := execution.lines) execution.graph_eq hsource
        hgrp
    rw [hpathNp]
    simp
  have hmemB : Labels.rectAt run.proper run.xs run.ys right ∈
      groupBorderRects (componentCandidate execution.graph comp candidate) run
        np.decl :=
    groupBorderRects_mem_of_record hproperR (Or.inr hborderR) hlast
  have hright_le := (boundsOf_rect_mem hmemB).2
  have hframe := frameRect_group_span (P := execution.params) (run := run) hnp hgrp
  have hfx : (loopFootprint (componentCandidate execution.graph comp candidate) run
      execution.measured t).x =
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w := rfl
  have hbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have hwpos : 0 < (Labels.rectAt run.proper run.xs run.ys right).w := by
    have hwEq : (Labels.rectAt run.proper run.xs run.ys right).w =
        execution.params.clusterBorderW := by
      simp only [rectAt_eq, RouteImpl.nodeW, OrderImpl.borderRight, hproperR]
    omega
  have hframeR : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).x +
      (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).w =
      (boundsOf (groupBorderRects (componentCandidate execution.graph comp candidate)
        run np.decl) []).right := by
    rw [hframe]
    dsimp only
    omega
  have hlt : (loopFootprint (componentCandidate execution.graph comp candidate) run
      execution.measured t).x + (loopFootprint (componentCandidate execution.graph comp candidate) run
      execution.measured t).w <
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).w := by
    omega
  rw [hfx] at hlt
  omega

end PipelineImpl
end Layered
end Elegant
