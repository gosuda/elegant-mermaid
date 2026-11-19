import Elegant.Layered.SizingFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open CoordsImpl

private theorem foldl_emits_record {α σ : Type} (step : σ → α → σ)
    (ready record : σ → Prop)
    (preserveReady : ∀ state entry, ready state → ready (step state entry))
    (preserveRecord : ∀ state entry, ready state → record state →
      record (step state entry))
    (entries : List α) (initial : σ) (hready : ready initial)
    (hemits : ∃ entry ∈ entries, ∀ state, ready state →
      record (step state entry)) :
    record (entries.foldl step initial) := by
  induction entries generalizing initial with
  | nil => simp at hemits
  | cons entry entries ih =>
      obtain ⟨chosen, hchosen, hrecord⟩ := hemits
      rcases List.mem_cons.mp hchosen with heq | htail
      · subst chosen
        have hstart := hrecord initial hready
        have hfold : ∀ (rest : List α) (state : σ), ready state →
            record state → record (rest.foldl step state) := by
          intro rest
          induction rest with
          | nil => intro state _ hr; exact hr
          | cons item rest ihr =>
              intro state hs hr
              exact ihr (step state item) (preserveReady state item hs)
                (preserveRecord state item hs hr)
        exact hfold entries (step initial entry)
          (preserveReady initial entry hready) hstart
      · exact ih (step initial entry) (preserveReady initial entry hready)
          ⟨chosen, htail, hrecord⟩

theorem cluster_border_rank_fold_emits
    (initial : Proper) (lo count decl : Nat) (path : List Nat)
    (width : Int) (loopExtent : Nat)
    (haligned : initial.nodes.length = initial.rank.length)
    {offset : Nat} (hoffset : offset < count) :
    let output := (List.range count).foldl (fun state position =>
      let node : Node := { decl := decl, w := width, h := 0, clusterPath := path }
      { state with
        edges := state.edges ++ OrderImpl.borderLinks state.nodes.length decl position
        nodes := state.nodes ++
          [⟨{ node with border := -1 }, false, none, false⟩,
           ⟨{ node with border := 1, loopExtent := loopExtent }, false, none, false⟩]
        rank := state.rank ++ [((lo + position : Nat) : Int),
          ((lo + position : Nat) : Int)] }) initial
    ∃ left right : Nat,
      output.nodes[left]? =
        some ⟨{ decl := decl
                w := width
                h := 0
                clusterPath := path
                border := -1 }, false, none, false⟩ ∧
      output.nodes[right]? =
        some ⟨{ decl := decl
                w := width
                h := 0
                clusterPath := path
                border := 1
                loopExtent := loopExtent }, false, none, false⟩ ∧
      output.rank[left]? = some ((lo + offset : Nat) : Int) ∧
      output.rank[right]? = some ((lo + offset : Nat) : Int) := by
  let leftNode : ProperNode :=
    ⟨{ decl := decl
       w := width
       h := 0
       clusterPath := path
       border := -1 }, false, none, false⟩
  let rightNode : ProperNode :=
    ⟨{ decl := decl
       w := width
       h := 0
       clusterPath := path
       border := 1
       loopExtent := loopExtent }, false, none, false⟩
  let step := fun (state : Proper) (position : Nat) =>
    { state with
      edges := state.edges ++ OrderImpl.borderLinks state.nodes.length decl position
      nodes := state.nodes ++ [leftNode, rightNode]
      rank := state.rank ++ [((lo + position : Nat) : Int),
        ((lo + position : Nat) : Int)] }
  let ready := fun state : Proper => state.nodes.length = state.rank.length
  let record := fun state : Proper => ∃ left right : Nat,
    state.nodes[left]? = some leftNode ∧ state.nodes[right]? = some rightNode ∧
    state.rank[left]? = some ((lo + offset : Nat) : Int) ∧
    state.rank[right]? = some ((lo + offset : Nat) : Int)
  change record ((List.range count).foldl step initial)
  apply foldl_emits_record step ready record
  · intro state position hs
    simpa only [ready, step, List.length_append, List.length_cons,
      List.length_nil] using congrArg (fun n : Nat => n + 2) hs
  · intro state position _ hr
    obtain ⟨left, right, hl, hr, hrl, hrr⟩ := hr
    have hleft := (List.getElem?_eq_some_iff.mp hl).1
    have hright := (List.getElem?_eq_some_iff.mp hr).1
    have hrleft := (List.getElem?_eq_some_iff.mp hrl).1
    have hrright := (List.getElem?_eq_some_iff.mp hrr).1
    refine ⟨left, right, ?_, ?_, ?_, ?_⟩
    · exact (List.getElem?_append_left hleft).trans hl
    · exact (List.getElem?_append_left hright).trans hr
    · exact (List.getElem?_append_left hrleft).trans hrl
    · exact (List.getElem?_append_left hrright).trans hrr
  · exact haligned
  · refine ⟨offset, List.mem_range.mpr hoffset, ?_⟩
    intro state hs
    refine ⟨state.nodes.length, state.nodes.length + 1, ?_, ?_, ?_, ?_⟩
    · simp [step]
    · simp [step]
    · simp [step, show state.nodes.length = state.rank.length from hs]
    · simp [step, show state.nodes.length = state.rank.length from hs]

private def RankedRecordExtension (source target : Proper) : Prop :=
  source.nodes.length = source.rank.length →
    target.nodes.length = target.rank.length ∧
      ∀ (i : Nat) (node : ProperNode) (rank : Int),
        source.nodes[i]? = some node → source.rank[i]? = some rank →
        target.nodes[i]? = some node ∧ target.rank[i]? = some rank

private theorem rankedRecordExtension_refl (source : Proper) :
    RankedRecordExtension source source := by
  intro h
  exact ⟨h, fun _ _ _ hn hr => ⟨hn, hr⟩⟩

private theorem rankedRecordExtension_append
    {source target : Proper} (h : RankedRecordExtension source target)
    (nodes : List ProperNode) (ranks : List Int)
    (hlen : nodes.length = ranks.length) (edges : List ProperEdge) :
    RankedRecordExtension source
      { target with
        nodes := target.nodes ++ nodes
        rank := target.rank ++ ranks
        edges := edges } := by
  intro hs
  obtain ⟨ht, hrecords⟩ := h hs
  refine ⟨?_, ?_⟩
  · simp only [List.length_append]
    omega
  intro i node rank hn hr
  obtain ⟨hn', hr'⟩ := hrecords i node rank hn hr
  exact ⟨(List.getElem?_append_left (List.getElem?_eq_some_iff.mp hn').1).trans hn',
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr').1).trans hr'⟩

theorem addClusterBorders_rank_pair (source : Proper) (width : Int)
    (haligned : source.nodes.length = source.rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ source.nodes.zipIdx) (hborder : top.1.node.border = -2)
    (hbottom : (source.nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk source.rank top.2).toNat ≤ rank)
    (hhi : rank ≤ (rk source.rank bottom.2).toNat) :
    let output := OrderImpl.addClusterBorders source width
    ∃ left right : Nat,
      output.nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := width
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      output.nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := width
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      output.rank[left]? = some (rank : Int) ∧
      output.rank[right]? = some (rank : Int) := by
  let ready := fun state : Proper => state.nodes.length = state.rank.length
  let record := fun state : Proper => ∃ left right : Nat,
    state.nodes[left]? =
      some ⟨{ decl := top.1.node.decl
              w := width
              h := 0
              clusterPath := top.1.node.clusterPath
              border := -1 }, false, none, false⟩ ∧
    state.nodes[right]? =
      some ⟨{ decl := top.1.node.decl
              w := width
              h := 0
              clusterPath := top.1.node.clusterPath
              border := 1
              loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
    state.rank[left]? = some (rank : Int) ∧ state.rank[right]? = some (rank : Int)
  let step := fun (state : Proper) (entry : ProperNode × Nat) =>
    match (source.nodes.zipIdx.find? fun b =>
        b.1.node.border == 2 && b.1.node.clusterPath == entry.1.node.clusterPath).map (·.2) with
    | none => state
    | some bot =>
        let lo := (rk source.rank entry.2).toNat
        let hi := (rk source.rank bot).toNat
        (List.range (hi + 1 - lo)).foldl (fun (current : Proper) (offset : Nat) =>
          let node : Node := {
            decl := entry.1.node.decl
            w := width
            h := 0
            clusterPath := entry.1.node.clusterPath }
          { current with
            edges := current.edges ++
              OrderImpl.borderLinks current.nodes.length entry.1.node.decl offset
            nodes := current.nodes ++
              [ProperNode.mk { node with border := -1 } false none false,
               ProperNode.mk
                 { node with
                   border := 1
                   loopExtent := entry.1.node.loopExtent } false none false]
            rank := current.rank ++ [((lo + offset : Nat) : Int),
              ((lo + offset : Nat) : Int)] }) state
  have hext : ∀ state entry, RankedRecordExtension state (step state entry) := by
    intro state entry
    dsimp only [step]
    split
    · exact rankedRecordExtension_refl state
    · apply OrderImpl.foldl_inv (RankedRecordExtension state)
      · exact rankedRecordExtension_refl state
      · intro current hc offset _
        exact rankedRecordExtension_append hc _ _ rfl _
  change record (((source.nodes.zipIdx.filter fun q =>
    q.1.node.border == -2)).foldl step source)
  apply foldl_emits_record step ready record
  · intro state entry hs
    exact (hext state entry hs).1
  · intro state entry hs hr
    obtain ⟨left, right, hl, hr, hrl, hrr⟩ := hr
    obtain ⟨_, hrecords⟩ := hext state entry hs
    obtain ⟨hl', hrl'⟩ := hrecords left _ _ hl hrl
    obtain ⟨hr', hrr'⟩ := hrecords right _ _ hr hrr
    exact ⟨left, right, hl', hr', hrl', hrr'⟩
  · exact haligned
  · refine ⟨top, List.mem_filter.mpr ⟨htop, by simp [hborder]⟩, ?_⟩
    intro state hs
    have hoffset :
        rank - (rk source.rank top.2).toNat <
          (rk source.rank bottom.2).toNat + 1 - (rk source.rank top.2).toNat := by
      omega
    have hsum : (rk source.rank top.2).toNat +
        (rank - (rk source.rank top.2).toNat) = rank := by omega
    have hemits := cluster_border_rank_fold_emits state
      (rk source.rank top.2).toNat
      ((rk source.rank bottom.2).toNat + 1 - (rk source.rank top.2).toNat)
      top.1.node.decl top.1.node.clusterPath width top.1.node.loopExtent hs hoffset
    simpa only [step, hbottom, Option.map_some, hsum] using hemits

theorem coordinateGraph_side_record {P : Params} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraph P source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

theorem coordinateGraph_rank_pair (P : Params) (source : Proper)
    (haligned : (titleReservations (sizeProperPorts P source)).nodes.length =
      (titleReservations (sizeProperPorts P source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPorts P source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPorts P source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPorts P source)).rank top.2).toNat ≤ rank)
    (hhi : rank ≤ (rk (titleReservations (sizeProperPorts P source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraph P source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraph P source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraph P source).rank[left]? = some (rank : Int) ∧
      (coordinateGraph P source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPorts P source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, coordinateGraph_side_record hl rfl (Or.inl rfl),
    coordinateGraph_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

theorem componentRun_ranked_source {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      ∀ edge ∈ (Compound.rankingGraph cg).edges,
        edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  unfold componentRun at h
  obtain ⟨rr, hrr, h⟩ := bind_ok h
  obtain ⟨normalized, hn, h⟩ := bind_ok h
  obtain ⟨labeled, hl, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨routing, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have heq := Except.ok.inj h
  subst run
  refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
  apply rank_feasible (Compound.rankingGraph cg) rr.ranks
  simp only [RankImpl.rank, hrr]

theorem normalizeEdge_rank_prefix {slot : Int} {source target : Proper}
    {edge : Edge} {index : Nat}
    (h : NormalizeImpl.normalizeEdge slot source edge index = .ok target) :
    ∃ extra, target.rank = source.rank ++ extra := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · cases h
    exact ⟨[], by simp⟩
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨_, rfl⟩

theorem normalizeLoop_rank_prefix {slot : Int} (entries : List (Edge × Nat))
    {source target : Proper}
    (h : NormalizeImpl.normalizeLoop slot entries source = .ok target) :
    ∃ extra, target.rank = source.rank ++ extra := by
  induction entries generalizing source with
  | nil =>
      cases h
      exact ⟨[], by simp⟩
  | cons entry entries ih =>
      simp only [NormalizeImpl.normalizeLoop] at h
      split at h
      · cases h
      · rename_i next hnext
        obtain ⟨first, hfirst⟩ := normalizeEdge_rank_prefix hnext
        obtain ⟨rest, hrest⟩ := ih h
        exact ⟨first ++ rest, by rw [hrest, hfirst, List.append_assoc]⟩

theorem normalize_rank_prefix {graph : Graph} {ranks : List Int} {output : Proper}
    (h : normalize graph ranks = .ok output) :
    ∃ extra, output.rank = ranks ++ extra := by
  unfold NormalizeImpl.normalize at h
  split at h
  · cases h
  · split at h
    · exact normalizeLoop_rank_prefix _ h
    · cases h

theorem normalize_rank_record {graph : Graph} {ranks : List Int} {output : Proper}
    (h : normalize graph ranks = .ok output)
    {index : Nat} {rank : Int} (hsource : ranks[index]? = some rank) :
    output.rank[index]? = some rank := by
  obtain ⟨extra, hprefix⟩ := normalize_rank_prefix h
  rw [hprefix, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hsource).1]
  exact hsource

theorem componentRun_ranked_node_records {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) ∧
      (∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      ∀ edge ∈ (Compound.rankingGraph cg).edges,
        edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, hfeasible⟩ :=
    componentRun_ranked_source h
  refine ⟨rr, labeled, hrr, hc, ?_, ?_, hfeasible⟩
  · intro index rank hr
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hr
  · intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl

theorem prepare_bottom_origin (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (source : Graph)
    (hplain : ∀ node ∈ source.nodes, node.border = 0)
    {node : Node} (hnode : node ∈ (Compound.prepare boxes pad titles source).nodes)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, boxes[node.decl]? = some box ∧ box.role = .group ∧
      node.clusterPath = Compound.path boxes box ++ [node.decl] ∧
      node.w = 0 ∧ node.h = 0 := by
  change node ∈ Compound.markNodes boxes pad titles source.nodes at hnode
  rw [markNodes_eq] at hnode
  rcases List.mem_append.mp hnode with horiginal | hextra
  · obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp horiginal
    have hzero := hplain entry.1
      (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hentry))
    have hnotBottom : (markOne boxes pad titles entry).border ≠ 2 := by
      unfold markOne
      split
      · simpa only [hzero] using (show (0 : Int) ≠ 2 by decide)
      · split
        · exact (show (-2 : Int) ≠ 2 by decide)
        · simpa only [hzero] using (show (0 : Int) ≠ 2 by decide)
    rw [heq] at hnotBottom
    exact (hnotBottom hborder).elim
  · unfold markExtras at hextra
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hextra
    split at heq
    · rename_i hgroup
      have hrecord := Option.some.inj heq
      subst node
      exact ⟨entry.1, List.mem_zipIdx_iff_getElem?.mp hentry,
        by simpa only [beq_iff_eq] using hgroup, rfl, rfl, rfl⟩
    · cases heq

theorem measuredGraph_bottom_origin {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {node : Node} (hnode : node ∈ graph.nodes) (hborder : node.border = 2) :
    ∃ box : ModelBox,
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[node.decl]? = some box ∧
      box.role = .group ∧
      node.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [node.decl] ∧
      node.w = 0 ∧ node.h = 0 := by
  obtain ⟨nodes, edges, titles, hprepared, _, hmetadata⟩ :=
    measuredGraph_prepared_source hgraph
  rw [hprepared] at hnode
  apply prepare_bottom_origin _ _ _ _ _ hnode hborder
  intro original horiginal
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp horiginal
  exact (hmetadata index original hindex).2

theorem measuredGraph_bottom_path_iff_decl {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {first second : Node} (hfirst : first ∈ graph.nodes) (hsecond : second ∈ graph.nodes)
    (hfirstBorder : first.border = 2) (hsecondBorder : second.border = 2) :
    first.clusterPath = second.clusterPath ↔ first.decl = second.decl := by
  obtain ⟨firstBox, hfirstBox, _, hfirstPath, _, _⟩ :=
    measuredGraph_bottom_origin hgraph hfirst hfirstBorder
  obtain ⟨secondBox, hsecondBox, _, hsecondPath, _, _⟩ :=
    measuredGraph_bottom_origin hgraph hsecond hsecondBorder
  constructor
  · intro hpath
    have hlast := congrArg List.getLast? hpath
    simpa [hfirstPath, hsecondPath] using hlast
  · intro hdecl
    rw [hdecl] at hfirstBox hfirstPath
    have hbox : firstBox = secondBox := Option.some.inj (hfirstBox.symm.trans hsecondBox)
    rw [hfirstPath, hsecondPath, hbox]

theorem componentCandidate_nonplain_source {graph : Graph} {comp : List Nat}
    {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hborder : node.border ≠ 0) :
    ∃ original, comp[index]? = some original ∧ graph.nodes[original]? = some node := by
  rw [componentCandidate_nodes] at hnode
  change (comp.map fun key => graph.nodes.getD key default)[index]? = some node at hnode
  cases hindex : comp[index]? with
  | none => simp [List.getElem?_map, hindex] at hnode
  | some original =>
      have hvalue : graph.nodes.getD original default = node := by
        simpa only [List.getElem?_map, hindex, Option.map_some, Option.some.injEq] using hnode
      cases horiginal : graph.nodes[original]? with
      | none =>
          have hdefault : (default : Node) = node := by
            simpa only [List.getD_eq_getElem?_getD, horiginal, Option.getD_none] using hvalue
          have hzero : node.border = 0 := by
            rw [← hdefault]
            rfl
          exact (hborder hzero).elim
      | some source =>
          have heq : source = node := by
            simpa only [List.getD_eq_getElem?_getD, horiginal, Option.getD_some] using hvalue
          exact ⟨original, rfl, horiginal.trans (congrArg some heq)⟩

theorem componentCandidate_bottom_path_iff_decl {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate firstIndex secondIndex : Nat} {first second : Node}
    (hfirst : (componentCandidate graph comp candidate).nodes[firstIndex]? = some first)
    (hsecond : (componentCandidate graph comp candidate).nodes[secondIndex]? = some second)
    (hfirstBorder : first.border = 2) (hsecondBorder : second.border = 2) :
    first.clusterPath = second.clusterPath ↔ first.decl = second.decl := by
  obtain ⟨_, _, hfirstSource⟩ :=
    componentCandidate_nonplain_source hfirst (by omega)
  obtain ⟨_, _, hsecondSource⟩ :=
    componentCandidate_nonplain_source hsecond (by omega)
  exact measuredGraph_bottom_path_iff_decl hgraph
    (List.mem_of_getElem? hfirstSource) (List.mem_of_getElem? hsecondSource)
    hfirstBorder hsecondBorder

theorem addLabelNodes_node_length {graph : Graph} {source target : Proper}
    {labels : List EdgeLabelSize}
    (h : Labels.addLabelNodes graph source labels = .ok target) :
    source.nodes.length = target.nodes.length := by
  have heq : source.nodes.map ProperNode.dummy = target.nodes.map ProperNode.dummy := by
    apply List.ext_getElem?
    intro index
    simpa only [List.getElem?_map] using
      ((Labels.addLabelNodes_metadata h).2.2.2 index).symm
  simpa only [List.length_map] using congrArg List.length heq

theorem titleReservations_node_rank_alignment (P : Params) {source : Proper}
    (h : source.nodes.length = source.rank.length) :
    (titleReservations (sizeProperPorts P source)).nodes.length =
      (titleReservations (sizeProperPorts P source)).rank.length := by
  rw [titleReservations_nodes]
  simp only [List.length_append, List.length_map, sizeProperPorts_length]
  have hrank : (titleReservations (sizeProperPorts P source)).rank =
      source.rank ++ (titleNodes (sizeProperPorts P source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPorts
    rfl
  rw [hrank]
  simp only [List.length_append, List.length_map]
  omega

theorem componentRun_coordinate_source_alignment {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∃ labeled : Proper, coordinateGraph P labeled = run.coordinateProper ∧
      NodeKeys cg labeled ∧ labeled.nodes.length = labeled.rank.length ∧
      (titleReservations (sizeProperPorts P labeled)).nodes.length =
        (titleReservations (sizeProperPorts P labeled)).rank.length := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := componentRun_ranked_source h
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  exact ⟨labeled, hc, addLabelNodes_keys _ _ _ (normalize_keys hn) hl,
    haligned, titleReservations_node_rank_alignment P haligned⟩

theorem prepare_group_origin (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (source : Graph)
    (hmetadata : ∀ (index : Nat) (node : Node), source.nodes[index]? = some node →
      node.decl = index ∧ node.border = 0)
    {index : Nat} {node : Node}
    (hnode : (Compound.prepare boxes pad titles source).nodes[index]? = some node)
    (hborder : node.border = -2) :
    node.decl = index ∧
      ∃ box : ModelBox, boxes[node.decl]? = some box ∧ box.role = .group ∧
        node.clusterPath = Compound.path boxes box ++ [node.decl] := by
  have hi : index < source.nodes.length := by
    by_cases hi : index < source.nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index boxes pad titles source index (by omega) hnode
      omega
  have hsource := hmetadata index source.nodes[index] (List.getElem?_eq_getElem hi)
  obtain ⟨box, hbox, hrole, hdecl, _, _, _, hpath⟩ :=
    Compound.prepare_group_title_of_border boxes pad titles source hi hnode hborder
      (by rw [hsource.2]; decide)
  have hdeclIndex : node.decl = index := hdecl.trans hsource.1
  refine ⟨hdeclIndex, box, ?_, hrole, ?_⟩
  · simpa only [hdeclIndex] using hbox
  · simpa only [hdeclIndex] using hpath

theorem measuredGraph_group_origin {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {index : Nat} {node : Node} (hnode : graph.nodes[index]? = some node)
    (hborder : node.border = -2) :
    node.decl = index ∧
      ∃ box : ModelBox,
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)[node.decl]? = some box ∧
        box.role = .group ∧
        node.clusterPath = Compound.path (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) box ++ [node.decl] := by
  obtain ⟨nodes, edges, titles, hprepared, _, hmetadata⟩ :=
    measuredGraph_prepared_source hgraph
  rw [hprepared] at hnode
  exact prepare_group_origin _ _ _ _ hmetadata hnode hborder

theorem measuredGraph_group_bottom_path_iff_decl {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {index : Nat} {top bottom : Node} (htop : graph.nodes[index]? = some top)
    (hgroup : top.border = -2) (hbottom : bottom ∈ graph.nodes)
    (hbottomBorder : bottom.border = 2) :
    bottom.clusterPath = top.clusterPath ↔ bottom.decl = top.decl := by
  obtain ⟨_, topBox, htopBox, _, htopPath⟩ :=
    measuredGraph_group_origin hgraph htop hgroup
  obtain ⟨bottomBox, hbottomBox, _, hbottomPath, _, _⟩ :=
    measuredGraph_bottom_origin hgraph hbottom hbottomBorder
  constructor
  · intro hpath
    have hlast := congrArg List.getLast? hpath
    simpa [htopPath, hbottomPath] using hlast
  · intro hdecl
    rw [hdecl] at hbottomBox hbottomPath
    have hbox : bottomBox = topBox := Option.some.inj (hbottomBox.symm.trans htopBox)
    rw [hbottomPath, htopPath, hbox]

theorem componentCandidate_bottom_lookup_keys {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {top : Node}
    (htop : (componentCandidate graph comp candidate).nodes[index]? = some top)
    (hgroup : top.border = -2) :
    ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.clusterPath == top.clusterPath) =
    ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) := by
  obtain ⟨_, _, htopSource⟩ := componentCandidate_nonplain_source htop (by omega)
  apply RankImpl.find?_congr'
  intro entry hentry
  by_cases hb : entry.1.border = 2
  · have hentryLookup := List.mem_zipIdx_iff_getElem?.mp hentry
    obtain ⟨_, _, hbottomSource⟩ :=
      componentCandidate_nonplain_source hentryLookup (by omega)
    have hkey := measuredGraph_group_bottom_path_iff_decl hgraph htopSource hgroup
      (List.mem_of_getElem? hbottomSource) hb
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => ⟨h.1, hkey.mp h.2⟩, fun h => ⟨h.1, hkey.mpr h.2⟩⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => (hb h.1).elim, fun h => (hb h.1).elim⟩

theorem rankingGraph_constraint_feasible {graph : Graph} {rr : RankImpl.RankResult}
    (h : rankWithBudget (Compound.rankingGraph graph) = .ok rr)
    {edge : Edge} (hedge : edge ∈ Compound.constraints graph) :
    edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  have hfeasible := rank_feasible (Compound.rankingGraph graph) rr.ranks
    (by simp only [RankImpl.rank, h])
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hedge
  have hrecord : ({ edge with decl := graph.edges.length + index } : Edge) ∈
      (Compound.rankingGraph graph).edges := by
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(edge, index), List.mk_mem_zipIdx_iff_getElem?.mpr hindex, rfl⟩
  exact hfeasible { edge with decl := graph.edges.length + index } hrecord

theorem compound_member_constraint_edges {graph : Graph}
    {top bottom member : Node × Nat}
    (htop : top ∈ graph.nodes.zipIdx) (hgroup : top.1.border = -2)
    (hbottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom)
    (hmember : member ∈ graph.nodes.zipIdx) (hplain : member.1.border = 0)
    (hinside : member.1.clusterPath.contains top.1.decl = true) :
    (⟨top.2, member.2, 1, 0, false⟩ : Edge) ∈ Compound.constraints graph ∧
      (⟨member.2, bottom.2, 1, 0, false⟩ : Edge) ∈ Compound.constraints graph := by
  let members := graph.nodes.zipIdx.filter fun entry =>
    entry.1.border == 0 && entry.1.clusterPath.contains top.1.decl
  have hmembers : member ∈ members :=
    List.mem_filter.mpr ⟨hmember,
      Bool.and_eq_true_iff.mpr ⟨by simp [hplain], hinside⟩⟩
  have hnonempty : members.isEmpty = false := by
    cases hm : members with
    | nil => simp [hm] at hmembers
    | cons first rest => rfl
  have hpair : ∀ edge ∈ ([⟨top.2, member.2, 1, 0, false⟩,
      ⟨member.2, bottom.2, 1, 0, false⟩] : List Edge),
      edge ∈ Compound.constraints graph := by
    intro edge hedge
    unfold Compound.constraints
    apply List.mem_flatMap.mpr
    refine ⟨top, List.mem_filter.mpr ⟨htop, by simp [hgroup]⟩, ?_⟩
    rw [hbottom]
    dsimp only
    split
    · rename_i hempty
      have hmembersEmpty : members.isEmpty = true := (Bool.and_eq_true_iff.mp hempty).1
      rw [hnonempty] at hmembersEmpty
      cases hmembersEmpty
    · apply List.mem_append_left
      apply List.mem_flatMap.mpr
      exact ⟨member, hmembers, hedge⟩
  exact ⟨hpair _ (by simp), hpair _ (by simp)⟩

theorem ranked_compound_member_interval {graph : Graph} {rr : RankImpl.RankResult}
    (hrank : rankWithBudget (Compound.rankingGraph graph) = .ok rr)
    {top bottom member : Node × Nat}
    (htop : top ∈ graph.nodes.zipIdx) (hgroup : top.1.border = -2)
    (hbottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom)
    (hmember : member ∈ graph.nodes.zipIdx) (hplain : member.1.border = 0)
    (hinside : member.1.clusterPath.contains top.1.decl = true) :
    rk rr.ranks top.2 + 1 ≤ rk rr.ranks member.2 ∧
      rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottom.2 := by
  obtain ⟨hleft, hright⟩ :=
    compound_member_constraint_edges htop hgroup hbottom hmember hplain hinside
  have hleftRank := rankingGraph_constraint_feasible hrank hleft
  have hrightRank := rankingGraph_constraint_feasible hrank hright
  dsimp only at hleftRank hrightRank
  omega

theorem prepare_border_cases (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (source : Graph)
    (hplain : ∀ node ∈ source.nodes, node.border = 0)
    {node : Node} (hnode : node ∈ (Compound.prepare boxes pad titles source).nodes) :
    node.border = 0 ∨ node.border = -2 ∨ node.border = 2 := by
  change node ∈ Compound.markNodes boxes pad titles source.nodes at hnode
  rw [markNodes_eq] at hnode
  rcases List.mem_append.mp hnode with horiginal | hextra
  · obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp horiginal
    have hzero := hplain entry.1
      (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hentry))
    rw [← heq]
    unfold markOne
    split
    · exact Or.inl hzero
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hzero
  · exact Or.inr (Or.inr (markExtras_border node hextra))

theorem measuredGraph_marker_shape {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {index : Nat} {node : Node} (hnode : graph.nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  constructor
  · obtain ⟨nodes, edges, titles, hprepared, _, hmetadata⟩ :=
      measuredGraph_prepared_source hgraph
    have hmember := List.mem_of_getElem? hnode
    rw [hprepared] at hmember
    apply prepare_border_cases _ _ _ _ _ hmember
    intro original horiginal
    obtain ⟨key, hkey⟩ := List.mem_iff_getElem?.mp horiginal
    exact (hmetadata key original hkey).2
  · intro hgroup
    obtain ⟨_, box, _, _, hpath⟩ := measuredGraph_group_origin hgraph hnode hgroup
    intro hempty
    have hlength := congrArg List.length hempty
    simp [hpath] at hlength

theorem componentCandidate_marker_shape {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  by_cases hplain : node.border = 0
  · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
  · obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hnode hplain
    exact measuredGraph_marker_shape hgraph hsource

theorem sizeProperPorts_node_origin (P : Params) (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPorts P source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPorts_key P source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

theorem titled_node_origin {cg : Graph} {P : Params} {source : Proper}
    (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
    (hnode : (titleReservations (sizeProperPorts P source)).nodes[index]? = some node) :
    (∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath) ∨
    (node.dummy = false ∧ node.node.border = 3) := by
  rw [titleReservations_nodes] at hnode
  by_cases hi : index < (sizeProperPorts P source).nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map] at hnode
    obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨original, horiginal, hd, hb, hp⟩ :=
      sizeProperPorts_node_origin P source hsized
    have ht := titleF_keys sized
    rw [heq] at ht
    exact Or.inl ⟨original, horiginal, ht.1.trans hd,
      ht.2.1.trans hb, ht.2.2.1.trans hp⟩
  · rw [List.getElem?_append_right (by
      simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getElem?_map] at hnode
    obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hd, hb, _⟩ :=
      sizeProperPorts_node_origin P source hsized
    have hreal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · rw [hplain] at hb
        omega
    right
    rw [← heq]
    exact ⟨hd.trans hreal, rfl⟩

theorem titled_border_ready {cg : Graph} {P : Params} {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P source)) := by
  refine ⟨?_, ?_, ?_, titleReservations_node_rank_alignment P haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases titled_node_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases titled_node_origin hkeys hb with
        ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases titled_node_origin hkeys hindex with
      ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy

theorem componentRun_titled_border_ready {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) :
    ∃ labeled : Proper, coordinateGraph P labeled = run.coordinateProper ∧
      OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P labeled)) := by
  obtain ⟨labeled, hc, hk, haligned, _⟩ := componentRun_coordinate_source_alignment hrun
  refine ⟨labeled, hc, titled_border_ready hk ?_ ?_ haligned⟩
  · exact componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  · intro index node hnode
    exact componentCandidate_marker_shape hgraph hnode

theorem bordersWellFormed_of_key_transport {source target : Proper}
    (hsource : OrderImpl.BordersWellFormed source)
    (hrank : target.rank = source.rank)
    (hlookup : ∀ (index : Nat) (node : ProperNode), target.nodes[index]? = some node →
      ∃ original : ProperNode, source.nodes[index]? = some original ∧
        node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
        (original.dummy = false → node.node.clusterPath = original.node.clusterPath)) :
    OrderImpl.BordersWellFormed target := by
  have hreal : ∀ (index : Nat) (node : ProperNode), source.nodes[index]? = some node →
      (node.node.border = -1 ∨ node.node.border = 1) → node.dummy = false := by
    intro index node hnode hside
    cases hd : node.dummy with
    | false => rfl
    | true =>
        have hzero := hsource.2.2 index node hnode hd
        rcases hside with hside | hside <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro index node hnode hside
    obtain ⟨original, horiginal, _, hb, hp⟩ := hlookup index node hnode
    have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
      rwa [hb] at hside
    rw [hp (hreal index original horiginal hoside)]
    exact hsource.1 index original horiginal hoside
  · intro a b na nb ha hb hside hborder hpath hlayer
    obtain ⟨oa, hoa, _, hba, hpa⟩ := hlookup a na ha
    obtain ⟨ob, hob, _, hbb, hpb⟩ := hlookup b nb hb
    have hsideA : oa.node.border = -1 ∨ oa.node.border = 1 := by
      rwa [hba] at hside
    have hsideB : ob.node.border = -1 ∨ ob.node.border = 1 := by
      rcases hsideA with hsideA | hsideA <;> omega
    apply hsource.2.1 a b oa ob hoa hob hsideA
    · omega
    · rw [← hpa (hreal a oa hoa hsideA), ← hpb (hreal b ob hob hsideB)]
      exact hpath
    · simpa only [OrderImpl.lay, hrank] using hlayer
  · intro index node hnode hdummy
    obtain ⟨original, horiginal, hd, hb, _⟩ := hlookup index node hnode
    rw [hb]
    exact hsource.2.2 index original horiginal (hd.symm.trans hdummy)

theorem clearProxyExtents_bordersWellFormed {source : Proper}
    (hsource : OrderImpl.BordersWellFormed source) :
    OrderImpl.BordersWellFormed (clearProxyExtents source) := by
  apply bordersWellFormed_of_key_transport hsource
  · unfold clearProxyExtents
    rfl
  · intro index node hnode
    rw [clearProxyExtents_nodes, List.getElem?_map] at hnode
    obtain ⟨original, horiginal, heq⟩ := Option.map_eq_some_iff.mp hnode
    have hk := clearF_keys original
    rw [heq] at hk
    exact ⟨original, horiginal, hk.1, hk.2.1, fun _ => hk.2.2.1⟩

theorem materializeDummyPaths_bordersWellFormed {source : Proper}
    (hsource : OrderImpl.BordersWellFormed source) :
    OrderImpl.BordersWellFormed (materializeDummyPaths source) := by
  apply bordersWellFormed_of_key_transport hsource
  · unfold materializeDummyPaths
    rfl
  · intro index node hnode
    obtain ⟨original, horiginal, hd, hb, _, heq⟩ := materialize_lookup source hnode
    exact ⟨original, horiginal, hd, hb, fun hreal =>
      congrArg (fun value : ProperNode => value.node.clusterPath) (heq hreal)⟩

theorem componentRun_coordinate_bordersWellFormed {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨labeled, hc, hready⟩ := componentRun_titled_border_ready hgraph hcomp hrun
  rw [← hc]
  unfold coordinateGraph
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready

theorem addClusterBorders_node_origin (source : Proper) (width : Int) :
    ∀ node ∈ (OrderImpl.addClusterBorders source width).nodes,
      node ∈ source.nodes ∨
      ∃ top ∈ source.nodes.zipIdx.filter (fun entry => entry.1.node.border == -2),
        ∃ bottom : ProperNode × Nat,
          (source.nodes.zipIdx.find? fun entry =>
            entry.1.node.border == 2 &&
              entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
          node.node.clusterPath = top.1.node.clusterPath := by
  let anchors := source.nodes.zipIdx.filter fun entry => entry.1.node.border == -2
  let evidence := fun emitted : ProperNode =>
    ∃ top ∈ anchors, ∃ bottom : ProperNode × Nat,
      (source.nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      emitted.node.clusterPath = top.1.node.clusterPath
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
          · exact Or.inr ⟨top, htop, bottom, hbottom, rfl⟩
          · exact Or.inr ⟨top, htop, bottom, hbottom, rfl⟩

theorem addClusterBorders_side_source (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {node : ProperNode} (hnode : node ∈ (OrderImpl.addClusterBorders source width).nodes)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ source.nodes.zipIdx.filter (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        (source.nodes.zipIdx.find? fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath := by
  rcases addClusterBorders_node_origin source width node hnode with horiginal | hemitted
  · have hnot := hready.1 node horiginal
    rcases hside with hside | hside
    · exact (hnot.1 hside).elim
    · exact (hnot.2 hside).elim
  · exact hemitted

theorem proxySpan_side_source {p : Proper} {xs : List Int} {owner index : Nat}
    {span : FramePorts.Span} (h : proxySpan p xs owner index = .ok span) :
    ∃ (sideIndex : Nat) (side : ProperNode), p.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      rk p.rank sideIndex = rk p.rank index := by
  let selected := p.nodes.zipIdx.filter fun entry =>
    (entry.1.node.border == -1 || entry.1.node.border == 1) &&
      entry.1.node.clusterPath.getLast? == some owner &&
      rk p.rank entry.2 == rk p.rank index
  have hnonempty : selected ≠ [] := by
    intro hempty
    unfold proxySpan at h
    split at h
    · cases h
    · rw [show (p.nodes.zipIdx.filter fun entry =>
          (entry.1.node.border == -1 || entry.1.node.border == 1) &&
            entry.1.node.clusterPath.getLast? == some owner &&
            rk p.rank entry.2 == rk p.rank index) = [] from hempty] at h
      change Except.error LayoutError.domain = Except.ok span at h
      cases h
  cases hselected : selected with
  | nil => exact (hnonempty hselected).elim
  | cons entry rest =>
      have hentry : entry ∈ selected := by
        rw [hselected]
        exact List.mem_cons_self ..
      obtain ⟨hlookup, hcondition⟩ := List.mem_filter.mp hentry
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcondition
      exact ⟨entry.2, entry.1, List.mem_zipIdx_iff_getElem?.mp hlookup,
        hcondition.1.1, hcondition.1.2, hcondition.2⟩

theorem proxyWidths_proxy_span_source {p q : Proper} {xs ys : List Int}
    (h : proxyWidths p xs = .ok (q, ys)) {index : Nat} {node : ProperNode}
    (hnode : p.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan p xs owner index = .ok span := by
  unfold proxyWidths at h
  obtain ⟨updated, hupdated, _⟩ := bind_ok h
  obtain ⟨_, hrecords⟩ := mapM_getElem? _ _ _ hupdated
  obtain ⟨record, hrecord, _⟩ := hrecords index (node, index)
    (by simp only [List.getElem?_zipIdx, hnode, Option.map_some, Nat.zero_add])
  dsimp only at hrecord
  have hproxy : (node.node.border == -2 || node.node.border == 2) = true := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  simp only [hproxy, ↓reduceIte] at hrecord
  cases howner : node.node.clusterPath.getLast? with
  | none =>
      simp only [howner] at hrecord
      change Except.error LayoutError.domain = Except.ok record at hrecord
      cases hrecord
  | some owner =>
      simp only [howner] at hrecord
      obtain ⟨span, hspan, _⟩ := bind_ok hrecord
      exact ⟨owner, span, rfl, hspan⟩

theorem componentRun_proxy_side_source {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner sideIndex : Nat) (side : ProperNode),
      node.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRun_spec h
  obtain ⟨owner, span, howner, hspan⟩ :=
    proxyWidths_proxy_span_source hproxy hnode hborder
  obtain ⟨sideIndex, side, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    proxySpan_side_source hspan
  exact ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩

theorem coordinateGraph_side_original {P : Params} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P source)))
    {index : Nat} {side : ProperNode}
    (hside : (coordinateGraph P source).nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P source))
      P.clusterBorderW).nodes[index]? = some side := by
  have hwf : OrderImpl.BordersWellFormed (coordinateGraph P source) := by
    unfold coordinateGraph
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed
        (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
        have hz := hwf.2.2 index side hside hd
        rcases hborder with hborder | hborder <;> omega
  obtain ⟨cleared, hcleared, hd, _, _, heq⟩ :=
    materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P source)) P.clusterBorderW)) hside
  have hclearedReal : cleared.dummy = false := hd.symm.trans hreal
  have hsame : side = cleared := heq hclearedReal
  have hclearLookup : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P source)) P.clusterBorderW)).nodes[index]? =
        some side := by
    rw [hsame]
    exact hcleared
  rw [clearProxyExtents_nodes, List.getElem?_map] at hclearLookup
  obtain ⟨original, horiginal, hclearEq⟩ := Option.map_eq_some_iff.mp hclearLookup
  have hb : side.node.border = original.node.border := by
    rw [← hclearEq]
    exact (clearF_keys original).2.1
  have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
    rwa [hb] at hborder
  have hclearId : clearF original = original := by
    unfold clearF
    rcases hoside with hoside | hoside <;> simp [hoside]
  exact horiginal.trans (congrArg some (hclearId.symm.trans hclearEq))

theorem componentRun_coordinate_side_source {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    ∃ (labeled : Proper) (top bottom : ProperNode × Nat),
      coordinateGraph P labeled = run.coordinateProper ∧
      top ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2) ∧
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      side.node.clusterPath = top.1.node.clusterPath := by
  obtain ⟨labeled, hc, hready⟩ := componentRun_titled_border_ready hgraph hcomp hrun
  have hcoordinate : (coordinateGraph P labeled).nodes[index]? = some side := by
    rw [hc]
    exact hside
  have horiginal := coordinateGraph_side_original hready hcoordinate hborder
  obtain ⟨top, htop, bottom, hbottom, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal) hborder
  exact ⟨labeled, top, bottom, hc, htop, hbottom, hpath⟩

theorem componentRun_proxy_bottom_source {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index : Nat} {proxy : ProperNode}
    (hproxy : run.coordinateProper.nodes[index]? = some proxy)
    (hborder : proxy.node.border = -2 ∨ proxy.node.border = 2) :
    ∃ (labeled : Proper) (owner sideIndex : Nat) (side : ProperNode)
      (top bottom : ProperNode × Nat),
      coordinateGraph P labeled = run.coordinateProper ∧
      proxy.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index ∧
      top ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2) ∧
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      side.node.clusterPath = top.1.node.clusterPath ∧
      top.1.node.clusterPath.getLast? = some owner := by
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    componentRun_proxy_side_source hrun hproxy hborder
  obtain ⟨labeled, top, bottom, hc, htop, hbottom, hpath⟩ :=
    componentRun_coordinate_side_source hgraph hcomp hrun hside hsideBorder
  refine ⟨labeled, owner, sideIndex, side, top, bottom, hc, howner, hside,
    hsideBorder, hsideRank, htop, hbottom, hpath, ?_⟩
  rw [← hpath]
  exact hsideOwner

theorem titled_marker_record {P : Params} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    (titleReservations (sizeProperPorts P source)).nodes[index]? = some (titleF node) := by
  have hnonplain : node.node.border ≠ 0 := by
    rcases hborder with hborder | hborder <;> omega
  have hsized : (sizeProperPorts P source).nodes[index]? = some node := by
    unfold sizeProperPorts
    simp only [List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some,
      Nat.zero_add]
    simp [hnonplain]
  rw [titleReservations_nodes, List.getElem?_append_left (by
    simp only [List.length_map, sizeProperPorts_length]
    exact (List.getElem?_eq_some_iff.mp hnode).1)]
  simp only [List.getElem?_map, hsized, Option.map_some]

theorem titled_marker_source_record {cg : Graph} {P : Params} {source : Proper}
    (hkeys : NodeKeys cg source)
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {index : Nat} {marker : ProperNode}
    (hmarker : (titleReservations (sizeProperPorts P source)).nodes[index]? = some marker)
    (hborder : marker.node.border = -2 ∨ marker.node.border = 2) :
    ∃ original : Node, cg.nodes[index]? = some original ∧
      marker.node.border = original.border ∧
      marker = titleF ⟨original, false, none, false⟩ := by
  rcases titled_node_origin hkeys hmarker with
    ⟨before, hbefore, _, hb, _⟩ | ⟨_, hb⟩
  · rcases hkeys index before hbefore with
      ⟨original, horiginal, _, hsourceBorder, _⟩ | ⟨_, hplain, _⟩
    · have hborderOriginal : original.border = -2 ∨ original.border = 2 := by
        rcases hborder with hborder | hborder <;> omega
      have hforward := titled_marker_record (P := P) (hrecords index original horiginal)
        hborderOriginal
      exact ⟨original, horiginal, hb.trans hsourceBorder,
        Option.some.inj (hmarker.symm.trans hforward)⟩
    · rcases hborder with hborder | hborder <;> omega
  · rcases hborder with hborder | hborder <;> omega

theorem componentCandidate_group_path_iff_decl {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate firstIndex secondIndex : Nat} {first second : Node}
    (hfirst : (componentCandidate graph comp candidate).nodes[firstIndex]? = some first)
    (hsecond : (componentCandidate graph comp candidate).nodes[secondIndex]? = some second)
    (hfirstBorder : first.border = -2) (hsecondBorder : second.border = -2) :
    first.clusterPath = second.clusterPath ↔ first.decl = second.decl := by
  obtain ⟨_, _, hfirstSource⟩ := componentCandidate_nonplain_source hfirst (by omega)
  obtain ⟨_, _, hsecondSource⟩ := componentCandidate_nonplain_source hsecond (by omega)
  obtain ⟨_, firstBox, hfirstBox, _, hfirstPath⟩ :=
    measuredGraph_group_origin hgraph hfirstSource hfirstBorder
  obtain ⟨_, secondBox, hsecondBox, _, hsecondPath⟩ :=
    measuredGraph_group_origin hgraph hsecondSource hsecondBorder
  constructor
  · intro hp
    have hlast := congrArg List.getLast? hp
    simpa [hfirstPath, hsecondPath] using hlast
  · intro hd
    rw [hd] at hfirstBox hfirstPath
    have hbox : firstBox = secondBox := Option.some.inj (hfirstBox.symm.trans hsecondBox)
    rw [hfirstPath, hsecondPath, hbox]

theorem componentRun_prepared_titled_source {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P labeled)) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := componentRun_ranked_source hrun
  have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (measuredGraph_shape hgraph) candidate
  have hready := titled_border_ready (P := P) hk hshape
    (fun _ _ hnode => componentCandidate_marker_shape hgraph hnode) haligned
  refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_⟩
  · intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  · intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank

theorem titled_group_owner_unique {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {source : Proper}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) source)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        source.nodes[index]? = some ⟨node, false, none, false⟩)
    {a b : Nat} {first second : ProperNode}
    (hfirst : (titleReservations (sizeProperPorts P source)).nodes[a]? = some first)
    (hsecond : (titleReservations (sizeProperPorts P source)).nodes[b]? = some second)
    (hfirstBorder : first.node.border = -2) (hsecondBorder : second.node.border = -2)
    (howner : first.node.clusterPath.getLast? = second.node.clusterPath.getLast?) :
    a = b := by
  obtain ⟨oa, hoa, hba, hea⟩ :=
    titled_marker_source_record hkeys hrecords hfirst (Or.inl hfirstBorder)
  obtain ⟨ob, hob, hbb, heb⟩ :=
    titled_marker_source_record hkeys hrecords hsecond (Or.inl hsecondBorder)
  have hgroupA : oa.border = -2 := hba.symm.trans hfirstBorder
  have hgroupB : ob.border = -2 := hbb.symm.trans hsecondBorder
  obtain ⟨_, _, hoaSource⟩ := componentCandidate_nonplain_source hoa (by omega)
  obtain ⟨_, _, hobSource⟩ := componentCandidate_nonplain_source hob (by omega)
  obtain ⟨_, boxA, _, _, hpathA⟩ := measuredGraph_group_origin hgraph hoaSource hgroupA
  obtain ⟨_, boxB, _, _, hpathB⟩ := measuredGraph_group_origin hgraph hobSource hgroupB
  have hlastA : first.node.clusterPath.getLast? = some oa.decl := by
    rw [hea]
    simp [titleF, hgroupA, hpathA]
  have hlastB : second.node.clusterPath.getLast? = some ob.decl := by
    rw [heb]
    simp [titleF, hgroupB, hpathB]
  have hdecl : oa.decl = ob.decl := by
    rw [hlastA, hlastB] at howner
    exact Option.some.inj howner
  have hpath := (componentCandidate_group_path_iff_decl hgraph hoa hob hgroupA hgroupB).mpr hdecl
  exact (componentCandidate_shape (components_nodup graph comp hcomp)
    (measuredGraph_shape hgraph) candidate).1 a b oa ob hoa hob hgroupA hgroupB hpath

theorem coordinateGraph_marker_record {P : Params} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2)
    (hdummy : node.dummy = false) :
    (coordinateGraph P source).nodes[index]? = some (clearF (titleF node)) := by
  have htitled := titled_marker_record (P := P) hnode hborder
  obtain ⟨extra, hextension, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P source)) P.clusterBorderW
  have hbordered : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P source)) P.clusterBorderW).nodes[index]? =
        some (titleF node) := by
    rw [hextension, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitled).1]
    exact htitled
  have hcleared : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P source)) P.clusterBorderW)).nodes[index]? =
        some (clearF (titleF node)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hbordered]
    rfl
  have hreal : (clearF (titleF node)).dummy = false :=
    (clearF_keys _).1.trans ((titleF_keys node).1.trans hdummy)
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hcleared, Option.map_some,
    Nat.zero_add, hreal, Bool.false_eq_true, ↓reduceIte]

theorem componentRun_prepared_group_bottom {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {labeled : Proper}
    (hc : coordinateGraph P labeled = run.coordinateProper)
    (hk : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ bottom : ProperNode × Nat,
      (titleReservations (sizeProperPorts P labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have hrequested : (titleReservations (sizeProperPorts P labeled)).nodes[index]? =
      some requested := titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have hrequestedBorder : requested.node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans hrequestedBorder
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    componentRun_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hsideCoordinate : (coordinateGraph P labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsideOriginal := coordinateGraph_side_original hready hsideCoordinate hsideBorder
  obtain ⟨anchor, hanchor, bottom, hbottom, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsideOriginal) hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? = requested.node.clusterPath.getLast? := by
    rw [← hpath, ← (clearF_keys requested).2.2.1]
    exact hsideOwner.trans howner.symm
  have hindex := titled_group_owner_unique hgraph hcomp hk hrecords
    hanchorLookup hrequested hanchorBorder hrequestedBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPorts P labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact hrequested
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  refine ⟨bottom, hrequested, ?_⟩
  rw [hanchorEq] at hbottom
  simpa only [requested, titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] using hbottom

theorem componentRun_group_bottom_source {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPorts P labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  obtain ⟨bottom, htitled, hbottom⟩ :=
    componentRun_prepared_group_bottom hgraph hcomp hrun hc hk hready hrecords hnode hgroup
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩

theorem titled_bottom_find_source {cg : Graph} {P : Params} {source : Proper}
    (hkeys : NodeKeys cg source)
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {path : List Nat} {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPorts P source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 && entry.1.node.clusterPath == path) =
        some bottom) :
    ∃ original : Node, cg.nodes[bottom.2]? = some original ∧
      original.border = 2 ∧ original.clusterPath = path ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      (cg.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.clusterPath == path) = some (original, bottom.2) := by
  have hbottomLookup := List.mem_zipIdx_iff_getElem?.mp
    (List.mem_of_find?_eq_some hfind)
  have hpredicate := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpredicate
  obtain ⟨original, horiginal, hborder, hrecord⟩ :=
    titled_marker_source_record hkeys hrecords hbottomLookup (Or.inr hpredicate.1)
  have horiginalBorder : original.border = 2 := hborder.symm.trans hpredicate.1
  have horiginalPath : original.clusterPath = path := by
    simpa [hrecord, titleF, horiginalBorder] using hpredicate.2
  refine ⟨original, horiginal, horiginalBorder, horiginalPath, hrecord, ?_⟩
  obtain ⟨_, position, hposition, hpositionRecord, hbefore⟩ :=
    List.find?_eq_some_iff_getElem.mp hfind
  have hpositionIndex : position = bottom.2 := by
    simpa only [List.getElem_zipIdx, Nat.zero_add] using
      congrArg Prod.snd hpositionRecord
  have hsourceZip : cg.nodes.zipIdx[bottom.2]? = some (original, bottom.2) := by
    simp only [List.getElem?_zipIdx, horiginal, Option.map_some, Nat.zero_add]
  obtain ⟨hsourceBound, hsourceRecord⟩ := List.getElem?_eq_some_iff.mp hsourceZip
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp [horiginalBorder, horiginalPath], bottom.2, hsourceBound,
    hsourceRecord, ?_⟩
  intro earlier hearlier
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  apply Bool.eq_false_iff.mpr
  intro hmatch
  have hearlierSource : earlier < cg.nodes.length := by
    simp only [List.length_zipIdx] at hsourceBound
    omega
  let previous := cg.nodes[earlier]'hearlierSource
  have hprevious : cg.nodes[earlier]? = some previous :=
    List.getElem?_eq_getElem hearlierSource
  have hpreviousMatch : previous.border = 2 ∧ previous.clusterPath = path := by
    simpa only [List.getElem_zipIdx, Nat.zero_add, Bool.and_eq_true, beq_iff_eq] using hmatch
  have hforward := titled_marker_record (P := P)
    (hrecords earlier previous hprevious) (Or.inr hpreviousMatch.1)
  have hprior := hbefore earlier (by omega)
  have htargetZip :
      (titleReservations (sizeProperPorts P source)).nodes.zipIdx[earlier]? =
        some (titleF ⟨previous, false, none, false⟩, earlier) := by
    simp only [List.getElem?_zipIdx, hforward, Option.map_some, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.mp htargetZip).2] at hprior
  simp [titleF, hpreviousMatch.1, hpreviousMatch.2] at hprior

theorem candidate_titled_bottom_constraint_source {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {source : Proper} {node : Node}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) source)
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate graph comp candidate).nodes[key]? = some original →
        source.nodes[key]? = some ⟨original, false, none, false⟩)
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPorts P source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
        some bottom) :
    ∃ original : Node,
      (componentCandidate graph comp candidate).nodes[bottom.2]? = some original ∧
      original.border = 2 ∧ original.clusterPath = node.clusterPath ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == node.decl) = some (original, bottom.2) := by
  obtain ⟨original, horiginal, hborder, hpath, hrecord, hsourceFind⟩ :=
    titled_bottom_find_source hkeys hrecords hfind
  refine ⟨original, horiginal, hborder, hpath, hrecord, ?_⟩
  rw [← componentCandidate_bottom_lookup_keys hgraph hnode hgroup]
  exact hsourceFind

theorem minRank_le_member {ranks : List Int} {rank : Int} (hmem : rank ∈ ranks) :
    RankImpl.minRank ranks ≤ rank := by
  have hfold : ∀ (values : List Int) (initial : Int),
      values.foldl min initial ≤ initial ∧
        ∀ value ∈ values, values.foldl min initial ≤ value := by
    intro values
    induction values with
    | nil => intro initial; exact ⟨Int.le_refl _, by simp⟩
    | cons head rest ih =>
        intro initial
        obtain ⟨hstart, hrest⟩ := ih (min initial head)
        refine ⟨Int.le_trans hstart (Int.min_le_left _ _), ?_⟩
        intro value hvalue
        rcases List.mem_cons.mp hvalue with rfl | hvalue
        · exact Int.le_trans hstart (Int.min_le_right _ _)
        · exact hrest value hvalue
  cases ranks with
  | nil => cases hmem
  | cons head rest =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact (hfold rest rank).1
      · exact (hfold rest head).2 rank hmem

theorem normalizedRanks_nonneg {before after : List Int}
    (h : RankImpl.normalizedRanks before = .ok after) :
    ∀ rank ∈ after, 0 ≤ rank := by
  unfold RankImpl.normalizedRanks at h
  split at h
  · cases h
    intro rank hrank
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hrank
    have hmin := minRank_le_member horiginal
    omega
  · cases h

theorem rankWithBudget_nonneg {graph : Graph} {rr : RankImpl.RankResult}
    (h : rankWithBudget graph = .ok rr) :
    ∀ rank ∈ rr.ranks, 0 ≤ rank := by
  unfold RankImpl.rankWithBudget at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · next before exhausted hsimplex =>
        split at h
        · cases h
        · next after hnormalized =>
          have heq := Except.ok.inj h
          subst rr
          exact normalizedRanks_nonneg hnormalized

theorem rankWithBudget_rk_nonneg {graph : Graph} {rr : RankImpl.RankResult}
    (h : rankWithBudget graph = .ok rr) (index : Nat) :
    0 ≤ rk rr.ranks index := by
  cases hindex : rr.ranks[index]? with
  | none => simp only [rk, List.getD_eq_getElem?_getD, hindex, Option.getD_none]; omega
  | some rank =>
      have hn := rankWithBudget_nonneg h rank (List.mem_of_getElem? hindex)
      simpa only [rk, List.getD_eq_getElem?_getD, hindex, Option.getD_some] using hn

theorem titled_rank_prefix (P : Params) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPorts P source)).rank = source.rank ++ extra := by
  unfold titleReservations sizeProperPorts
  exact ⟨_, rfl⟩

theorem titled_rank_record {P : Params} {source : Proper} {index : Nat} {rank : Int}
    (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPorts P source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := titled_rank_prefix P source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem prepared_titled_original_rk {P : Params} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPorts P source)).rank index = rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPorts P source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := titled_rank_record (P := P)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPorts P source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index

theorem coordinateGraph_rank_record {P : Params} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (coordinateGraph P source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := (coordinateGraph_anchor_prefix P source).2
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem prepared_coordinate_original_rk {P : Params} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (coordinateGraph P source).rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hcoordinateLookup := coordinateGraph_rank_record (P := P)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

theorem componentRun_group_member_borders {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate graph comp candidate).nodes[memberIndex]? = some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index) P.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index) P.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank memberIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank memberIndex := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    componentRun_group_bottom_source hgraph hcomp hrun hnode hgroup
  obtain ⟨originalBottom, horiginalBottom, _, _, _, hconstraintBottom⟩ :=
    candidate_titled_bottom_constraint_source hgraph hk hrecords hnode hgroup hbottom
  have hinterval := ranked_compound_member_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hgroup hconstraintBottom
    (List.mk_mem_zipIdx_iff_getElem?.mpr hmember) hplain hinside
  have htopRank := prepared_titled_original_rk (P := P) hrr hranks
    (List.getElem?_eq_some_iff.mp hnode).1
  have hmemberRank := prepared_titled_original_rk (P := P) hrr hranks
    (List.getElem?_eq_some_iff.mp hmember).1
  have hbottomRank := prepared_titled_original_rk (P := P) hrr hranks
    (List.getElem?_eq_some_iff.mp horiginalBottom).1
  have hnonnegative := rankWithBudget_rk_nonneg hrr memberIndex
  have htopBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hbottomForTop :
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨node, false, none, false⟩).node.clusterPath) =
        some bottom := by
    simpa [titleF, hgroup] using hbottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    coordinateGraph_rank_pair P labeled hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) htopBorder hbottomForTop
      (rank := (rk rr.ranks memberIndex).toNat)
      (by
        dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢
        omega)
      (by
        dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢
        omega)
  have hmemberCoordinate := prepared_coordinate_original_rk (P := P) hrr hranks
    (List.getElem?_eq_some_iff.mp hmember).1
  have hnatcast : ((rk rr.ranks memberIndex).toNat : Int) = rk rr.ranks memberIndex := by
    omega
  have hleftValue : rk (coordinateGraph P labeled).rank left = rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraph P labeled).rank right = rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [← hc]
  exact ⟨left, right, hleft, hright, hleftValue.trans hmemberCoordinate.symm,
    hrightValue.trans hmemberCoordinate.symm⟩

theorem titled_copy_rank_record {P : Params} {source : Proper}
    (haligned : source.nodes.length = source.rank.length)
    {position : Nat} {entry : ProperNode × Nat}
    (hentry : (titleNodes (sizeProperPorts P source))[position]? = some entry) :
    (titleReservations (sizeProperPorts P source)).rank[source.nodes.length + position]? =
      some (rk source.rank entry.2) := by
  have hrank : (titleReservations (sizeProperPorts P source)).rank =
      source.rank ++ (titleNodes (sizeProperPorts P source)).map
        (fun value => rk source.rank value.2) := by
    unfold titleReservations titleNodes sizeProperPorts
    rfl
  rw [hrank, List.getElem?_append_right (by omega)]
  have hindex : source.nodes.length + position - source.rank.length = position := by omega
  rw [hindex, List.getElem?_map, hentry]
  rfl

theorem coordinateGraph_titled_rank_record {P : Params} {source : Proper}
    {index : Nat} {rank : Int}
    (h : (titleReservations (sizeProperPorts P source)).rank[index]? = some rank) :
    (coordinateGraph P source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPorts P source)) P.clusterBorderW
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPorts P source)) P.clusterBorderW).rank[index]? = some rank
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem coordinateGraph_title_rank_source {cg : Graph} {P : Params} {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (haligned : source.nodes.length = source.rank.length)
    {titleIndex : Nat} {title : ProperNode}
    (htitle : (coordinateGraph P source).nodes[titleIndex]? = some title)
    (hborder : title.node.border = 3) :
    ∃ (originalIndex : Nat) (original : ProperNode),
      source.nodes[originalIndex]? = some original ∧
      original.node.border = -2 ∧ original.dummy = false ∧
      title.dummy = false ∧ title.node.clusterPath = original.node.clusterPath ∧
      rk (coordinateGraph P source).rank titleIndex = rk source.rank originalIndex := by
  rcases coordinateGraph_lookup P source htitle with
    ⟨original, horiginal, _, hb, _, _⟩ | ⟨_, hside⟩ |
      ⟨position, entry, hentry, hindex, hd, _, hp⟩
  · rcases hkeys titleIndex original horiginal with
      ⟨before, hbefore, _, hbeforeBorder, _⟩ | ⟨_, hplain, _⟩
    · have hnot := hshape.2 before (List.mem_of_getElem? hbefore)
      exact (hnot (hbeforeBorder.symm.trans (hb.symm.trans hborder))).elim
    · omega
  · rcases hside with hside | hside <;> omega
  · obtain ⟨hsized, hsizedBorder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hsourceDummy, hsourceBorder, hsourcePath⟩ :=
      sizeProperPorts_node_origin P source hsized
    have hsourceGroup : original.node.border = -2 := hsourceBorder.symm.trans hsizedBorder
    have horiginalReal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · omega
    have hentryReal : entry.1.dummy = false := hsourceDummy.trans horiginalReal
    have htitleReal : title.dummy = false := hd.trans hentryReal
    have htitlePath : title.node.clusterPath = original.node.clusterPath :=
      (hp hentryReal).trans hsourcePath
    have htitledRank := titled_copy_rank_record haligned hentry
    have hcoordinateRank := coordinateGraph_titled_rank_record htitledRank
    refine ⟨entry.2, original, horiginal, hsourceGroup, horiginalReal,
      htitleReal, htitlePath, ?_⟩
    rw [hindex]
    simp only [rk, List.getD_eq_getElem?_getD, hcoordinateRank, Option.getD_some]

theorem addClusterBorders_side_range_source (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {node : ProperNode} (hnode : node ∈ (OrderImpl.addClusterBorders source width).nodes)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ source.nodes.zipIdx.filter (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        (source.nodes.zipIdx.find? fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath ∧
        (rk source.rank top.2).toNat ≤ (rk source.rank bottom.2).toNat := by
  let anchors := source.nodes.zipIdx.filter fun entry => entry.1.node.border == -2
  let evidence := fun emitted : ProperNode =>
    ∃ top ∈ anchors, ∃ bottom : ProperNode × Nat,
      (source.nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      emitted.node.clusterPath = top.1.node.clusterPath ∧
      (rk source.rank top.2).toNat ≤ (rk source.rank bottom.2).toNat
  have hinvariant :
      ∀ emitted ∈ (OrderImpl.addClusterBorders source width).nodes,
        emitted ∈ source.nodes ∨ evidence emitted := by
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
        obtain ⟨bottom, hbottom, hbottomEq⟩ := Option.map_eq_some_iff.mp hbottomIndex
        apply OrderImpl.foldl_inv
          (fun state : Proper => ∀ emitted ∈ state.nodes,
            emitted ∈ source.nodes ∨ evidence emitted)
        · exact hcurrent
        · intro state hstate offset hoffset
          have hoffsetBound := List.mem_range.mp hoffset
          have hrange : (rk source.rank top.2).toNat ≤
              (rk source.rank bottom.2).toNat := by
            rw [hbottomEq]
            omega
          intro emitted he
          change emitted ∈ state.nodes ++
            [OrderImpl.borderLeft top width, OrderImpl.borderRight top width] at he
          rcases List.mem_append.mp he with hold | hnew
          · exact hstate emitted hold
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
            rcases hnew with rfl | rfl
            · exact Or.inr ⟨top, htop, bottom, hbottom, rfl, hrange⟩
            · exact Or.inr ⟨top, htop, bottom, hbottom, rfl, hrange⟩
  rcases hinvariant node hnode with horiginal | hemitted
  · have hnot := hready.1 node horiginal
    rcases hside with hside | hside
    · exact (hnot.1 hside).elim
    · exact (hnot.2 hside).elim
  · exact hemitted

theorem componentRun_requested_group_range {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {labeled : Proper}
    (hc : coordinateGraph P labeled = run.coordinateProper)
    (hk : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hbottom : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
        some bottom) :
    (rk (titleReservations (sizeProperPorts P labeled)).rank index).toNat ≤
      (rk (titleReservations (sizeProperPorts P labeled)).rank bottom.2).toNat := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have htitled : (titleReservations (sizeProperPorts P labeled)).nodes[index]? =
      some requested := titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have htitledBorder : requested.node.border = -2 := (titleF_keys _).2.1.trans hgroup
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans htitledBorder
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    componentRun_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hcoordinate : (coordinateGraph P labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsource := coordinateGraph_side_original hready hcoordinate hsideBorder
  obtain ⟨anchor, hanchor, generatedBottom, hfind, hpath, hrange⟩ :=
    addClusterBorders_side_range_source _ _ hready (List.mem_of_getElem? hsource) hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? = requested.node.clusterPath.getLast? := by
    rw [← hpath, ← (clearF_keys requested).2.2.1]
    exact hsideOwner.trans howner.symm
  have hindex := titled_group_owner_unique hgraph hcomp hk hrecords hanchorLookup
    htitled hanchorBorder htitledBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPorts P labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact htitled
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  rw [hanchorEq] at hfind
  have hfindForNode :
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some generatedBottom := by
    simpa only [requested, titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] using hfind
  have hbottomEq : generatedBottom = bottom := Option.some.inj (hfindForNode.symm.trans hbottom)
  rw [hindex, hbottomEq] at hrange
  exact hrange

theorem source_alignment_of_titled {P : Params} {source : Proper}
    (h : (titleReservations (sizeProperPorts P source)).nodes.length =
      (titleReservations (sizeProperPorts P source)).rank.length) :
    source.nodes.length = source.rank.length := by
  rw [titleReservations_nodes] at h
  simp only [List.length_append, List.length_map, sizeProperPorts_length] at h
  have hrank : (titleReservations (sizeProperPorts P source)).rank =
      source.rank ++ (titleNodes (sizeProperPorts P source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPorts
    rfl
  rw [hrank] at h
  simp only [List.length_append, List.length_map] at h
  omega

theorem componentRun_group_title_borders {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index titleIndex : Nat} {node : Node} {title : ProperNode}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (htitle : run.coordinateProper.nodes[titleIndex]? = some title)
    (htitleBorder : title.node.border = 3)
    (htitlePath : title.node.clusterPath = node.clusterPath) :
    title.dummy = false ∧ ∃ left right : Nat,
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index) P.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index) P.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank titleIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank titleIndex := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    componentRun_group_bottom_source hgraph hcomp hrun hnode hgroup
  have haligned := source_alignment_of_titled hready.2.2.2.1
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (measuredGraph_shape hgraph) candidate
  have htitleCoordinate : (coordinateGraph P labeled).nodes[titleIndex]? = some title := by
    rw [hc]
    exact htitle
  obtain ⟨originalIndex, original, horiginal, hOriginalBorder, _, htitleReal, hpath, htitleRank⟩ :=
    coordinateGraph_title_rank_source hk hshape haligned htitleCoordinate htitleBorder
  have hindex : originalIndex = index := labeled_topUnique hk hshape horiginal
    (hrecords index node hnode) hOriginalBorder hgroup (hpath.symm.trans htitlePath)
  have hsourceBound : index < labeled.rank.length := by
    have hn := (List.getElem?_eq_some_iff.mp (hrecords index node hnode)).1
    omega
  have hsourceRank : labeled.rank[index]? = some labeled.rank[index] :=
    List.getElem?_eq_getElem hsourceBound
  have htitledRank := titled_rank_record (P := P) hsourceRank
  have hsourceToTitled :
      rk labeled.rank index = rk (titleReservations (sizeProperPorts P labeled)).rank index := by
    simp only [rk, List.getD_eq_getElem?_getD, hsourceRank, htitledRank, Option.getD_some]
  have htitleToTitled :
      rk (coordinateGraph P labeled).rank titleIndex =
        rk (titleReservations (sizeProperPorts P labeled)).rank index := by
    rw [htitleRank, hindex]
    exact hsourceToTitled
  have htopRank := prepared_titled_original_rk (P := P) hrr hranks
    (List.getElem?_eq_some_iff.mp hnode).1
  have hrange := componentRun_requested_group_range hgraph hcomp hrun hc hk hready
    hrecords hnode hgroup hbottom
  have htopBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hbottomForTop :
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨node, false, none, false⟩).node.clusterPath) =
        some bottom := by
    simpa [titleF, hgroup] using hbottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    coordinateGraph_rank_pair P labeled hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) htopBorder hbottomForTop
      (rank := (rk (titleReservations (sizeProperPorts P labeled)).rank index).toNat)
      (by dsimp only; exact Nat.le_refl _) (by exact hrange)
  have hcast : ((rk (titleReservations (sizeProperPorts P labeled)).rank index).toNat : Int) =
      rk (titleReservations (sizeProperPorts P labeled)).rank index := by omega
  have hlvalue : rk (coordinateGraph P labeled).rank left =
      rk (titleReservations (sizeProperPorts P labeled)).rank index := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hcast
  have hrvalue : rk (coordinateGraph P labeled).rank right =
      rk (titleReservations (sizeProperPorts P labeled)).rank index := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hcast
  refine ⟨htitleReal, ?_⟩
  rw [← hc]
  exact ⟨left, right, hleft, hright, hlvalue.trans htitleToTitled.symm,
    hrvalue.trans htitleToTitled.symm⟩

theorem componentRun_group_title_bracket {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index titleIndex : Nat} {node : Node} {title : ProperNode}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (htitle : run.coordinateProper.nodes[titleIndex]? = some title)
    (htitleBorder : title.node.border = 3)
    (htitlePath : title.node.clusterPath = node.clusterPath) :
    ∃ (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers ∧
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index) P.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index) P.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left titleIndex right := by
  obtain ⟨htitleReal, left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    componentRun_group_title_borders hgraph hcomp hrun hnode hgroup htitle htitleBorder htitlePath
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ := componentRun_spec hrun
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper titleIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper titleIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hprefix :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        P.clusterBorderW).node.clusterPath <+: title.node.clusterPath := by
    refine ⟨[], ?_⟩
    simp only [List.append_nil]
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = title.node.clusterPath
    exact (titleF_keys _).2.2.1.trans htitlePath.symm
  refine ⟨ord, left, right, horder, hlayers, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.title_bracket run.coordinateProper orderOptions ord horder hwf
    left titleIndex right _ title _ hleft htitle hright hleftLay hrightLay
    rfl htitleBorder rfl rfl htitleReal rfl hprefix hprefix

theorem fixedSizes_path_index (inp : Input) {index : Nat} {box : ModelBox}
    (hbox : inp.boxes[index]? = some box) :
    let changeRole := fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source
    (inp.boxes.map changeRole).length = inp.boxes.length ∧
      (inp.boxes.map changeRole)[index]? = some (changeRole box) ∧
      Compound.path (inp.boxes.map changeRole) (changeRole box) =
        Compound.path inp.boxes box := by
  apply Compound.path_index_map
  · intro source _
    split <;> rfl
  · intro source _
    split <;> rfl
  · exact hbox

theorem prepare_plain_path_origin (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (source : Graph)
    (hmetadata : ∀ (key : Nat) (original : Node), source.nodes[key]? = some original →
      original.decl = key ∧ original.border = 0)
    {index : Nat} {node : Node} {box : ModelBox}
    (hnode : (Compound.prepare boxes pad titles source).nodes[index]? = some node)
    (hplain : node.border = 0) (hbox : boxes[index]? = some box) :
    node.decl = index ∧ node.clusterPath = Compound.path boxes box := by
  have hi : index < source.nodes.length := by
    by_cases hi : index < source.nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index boxes pad titles source index (by omega) hnode
      omega
  have hrole : box.role ≠ .group := by
    intro hgroup
    have hgroupRecord := Compound.prepare_group_title_record boxes pad titles source hi hbox hgroup
    have heq := Option.some.inj (hnode.symm.trans hgroupRecord)
    have hborder : node.border = -2 := congrArg Node.border heq
    omega
  have hmarked : (Compound.markNodes boxes pad titles source.nodes)[index]? =
      some { source.nodes[index] with clusterPath := Compound.path boxes box } := by
    rw [markNodes_eq, List.getElem?_append_left (by
      simp only [List.length_map, List.length_zipIdx]
      exact hi)]
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
      Option.map_some, Nat.zero_add]
    simp [markOne, hbox, hrole]
  have heq := Option.some.inj (hnode.symm.trans hmarked)
  have hsource := hmetadata index source.nodes[index] (List.getElem?_eq_getElem hi)
  rw [heq]
  exact ⟨hsource.1, rfl⟩

theorem SceneExecution.plain_node_path_source {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlineLength : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
  obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩

theorem SceneExecution.group_node_path_source {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box ++ [index] := by
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph_eq hnode hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, hdecl, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap, hdecl] at hpath
  exact hpath

theorem componentCandidate_nonempty_path_source {graph : Graph} {comp : List Nat}
    {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hpath : node.clusterPath ≠ []) :
    ∃ original, comp[index]? = some original ∧ graph.nodes[original]? = some node := by
  rw [componentCandidate_nodes] at hnode
  change (comp.map fun key => graph.nodes.getD key default)[index]? = some node at hnode
  cases hindex : comp[index]? with
  | none => simp [List.getElem?_map, hindex] at hnode
  | some original =>
      have hvalue : graph.nodes.getD original default = node := by
        simpa only [List.getElem?_map, hindex, Option.map_some, Option.some.injEq] using hnode
      cases horiginal : graph.nodes[original]? with
      | none =>
          have hdefault : (default : Node) = node := by
            simpa only [List.getD_eq_getElem?_getD, horiginal, Option.getD_none] using hvalue
          have hempty : node.clusterPath = [] := by
            rw [← hdefault]
            rfl
          exact (hpath hempty).elim
      | some source =>
          have heq : source = node := by
            simpa only [List.getD_eq_getElem?_getD, horiginal, Option.getD_some] using hvalue
          exact ⟨original, rfl, horiginal.trans (congrArg some heq)⟩

theorem SceneExecution.component_member_path_prefix {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    node.clusterPath <+: member.clusterPath := by
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  have hnonempty : member.clusterPath ≠ [] := by
    intro hempty
    simp [hempty] at hinside
  obtain ⟨_, _, hmemberSource⟩ := componentCandidate_nonempty_path_source hmember hnonempty
  obtain ⟨groupBox, hgroupBox, hgroupDecl, hgroupPath⟩ :=
    execution.group_node_path_source hgroupSource hgroup
  obtain ⟨memberBox, hmemberBox, _, hmemberPath⟩ :=
    execution.plain_node_path_source hmemberSource hplain
  have hin : node.decl ∈ Compound.path inp.boxes memberBox := by
    simpa only [hmemberPath, List.contains_iff_mem] using hinside
  rw [hgroupDecl] at hin
  have hprefix := Compound.path_ancestor_prefix (inputModel inp o) hwf
    hgroupBox hmemberBox hin
  rw [hgroupPath, hmemberPath]
  exact hprefix

theorem componentRun_original_plain_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = node.clusterPath ∧ actual.edge = none ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := componentRun_ranked_source hrun
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, hedge, hborder, hwidth, hheight⟩ :=
    coordinateGraph_plain_anchor_dims P hsource hplain
  have hmetadata : actual.dummy = false ∧ actual.node.clusterPath = node.clusterPath := by
    rcases coordinateGraph_lookup P labeled hactual with
      ⟨original, horiginal, hd, _, hp, _⟩ | ⟨_, hside⟩ |
        ⟨_, _, _, _, _, htitle, _⟩
    · have heq : original = ⟨node, false, none, false⟩ :=
        Option.some.inj (horiginal.symm.trans hsource)
      subst original
      exact ⟨hd, hp rfl⟩
    · rcases hside with hside | hside <;> omega
    · omega
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := componentRun_plain_node_dims hrun hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRun_spec hrun
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hmetadata.1, hborder, hmetadata.2,
    hedge, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

theorem SceneExecution.component_member_bracket {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers ∧
      run.coordinateProper.nodes[memberIndex]? = some actual ∧
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.xs.getD memberIndex 0 = run.coordinateXs.getD memberIndex 0 ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left memberIndex right := by
  have hprefix := execution.component_member_path_prefix hwf hnode hgroup hmember hplain hinside
  obtain ⟨actual, hcoordinate, hproper, hreal, hactualPlain, hactualPath,
    _, _, _, hx⟩ := componentRun_original_plain_record hrun hmember hplain
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    componentRun_group_member_borders execution.graph_eq hcomp hrun hnode hgroup
      hmember hplain hinside
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ := componentRun_spec hrun
  have hwformed := componentRun_coordinate_bordersWellFormed execution.graph_eq hcomp hrun
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath <+: actual.node.clusterPath := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath <+: actual.node.clusterPath
    rw [(titleF_keys _).2.2.1, hactualPath]
    exact hprefix
  have hleftNe : left ≠ memberIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (-1 : Int) = actual.node.border at hb
    omega
  have hrightNe : right ≠ memberIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (1 : Int) = actual.node.border at hb
    omega
  refine ⟨actual, ord, left, right, horder, hlayers, hcoordinate, hproper, hreal,
    hactualPlain, hactualPath, hx, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left memberIndex right _ actual _ hleft hcoordinate hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

theorem componentRun_cluster_separated {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∀ layer ∈ run.layers, ∀ i a b,
      layer[i]? = some a → layer[i + 1]? = some b →
      clusterSep P.nodeGap P.clusterPad run.coordinateProper a b ≤
        run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec h
  exact cluster_balance_separated hcross

theorem componentRun_cluster_gap_separated {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∀ layer ∈ run.layers, ∀ i a b,
      layer[i]? = some a → layer[i + 1]? = some b →
      clusterGap P.nodeGap P.clusterPad run.coordinateProper a b ≤
        run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec h
  obtain ⟨_, _, _, hs, _⟩ := crossCoordsClusterWith_spec hcross
  intro layer hl i a b ha hb
  have hsep := componentRun_cluster_separated h layer hl i a b ha hb
  have hwa := nodeW_nonneg hs a
  have hwb := nodeW_nonneg hs b
  unfold clusterSep coordSep at hsep
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide),
    Int.fdiv_eq_ediv_of_nonneg _ (by decide)] at hsep
  omega

theorem componentRun_border_member_gap {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i a b : Nat}
    (ha : layer[i]? = some a) (hb : layer[i + 1]? = some b)
    (hm : borderMember run.coordinateProper a b = true) :
    P.clusterPad ≤ run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  have hgap := componentRun_cluster_gap_separated h layer hl i a b ha hb
  simpa only [clusterGap, hm, ite_true] using hgap

theorem componentRun_two_border_member_gaps {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i a member b : Nat}
    (ha : layer[i]? = some a)
    (hm : layer[i + 1]? = some member)
    (hb : layer[(i + 1) + 1]? = some b)
    (ham : borderMember run.coordinateProper a member = true)
    (hmb : borderMember run.coordinateProper member b = true) :
    2 * P.clusterPad ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  have hleft := componentRun_border_member_gap h hl ha hm ham
  have hright := componentRun_border_member_gap h hl hm hb hmb
  omega

theorem componentRun_layer_step_nonnegative {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i a b : Nat}
    (ha : layer[i]? = some a) (hb : layer[i + 1]? = some b) :
    run.coordinateXs.getD a 0 ≤ run.coordinateXs.getD b 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec h
  obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
  have hgap := componentRun_cluster_gap_separated h layer hl i a b ha hb
  have hnonneg :
      0 ≤ clusterGap P.nodeGap P.clusterPad run.coordinateProper a b := by
    unfold clusterGap
    split
    · omega
    · split <;> omega
  omega

theorem componentRun_layer_ordered {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i j a b : Nat}
    (hij : i ≤ j) (ha : layer[i]? = some a) (hb : layer[j]? = some b) :
    run.coordinateXs.getD a 0 ≤ run.coordinateXs.getD b 0 := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction distance generalizing b with
  | zero =>
      simp only [Nat.add_zero] at hb
      have hab : a = b := Option.some.inj (ha.symm.trans hb)
      subst b
      exact Int.le_refl _
  | succ distance ih =>
      have hlast : i + distance + 1 < layer.length :=
        (List.getElem?_eq_some_iff.mp hb).1
      have hindex : i + distance < layer.length := by omega
      have hmiddle : layer[i + distance]? = some (layer[i + distance]'hindex) :=
        List.getElem?_eq_getElem hindex
      have hprefix := ih (by omega) hmiddle
      have hstep := componentRun_layer_step_nonnegative h hl hmiddle
        (show layer[(i + distance) + 1]? = some b from hb)
      exact Int.le_trans hprefix hstep

theorem componentRun_two_border_member_gaps_with_intervening
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers)
    {i j left first last right : Nat}
    (hij : i + 1 ≤ j)
    (hleft : layer[i]? = some left)
    (hfirst : layer[i + 1]? = some first)
    (hlast : layer[j]? = some last)
    (hright : layer[j + 1]? = some right)
    (hleftMember : borderMember run.coordinateProper left first = true)
    (hrightMember : borderMember run.coordinateProper last right = true) :
    2 * P.clusterPad ≤
      run.coordinateXs.getD right 0 - run.coordinateXs.getD left 0 := by
  have hleftGap := componentRun_border_member_gap h hl hleft hfirst hleftMember
  have hrightGap := componentRun_border_member_gap h hl hlast hright hrightMember
  have hmiddle := componentRun_layer_ordered h hl hij hfirst hlast
  omega

theorem componentRun_border_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _⟩ :=
    componentRun_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

theorem componentRun_border_hull_width_of_layer_configuration
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {group : Nat} (hgroup : (cg.nodes.getD group default).border = -2)
    {layer : List Nat} (hl : layer ∈ run.layers)
    {i j left first last right : Nat} {leftNode rightNode : ProperNode}
    (hij : i + 1 ≤ j)
    (hleft : layer[i]? = some left)
    (hfirst : layer[i + 1]? = some first)
    (hlast : layer[j]? = some last)
    (hright : layer[j + 1]? = some right)
    (hleftMember : borderMember run.coordinateProper left first = true)
    (hrightMember : borderMember run.coordinateProper last right = true)
    (hleftNode : run.coordinateProper.nodes[left]? = some leftNode)
    (hrightNode : run.coordinateProper.nodes[right]? = some rightNode)
    (hleftBorder : leftNode.node.border = -1)
    (hrightBorder : rightNode.node.border = 1)
    (hleftOwner : leftNode.node.clusterPath.getLast? =
      some (cg.nodes.getD group default).decl)
    (hrightOwner : rightNode.node.clusterPath.getLast? =
      some (cg.nodes.getD group default).decl) :
    2 * P.clusterPad ≤ (frameRect P cg run group).w := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec h
  obtain ⟨_, _, _, hs, _⟩ := crossCoordsClusterWith_spec hcross
  have hleftWidth : 0 ≤ leftNode.node.w :=
    (sizesNonneg_lookup hs left leftNode hleftNode).1
  have hrightWidth : 0 ≤ rightNode.node.w :=
    (sizesNonneg_lookup hs right rightNode hrightNode).1
  obtain ⟨hleftFinal, hleftX⟩ :=
    componentRun_border_record h hleftNode (Or.inl hleftBorder)
  obtain ⟨hrightFinal, hrightX⟩ :=
    componentRun_border_record h hrightNode (Or.inr hrightBorder)
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some (cg.nodes.getD group default).decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(leftNode, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal, ?_⟩
    simp [hleftBorder, hleftOwner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(rightNode, right), List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal, ?_⟩
    simp [hrightBorder, hrightOwner]
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hgap := componentRun_two_border_member_gaps_with_intervening h hl hij
    hleft hfirst hlast hright hleftMember hrightMember
  simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
    hleftFinal, hrightFinal, hleftX, hrightX] at hlo hhi
  have hleftHalf : 0 ≤ Int.fdiv leftNode.node.w 2 :=
    Int.fdiv_nonneg hleftWidth (by decide)
  have hrightHalf : Int.fdiv rightNode.node.w 2 ≤ rightNode.node.w := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  change (cg.nodes[group]?.getD default).border = -2 at hgroup
  have hwidth : (frameRect P cg run group).w =
      (boundsOf borders []).right - (boundsOf borders []).minX := by
    simp [frameRect, hgroup, borders]
  rw [hwidth]
  omega

theorem SceneExecution.component_member_border_interval {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (left right : Nat),
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.proper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x ≤
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
      (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
          (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
  obtain ⟨actual, ord, left, right, _, hlayers, hcoordinate, hproper, _, hactualPlain,
    hactualPath, hx, hleft, hright, hbracket⟩ :=
    execution.component_member_bracket hwf hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨labeled, hc, hk, _⟩ := componentRun_coordinate_source_alignment hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (measuredGraph_shape execution.graph_eq) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb) hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left memberIndex _ _ hlt hli hmi hleft hcoordinate
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri memberIndex right _ _ htr hmi hri hcoordinate hright
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ := componentRun_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ := componentRun_border_record hrun hright (Or.inr rfl)
  have hactualWidth := (sizesNonneg_lookup hsizes memberIndex actual hcoordinate).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
  have hactualLoops : 0 ≤ (actual.node.loopExtent : Int) := Int.natCast_nonneg _
  have hgroupLoops : 0 ≤ (node.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
  refine ⟨actual, left, right, hproper, hactualPath, hleftFinal, hrightFinal, ?_, ?_⟩
  · simp only [coordSep, CoordsImpl.nodeW, hleft, hcoordinate, OrderImpl.borderLeft] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hproper, hleftX, hx, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  · simp only [coordSep, CoordsImpl.nodeW, hcoordinate, hright, OrderImpl.borderRight,
      titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproper, hrightFinal, hx, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega

theorem SceneExecution.component_member_contained {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run index).Contained
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run memberIndex) := by
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨actual, left, right, hproper, hactualPath, hleft, hright, hleftInterval, hrightInterval⟩ :=
    execution.component_member_border_interval hwf hcomp hrun hnode hgroup hmember hplain hinside
  have hgroupGet : cg.nodes.getD index default = node := by
    simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframeGroup : (cg.nodes.getD index default).border = -2 := by
    rw [hgroupGet]
    exact hgroup
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨box, _, hdecl, hpath⟩ := execution.group_node_path_source hgroupSource hgroup
  have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    simpa only [hdecl] using hpath
  have hleftPath : (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hgroupGet]
    exact hgroupPath
  have hrightPath : (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := hleftPath
  have hleftContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
  have hscope : actual.node.clusterPath.contains (cg.nodes.getD index default).decl = true := by
    rw [hgroupGet, hactualPath]
    exact hinside
  have hvertical := frameRect_member_vertical (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hproper) hscope
  have hcontained : (frameRect execution.params cg run index).Contained
      (Labels.rectAt run.proper run.xs run.ys memberIndex) := by
    unfold Rect.Contained at hleftContained hrightContained ⊢
    exact ⟨Int.le_trans hleftContained.1 hleftInterval,
      Int.le_trans hrightInterval hrightContained.2.1, hvertical.1, hvertical.2⟩
  have hmemberGet : cg.nodes.getD memberIndex default = member := by
    simp only [cg, List.getD_eq_getElem?_getD, hmember, Option.getD_some]
  have hmemberFrame : frameRect execution.params cg run memberIndex =
      Labels.rectAt run.proper run.xs run.ys memberIndex := by
    unfold frameRect
    rw [hmemberGet]
    simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
    unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
      RouteImpl.nodeW RouteImpl.nodeH
    simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
  rw [hmemberFrame]
  exact hcontained

theorem compound_child_constraint_edges {graph : Graph}
    {parent parentBottom child childBottom : Node × Nat}
    (hparent : parent ∈ graph.nodes.zipIdx) (hparentGroup : parent.1.border = -2)
    (hparentBottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == parent.1.decl) = some parentBottom)
    (hchild : child ∈ graph.nodes.zipIdx) (hchildGroup : child.1.border = -2)
    (hpath : child.1.clusterPath.dropLast = parent.1.clusterPath)
    (hchildBottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == child.1.decl) = some childBottom) :
    (⟨parent.2, child.2, 1, 0, false⟩ : Edge) ∈ Compound.constraints graph ∧
      (⟨childBottom.2, parentBottom.2, 1, 0, false⟩ : Edge) ∈ Compound.constraints graph := by
  let children := (graph.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
    fun entry => entry.1.clusterPath.dropLast == parent.1.clusterPath
  have hchildren : child ∈ children :=
    List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hchild, by simp [hchildGroup]⟩,
      by simp [hpath]⟩
  have hnonempty : children.isEmpty = false := by
    cases hc : children with
    | nil => simp [hc] at hchildren
    | cons first rest => rfl
  have hpair : ∀ edge ∈ ([⟨parent.2, child.2, 1, 0, false⟩,
      ⟨childBottom.2, parentBottom.2, 1, 0, false⟩] : List Edge),
      edge ∈ Compound.constraints graph := by
    intro edge hedge
    unfold Compound.constraints
    apply List.mem_flatMap.mpr
    refine ⟨parent, List.mem_filter.mpr ⟨hparent, by simp [hparentGroup]⟩, ?_⟩
    rw [hparentBottom]
    dsimp only
    split
    · rename_i hempty
      have hc : children.isEmpty = true := (Bool.and_eq_true_iff.mp hempty).2
      rw [hnonempty] at hc
      cases hc
    · apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨child, hchildren, ?_⟩
      rw [hchildBottom]
      exact hedge
  exact ⟨hpair _ (by simp), hpair _ (by simp)⟩

theorem ranked_compound_child_interval {graph : Graph} {rr : RankImpl.RankResult}
    (hrank : rankWithBudget (Compound.rankingGraph graph) = .ok rr)
    {parent parentBottom child childBottom : Node × Nat}
    (hparent : parent ∈ graph.nodes.zipIdx) (hparentGroup : parent.1.border = -2)
    (hparentBottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == parent.1.decl) = some parentBottom)
    (hchild : child ∈ graph.nodes.zipIdx) (hchildGroup : child.1.border = -2)
    (hpath : child.1.clusterPath.dropLast = parent.1.clusterPath)
    (hchildBottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == child.1.decl) = some childBottom) :
    rk rr.ranks parent.2 + 1 ≤ rk rr.ranks child.2 ∧
      rk rr.ranks childBottom.2 + 1 ≤ rk rr.ranks parentBottom.2 := by
  obtain ⟨hleft, hright⟩ := compound_child_constraint_edges hparent hparentGroup
    hparentBottom hchild hchildGroup hpath hchildBottom
  have hleftRank := rankingGraph_constraint_feasible hrank hleft
  have hrightRank := rankingGraph_constraint_feasible hrank hright
  dsimp only at hleftRank hrightRank
  omega

theorem componentRun_direct_group_rank_interval {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    (hpath : child.clusterPath.dropLast = parent.clusterPath) :
    ∃ (rr : RankImpl.RankResult) (parentBottom childBottom : Node)
      (parentBottomIndex childBottomIndex : Nat),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      (componentCandidate graph comp candidate).nodes[parentBottomIndex]? = some parentBottom ∧
      (componentCandidate graph comp candidate).nodes[childBottomIndex]? = some childBottom ∧
      ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == parent.decl) = some (parentBottom, parentBottomIndex) ∧
      ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == child.decl) = some (childBottom, childBottomIndex) ∧
      rk rr.ranks parentIndex + 1 ≤ rk rr.ranks childIndex ∧
      rk rr.ranks childBottomIndex + 1 ≤ rk rr.ranks parentBottomIndex := by
  obtain ⟨rr, parentLabeled, parentMarker, hrr, _, parentKeys, _, parentRecords,
    _, _, parentFind⟩ := componentRun_group_bottom_source hgraph hcomp hrun hparent hparentGroup
  obtain ⟨parentBottom, hparentBottom, _, _, _, hparentFind⟩ :=
    candidate_titled_bottom_constraint_source hgraph parentKeys parentRecords
      hparent hparentGroup parentFind
  obtain ⟨_, childLabeled, childMarker, _, _, childKeys, _, childRecords,
    _, _, childFind⟩ := componentRun_group_bottom_source hgraph hcomp hrun hchild hchildGroup
  obtain ⟨childBottom, hchildBottom, _, _, _, hchildFind⟩ :=
    candidate_titled_bottom_constraint_source hgraph childKeys childRecords
      hchild hchildGroup childFind
  have hinterval := ranked_compound_child_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hparent) hparentGroup hparentFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr hchild) hchildGroup hpath hchildFind
  refine ⟨rr, parentBottom, childBottom, parentMarker.2, childMarker.2, hrr,
    hparentBottom, hchildBottom, hparentFind, hchildFind, ?_⟩
  exact hinterval

theorem addClusterBorders_side_rank_bounds (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ source.nodes.zipIdx.filter (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        (source.nodes.zipIdx.find? fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath ∧
        0 ≤ rk (OrderImpl.addClusterBorders source width).rank index ∧
        (rk source.rank top.2).toNat ≤
          (rk (OrderImpl.addClusterBorders source width).rank index).toNat ∧
        (rk (OrderImpl.addClusterBorders source width).rank index).toNat ≤
          (rk source.rank bottom.2).toNat := by
  let anchors := source.nodes.zipIdx.filter fun entry => entry.1.node.border == -2
  let evidence := fun emitted : ProperNode × Int =>
    ∃ top ∈ anchors, ∃ bottom : ProperNode × Nat,
      (source.nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      emitted.1.node.clusterPath = top.1.node.clusterPath ∧ 0 ≤ emitted.2 ∧
      (rk source.rank top.2).toNat ≤ emitted.2.toNat ∧
      emitted.2.toNat ≤ (rk source.rank bottom.2).toNat
  let invariant := fun current : Proper =>
    current.nodes.length = current.rank.length ∧
      ∀ emitted ∈ current.nodes.zip current.rank,
        emitted ∈ source.nodes.zip source.rank ∨ evidence emitted
  let output := OrderImpl.addClusterBorders source width
  change evidence (node, rk output.rank index)
  have hactual : invariant output := by
    change invariant (OrderImpl.addClusterBorders source width)
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv invariant
    · refine ⟨hready.2.2.2.1, ?_⟩
      intro emitted hemitted
      exact Or.inl hemitted
    · intro current hcurrent top htop
      unfold OrderImpl.borderStep
      split
      · exact hcurrent
      · rename_i bottomIndex hbottomIndex
        obtain ⟨bottom, hbottom, hbottomEq⟩ := Option.map_eq_some_iff.mp hbottomIndex
        apply OrderImpl.foldl_inv invariant
        · exact hcurrent
        · intro state hstate offset hoffset
          have hoffsetBound := List.mem_range.mp hoffset
          have hlo : (rk source.rank top.2).toNat ≤
              (((rk source.rank top.2).toNat + offset : Nat) : Int).toNat := by
            change (rk source.rank top.2).toNat ≤ (rk source.rank top.2).toNat + offset
            omega
          have hhi : (((rk source.rank top.2).toNat + offset : Nat) : Int).toNat ≤
              (rk source.rank bottom.2).toNat := by
            change (rk source.rank top.2).toNat + offset ≤ (rk source.rank bottom.2).toNat
            rw [hbottomEq]
            omega
          refine ⟨?_, ?_⟩
          · simp only [OrderImpl.borderInner, List.length_append, List.length_cons,
              List.length_nil]
            exact congrArg (fun count : Nat => count + 2) hstate.1
          · intro emitted hemitted
            change emitted ∈ (state.nodes ++ [OrderImpl.borderLeft top width,
              OrderImpl.borderRight top width]).zip (state.rank ++
                [(((rk source.rank top.2).toNat + offset : Nat) : Int),
                 (((rk source.rank top.2).toNat + offset : Nat) : Int)]) at hemitted
            rw [List.zip_append hstate.1] at hemitted
            rcases List.mem_append.mp hemitted with hold | hnew
            · exact hstate.2 emitted hold
            · change emitted ∈
                [(OrderImpl.borderLeft top width,
                    (((rk source.rank top.2).toNat + offset : Nat) : Int)),
                 (OrderImpl.borderRight top width,
                    (((rk source.rank top.2).toNat + offset : Nat) : Int))] at hnew
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
              rcases hnew with rfl | rfl
              · exact Or.inr ⟨top, htop, bottom, hbottom, rfl, Int.natCast_nonneg _, hlo, hhi⟩
              · exact Or.inr ⟨top, htop, bottom, hbottom, rfl, Int.natCast_nonneg _, hlo, hhi⟩
  have hbound : index < output.rank.length := by
    have hn := (List.getElem?_eq_some_iff.mp hnode).1
    change index < output.nodes.length at hn
    have haligned := hactual.1
    omega
  have hrank : output.rank[index]? = some output.rank[index] := List.getElem?_eq_getElem hbound
  have hzipped : (output.nodes.zip output.rank)[index]? = some (node, output.rank[index]) :=
    List.getElem?_zip_eq_some.mpr ⟨hnode, hrank⟩
  rcases hactual.2 (node, output.rank[index]) (List.mem_of_getElem? hzipped) with
    horiginal | hemitted
  · obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp horiginal
    have hsourceNode := (List.getElem?_zip_eq_some.mp hposition).1
    have hnot := hready.1 node (List.mem_of_getElem? hsourceNode)
    rcases hside with hside | hside
    · exact (hnot.1 hside).elim
    · exact (hnot.2 hside).elim
  · rw [RankImpl.rk_of_lt hbound]
    exact hemitted

theorem coordinateGraph_side_rank_bounds {P : Params} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P source)))
    {index : Nat} {node : ProperNode}
    (hnode : (coordinateGraph P source).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ (titleReservations (sizeProperPorts P source)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        ((titleReservations (sizeProperPorts P source)).nodes.zipIdx.find? fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath ∧
        0 ≤ rk (coordinateGraph P source).rank index ∧
        (rk (titleReservations (sizeProperPorts P source)).rank top.2).toNat ≤
          (rk (coordinateGraph P source).rank index).toNat ∧
        (rk (coordinateGraph P source).rank index).toNat ≤
          (rk (titleReservations (sizeProperPorts P source)).rank bottom.2).toNat := by
  have horiginal := coordinateGraph_side_original hready hnode hside
  exact addClusterBorders_side_rank_bounds _ _ hready horiginal hside

theorem SceneExecution.component_direct_group_path {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    child.clusterPath.dropLast = parent.clusterPath := by
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨_, _, hchildSource⟩ := componentCandidate_nonplain_source hchild (by omega)
  obtain ⟨parentOriginal, hparentOriginal, hparentDecl, hparentPath⟩ :=
    execution.group_node_path_source hparentSource hparentGroup
  obtain ⟨childOriginal, hchildOriginal, hchildDecl, hchildPath⟩ :=
    execution.group_node_path_source hchildSource hchildGroup
  rw [← hparentDecl] at hparentOriginal
  rw [← hchildDecl] at hchildOriginal
  have hparentEq : parentOriginal = parentBox :=
    Option.some.inj (hparentOriginal.symm.trans hparentBox)
  have hchildEq : childOriginal = childBox :=
    Option.some.inj (hchildOriginal.symm.trans hchildBox)
  rw [hparentEq, ← hparentDecl] at hparentPath
  rw [hchildEq, ← hchildDecl] at hchildPath
  have himmediate := Compound.path_of_parent (inputModel inp o) hwf
    hparentBox hchildBox hparentRef hne
  calc
    child.clusterPath.dropLast = Compound.path inp.boxes childBox := by
      rw [hchildPath, List.dropLast_concat]
    _ = Compound.path inp.boxes parentBox ++ [parent.decl] := himmediate
    _ = parent.clusterPath := hparentPath.symm

theorem SceneExecution.component_direct_group_rank_interval {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    ∃ (rr : RankImpl.RankResult) (parentBottom childBottom : Node)
      (parentBottomIndex childBottomIndex : Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      (componentCandidate execution.graph comp candidate).nodes[parentBottomIndex]? =
        some parentBottom ∧
      (componentCandidate execution.graph comp candidate).nodes[childBottomIndex]? =
        some childBottom ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == parent.decl) =
          some (parentBottom, parentBottomIndex) ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == child.decl) =
          some (childBottom, childBottomIndex) ∧
      rk rr.ranks parentIndex + 1 ≤ rk rr.ranks childIndex ∧
      rk rr.ranks childBottomIndex + 1 ≤ rk rr.ranks parentBottomIndex := by
  exact componentRun_direct_group_rank_interval execution.graph_eq hcomp hrun
    hparent hparentGroup hchild hchildGroup
    (execution.component_direct_group_path hwf hparent hparentGroup hchild hchildGroup
      hparentBox hchildBox hparentRef hne)

theorem SceneExecution.component_group_side_rank_bounds {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some node.decl) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraph execution.params labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady
        (titleReservations (sizeProperPorts execution.params labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPorts execution.params labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPorts execution.params labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) = some bottom ∧
      side.node.clusterPath = node.clusterPath ∧
      0 ≤ rk run.coordinateProper.rank sideIndex ∧
      (rk (titleReservations (sizeProperPorts execution.params labeled)).rank index).toNat ≤
        (rk run.coordinateProper.rank sideIndex).toNat ∧
      (rk run.coordinateProper.rank sideIndex).toNat ≤
        (rk (titleReservations (sizeProperPorts execution.params labeled)).rank bottom.2).toNat := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks,
    htitled, hbottom⟩ :=
    componentRun_group_bottom_source execution.graph_eq hcomp hrun hnode hgroup
  have hcoordinate : (coordinateGraph execution.params labeled).nodes[sideIndex]? =
      some side := by
    rw [hc]
    exact hside
  obtain ⟨anchor, hanchor, generatedBottom, hfind, hpath, hnonneg, hlo, hhi⟩ :=
    coordinateGraph_side_rank_bounds hready hcoordinate hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨box, _, hdecl, hgroupPath⟩ :=
    execution.group_node_path_source hgroupSource hgroup
  have hlast : node.clusterPath.getLast? = some node.decl := by
    simp [hgroupPath, hdecl]
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      (titleF ⟨node, false, none, false⟩).node.clusterPath.getLast? := by
    rw [← hpath, (titleF_keys _).2.2.1]
    exact howner.trans hlast.symm
  have htitledBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hindex := titled_group_owner_unique execution.graph_eq hcomp hk hrecords
    hanchorLookup htitled hanchorBorder htitledBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPorts execution.params labeled)).nodes[anchor.2]? =
        some (titleF ⟨node, false, none, false⟩) := by
    rw [hindex]
    exact htitled
  have hanchorEq : anchor.1 = titleF ⟨node, false, none, false⟩ :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  rw [hanchorEq, (titleF_keys _).2.2.1] at hfind hpath
  have hbottomEq : generatedBottom = bottom :=
    Option.some.inj (hfind.symm.trans hbottom)
  rw [hindex] at hlo
  rw [hbottomEq] at hhi
  rw [hc] at hnonneg hlo hhi
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks,
    htitled, hbottom, hpath, hnonneg, hlo, hhi⟩

theorem SceneExecution.component_child_side_parent_borders {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank sideIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank sideIndex := by
  obtain ⟨rr, labeled, childBottom, hrr, hc, hk, hready, hrecords, hranks,
    _, hchildBottom, _, hnonneg, hlo, hhi⟩ :=
    execution.component_group_side_rank_bounds hcomp hrun hchild hchildGroup
      hside hsideBorder howner
  obtain ⟨parentBottom, hparentTitled, hparentBottom⟩ :=
    componentRun_prepared_group_bottom execution.graph_eq hcomp hrun hc hk hready
      hrecords hparent hparentGroup
  obtain ⟨parentOriginalBottom, hparentOriginalBottom, _, _, _, hparentFind⟩ :=
    candidate_titled_bottom_constraint_source execution.graph_eq hk hrecords
      hparent hparentGroup hparentBottom
  obtain ⟨childOriginalBottom, hchildOriginalBottom, _, _, _, hchildFind⟩ :=
    candidate_titled_bottom_constraint_source execution.graph_eq hk hrecords
      hchild hchildGroup hchildBottom
  have hpath := execution.component_direct_group_path hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hinterval := ranked_compound_child_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hparent) hparentGroup hparentFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr hchild) hchildGroup hpath hchildFind
  have hparentRank := prepared_titled_original_rk (P := execution.params) hrr hranks
    (List.getElem?_eq_some_iff.mp hparent).1
  have hchildRank := prepared_titled_original_rk (P := execution.params) hrr hranks
    (List.getElem?_eq_some_iff.mp hchild).1
  have hparentBottomRank := prepared_titled_original_rk (P := execution.params) hrr hranks
    (List.getElem?_eq_some_iff.mp hparentOriginalBottom).1
  have hchildBottomRank := prepared_titled_original_rk (P := execution.params) hrr hranks
    (List.getElem?_eq_some_iff.mp hchildOriginalBottom).1
  have htopBorder : (titleF ⟨parent, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hparentGroup
  have hbottomForTop :
      ((titleReservations (sizeProperPorts execution.params labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨parent, false, none, false⟩).node.clusterPath) =
            some parentBottom := by
    simpa only [(titleF_keys _).2.2.1] using hparentBottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    coordinateGraph_rank_pair execution.params labeled hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr hparentTitled) htopBorder hbottomForTop
      (rank := (rk run.coordinateProper.rank sideIndex).toNat)
      (by
        dsimp only at hinterval hparentRank hchildRank hparentBottomRank hchildBottomRank ⊢
        omega)
      (by
        dsimp only at hinterval hparentRank hchildRank hparentBottomRank hchildBottomRank ⊢
        omega)
  have hnatcast : ((rk run.coordinateProper.rank sideIndex).toNat : Int) =
      rk run.coordinateProper.rank sideIndex := by omega
  have hleftValue : rk (coordinateGraph execution.params labeled).rank left =
      rk run.coordinateProper.rank sideIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraph execution.params labeled).rank right =
      rk run.coordinateProper.rank sideIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [hc] at hleft hright hleftValue hrightValue
  exact ⟨left, right, hleft, hright, hleftValue, hrightValue⟩

theorem SceneExecution.component_child_side_parent_bracket {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
      ord.layers = run.layers ∧ side.dummy = false ∧
      side.node.clusterPath = child.clusterPath ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left sideIndex right := by
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    execution.component_child_side_parent_borders hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsidePath, _, _, _⟩ :=
    execution.component_group_side_rank_bounds hcomp hrun hchild hchildGroup
      hside hsideBorder howner
  have hdirect := execution.component_direct_group_path hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ := componentRun_spec hrun
  have hwformed := componentRun_coordinate_bordersWellFormed execution.graph_eq hcomp hrun
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
      have hz := hwformed.2.2 sideIndex side hside hd
      rcases hsideBorder with hb | hb <;> omega
  have hnonempty := hwformed.1 sideIndex side hside hsideBorder
  rw [hsidePath] at hnonempty
  have hpositive := List.length_pos_iff.mpr hnonempty
  have hpathNe : parent.clusterPath ≠ child.clusterPath := by
    intro heq
    have hlength := congrArg List.length hdirect
    rw [List.length_dropLast, heq] at hlength
    omega
  have hprefix : parent.clusterPath <+: side.node.clusterPath := by
    rw [hsidePath, ← hdirect]
    exact List.dropLast_prefix _
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨parent, false, none, false⟩, parentIndex)
        execution.params.clusterBorderW).node.clusterPath <+: side.node.clusterPath := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath <+: side.node.clusterPath
    rw [(titleF_keys _).2.2.1]
    exact hprefix
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper sideIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper sideIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hleftNe : left ≠ sideIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hside)
    have hp := congrArg (fun value : ProperNode => value.node.clusterPath) hn
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = side.node.clusterPath at hp
    rw [(titleF_keys _).2.2.1, hsidePath] at hp
    exact hpathNe hp
  have hrightNe : right ≠ sideIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hside)
    have hp := congrArg (fun value : ProperNode => value.node.clusterPath) hn
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = side.node.clusterPath at hp
    rw [(titleF_keys _).2.2.1, hsidePath] at hp
    exact hpathNe hp
  refine ⟨ord, left, right, horder, hlayers, hreal, hsidePath, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left sideIndex right _ side _ hleft hside hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

theorem SceneExecution.component_child_side_parent_border_interval {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ left right : Nat,
      run.proper.nodes[sideIndex]? = some side ∧
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.proper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x ≤
        (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
      (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
          (Labels.rectAt run.proper run.xs run.ys sideIndex).w ≤
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
  obtain ⟨ord, left, right, _, hlayers, _, _, hleft, hright, hbracket⟩ :=
    execution.component_child_side_parent_bracket hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨labeled, hc, hk, _⟩ := componentRun_coordinate_source_alignment hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (measuredGraph_shape execution.graph_eq) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb) hba hbb hp
  have hsideNotTop : side.node.border ≠ -2 := by
    rcases hsideBorder with hb | hb <;> omega
  have hsideNotBottom : side.node.border ≠ 2 := by
    rcases hsideBorder with hb | hb <;> omega
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left sideIndex _ _ hlt hli hmi hleft hside
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    hsideNotTop hsideNotBottom
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri sideIndex right _ _ htr hmi hri hside hright
    hsideNotTop hsideNotBottom
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ := componentRun_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ := componentRun_border_record hrun hright (Or.inr rfl)
  obtain ⟨hsideFinal, hsideX⟩ := componentRun_border_record hrun hside hsideBorder
  have hsideWidth := (sizesNonneg_lookup hsizes sideIndex side hside).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
  have hsideLoops : 0 ≤ (side.node.loopExtent : Int) := Int.natCast_nonneg _
  have hparentLoops : 0 ≤ (parent.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
  refine ⟨left, right, hsideFinal, hleftFinal, hrightFinal, ?_, ?_⟩
  · simp only [coordSep, CoordsImpl.nodeW, hleft, hside, OrderImpl.borderLeft] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hsideFinal, hleftX, hsideX, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  · simp only [coordSep, CoordsImpl.nodeW, hside, hright, OrderImpl.borderRight,
      titleF, hparentGroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hsideFinal, hrightFinal, hsideX, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega

theorem componentRun_final_border_source {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.proper.nodes[index]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.coordinateProper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _⟩ :=
    componentRun_spec h
  obtain ⟨_, _, hlength, _, hrecords, hunchanged⟩ := proxyWidths_rel hproxy
  have hrouted : routed.nodes[index]? = some node := by
    rw [← hdrop] at hnode
    exact hnode
  have hbound : index < run.coordinateProper.nodes.length := by
    have hn := (List.getElem?_eq_some_iff.mp hrouted).1
    omega
  have hsource : run.coordinateProper.nodes[index]? =
      some run.coordinateProper.nodes[index] := List.getElem?_eq_getElem hbound
  obtain ⟨updated, hupdated, _, hborderEq, _⟩ := hrecords index _ hsource
  have hupdatedEq : updated = node := Option.some.inj (hupdated.symm.trans hrouted)
  have hsourceBorder : (run.coordinateProper.nodes[index]).node.border = node.node.border :=
    hborderEq.symm.trans (congrArg (fun value : ProperNode => value.node.border) hupdatedEq)
  have hnotProxy : ¬ ((run.coordinateProper.nodes[index]).node.border = -2 ∨
      (run.coordinateProper.nodes[index]).node.border = 2) := by
    rw [hsourceBorder]
    rcases hborder with hb | hb <;> omega
  obtain ⟨hexact, hx⟩ := hunchanged index _ hsource hnotProxy
  have heq : run.coordinateProper.nodes[index] = node :=
    Option.some.inj (hexact.symm.trans hrouted)
  refine ⟨hsource.trans (congrArg some heq), ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

theorem SceneExecution.component_child_side_parent_horizontal {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.proper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).x ≤ (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
    (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
        (Labels.rectAt run.proper run.xs run.ys sideIndex).w ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).w := by
  have hcoordinate := (componentRun_final_border_source hrun hside hsideBorder).1
  obtain ⟨left, right, _, hleft, hright, hlo, hhi⟩ :=
    execution.component_child_side_parent_border_interval hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hcoordinate hsideBorder howner
  let cg := componentCandidate execution.graph comp candidate
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hframeGroup : (cg.nodes.getD parentIndex default).border = -2 := by
    rw [hparentGet]
    exact hparentGroup
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨box, _, hdecl, hpath⟩ :=
    execution.group_node_path_source hparentSource hparentGroup
  have hleftPath : (OrderImpl.borderLeft
      (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hparentGet]
    simpa only [hdecl] using hpath
  have hrightPath : (OrderImpl.borderRight
      (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    exact hleftPath
  have hleftContained := frameRect_side_marker_contained (P := execution.params)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
  exact ⟨Int.le_trans hleftContained.1 hlo, Int.le_trans hhi hrightContained.2.1⟩

private theorem boundsOf_rects_right_nonneg (rects : List Rect) :
    0 ≤ (boundsOf rects []).right := by
  cases rects with
  | nil => exact Int.le_refl 0
  | cons first rest =>
    change 0 ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).right
    exact foldl_stepRect_le_right _ _

private theorem boundsOf_rects_horizontal (rects : List Rect) (lo hi : Int)
    (hne : rects ≠ []) (hhi : 0 ≤ hi)
    (hrects : ∀ rect ∈ rects, lo ≤ rect.x ∧ rect.x + rect.w ≤ hi) :
    lo ≤ (boundsOf rects []).minX ∧ (boundsOf rects []).right ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minX → initial.right ≤ hi →
      (∀ rect ∈ remaining, lo ≤ rect.x ∧ rect.x + rect.w ≤ hi) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minX ∧
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).right ≤ hi := by
    intro remaining
    induction remaining with
    | nil =>
      intro initial hlo hupper _
      exact ⟨hlo, hupper⟩
    | cons first rest ih =>
      intro initial hlo hupper hall
      simp only [List.foldl_cons]
      apply ih
      · exact Int.le_min.mpr ⟨hlo, (hall first (by simp)).1⟩
      · exact Int.max_le.mpr ⟨hupper, (hall first (by simp)).2⟩
      · intro rect hr
        exact hall rect (List.mem_cons_of_mem _ hr)
  cases rects with
  | nil => exact (hne rfl).elim
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minX ∧ _
    exact preserve _ _ (hrects first (by simp)).1 hhi hrects

theorem SceneExecution.component_group_final_side {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (sideIndex : Nat) (side : ProperNode),
      run.proper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some node.decl := by
  obtain ⟨_, labeled, _, _, hc, _, _, hrecords, _, _, _⟩ :=
    componentRun_group_bottom_source execution.graph_eq hcomp hrun hnode hgroup
  let proxy := clearF (titleF ⟨node, false, none, false⟩)
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    componentRun_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨box, _, hdecl, hpath⟩ := execution.group_node_path_source hgroupSource hgroup
  have hproxyLast : proxy.node.clusterPath.getLast? = some node.decl := by
    change (clearF (titleF ⟨node, false, none, false⟩)).node.clusterPath.getLast? = _
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1]
    simp [hpath, hdecl]
  exact ⟨sideIndex, side, (componentRun_border_record hrun hside hsideBorder).1,
    hsideBorder, hsideOwner.trans (howner.symm.trans hproxyLast)⟩

theorem SceneExecution.component_child_frame_parent_horizontal {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).x ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).x ∧
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).w ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).w := by
  let cg := componentCandidate execution.graph comp candidate
  let parentFrame := frameRect execution.params cg run parentIndex
  let childFrame := frameRect execution.params cg run childIndex
  let borders := run.proper.nodes.zipIdx.filterMap fun entry =>
    if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
        entry.1.node.clusterPath.getLast? == some child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  let parentBorders := run.proper.nodes.zipIdx.filterMap fun entry =>
    if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
        entry.1.node.clusterPath.getLast? == some parent.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hchildGet : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  obtain ⟨sideIndex, side, hside, hsideBorder, howner⟩ :=
    execution.component_group_final_side hcomp hrun hchild hchildGroup
  have hmember : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
    rcases hsideBorder with hb | hb <;> simp [hb, howner]
  have hnonempty : borders ≠ [] := by
    intro hempty
    rw [hempty] at hmember
    exact List.not_mem_nil hmember
  have hparentRight : parentFrame.x + parentFrame.w = (boundsOf parentBorders []).right := by
    dsimp only [parentFrame]
    simp only [frameRect, hparentGet, hparentGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf parentBorders []).minX +
      ((boundsOf parentBorders []).right - (boundsOf parentBorders []).minX) = _
    omega
  have hupperNonnegative : 0 ≤ parentFrame.x + parentFrame.w := by
    rw [hparentRight]
    exact boundsOf_rects_right_nonneg _
  have hall : ∀ rect ∈ borders,
      parentFrame.x ≤ rect.x ∧ rect.x + rect.w ≤ parentFrame.x + parentFrame.w := by
    intro rect hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcondition
      have hconditions := Bool.and_eq_true_iff.mp hcondition
      have hb : entry.1.node.border = -1 ∨ entry.1.node.border = 1 := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using hconditions.1
      have ho : entry.1.node.clusterPath.getLast? = some child.decl :=
        beq_iff_eq.mp hconditions.2
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      exact execution.component_child_side_parent_horizontal hwf hcomp hrun
        hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
        (List.mem_zipIdx_iff_getElem?.mp hentry) hb ho
    · cases heq
  have hhull := boundsOf_rects_horizontal borders parentFrame.x
    (parentFrame.x + parentFrame.w) hnonempty hupperNonnegative hall
  have hchildX : childFrame.x = (boundsOf borders []).minX := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hchildRight : childFrame.x + childFrame.w = (boundsOf borders []).right := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf borders []).minX +
      ((boundsOf borders []).right - (boundsOf borders []).minX) = _
    omega
  change parentFrame.x ≤ childFrame.x ∧
    childFrame.x + childFrame.w ≤ parentFrame.x + parentFrame.w
  rw [hchildRight, hchildX]
  exact hhull

theorem commonPath_prefix_of_prefix :
    ∀ (C left right : List Nat), C <+: left → C <+: right →
      C <+: OrderImpl.commonPath left right
  | [], _, _, _, _ => List.nil_prefix
  | c :: C', left, right, hl, hr => by
    cases left with
    | nil => exact absurd hl (by simp)
    | cons l ls =>
      cases right with
      | nil => exact absurd hr (by simp)
      | cons r rs =>
        obtain ⟨hcl, hl'⟩ := List.cons_prefix_cons.mp hl
        obtain ⟨hcr, hr'⟩ := List.cons_prefix_cons.mp hr
        subst hcl hcr
        simp only [OrderImpl.commonPath, ↓reduceIte]
        exact List.cons_prefix_cons.mpr ⟨rfl, commonPath_prefix_of_prefix C' ls rs hl' hr'⟩

theorem commonPath_member_both {owner : Nat} :
    ∀ left right : List Nat, owner ∈ OrderImpl.commonPath left right →
      owner ∈ left ∧ owner ∈ right := by
  intro left
  induction left with
  | nil =>
    intro right h
    simp only [OrderImpl.commonPath, List.not_mem_nil] at h
  | cons first rest ih =>
    intro right h
    cases right with
    | nil =>
      simp only [OrderImpl.commonPath, List.not_mem_nil] at h
    | cons other tail =>
      by_cases heq : first = other
      · subst other
        simp only [OrderImpl.commonPath, ↓reduceIte] at h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨List.mem_cons.mpr (Or.inl h), List.mem_cons.mpr (Or.inl h)⟩
        · obtain ⟨hl, hr⟩ := ih tail h
          exact ⟨List.mem_cons.mpr (Or.inr hl), List.mem_cons.mpr (Or.inr hr)⟩
      · simp only [OrderImpl.commonPath, heq, ↓reduceIte, List.not_mem_nil] at h

def PathScoped (c : Nat) (C L : List Nat) : Prop := c ∈ L → C <+: L

theorem pathScoped_nil (c : Nat) (C : List Nat) : PathScoped c C [] :=
  fun h => absurd h List.not_mem_nil

theorem pathScoped_commonPath {c : Nat} {C L R : List Nat}
    (hl : PathScoped c C L) (hr : PathScoped c C R) :
    PathScoped c C (OrderImpl.commonPath L R) := by
  intro hin
  obtain ⟨hL, hR⟩ := commonPath_member_both L R hin
  exact commonPath_prefix_of_prefix C L R (hl hL) (hr hR)

theorem nodes_getD_scoped {c : Nat} {C : List Nat} {p : Proper}
    (hnodes : ∀ e ∈ p.nodes, PathScoped c C e.node.clusterPath) (v : Nat) :
    PathScoped c C (p.nodes.getD v default).node.clusterPath := by
  by_cases hv : v < p.nodes.length
  · have hget : p.nodes.getD v default = p.nodes[v] := by
      simp [List.getD_eq_getElem?_getD, hv]
    rw [hget]
    exact hnodes _ (List.getElem_mem hv)
  · have hget : p.nodes.getD v default = default := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hv)]
    rw [hget]
    exact pathScoped_nil c C

theorem nodePath_scoped {c : Nat} {C : List Nat} {p : Proper}
    (hnodes : ∀ e ∈ p.nodes, PathScoped c C e.node.clusterPath) (v : Nat) :
    PathScoped c C (OrderImpl.nodePath p v) := by
  unfold OrderImpl.nodePath
  dsimp only
  split
  · exact nodes_getD_scoped hnodes v
  · split
    · exact pathScoped_nil c C
    · exact pathScoped_commonPath (nodes_getD_scoped hnodes _) (nodes_getD_scoped hnodes _)

theorem materializeDummyPaths_scoped {c : Nat} {C : List Nat} {p : Proper}
    (hnodes : ∀ e ∈ p.nodes, PathScoped c C e.node.clusterPath) :
    ∀ e ∈ (materializeDummyPaths p).nodes, PathScoped c C e.node.clusterPath := by
  intro e he
  unfold materializeDummyPaths at he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  have hmem : q.1 ∈ p.nodes := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)
  by_cases hd : q.1.dummy = true
  · simp only [hd, ↓reduceIte]
    exact nodePath_scoped hnodes q.2
  · have hd' : q.1.dummy = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, ↓reduceIte]
    exact hnodes q.1 hmem

theorem sizedNodes_scoped {c : Nat} {C : List Nat} {P : Params} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ s ∈ (sizeProperPorts P labeled).nodes, PathScoped c C s.node.clusterPath := by
  intro s hs
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hs
  obtain ⟨original, horiginal, _, _, hpath⟩ := sizeProperPorts_node_origin P labeled hindex
  rw [hpath]
  exact hlabeled original (List.mem_of_getElem? horiginal)

theorem titled_nodes_scoped {c : Nat} {C : List Nat} {P : Params} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ f ∈ (titleReservations (sizeProperPorts P labeled)).nodes,
      PathScoped c C f.node.clusterPath := by
  intro f hf
  rw [titleReservations_nodes] at hf
  rcases List.mem_append.mp hf with hleft | hright
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hleft
    rw [(titleF_keys s).2.2.1]
    exact sizedNodes_scoped hlabeled s hs
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hright
    have hmem : q.1 ∈ (sizeProperPorts P labeled).nodes := by
      obtain ⟨hzip, _⟩ := List.mem_filter.mp hq
      exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip)
    exact sizedNodes_scoped hlabeled q.1 hmem

theorem coordinatePrepared_scoped {c : Nat} {C : List Nat} {P : Params} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ e ∈ (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes,
      PathScoped c C e.node.clusterPath := by
  intro e he
  rw [clearProxyExtents_nodes] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  rw [(clearF_keys f).2.2.1]
  rcases addClusterBorders_node_origin _ _ f hf with htitled | ⟨top, htop, _, _, hpath⟩
  · exact titled_nodes_scoped hlabeled f htitled
  · rw [hpath]
    obtain ⟨hzip, _⟩ := List.mem_filter.mp htop
    exact titled_nodes_scoped hlabeled top.1
      (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip))

theorem coordinateGraph_scoped {c : Nat} {C : List Nat} {P : Params} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ e ∈ (coordinateGraph P labeled).nodes, PathScoped c C e.node.clusterPath :=
  materializeDummyPaths_scoped (coordinatePrepared_scoped hlabeled)


theorem proxyWidths_nodes_scoped {Q : List Nat → Prop} {p q : Proper} {xs ys : List Int}
    (h : proxyWidths p xs = .ok (q, ys)) (hp : ∀ e ∈ p.nodes, Q e.node.clusterPath) :
    ∀ e ∈ q.nodes, Q e.node.clusterPath := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, h⟩ := bind_ok' h
  have h : (Except.ok _ : Except LayoutError (Proper × List Int)) = Except.ok (q, ys) := h
  have h := Except.ok.inj h
  have hq : q = { p with nodes := updated.map (·.1) } := (Prod.mk.inj h).1.symm
  have hproj : updated.map (fun b => b.1.node.clusterPath) =
      p.nodes.zipIdx.map (fun a => a.1.node.clusterPath) :=
    Metadata.mapM_projection _ (fun a => a.1.node.clusterPath) (fun b => b.1.node.clusterPath)
      (by
        intro a b hab
        dsimp only at hab
        by_cases hcond : (a.1.node.border == -2 || a.1.node.border == 2) = true
        · simp only [hcond, ↓reduceIte] at hab
          cases hl : a.1.node.clusterPath.getLast? with
          | none => simp [hl] at hab
          | some owner =>
            simp only [hl] at hab
            obtain ⟨span, _, hab⟩ := bind_ok' hab
            obtain ⟨w, _, hab⟩ := bind_ok' hab
            by_cases hw0 : w < 0
            · simp only [hw0, ↓reduceIte] at hab
              simp [bind, Except.bind] at hab
            simp only [hw0, ↓reduceIte] at hab
            obtain ⟨c, _, hab⟩ := bind_ok' hab
            have hab : (Except.ok _ : Except LayoutError (ProperNode × Int)) = Except.ok b := hab
            have hab := Except.ok.inj hab
            subst hab
            rfl
        · simp only [hcond] at hab
          have hab : (Except.ok (a.1, xs.getD a.2 0) : Except LayoutError (ProperNode × Int)) =
              Except.ok b := hab
          have hab := Except.ok.inj hab
          subst hab
          rfl)
      hu
  intro e he
  rw [hq] at he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  have hmem : b.1.node.clusterPath ∈ updated.map (fun b => b.1.node.clusterPath) :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  rw [hproj] at hmem
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
  rw [← heq]
  exact hp a.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp ha))

theorem SceneExecution.bottom_node_path_source {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨effective, heffective, _, hpath, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph_eq (List.mem_of_getElem? hnode) hborder
  rw [List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath

theorem SceneExecution.original_path_scoped {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {childIndex : Nat} {child : Node}
    (hchild : execution.graph.nodes[childIndex]? = some child) (hchildGroup : child.border = -2)
    {index : Nat} {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hborder : node.border = 0 ∨ node.border = -2 ∨ node.border = 2) :
    PathScoped child.decl child.clusterPath node.clusterPath := by
  obtain ⟨childBox, hchildBox, hchildDecl, hchildPath⟩ :=
    execution.group_node_path_source hchild hchildGroup
  intro hin
  rcases hborder with hb | hb | hb
  · obtain ⟨box, hbox, _, hpath⟩ := execution.plain_node_path_source hnode hb
    rw [hpath, hchildDecl] at hin
    rw [hpath, hchildPath]
    exact Compound.path_ancestor_prefix (inputModel inp o) hwf hchildBox hbox hin
  · obtain ⟨box, hbox, hdecl, hpath⟩ := execution.group_node_path_source hnode hb
    rw [hpath] at hin ⊢
    rcases List.mem_append.mp hin with hin | hin
    · rw [hchildDecl] at hin
      rw [hchildPath]
      exact (Compound.path_ancestor_prefix (inputModel inp o) hwf hchildBox hbox hin).trans
        (List.prefix_append _ _)
    · have hsame : childIndex = index := hchildDecl.symm.trans (List.mem_singleton.mp hin)
      subst hsame
      have hnodeEq : node = child := Option.some.inj (hnode.symm.trans hchild)
      subst hnodeEq
      rw [hpath]
      exact List.prefix_refl _
  · obtain ⟨box, hbox, hpath⟩ := execution.bottom_node_path_source hnode hb
    rw [hpath] at hin ⊢
    rcases List.mem_append.mp hin with hin | hin
    · rw [hchildDecl] at hin
      rw [hchildPath]
      exact (Compound.path_ancestor_prefix (inputModel inp o) hwf hchildBox hbox hin).trans
        (List.prefix_append _ _)
    · have hsame : childIndex = node.decl := hchildDecl.symm.trans (List.mem_singleton.mp hin)
      rw [← hsame] at hbox
      have hboxEq : box = childBox := Option.some.inj (hbox.symm.trans hchildBox)
      subst hboxEq
      rw [hchildPath, ← hsame]
      exact List.prefix_refl _


theorem SceneExecution.candidate_node_scoped {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate : Nat} {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
    PathScoped child.decl child.clusterPath node.clusterPath := by
  by_cases hempty : node.clusterPath = []
  · rw [hempty]
    exact pathScoped_nil _ _
  · obtain ⟨_, _, hsource⟩ := componentCandidate_nonempty_path_source hnode hempty
    obtain ⟨_, _, hchildSource⟩ := componentCandidate_nonplain_source hchild (by omega)
    exact execution.original_path_scoped hwf hchildSource hchildGroup hsource
      (componentCandidate_marker_shape execution.graph_eq hnode).1

theorem SceneExecution.labeled_nodes_scoped {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate : Nat} {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2) {labeled : Proper}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) labeled) :
    ∀ g ∈ labeled.nodes, PathScoped child.decl child.clusterPath g.node.clusterPath := by
  intro g hg
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hg
  rcases hkeys v g hv with ⟨n, hn, _, _, hpath⟩ | ⟨_, _, hpath⟩
  · rw [hpath]
    exact execution.candidate_node_scoped hwf hchild hchildGroup hn
  · rw [hpath]
    exact pathScoped_nil _ _

theorem SceneExecution.component_run_proper_scoped {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2) :
    ∀ e ∈ run.proper.nodes, PathScoped child.decl child.clusterPath e.node.clusterPath := by
  obtain ⟨labeled, hc, hk, _⟩ := componentRun_coordinate_source_alignment hrun
  have hlabeled := execution.labeled_nodes_scoped hwf hchild hchildGroup hk
  have hcoordinate := coordinateGraph_scoped (P := execution.params) hlabeled
  rw [hc] at hcoordinate
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _⟩ := componentRun_spec hrun
  have hq := proxyWidths_nodes_scoped hproxy hcoordinate
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact hq

private theorem boundsOf_rects_bottom_nonneg (rects : List Rect) :
    0 ≤ (boundsOf rects []).bottom := by
  cases rects with
  | nil => exact Int.le_refl 0
  | cons first rest =>
    change 0 ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).bottom
    exact foldl_stepRect_le_bottom _ _

private theorem boundsOf_rects_vertical (rects : List Rect) (lo hi : Int)
    (hne : rects ≠ []) (hhi : 0 ≤ hi)
    (hrects : ∀ rect ∈ rects, lo ≤ rect.y ∧ rect.y + rect.h ≤ hi) :
    lo ≤ (boundsOf rects []).minY ∧ (boundsOf rects []).bottom ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minY → initial.bottom ≤ hi →
      (∀ rect ∈ remaining, lo ≤ rect.y ∧ rect.y + rect.h ≤ hi) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minY ∧
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).bottom ≤ hi := by
    intro remaining
    induction remaining with
    | nil =>
      intro initial hlo hupper _
      exact ⟨hlo, hupper⟩
    | cons first rest ih =>
      intro initial hlo hupper hall
      simp only [List.foldl_cons]
      apply ih
      · exact Int.le_min.mpr ⟨hlo, (hall first (by simp)).1⟩
      · exact Int.max_le.mpr ⟨hupper, (hall first (by simp)).2⟩
      · intro rect hr
        exact hall rect (List.mem_cons_of_mem _ hr)
  cases rects with
  | nil => exact (hne rfl).elim
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minY ∧ _
    exact preserve _ _ (hrects first (by simp)).1 hhi hrects

theorem SceneExecution.component_child_frame_parent_vertical {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).y ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).y ∧
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).h ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).h := by
  let cg := componentCandidate execution.graph comp candidate
  let parentFrame := frameRect execution.params cg run parentIndex
  let childFrame := frameRect execution.params cg run childIndex
  let childRects := run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  let parentRects := run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains parent.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hchildGet : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hdirect := execution.component_direct_group_path hwf hparent hparentGroup hchild
    hchildGroup hparentBox hchildBox hparentRef hne
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨_, _, hparentDecl, hparentPath⟩ :=
    execution.group_node_path_source hparentSource hparentGroup
  have hparentOwn : parent.decl ∈ parent.clusterPath := by
    rw [hparentPath, hparentDecl]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hparentInChild : parent.decl ∈ child.clusterPath := by
    apply (List.dropLast_prefix child.clusterPath).subset
    rw [hdirect]
    exact hparentOwn
  have hscope := execution.component_run_proper_scoped hwf hrun hchild hchildGroup
  have hparentContains : ∀ entry ∈ run.proper.nodes.zipIdx,
      entry.1.node.clusterPath.contains child.decl = true →
      entry.1.node.clusterPath.contains parent.decl = true := by
    intro entry hentry hcontains
    have hmem : entry.1 ∈ run.proper.nodes :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hentry)
    have hprefix := hscope entry.1 hmem (List.contains_iff_mem.mp hcontains)
    exact List.contains_iff_mem.mpr (hprefix.subset hparentInChild)
  obtain ⟨sideIndex, side, hside, _, howner⟩ :=
    execution.component_group_final_side hcomp hrun hchild hchildGroup
  have hmember : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ childRects := by
    apply List.mem_filterMap.mpr
    refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
    have hmem : child.decl ∈ side.node.clusterPath := List.mem_of_getLast? howner
    simp [hmem]
  have hnonempty : childRects ≠ [] := by
    intro hempty
    rw [hempty] at hmember
    exact List.not_mem_nil hmember
  have hparentBottom : parentFrame.y + parentFrame.h = (boundsOf parentRects []).bottom := by
    dsimp only [parentFrame]
    simp only [frameRect, hparentGet, hparentGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf parentRects []).minY +
      ((boundsOf parentRects []).bottom - (boundsOf parentRects []).minY) = _
    omega
  have hupperNonnegative : 0 ≤ parentFrame.y + parentFrame.h := by
    rw [hparentBottom]
    exact boundsOf_rects_bottom_nonneg _
  have hall : ∀ rect ∈ childRects,
      parentFrame.y ≤ rect.y ∧ rect.y + rect.h ≤ parentFrame.y + parentFrame.h := by
    intro rect hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcontains
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      exact frameRect_member_vertical (P := execution.params) (cg := cg) (run := run)
        (i := parentIndex) (q := entry)
        (by rw [hparentGet]; exact hparentGroup) hentry
        (by rw [hparentGet]; exact hparentContains entry hentry hcontains)
    · cases heq
  have hhull := boundsOf_rects_vertical childRects parentFrame.y
    (parentFrame.y + parentFrame.h) hnonempty hupperNonnegative hall
  have hchildY : childFrame.y = (boundsOf childRects []).minY := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hchildBottom : childFrame.y + childFrame.h = (boundsOf childRects []).bottom := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf childRects []).minY +
      ((boundsOf childRects []).bottom - (boundsOf childRects []).minY) = _
    omega
  change parentFrame.y ≤ childFrame.y ∧
    childFrame.y + childFrame.h ≤ parentFrame.y + parentFrame.h
  rw [hchildBottom, hchildY]
  exact hhull

theorem SceneExecution.component_child_frame_contained {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).Contained
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex) := by
  have hhorizontal := execution.component_child_frame_parent_horizontal hwf hcomp hrun
    hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hvertical := execution.component_child_frame_parent_vertical hwf hcomp hrun
    hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
  unfold Rect.Contained
  exact ⟨hhorizontal.1, hhorizontal.2, hvertical.1, hvertical.2⟩

end Elegant.Layered.PipelineImpl
