import Elegant.Layered.Order
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameEnvelope
import Elegant.Layered.ForeignSideChainShapeProof
import Elegant.Layered.ShapeIncidentInheritedProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Fold invariant of the border-marker emission.

The border markers of one group are emitted by `OrderImpl.addClusterBorders`
through an inner fold (`OrderImpl.borderInner`) over the ranks of the group
span, and linked by `OrderImpl.borderLinks`. No lemma states the fold
invariant. This module proves it:

- `borderInner_fold_lengths`: every inner step appends two nodes and two
  ranks;
- `borderInner_emission`: the markers the fold emits for one box sit at
  consecutive fresh indices (`base + 2 * offset`, `base + 2 * offset + 1`),
  one left and one right marker per offset, with rank entry `lo + offset`;
- `borderInner_emission_inj`: distinct offsets give distinct indices;
- `borderInner_links_mem` / `borderInner_links_endpoints` /
  `borderInner_link_endpoints_are_markers`: the `borderLinks` edges appended
  at a positive step join the markers of consecutive offsets;
- `titled_anchor_unique` / `chainMarkers_shareAnchor`: a side marker
  determines its anchor box uniquely (the third conjunct of
  `OrderImpl.BorderConstructionReady`, fed by the `NodeKeys` transport
  inside `titled_border_ready`);
- `executed_border_binv`: the `BInv` witness for the executed construction,
  giving nodup `(border, path, rank-entry)` keys over every emitted marker.
-/
theorem borderInner_fold_lengths (q : ProperNode × Nat) (w : Int) (lo : Nat)
    (l : List Nat) (state : Proper) :
    (l.foldl (OrderImpl.borderInner q w lo) state).nodes.length =
      state.nodes.length + 2 * l.length ∧
    (l.foldl (OrderImpl.borderInner q w lo) state).rank.length =
      state.rank.length + 2 * l.length := by
  induction l generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons off rest ih =>
    rw [List.foldl_cons]
    have hstep : (OrderImpl.borderInner q w lo state off).nodes.length =
        state.nodes.length + 2 := by
      simp [OrderImpl.borderInner]
    have hstepr : (OrderImpl.borderInner q w lo state off).rank.length =
        state.rank.length + 2 := by
      simp [OrderImpl.borderInner]
    obtain ⟨hn, hr⟩ := ih (OrderImpl.borderInner q w lo state off)
    rw [hstep] at hn
    rw [hstepr] at hr
    simp only [List.length_cons] at hn hr ⊢
    omega

/-- The emission invariant: the markers the inner fold emits for one box sit
at consecutive fresh indices (`base + 2 * offset`, `base + 2 * offset + 1`),
one left and one right marker per offset, with rank entry `lo + offset`.
The `aligned` premise holds for every state of the executed construction
(`BorderConstructionReady` length alignment, preserved by every step). -/
theorem borderInner_emission (q : ProperNode × Nat) (w : Int) (lo : Nat)
    (state : Proper) (haligned : state.nodes.length = state.rank.length)
    (count offset : Nat) (hoff : offset < count) :
    ∃ left right : Nat,
      left = state.nodes.length + 2 * offset ∧ right = left + 1 ∧
      ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes[left]? =
        some (OrderImpl.borderLeft q w) ∧
      ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes[right]? =
        some (OrderImpl.borderRight q w) ∧
      ((List.range count).foldl (OrderImpl.borderInner q w lo) state).rank[left]? =
        some ((lo + offset : Nat) : Int) ∧
      ((List.range count).foldl (OrderImpl.borderInner q w lo) state).rank[right]? =
        some ((lo + offset : Nat) : Int) := by
  have hnodes : ∀ (s : Proper) (k : Nat),
      (OrderImpl.borderInner q w lo s k).nodes =
        s.nodes ++ [OrderImpl.borderLeft q w, OrderImpl.borderRight q w] :=
    fun s k => rfl
  have hranks : ∀ (s : Proper) (k : Nat),
      (OrderImpl.borderInner q w lo s k).rank =
        s.rank ++ [((lo + k : Nat) : Int), ((lo + k : Nat) : Int)] :=
    fun s k => rfl
  have hfold : ∀ (n : Nat),
      (List.range (n + 1)).foldl (OrderImpl.borderInner q w lo) state =
        OrderImpl.borderInner q w lo
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state) n := by
    intro n
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
  induction count with
  | zero => omega
  | succ n ih =>
    by_cases hlt : offset < n
    · obtain ⟨left, right, hl, hr, hnl, hnr, hrl, hrr⟩ := ih hlt
      have hlen := (borderInner_fold_lengths q w lo (List.range n) state).1
      have hlenr := (borderInner_fold_lengths q w lo (List.range n) state).2
      simp only [List.length_range] at hlen hlenr
      have hleft : left <
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length := by
        omega
      have hleftr : left <
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank.length := by
        omega
      have hright : right <
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length := by
        omega
      have hrightr : right <
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank.length := by
        omega
      refine ⟨left, right, hl, hr, ?_, ?_, ?_, ?_⟩
      · rw [hfold n, hnodes]
        exact (List.getElem?_append_left hleft).trans hnl
      · rw [hfold n, hnodes]
        exact (List.getElem?_append_left hright).trans hnr
      · rw [hfold n, hranks]
        exact (List.getElem?_append_left hleftr).trans hrl
      · rw [hfold n, hranks]
        exact (List.getElem?_append_left hrightr).trans hrr
    · have heq : offset = n := by omega
      rw [heq]
      have hlen := (borderInner_fold_lengths q w lo (List.range n) state).1
      have hlenr := (borderInner_fold_lengths q w lo (List.range n) state).2
      simp only [List.length_range] at hlen hlenr
      have hbase : state.nodes.length + 2 * n =
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length := by
        omega
      have hbaser : state.rank.length + 2 * n =
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank.length := by
        omega
      have hbaseEq : state.nodes.length + 2 * n =
          state.rank.length + 2 * n := by omega
      refine ⟨state.nodes.length + 2 * n, state.nodes.length + 2 * n + 1,
        rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hfold n, hnodes, hbase]
        have h1 : ((((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes ++
            [OrderImpl.borderLeft q w, OrderImpl.borderRight q w])[((List.range n).foldl
              (OrderImpl.borderInner q w lo) state).nodes.length]? =
            ([OrderImpl.borderLeft q w, OrderImpl.borderRight q w])[((List.range n).foldl
              (OrderImpl.borderInner q w lo) state).nodes.length -
              ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length]?) :=
          List.getElem?_append_right (Nat.le_refl _)
        simp only [Nat.sub_self] at h1
        rw [show (([OrderImpl.borderLeft q w, OrderImpl.borderRight q w] :
          List ProperNode))[0]? = some (OrderImpl.borderLeft q w) from rfl] at h1
        exact h1
      · rw [hfold n, hnodes]
        have hle : ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length ≤
            state.nodes.length + 2 * n + 1 := by omega
        have h1 : ((((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes ++
            [OrderImpl.borderLeft q w, OrderImpl.borderRight q w])[state.nodes.length + 2 * n + 1]? =
            ([OrderImpl.borderLeft q w, OrderImpl.borderRight q w])[state.nodes.length + 2 * n + 1 -
              ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length]?) :=
          List.getElem?_append_right hle
        rw [← hbase] at h1
        simp only [Nat.add_sub_cancel_left] at h1
        rw [show (([OrderImpl.borderLeft q w, OrderImpl.borderRight q w] :
          List ProperNode))[1]? = some (OrderImpl.borderRight q w) from rfl] at h1
        exact h1
      · rw [hfold n, hranks, hbaseEq, hbaser]
        have h1 : ((((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank ++
            [((lo + n : Nat) : Int), ((lo + n : Nat) : Int)])[((List.range n).foldl
              (OrderImpl.borderInner q w lo) state).rank.length]? =
            ([((lo + n : Nat) : Int), ((lo + n : Nat) : Int)])[((List.range n).foldl
              (OrderImpl.borderInner q w lo) state).rank.length -
              ((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank.length]?) :=
          List.getElem?_append_right (Nat.le_refl _)
        simp only [Nat.sub_self] at h1
        rw [show (([((lo + n : Nat) : Int), ((lo + n : Nat) : Int)] :
          List Int))[0]? = some ((lo + n : Nat) : Int) from rfl] at h1
        exact h1
      · rw [hfold n, hranks, hbaseEq]
        have hle : ((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank.length ≤
            state.rank.length + 2 * n + 1 := by omega
        have h1 : ((((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank ++
            [((lo + n : Nat) : Int), ((lo + n : Nat) : Int)])[state.rank.length + 2 * n + 1]? =
            ([((lo + n : Nat) : Int), ((lo + n : Nat) : Int)])[state.rank.length + 2 * n + 1 -
              ((List.range n).foldl (OrderImpl.borderInner q w lo) state).rank.length]?) :=
          List.getElem?_append_right hle
        rw [← hbaser] at h1
        simp only [Nat.add_sub_cancel_left] at h1
        rw [show (([((lo + n : Nat) : Int), ((lo + n : Nat) : Int)] :
          List Int))[1]? = some ((lo + n : Nat) : Int) from rfl] at h1
        exact h1
theorem borderInner_emission_inj (base o1 o2 : Nat)
    (heq : base + 2 * o1 = base + 2 * o2) : o1 = o2 := by
  omega
/-- Every edge the inner fold appends at step `offset` is a member of the
`borderLinks` block for that step. -/
theorem borderInner_links_mem (q : ProperNode × Nat) (w : Int) (lo : Nat)
    (state : Proper) (count offset : Nat) (hoff : offset < count)
    {e : ProperEdge}
    (hmem : e ∈ OrderImpl.borderLinks (state.nodes.length + 2 * offset)
      q.1.node.decl offset) :
    e ∈ ((List.range count).foldl (OrderImpl.borderInner q w lo) state).edges := by
  have hedge : ∀ (s : Proper) (k : Nat),
      (OrderImpl.borderInner q w lo s k).edges =
        s.edges ++ OrderImpl.borderLinks s.nodes.length q.1.node.decl k :=
    fun s k => rfl
  have hlen : ∀ (n : Nat),
      ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length =
        state.nodes.length + 2 * n := by
    intro n
    have h := (borderInner_fold_lengths q w lo (List.range n) state).1
    simp only [List.length_range] at h
    exact h
  have hfold : ∀ (n : Nat),
      (List.range (n + 1)).foldl (OrderImpl.borderInner q w lo) state =
        OrderImpl.borderInner q w lo
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state) n := by
    intro n
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
  induction count with
  | zero => omega
  | succ n ih =>
    by_cases hlt : offset < n
    · have hmem' : e ∈
          ((List.range n).foldl (OrderImpl.borderInner q w lo) state).edges :=
        ih hlt
      rw [hfold n, hedge]
      exact List.mem_append.mpr (Or.inl hmem')
    · have heq : offset = n := by omega
      rw [heq] at hmem
      rw [hfold n, hedge, hlen]
      exact List.mem_append.mpr (Or.inr hmem)

/-- A positive-step `borderLinks` block joins the previous offset pair to the
current one, on both sides. -/
theorem borderInner_links_endpoints (next decl offset : Nat) (hpos : 0 < offset)
    {e : ProperEdge} (hmem : e ∈ OrderImpl.borderLinks next decl offset) :
    (e.tail = next - 2 ∧ e.head = next ∧ e.decl = decl) ∨
    (e.tail = next - 1 ∧ e.head = next + 1 ∧ e.decl = decl) := by
  unfold OrderImpl.borderLinks at hmem
  by_cases h0 : offset = 0
  · omega
  · simp only [h0, ↓reduceIte] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> simp

/-- The links appended at a positive step join consecutive same-side emitted
markers: the previous offset pair to the current one. -/
theorem borderInner_link_endpoints_are_markers (q : ProperNode × Nat) (w : Int)
    (lo : Nat) (state : Proper)
    (haligned : state.nodes.length = state.rank.length)
    (count offset : Nat) (hoff : offset < count) (hpos : 0 < offset)
    {e : ProperEdge}
    (hmem : e ∈ OrderImpl.borderLinks (state.nodes.length + 2 * offset)
      q.1.node.decl offset) :
    ((e.tail = state.nodes.length + 2 * offset - 2 ∧
        e.head = state.nodes.length + 2 * offset ∧
        ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes[e.tail]? =
          some (OrderImpl.borderLeft q w) ∧
        ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes[e.head]? =
          some (OrderImpl.borderLeft q w)) ∨
      (e.tail = state.nodes.length + 2 * offset - 1 ∧
        e.head = state.nodes.length + 2 * offset + 1 ∧
        ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes[e.tail]? =
          some (OrderImpl.borderRight q w) ∧
        ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes[e.head]? =
          some (OrderImpl.borderRight q w))) := by
  obtain ⟨lp, rp, hlp, hrp, hnl, hnr, _, _⟩ :=
    borderInner_emission q w lo state haligned count (offset - 1) (by omega)
  obtain ⟨lc, rc, hlc, hrc, hnlc, hnrc, _, _⟩ :=
    borderInner_emission q w lo state haligned count offset hoff
  rcases borderInner_links_endpoints _ _ _ hpos hmem with ⟨ht, hh, _⟩ | ⟨ht, hh, _⟩
  · left
    refine ⟨?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · rw [ht]
      have : state.nodes.length + 2 * offset - 2 =
          state.nodes.length + 2 * (offset - 1) := by omega
      rw [this, ← hlp]
      exact hnl
    · rw [hh, ← hlc]
      exact hnlc
  · right
    refine ⟨?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · rw [ht]
      have : state.nodes.length + 2 * offset - 1 =
          state.nodes.length + 2 * (offset - 1) + 1 := by omega
      rw [this, ← hlp, ← hrp]
      exact hnr
    · rw [hh, ← hlc, ← hrc]
      exact hnrc


/-- A side marker determines its anchor box uniquely: the third conjunct of
`OrderImpl.BorderConstructionReady` (whose proof, `titled_border_ready`,
carries the `NodeKeys` transport through `titleReservations`). -/
theorem titled_anchor_unique {source : Proper}
    (hready : OrderImpl.BorderConstructionReady source)
    {a b : Nat} {na nb : ProperNode}
    (ha : source.nodes[a]? = some na) (hb : source.nodes[b]? = some nb)
    (h1 : na.node.border = -2) (h2 : nb.node.border = -2)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b :=
  hready.2.2.1 a b na nb ha hb h1 h2 hp

/-- Two side markers with the same cluster path share their `-2` anchor. -/
theorem chainMarkers_shareAnchor {source : Proper} (w : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {a b : Nat} {na nb : ProperNode}
    (hna : (OrderImpl.addClusterBorders source w).nodes[a]? = some na)
    (hnb : (OrderImpl.addClusterBorders source w).nodes[b]? = some nb)
    (hsa : na.node.border = -1 ∨ na.node.border = 1)
    (hsb : nb.node.border = -1 ∨ nb.node.border = 1)
    (hp : na.node.clusterPath = nb.node.clusterPath) :
    ∃ top : ProperNode × Nat,
      top ∈ source.nodes.zipIdx.filter (fun entry => entry.1.node.border == -2) ∧
      na.node.clusterPath = top.1.node.clusterPath ∧
      nb.node.clusterPath = top.1.node.clusterPath := by
  obtain ⟨topA, htopA, _, _, hpathA⟩ :=
    addClusterBorders_side_source source w hready
      (List.mem_of_getElem? hna) hsa
  obtain ⟨topB, htopB, _, _, hpathB⟩ :=
    addClusterBorders_side_source source w hready
      (List.mem_of_getElem? hnb) hsb
  obtain ⟨hmemA, hcondA⟩ := List.mem_filter.mp htopA
  obtain ⟨hmemB, hcondB⟩ := List.mem_filter.mp htopB
  have hgetA : source.nodes[topA.2]? = some topA.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmemA
  have hgetB : source.nodes[topB.2]? = some topB.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmemB
  have hbA : topA.1.node.border = -2 := by simpa using hcondA
  have hbB : topB.1.node.border = -2 := by simpa using hcondB
  have hpathAB : topA.1.node.clusterPath = topB.1.node.clusterPath := by
    rw [← hpathA, ← hpathB]
    exact hp
  have heq : topA.2 = topB.2 :=
    hready.2.2.1 topA.2 topB.2 topA.1 topB.1 hgetA hgetB hbA hbB hpathAB
  have hnode : topA.1 = topB.1 := by
    have h1 : source.nodes[topB.2]? = some topA.1 := heq ▸ hgetA
    exact Option.some.inj (h1.symm.trans hgetB)
  exact ⟨topA, htopA, hpathA, by rw [hnode]; exact hpathB⟩

/-- The `BInv` witness for the executed border construction: every emitted
marker is an extra keyed by `(border, clusterPath, rank-entry)` with nodup
keys. This is the offset inversion the rank-injectivity residual needs,
without naming emission offsets explicitly. -/
theorem executed_border_binv {source : Proper} (w : Int)
    (hready : OrderImpl.BorderConstructionReady source) :
    ∃ es : List (ProperNode × Int),
      OrderImpl.BInv source (OrderImpl.addClusterBorders source w) es := by
  obtain ⟨hno, hanch, huniq, hlen, hdum⟩ := hready
  have hmem : ∀ q ∈ source.nodes.zipIdx.filter (fun q => q.1.node.border == -2),
      source.nodes[q.2]? = some q.1 ∧ q.1.node.border = -2 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
    exact ⟨List.mem_zipIdx_iff_getElem?.mp hq1, by simpa using hq2⟩
  have hnd : ((source.nodes.zipIdx.filter
      (fun q => q.1.node.border == -2)).map Prod.snd).Nodup := by
    have h0 : (source.nodes.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' 1 (by omega)
    exact List.Nodup.sublist ((List.filter_sublist).map Prod.snd) h0
  have hpw : (source.nodes.zipIdx.filter
      (fun q => q.1.node.border == -2)).Pairwise
      (fun q q' => q.1.node.clusterPath ≠ q'.1.node.clusterPath) := by
    have h1 : (source.nodes.zipIdx.filter
        (fun q => q.1.node.border == -2)).Pairwise
        (fun q q' => q.2 ≠ q'.2) := by
      have := List.nodup_iff_pairwise_ne.mp hnd
      rwa [List.pairwise_map] at this
    refine List.Pairwise.imp_of_mem ?_ h1
    intro q q' hq hq' hne hpath
    have hq1 := hmem q hq
    have hq2 := hmem q' hq'
    exact hne (huniq q.2 q'.2 q.1 q'.1 hq1.1 hq2.1 hq1.2 hq2.2 hpath)
  obtain ⟨es, hinv⟩ := OrderImpl.borders_fold_binv source w _
    (fun q hq => by
      have := hmem q hq
      exact hanch q.1 (List.mem_of_getElem? this.1) this.2)
    hpw source [] (OrderImpl.binv_base source)
    (fun q _ e he => by simp at he)
  rw [← OrderImpl.addClusterBorders_eq] at hinv
  exact ⟨es, hinv⟩

/-- Canonical cluster path of an executed side marker (copied verbatim). -/
private theorem sideChainCanon {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[decl]? = some box ∧
      na.node.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [decl] := by
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ := componentRun_ranked_source hrun
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun index node hnode => componentCandidate_marker_shape hgraph hnode
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)) :=
    titled_border_ready hkeys hshape hmarkers haligned
  have hcoordinate : (coordinateGraph P labeled).nodes[a]? = some na := by
    rw [hcoord]; exact hna
  have horiginal := coordinateGraph_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal)
      hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases titled_node_origin hkeys hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hkeys top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨_, _, hsrcG⟩ := componentCandidate_nonplain_source hbn (by omega)
      obtain ⟨_, boxG, hboxG, _, hpathG⟩ :=
        measuredGraph_group_origin hgraph hsrcG hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp, hlastG]
      have hdeclEq : bn.decl = decl :=
        Option.some.inj (hnaLast.symm.trans hlast)
      rw [hdeclEq] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hpathG, hdeclEq]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega

/-! ## Field 2: `rank_inj` — two distinct markers of one side chain have
distinct pass ranks.

Route: same side and declaration give the same anchor path
(`shape_chain_uniform`); equal pass ranks give the same layer index
(`rank_orient`, injective in both `k` orientations), hence equal construction
ranks (`layerPositions_spec`); equal construction ranks, same border, same
path give the same `BInv` extra key, and keys are nodup
(`executed_border_binv`), so the indices agree. -/
theorem shapeRankInjResidual {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeRankInjResidual P run side decl pos k := by
  intro u hu w hw hrk
  obtain ⟨na, hna, hba, _, _⟩ := mem_sideChainNodes_forward hu
  obtain ⟨nb, hnb, hbb, _, _⟩ := mem_sideChainNodes_forward hw
  have hLmk : CoordsImpl.Lay (CoordsImpl.mkCtx P.nodeGap (sideBase run) run.layers
      (CoordsImpl.typeOneConflicts (sideBase run) pos) k) :=
    (CoordsImpl.layout_facts
      (marked := CoordsImpl.typeOneConflicts (sideBase run) pos) (k := k) hpos).1
  obtain ⟨lvu, hmlu, hviu⟩ := List.mem_flatten.mp (sideChainNodes_flat hu)
  obtain ⟨lvw, hmlw, hviw⟩ := List.mem_flatten.mp (sideChainNodes_flat hw)
  obtain ⟨iu, hiu⟩ := List.mem_iff_getElem?.mp hmlu
  obtain ⟨iw, hiw⟩ := List.mem_iff_getElem?.mp hmlw
  have hru : (sideCtx P run pos k).rank[u]! =
      (if 2 ≤ k then run.layers.length - 1 - iu else iu) :=
    CoordsImpl.rank_orient hLmk hiu hviu
  have hrw : (sideCtx P run pos k).rank[w]! =
      (if 2 ≤ k then run.layers.length - 1 - iw else iw) :=
    CoordsImpl.rank_orient hLmk hiw hviw
  have hivlt : iu < run.layers.length := (List.getElem?_eq_some_iff.mp hiu).1
  have hiwlt : iw < run.layers.length := (List.getElem?_eq_some_iff.mp hiw).1
  have hiuw : iu = iw := by
    by_cases h2k : 2 ≤ k
    · simp only [h2k, ite_true] at hru hrw
      omega
    · simp only [h2k, ite_false] at hru hrw
      omega
  have hiu' : run.layers[iw]? = some lvu := by
    rw [← hiuw]; exact hiu
  have hluvw : lvu = lvw :=
    Option.some.inj (hiu'.symm.trans hiw)
  obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
  obtain ⟨_, hpos'⟩ := hlp
  obtain ⟨_, hrkLayer, _⟩ := CoordsImpl.layerPositions_spec hpos'
  have hRKu : rk (sideBase run).rank u = (iw : Int) :=
    hrkLayer iw lvw u (by rw [← hluvw]; exact hiu') (by rw [← hluvw]; exact hviu)
  have hRKw : rk (sideBase run).rank w = (iw : Int) :=
    hrkLayer iw lvw w hiw hviw
  obtain ⟨labeled, hcoordL, hready⟩ := shape_ready hgraph hcomp hrun
  have h1 : (sideBase run).rank = run.coordinateProper.rank := rfl
  have h2 : (coordinateGraph P labeled).rank =
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).rank := rfl
  rw [hcoordL] at h2
  have hrankEq : (sideBase run).rank =
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).rank :=
    h1.trans h2
  have hRKc : rk (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).rank u =
      rk (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).rank w := by
    rw [← hrankEq]
    exact hRKu.trans hRKw.symm
  obtain ⟨es, hinv⟩ := executed_border_binv P.clusterBorderW hready
  have haddedU : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes[u]? = some na := by
    have hcoordU : (coordinateGraph P labeled).nodes[u]? = some na := by
      rw [hcoordL]; exact hna
    have hbordU : na.node.border = -1 ∨ na.node.border = 1 := by
      rw [hba]; exact hside
    exact coordinateGraph_side_original hready hcoordU hbordU
  have haddedW : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes[w]? = some nb := by
    have hcoordW : (coordinateGraph P labeled).nodes[w]? = some nb := by
      rw [hcoordL]; exact hnb
    have hbordW : nb.node.border = -1 ∨ nb.node.border = 1 := by
      rw [hbb]; exact hside
    exact coordinateGraph_side_original hready hcoordW hbordW
  have hsideU : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have hsideW : nb.node.border = -1 ∨ nb.node.border = 1 := by
    rw [hbb]; exact hside
  have hN : (titleReservations (sizeProperPorts P labeled)).nodes.length =
      (titleReservations (sizeProperPorts P labeled)).rank.length :=
    hready.2.2.2.1
  rcases OrderImpl.binv_lookup hinv haddedU with ⟨_, hnodeU⟩ | ⟨hleU, ea, hea, heqU⟩
  · have hmemU : na ∈ (titleReservations (sizeProperPorts P labeled)).nodes :=
      List.mem_of_getElem? hnodeU
    rcases hsideU with hs | hs
    · exact ((hready.1 na hmemU).1 hs).elim
    · exact ((hready.1 na hmemU).2 hs).elim
  rcases OrderImpl.binv_lookup hinv haddedW with ⟨_, hnodeW⟩ | ⟨hleW, eb, heb, heqW⟩
  · have hmemW : nb ∈ (titleReservations (sizeProperPorts P labeled)).nodes :=
      List.mem_of_getElem? hnodeW
    rcases hsideW with hs | hs
    · exact ((hready.1 nb hmemW).1 hs).elim
    · exact ((hready.1 nb hmemW).2 hs).elim
  have huni := shape_chain_uniform hgraph hcomp hrun hside u hu w hw
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hgetU : (sideBase run).nodes.getD u default = na := by
    rw [hnodes]; exact borderEnv_getD_of_get? hna
  have hgetW : (sideBase run).nodes.getD w default = nb := by
    rw [hnodes]; exact borderEnv_getD_of_get? hnb
  have hpath : na.node.clusterPath = nb.node.clusterPath := by
    rw [hgetU, hgetW] at huni
    exact huni
  have hlenEq : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes.length =
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).rank.length := by
    rw [hinv.nodes, hinv.rank, List.length_append, List.length_append,
      List.length_map, List.length_map, hN]
  have hub : u < (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).rank.length := by
    have hulen : u < (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).nodes.length :=
      (List.getElem?_eq_some_iff.mp haddedU).1
    omega
  have hwb : w < (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).rank.length := by
    have hwlen : w < (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).nodes.length :=
      (List.getElem?_eq_some_iff.mp haddedW).1
    omega
  have hgu : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).rank[u]? = some ea.2 := by
    have hle : (titleReservations (sizeProperPorts P labeled)).rank.length ≤ u := by
      rw [← hN]; exact hleU
    rw [hinv.rank, List.getElem?_append_right hle, ← hN, List.getElem?_map, hea,
      Option.map_some]
  have hgw : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).rank[w]? = some eb.2 := by
    have hle : (titleReservations (sizeProperPorts P labeled)).rank.length ≤ w := by
      rw [← hN]; exact hleW
    rw [hinv.rank, List.getElem?_append_right hle, ← hN, List.getElem?_map, heb,
      Option.map_some]
  have hrEntry : ea.2 = eb.2 := by
    have hrw' : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).rank[u] =
        (OrderImpl.addClusterBorders (titleReservations
          (sizeProperPorts P labeled)) P.clusterBorderW).rank[w] := by
      rw [← RankImpl.rk_of_lt hub, ← RankImpl.rk_of_lt hwb]
      exact hRKc
    have e1 : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).rank[u] = ea.2 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hub]; exact hgu)
    have e2 : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).rank[w] = eb.2 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hwb]; exact hgw)
    exact e1.symm.trans (hrw'.trans e2)
  have hkey : OrderImpl.extraKey ea = OrderImpl.extraKey eb := by
    have hb : ea.1.node.border = eb.1.node.border := by
      rw [heqU, heqW, hba, hbb]
    have hp : ea.1.node.clusterPath = eb.1.node.clusterPath := by
      rw [heqU, heqW]; exact hpath
    unfold OrderImpl.extraKey
    simp only [Prod.mk.injEq]
    exact ⟨hb, hp, hrEntry⟩
  have hinj : u - (titleReservations (sizeProperPorts P labeled)).nodes.length =
      w - (titleReservations (sizeProperPorts P labeled)).nodes.length := by
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨hai, hax⟩ := List.getElem?_eq_some_iff.mp hea
    obtain ⟨hbi, hbx⟩ := List.getElem?_eq_some_iff.mp heb
    have hpa := List.pairwise_iff_getElem.mp hinv.keys
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hcon := hpa _ _ (by simpa using hai) (by simpa using hbi) hlt
      simp [hax, hbx, hkey] at hcon
    · have hcon := hpa _ _ (by simpa using hbi) (by simpa using hai) hlt
      simp [hax, hbx, hkey] at hcon
  omega

/-! ## Field 3: `rank_consec` — the ranks of one side chain form an interval.

Route: pass ranks transport to layer indices (`rank_orient`, injective in
both `k` orientations); layer indices are construction ranks
(`layerPositions_spec`); the shared anchor (same path gives the same `-2`
index, and the same path gives the same bottom) bounds every chain rank in
one interval; a gap would supply a middle rank whose emitted marker
(`coordinateGraph_rank_pair`) is a chain marker with strictly intermediate
pass rank, contradicting the no-between hypothesis. -/
theorem shapeRankConsec {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ∀ u ∈ sideChainNodes P run side decl, ∀ v ∈ sideChainNodes P run side decl,
      (sideCtx P run pos k).rank[u]! < (sideCtx P run pos k).rank[v]! →
      (∀ x ∈ sideChainNodes P run side decl,
        ¬ ((sideCtx P run pos k).rank[u]! < (sideCtx P run pos k).rank[x]! ∧
          (sideCtx P run pos k).rank[x]! < (sideCtx P run pos k).rank[v]!)) →
      (sideCtx P run pos k).rank[u]! + 1 = (sideCtx P run pos k).rank[v]! := by
  intro u hu v hv hlt hnone
  obtain ⟨na, hna, hba, _, hla⟩ := mem_sideChainNodes_forward hu
  obtain ⟨nb, hnb, hbb, _, _⟩ := mem_sideChainNodes_forward hv
  have hLmk : CoordsImpl.Lay (CoordsImpl.mkCtx P.nodeGap (sideBase run) run.layers
      (CoordsImpl.typeOneConflicts (sideBase run) pos) k) :=
    (CoordsImpl.layout_facts
      (marked := CoordsImpl.typeOneConflicts (sideBase run) pos) (k := k) hpos).1
  obtain ⟨lvu, hmlu, hviu⟩ := List.mem_flatten.mp (sideChainNodes_flat hu)
  obtain ⟨lvw, hmlw, hviw⟩ := List.mem_flatten.mp (sideChainNodes_flat hv)
  obtain ⟨iu, hiu⟩ := List.mem_iff_getElem?.mp hmlu
  obtain ⟨iw, hiw⟩ := List.mem_iff_getElem?.mp hmlw
  have hivlt : iu < run.layers.length := (List.getElem?_eq_some_iff.mp hiu).1
  have hiwlt : iw < run.layers.length := (List.getElem?_eq_some_iff.mp hiw).1
  have hru : (sideCtx P run pos k).rank[u]! =
      (if 2 ≤ k then run.layers.length - 1 - iu else iu) :=
    CoordsImpl.rank_orient hLmk hiu hviu
  have hrw : (sideCtx P run pos k).rank[v]! =
      (if 2 ≤ k then run.layers.length - 1 - iw else iw) :=
    CoordsImpl.rank_orient hLmk hiw hviw
  obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
  obtain ⟨_, hpos'⟩ := hlp
  obtain ⟨_, hrkLayer, hcov⟩ := CoordsImpl.layerPositions_spec hpos'
  have hRKu : rk (sideBase run).rank u = (iu : Int) :=
    hrkLayer iu lvu u hiu hviu
  have hRKw : rk (sideBase run).rank v = (iw : Int) :=
    hrkLayer iw lvw v hiw hviw
  obtain ⟨labeled, hcoordL, hready⟩ := shape_ready hgraph hcomp hrun
  have h1 : (sideBase run).rank = run.coordinateProper.rank := rfl
  have hsb : (sideBase run).rank = (coordinateGraph P labeled).rank := by
    rw [h1, ← hcoordL]
  have haddedU : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes[u]? = some na := by
    have hcoordU : (coordinateGraph P labeled).nodes[u]? = some na := by
      rw [hcoordL]; exact hna
    have hbordU : na.node.border = -1 ∨ na.node.border = 1 := by
      rw [hba]; exact hside
    exact coordinateGraph_side_original hready hcoordU hbordU
  have haddedW : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes[v]? = some nb := by
    have hcoordW : (coordinateGraph P labeled).nodes[v]? = some nb := by
      rw [hcoordL]; exact hnb
    have hbordW : nb.node.border = -1 ∨ nb.node.border = 1 := by
      rw [hbb]; exact hside
    exact coordinateGraph_side_original hready hcoordW hbordW
  have hsideU : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have hsideW : nb.node.border = -1 ∨ nb.node.border = 1 := by
    rw [hbb]; exact hside
  have huni := shape_chain_uniform hgraph hcomp hrun hside u hu v hv
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hgetU : (sideBase run).nodes.getD u default = na := by
    rw [hnodes]; exact borderEnv_getD_of_get? hna
  have hgetW : (sideBase run).nodes.getD v default = nb := by
    rw [hnodes]; exact borderEnv_getD_of_get? hnb
  have hpath : na.node.clusterPath = nb.node.clusterPath := by
    rw [hgetU, hgetW] at huni
    exact huni
  obtain ⟨topA, htopA, hpathA, hpathB⟩ := chainMarkers_shareAnchor
    P.clusterBorderW hready haddedU haddedW hsideU hsideW hpath
  have hcoordU : (coordinateGraph P labeled).nodes[u]? = some na := by
    rw [hcoordL]; exact hna
  have hcoordW : (coordinateGraph P labeled).nodes[v]? = some nb := by
    rw [hcoordL]; exact hnb
  obtain ⟨topU, htopU, bottomU, hfindU, hpathU, _, hloU, hhiU⟩ :=
    coordinateGraph_side_rank_bounds hready hcoordU hsideU
  obtain ⟨topV, htopV, bottomV, hfindV, hpathV, _, hloV, hhiV⟩ :=
    coordinateGraph_side_rank_bounds hready hcoordW hsideW
  obtain ⟨hmemA, hcondA⟩ := List.mem_filter.mp htopA
  obtain ⟨hmemU, hcondU⟩ := List.mem_filter.mp htopU
  obtain ⟨hmemV, hcondV⟩ := List.mem_filter.mp htopV
  have hgetA : (titleReservations (sizeProperPorts P labeled)).nodes[topA.2]? =
      some topA.1 := List.mem_zipIdx_iff_getElem?.mp hmemA
  have hgetU' : (titleReservations (sizeProperPorts P labeled)).nodes[topU.2]? =
      some topU.1 := List.mem_zipIdx_iff_getElem?.mp hmemU
  have hgetV' : (titleReservations (sizeProperPorts P labeled)).nodes[topV.2]? =
      some topV.1 := List.mem_zipIdx_iff_getElem?.mp hmemV
  have hbA : topA.1.node.border = -2 := by simpa using hcondA
  have hbU : topU.1.node.border = -2 := by simpa using hcondU
  have hbV : topV.1.node.border = -2 := by simpa using hcondV
  have hpathUA : topU.1.node.clusterPath = topA.1.node.clusterPath :=
    hpathU.symm.trans hpathA
  have hpathVA : topV.1.node.clusterPath = topA.1.node.clusterPath :=
    hpathV.symm.trans hpathB
  have heqU : topU.2 = topA.2 :=
    titled_anchor_unique hready hgetU' hgetA hbU hbA hpathUA
  have heqV : topV.2 = topA.2 :=
    titled_anchor_unique hready hgetV' hgetA hbV hbA hpathVA
  rw [heqU] at hloU
  rw [hpathUA] at hfindU
  rw [heqV] at hloV
  rw [hpathVA] at hfindV
  have hbotEq : bottomU = bottomV :=
    Option.some.inj (hfindU.symm.trans hfindV)
  rw [← hbotEq] at hhiV
  have hcuN : (rk (coordinateGraph P labeled).rank u).toNat = iu := by
    have hcu : rk (coordinateGraph P labeled).rank u = (iu : Int) := by
      rw [← hsb]; exact hRKu
    omega
  have hcvN : (rk (coordinateGraph P labeled).rank v).toNat = iw := by
    have hcv : rk (coordinateGraph P labeled).rank v = (iw : Int) := by
      rw [← hsb]; exact hRKw
    omega
  have hbU' : (rk (titleReservations (sizeProperPorts P labeled)).rank
      topA.2).toNat ≤ iu ∧
      iu ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank
        bottomU.2).toNat := by omega
  have hbV' : (rk (titleReservations (sizeProperPorts P labeled)).rank
      topA.2).toNat ≤ iw ∧
      iw ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank
        bottomU.2).toNat := by omega
  have htopmem : topA ∈ (titleReservations
      (sizeProperPorts P labeled)).nodes.zipIdx :=
    (List.mem_filter.mp htopA).1
  have hborder : topA.1.node.border = -2 := by
    simpa using (List.mem_filter.mp htopA).2
  have hmiddle : ∀ mid : Nat, (rk (titleReservations
        (sizeProperPorts P labeled)).rank topA.2).toNat ≤ mid →
      mid ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank
        bottomU.2).toNat →
      ∃ m, m ∈ sideChainNodes P run side decl ∧
        (sideCtx P run pos k).rank[m]! =
          (if 2 ≤ k then run.layers.length - 1 - mid else mid) := by
    intro mid hmidlo hmidhi
    obtain ⟨mleft, mright, hmln, hmrn, hmlr, hmrr⟩ :=
      coordinateGraph_rank_pair P _ hready.2.2.2.1 htopmem hborder hfindU
        hmidlo hmidhi
    have hlastA : topA.1.node.clusterPath.getLast? = some decl := by
      rw [← hpathA]; exact hla
    obtain ⟨m, hmemM, hmrank⟩ :
        ∃ m, m ∈ sideChainNodes P run side decl ∧
          (coordinateGraph P labeled).rank[m]? = some ((mid : Nat) : Int) := by
      rcases hside with hneg | hposS
      · refine ⟨mleft, ?_, hmlr⟩
        rw [hcoordL] at hmln
        rw [mem_sideChainNodes hpos]
        refine ⟨_, hmln, ?_, ?_, ?_⟩
        · rw [hneg]
        · rfl
        · exact hlastA
      · refine ⟨mright, ?_, hmrr⟩
        rw [hcoordL] at hmrn
        rw [mem_sideChainNodes hpos]
        refine ⟨_, hmrn, ?_, ?_, ?_⟩
        · rw [hposS]
        · rfl
        · exact hlastA
    have hmrankS : (sideBase run).rank[m]? = some ((mid : Nat) : Int) := by
      rw [hsb]; exact hmrank
    have hmlenR : m < (sideBase run).rank.length :=
      (List.getElem?_eq_some_iff.mp hmrankS).1
    have hRKm : rk (sideBase run).rank m = ((mid : Nat) : Int) := by
      rw [RankImpl.rk_of_lt hmlenR]
      exact Option.some.inj
        ((List.getElem?_eq_getElem hmlenR).symm.trans hmrankS)
    have hmlt : m < (sideBase run).nodes.length := by
      obtain ⟨nm, hnm, _, _, _⟩ := mem_sideChainNodes_forward hmemM
      have hb : m < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp hnm).1
      rw [hnodes]; exact hb
    obtain ⟨lm, hmlm, hvim⟩ := List.mem_flatten.mp (hcov m hmlt)
    obtain ⟨im, him⟩ := List.mem_iff_getElem?.mp hmlm
    have hRi : rk (sideBase run).rank m = (im : Int) :=
      hrkLayer im lm m him hvim
    have himEq : im = mid := by omega
    have hpm : (sideCtx P run pos k).rank[m]! =
        (if 2 ≤ k then run.layers.length - 1 - im else im) :=
      CoordsImpl.rank_orient hLmk him hvim
    rw [himEq] at hpm
    exact ⟨m, hmemM, hpm⟩
  by_cases h2k : 2 ≤ k
  · simp only [h2k, ite_true] at hru hrw
    by_cases heq : (sideCtx P run pos k).rank[u]! + 1 =
        (sideCtx P run pos k).rank[v]!
    · exact heq
    · have hge : iu ≥ iw + 2 := by omega
      obtain ⟨m, hmemM, hpm⟩ := hmiddle (iw + 1) (by omega) (by omega)
      simp only [h2k, ite_true] at hpm
      have hlt1 : (sideCtx P run pos k).rank[u]! <
          (sideCtx P run pos k).rank[m]! := by omega
      have hlt2 : (sideCtx P run pos k).rank[m]! <
          (sideCtx P run pos k).rank[v]! := by omega
      exact (hnone m hmemM ⟨hlt1, hlt2⟩).elim
  · simp only [h2k, ite_false] at hru hrw
    by_cases heq : (sideCtx P run pos k).rank[u]! + 1 =
        (sideCtx P run pos k).rank[v]!
    · exact heq
    · have hge : iw ≥ iu + 2 := by omega
      obtain ⟨m, hmemM, hpm⟩ := hmiddle (iu + 1) (by omega) (by omega)
      simp only [h2k, ite_false] at hpm
      have hlt1 : (sideCtx P run pos k).rank[u]! <
          (sideCtx P run pos k).rank[m]! := by omega
      have hlt2 : (sideCtx P run pos k).rank[m]! <
          (sideCtx P run pos k).rank[v]! := by omega
      exact (hnone m hmemM ⟨hlt1, hlt2⟩).elim

/-! ## Field 5: `incident_border` — links join consecutive markers.

Route: the inner fold appends exactly the `borderLinks` blocks
(`borderInner_fold_edges_range`); a positive-step block joins consecutive
same-side markers (`borderInner_link_endpoints_are_markers`); the outer fold
preserves the link form (`addClusterBorders_links_form`); a link touching a
chain marker reaches another chain marker (`shapeIncidentLinksOfForm`).
Titled edges need endpoint bounds (`BorderInnerTitledBoundResidual`), proved
for the executed source by `borderInnerTitledBound_executed`. -/
theorem borderInner_fold_nodes_append (q : ProperNode × Nat) (w : Int) (lo : Nat)
    (count : Nat) (state : Proper) :
    ∃ extra : List ProperNode,
      ((List.range count).foldl (OrderImpl.borderInner q w lo) state).nodes =
        state.nodes ++ extra := by
  have hnodes : ∀ (s : Proper) (k : Nat),
      (OrderImpl.borderInner q w lo s k).nodes =
        s.nodes ++ [OrderImpl.borderLeft q w, OrderImpl.borderRight q w] :=
    fun s k => rfl
  induction count with
  | zero => exact ⟨[], by simp⟩
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨extra, he⟩ := ih
    exact ⟨extra ++ [OrderImpl.borderLeft q w, OrderImpl.borderRight q w], by
      rw [hnodes, he, List.append_assoc]⟩

theorem borderInner_fold_edges_range (q : ProperNode × Nat) (w : Int) (lo : Nat)
    (count : Nat) (state : Proper) :
    ((List.range count).foldl (OrderImpl.borderInner q w lo) state).edges =
      state.edges ++ (List.range count).flatMap fun off =>
        OrderImpl.borderLinks (state.nodes.length + 2 * off) q.1.node.decl off := by
  have hedge : ∀ (s : Proper) (k : Nat),
      (OrderImpl.borderInner q w lo s k).edges =
        s.edges ++ OrderImpl.borderLinks s.nodes.length q.1.node.decl k :=
    fun s k => rfl
  have hlen : ∀ (n : Nat),
      ((List.range n).foldl (OrderImpl.borderInner q w lo) state).nodes.length =
        state.nodes.length + 2 * n := by
    intro n
    have h := (borderInner_fold_lengths q w lo (List.range n) state).1
    simp only [List.length_range] at h
    exact h
  induction count with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hedge, hlen, ih, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]

/-- Link form: the edge joins consecutive same-side emitted markers. -/
def IsLinkOut (out : Proper) (e : ProperEdge) : Prop :=
  ∃ (q : ProperNode × Nat) (w : Int) (m : Nat),
    e.synthetic = true ∧ e.decl = q.1.node.decl ∧
      ((e.tail = m ∧ e.head = m + 2 ∧
        out.nodes[m]? = some (OrderImpl.borderLeft q w) ∧
        out.nodes[m + 2]? = some (OrderImpl.borderLeft q w)) ∨
       (e.tail = m + 1 ∧ e.head = m + 3 ∧
        out.nodes[m + 1]? = some (OrderImpl.borderRight q w) ∧
        out.nodes[m + 3]? = some (OrderImpl.borderRight q w)))

/-- Link-form lookups persist across appended nodes. -/
theorem isLinkOut_transfer {out newOut : Proper} (extra : List ProperNode)
    (hN : newOut.nodes = out.nodes ++ extra)
    {e : ProperEdge} (h : IsLinkOut out e) : IsLinkOut newOut e := by
  obtain ⟨q, w, m, hsyn, hdecl, hlink⟩ := h
  refine ⟨q, w, m, hsyn, hdecl, ?_⟩
  rcases hlink with ⟨ht, hh, h1, h2⟩ | ⟨ht, hh, h1, h2⟩
  · left
    refine ⟨ht, hh, ?_, ?_⟩
    · have hb : m < out.nodes.length :=
        (List.getElem?_eq_some_iff.mp h1).1
      rw [hN]
      exact (List.getElem?_append_left hb).trans h1
    · have hb : m + 2 < out.nodes.length :=
        (List.getElem?_eq_some_iff.mp h2).1
      rw [hN]
      exact (List.getElem?_append_left hb).trans h2
  · right
    refine ⟨ht, hh, ?_, ?_⟩
    · have hb : m + 1 < out.nodes.length :=
        (List.getElem?_eq_some_iff.mp h1).1
      rw [hN]
      exact (List.getElem?_append_left hb).trans h1
    · have hb : m + 3 < out.nodes.length :=
        (List.getElem?_eq_some_iff.mp h2).1
      rw [hN]
      exact (List.getElem?_append_left hb).trans h2

/-- Every non-titled edge of the border construction is a consecutive
same-side link. -/
theorem addClusterBorders_links_form (source : Proper) (w : Int)
    (hlen : source.nodes.length = source.rank.length) :
    ∀ e ∈ (OrderImpl.addClusterBorders source w).edges,
      e ∈ source.edges ∨ IsLinkOut (OrderImpl.addClusterBorders source w) e := by
  rw [OrderImpl.addClusterBorders_eq]
  have step : ∀ (out : Proper), out.nodes.length = out.rank.length →
      (∀ e ∈ out.edges, e ∈ source.edges ∨ IsLinkOut out e) →
      ∀ q ∈ (source.nodes.zipIdx.filter fun q => q.1.node.border == -2),
      (OrderImpl.borderStep source w out q).nodes.length =
        (OrderImpl.borderStep source w out q).rank.length ∧
      ∀ e ∈ (OrderImpl.borderStep source w out q).edges,
        e ∈ source.edges ∨
          IsLinkOut (OrderImpl.borderStep source w out q) e := by
    intro out hal hprop q _
    cases hbot : ((source.nodes.zipIdx.find? fun b =>
        b.1.node.border == 2 && b.1.node.clusterPath == q.1.node.clusterPath).map
        (·.2)) with
    | none =>
      have hstep : OrderImpl.borderStep source w out q = out := by
        unfold OrderImpl.borderStep
        rw [hbot]
      rw [hstep]
      exact ⟨hal, hprop⟩
    | some bot =>
      have hstep : OrderImpl.borderStep source w out q =
          (List.range ((rk source.rank bot).toNat + 1 -
            (rk source.rank q.2).toNat)).foldl
            (OrderImpl.borderInner q w (rk source.rank q.2).toNat) out := by
        unfold OrderImpl.borderStep
        rw [hbot]
      have hlen' : ((List.range ((rk source.rank bot).toNat + 1 -
          (rk source.rank q.2).toNat)).foldl
          (OrderImpl.borderInner q w (rk source.rank q.2).toNat)
          out).nodes.length =
          ((List.range ((rk source.rank bot).toNat + 1 -
            (rk source.rank q.2).toNat)).foldl
            (OrderImpl.borderInner q w (rk source.rank q.2).toNat)
            out).rank.length := by
        obtain ⟨hnN, hnR⟩ := borderInner_fold_lengths q w
          (rk source.rank q.2).toNat
          (List.range ((rk source.rank bot).toNat + 1 -
            (rk source.rank q.2).toNat)) out
        simp only [List.length_range] at hnN hnR
        omega
      rw [hstep]
      refine ⟨hlen', ?_⟩
      obtain ⟨extraN, hNe⟩ :=
        borderInner_fold_nodes_append q w (rk source.rank q.2).toNat
          ((rk source.rank bot).toNat + 1 - (rk source.rank q.2).toNat) out
      have hE := borderInner_fold_edges_range q w (rk source.rank q.2).toNat
        ((rk source.rank bot).toNat + 1 - (rk source.rank q.2).toNat) out
      intro e he
      rw [hE] at he
      rcases List.mem_append.mp he with hold | hnew
      · rcases hprop e hold with hs | hlink
        · exact Or.inl hs
        · exact Or.inr (isLinkOut_transfer extraN hNe hlink)
      · rw [List.mem_flatMap] at hnew
        obtain ⟨off, hoffmem, hmem⟩ := hnew
        have hoff : off <
            (rk source.rank bot).toNat + 1 - (rk source.rank q.2).toNat :=
          List.mem_range.mp hoffmem
        by_cases h0 : off = 0
        · subst h0
          have hnil : OrderImpl.borderLinks (out.nodes.length + 2 * 0)
              q.1.node.decl 0 = [] := rfl
          rw [hnil] at hmem
          simp at hmem
        · have hpos : 0 < off := by omega
          have hsyn : e.synthetic = true :=
            OrderImpl.borderLinks_synthetic _ _ _ e hmem
          have hmark := borderInner_link_endpoints_are_markers q w
            (rk source.rank q.2).toNat out hal
            ((rk source.rank bot).toNat + 1 - (rk source.rank q.2).toNat)
            off hoff hpos hmem
          rcases borderInner_links_endpoints _ _ _ hpos hmem with
            ⟨htL, hhL, hd⟩ | ⟨htR, hhR, hd⟩
          · rcases hmark with ⟨_, _, h1, h2⟩ | ⟨ht', _, _, _⟩
            · have hm : out.nodes.length + 2 * off - 2 + 2 =
                  out.nodes.length + 2 * off := by omega
              exact Or.inr ⟨q, w, out.nodes.length + 2 * off - 2, hsyn, hd,
                Or.inl ⟨htL, by omega, by rw [← htL]; exact h1,
                  by rw [hm, ← hhL]; exact h2⟩⟩
            · exact (by omega : False).elim
          · rcases hmark with ⟨ht', _, _, _⟩ | ⟨_, _, h1, h2⟩
            · exact (by omega : False).elim
            · have hm1 : out.nodes.length + 2 * off - 2 + 1 = e.tail := by omega
              have hm3 : out.nodes.length + 2 * off - 2 + 3 = e.head := by omega
              exact Or.inr ⟨q, w, out.nodes.length + 2 * off - 2, hsyn, hd,
                Or.inr ⟨by omega, by omega, by rw [hm1]; exact h1,
                  by rw [hm3]; exact h2⟩⟩
  have hfold := OrderImpl.foldl_inv
    (fun out : Proper => out.nodes.length = out.rank.length ∧
      ∀ e ∈ out.edges, e ∈ source.edges ∨ IsLinkOut out e)
    (OrderImpl.borderStep source w)
    (source.nodes.zipIdx.filter fun q => q.1.node.border == -2)
    source
    ⟨hlen, fun e he => Or.inl he⟩
    (fun out ⟨hal, hprop⟩ q hq => step out hal hprop q hq)
  exact hfold.2

/-- A `borderLinks` edge touching a chain marker reaches another chain
marker: both ends are consecutive same-side markers. -/
theorem shapeIncidentLinksOfForm {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (_hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (_hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {_k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {labeled : Proper}
    (hcoordL : coordinateGraph P labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)))
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl)
    {e : ProperEdge}
    (hlink : IsLinkOut (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW) e)
    (htouch : e.tail = v ∨ e.head = v) :
    CoordsImpl.borderChain (sideBase run) e = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd e v = u ∧ u ≠ v := by
  obtain ⟨na, hna, hba, hwa, hla⟩ := mem_sideChainNodes_forward hv
  have hcoordV : (coordinateGraph P labeled).nodes[v]? = some na := by
    rw [hcoordL]; exact hna
  have hbordV : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have haddedV : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes[v]? = some na :=
    coordinateGraph_side_original hready hcoordV hbordV
  obtain ⟨q, w', m, _, _, hform⟩ := hlink
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hSmL : ∀ (idx : Nat) (h : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).nodes[idx]? =
          some (OrderImpl.borderLeft q w')),
      (sideBase run).nodes[idx]? = some (OrderImpl.borderLeft q w') := by
    intro idx h
    have hLm : (coordinateGraph P labeled).nodes[idx]? =
        some (OrderImpl.borderLeft q w') :=
      coordinateGraph_side_record h rfl (Or.inl rfl)
    rw [hnodes, ← hcoordL]; exact hLm
  have hSmR : ∀ (idx : Nat) (h : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).nodes[idx]? =
          some (OrderImpl.borderRight q w')),
      (sideBase run).nodes[idx]? = some (OrderImpl.borderRight q w') := by
    intro idx h
    have hLm : (coordinateGraph P labeled).nodes[idx]? =
        some (OrderImpl.borderRight q w') :=
      coordinateGraph_side_record h rfl (Or.inr rfl)
    rw [hnodes, ← hcoordL]; exact hLm
  have hC1L : ((OrderImpl.borderLeft q w').node.border == -1 ||
      (OrderImpl.borderLeft q w').node.border == 1) = true := by
    show (((-1 : Int) == -1) || ((-1 : Int) == 1)) = true
    decide
  have hC1R : ((OrderImpl.borderRight q w').node.border == -1 ||
      (OrderImpl.borderRight q w').node.border == 1) = true := by
    show (((1 : Int) == -1) || ((1 : Int) == 1)) = true
    decide
  have e2L : ((OrderImpl.borderLeft q w').node.border ==
      (OrderImpl.borderLeft q w').node.border) = true := by
    show (((-1 : Int) == (-1 : Int))) = true
    decide
  have e2R : ((OrderImpl.borderRight q w').node.border ==
      (OrderImpl.borderRight q w').node.border) = true := by
    show (((1 : Int) == (1 : Int))) = true
    decide
  have e3L : ((OrderImpl.borderLeft q w').node.clusterPath ==
      (OrderImpl.borderLeft q w').node.clusterPath) = true := by simp
  have e3R : ((OrderImpl.borderRight q w').node.clusterPath ==
      (OrderImpl.borderRight q w').node.clusterPath) = true := by simp
  rcases hform with ⟨ht, hh, h1, h2⟩ | ⟨ht, hh, h1, h2⟩
  · -- left link joins two left markers
    have hbc : CoordsImpl.borderChain (sideBase run) e = true := by
      have htail : (sideBase run).nodes[e.tail]? =
          some (OrderImpl.borderLeft q w') := by
        rw [ht]; exact hSmL m h1
      have hhead : (sideBase run).nodes[e.head]? =
          some (OrderImpl.borderLeft q w') := by
        rw [hh]; exact hSmL (m + 2) h2
      unfold CoordsImpl.borderChain
      simp only [htail, hhead]
      rw [hC1L, e2L, e3L]; rfl
    rcases htouch with htv | hhv
    · -- v is the tail; u is the head
      have hvm : v = m := by omega
      have hrecV : na = OrderImpl.borderLeft q w' := by
        rw [hvm] at haddedV
        exact Option.some.inj (haddedV.symm.trans h1)
      have hsideEq : side = -1 := by rw [← hba, hrecV]; rfl
      have hW : w' = P.clusterBorderW := by
        have h1w : na.node.w = w' := by rw [hrecV]; rfl
        exact h1w.symm.trans hwa
      have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
        have hpq : na.node.clusterPath = q.1.node.clusterPath := by rw [hrecV]; rfl
        rw [← hpq]; exact hla
      have hmemU : m + 2 ∈ sideChainNodes P run side decl := by
        rw [mem_sideChainNodes hpos]
        have hUm : run.coordinateProper.nodes[m + 2]? =
            some (OrderImpl.borderLeft q w') := by
          have hLm : (coordinateGraph P labeled).nodes[m + 2]? =
              some (OrderImpl.borderLeft q w') :=
            coordinateGraph_side_record h2 rfl (Or.inl rfl)
          rw [← hcoordL]; exact hLm
        exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
      have hother : CoordsImpl.otherEnd e v = m + 2 := by
        have hcond : (e.tail == v) = true := by rw [htv]; exact beq_self_eq_true' _
        unfold CoordsImpl.otherEnd
        rw [hcond]
        exact hh
      exact ⟨hbc, m + 2, hmemU, hother, by omega⟩
    · -- v is the head; u is the tail
      have hvm : v = m + 2 := by omega
      have hrecV : na = OrderImpl.borderLeft q w' := by
        rw [hvm] at haddedV
        exact Option.some.inj (haddedV.symm.trans h2)
      have hsideEq : side = -1 := by
        rw [← hba, hrecV]
        rfl
      have hW : w' = P.clusterBorderW := by
        have h1w : na.node.w = w' := by
          rw [hrecV]
          rfl
        exact h1w.symm.trans hwa
      have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
        have hpq : na.node.clusterPath = q.1.node.clusterPath := by
          rw [hrecV]
          rfl
        rw [← hpq]; exact hla
      have hmemU : m ∈ sideChainNodes P run side decl := by
        rw [mem_sideChainNodes hpos]
        have hUm : run.coordinateProper.nodes[m]? =
            some (OrderImpl.borderLeft q w') := by
          have hLm : (coordinateGraph P labeled).nodes[m]? =
              some (OrderImpl.borderLeft q w') :=
            coordinateGraph_side_record h1 rfl (Or.inl rfl)
          rw [← hcoordL]; exact hLm
        exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
      have hother : CoordsImpl.otherEnd e v = m := by
        have hne : e.tail ≠ v := by omega
        have hcond : (e.tail == v) = false := beq_eq_false_iff_ne.mpr hne
        unfold CoordsImpl.otherEnd
        rw [hcond]
        exact ht
      exact ⟨hbc, m, hmemU, hother, by omega⟩
  · -- right link joins two right markers
    have hbc : CoordsImpl.borderChain (sideBase run) e = true := by
      have htail : (sideBase run).nodes[e.tail]? =
          some (OrderImpl.borderRight q w') := by
        rw [ht]; exact hSmR (m + 1) h1
      have hhead : (sideBase run).nodes[e.head]? =
          some (OrderImpl.borderRight q w') := by
        rw [hh]; exact hSmR (m + 1 + 2) h2
      unfold CoordsImpl.borderChain
      simp only [htail, hhead]
      rw [hC1R, e2R, e3R]; rfl
    rcases htouch with htv | hhv
    · have hvm : v = m + 1 := by omega
      have hrecV : na = OrderImpl.borderRight q w' := by
        rw [hvm] at haddedV
        exact Option.some.inj (haddedV.symm.trans h1)
      have hsideEq : side = 1 := by
        rw [← hba, hrecV]
        rfl
      have hW : w' = P.clusterBorderW := by
        have h1w : na.node.w = w' := by
          rw [hrecV]
          rfl
        exact h1w.symm.trans hwa
      have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
        have hpq : na.node.clusterPath = q.1.node.clusterPath := by
          rw [hrecV]
          rfl
        rw [← hpq]; exact hla
      have hmemU : m + 1 + 2 ∈ sideChainNodes P run side decl := by
        rw [mem_sideChainNodes hpos]
        have hUm : run.coordinateProper.nodes[m + 1 + 2]? =
            some (OrderImpl.borderRight q w') := by
          have hLm : (coordinateGraph P labeled).nodes[m + 1 + 2]? =
              some (OrderImpl.borderRight q w') :=
            coordinateGraph_side_record h2 rfl (Or.inr rfl)
          rw [← hcoordL]; exact hLm
        exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
      have hother : CoordsImpl.otherEnd e v = m + 1 + 2 := by
        have hcond : (e.tail == v) = true := by
          rw [htv]; exact beq_self_eq_true' _
        unfold CoordsImpl.otherEnd
        rw [hcond]
        exact hh
      exact ⟨hbc, m + 1 + 2, hmemU, hother, by omega⟩
    · have hvm : v = m + 1 + 2 := by omega
      have hrecV : na = OrderImpl.borderRight q w' := by
        rw [hvm] at haddedV
        exact Option.some.inj (haddedV.symm.trans h2)
      have hsideEq : side = 1 := by
        rw [← hba, hrecV]
        rfl
      have hW : w' = P.clusterBorderW := by
        have h1w : na.node.w = w' := by
          rw [hrecV]
          rfl
        exact h1w.symm.trans hwa
      have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
        have hpq : na.node.clusterPath = q.1.node.clusterPath := by
          rw [hrecV]
          rfl
        rw [← hpq]; exact hla
      have hmemU : m + 1 ∈ sideChainNodes P run side decl := by
        rw [mem_sideChainNodes hpos]
        have hUm : run.coordinateProper.nodes[m + 1]? =
            some (OrderImpl.borderRight q w') := by
          have hLm : (coordinateGraph P labeled).nodes[m + 1]? =
              some (OrderImpl.borderRight q w') :=
            coordinateGraph_side_record h1 rfl (Or.inr rfl)
          rw [← hcoordL]; exact hLm
        exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
      have hother : CoordsImpl.otherEnd e v = m + 1 := by
        have hne : e.tail ≠ v := by omega
        have hcond : (e.tail == v) = false := beq_eq_false_iff_ne.mpr hne
        unfold CoordsImpl.otherEnd
        rw [hcond]
        exact ht
      exact ⟨hbc, m + 1, hmemU, hother, by omega⟩

/-- Titled-edge half hypothesis of `ShapeIncidentInheritedResidual`:
titled edges never reach the appended markers. Proved for the executed source
by `borderInnerTitledBound_executed` (`ShapeIncidentInheritedProof`), which
`shapeIncidentInherited_executed` applies below. -/
def BorderInnerTitledBoundResidual (source : Proper) : Prop :=
  ∀ e ∈ source.edges, e.tail < source.nodes.length ∧ e.head < source.nodes.length

/-- The inherited half from its two construction halves: `borderLinks`
edges join consecutive same-side markers (`shapeIncidentLinksOfForm`
over `addClusterBorders_links_form`); titled edges cannot touch an appended
marker (`BorderInnerTitledBoundResidual`). -/
theorem shapeIncidentInherited_of_parts {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {labeled : Proper}
    (hcoordL : coordinateGraph P labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)))
    (hbound : BorderInnerTitledBoundResidual
      (titleReservations (sizeProperPorts P labeled))) :
    ShapeIncidentInheritedResidual P run side decl := by
  intro v hv e he htouch
  obtain ⟨na, hna, hba, _, _⟩ := mem_sideChainNodes_forward hv
  have hcoordV : (coordinateGraph P labeled).nodes[v]? = some na := by
    rw [hcoordL]; exact hna
  have hbordV : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have haddedV : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).nodes[v]? = some na :=
    coordinateGraph_side_original hready hcoordV hbordV
  have hedges : run.coordinateProper.edges =
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).edges := by
    rw [← hcoordL]; rfl
  have hlenE : e < (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).edges.length := by
    have hlenEq' := congrArg List.length hedges
    omega
  have heEq : run.coordinateProper.edges[e]! =
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).edges[e]! := by
    rw [hedges]
  have hmemE : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).edges[e]! ∈
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).edges := by
    rw [getElem!_pos ((OrderImpl.addClusterBorders (titleReservations
      (sizeProperPorts P labeled)) P.clusterBorderW).edges) e hlenE]
    exact List.getElem_mem hlenE
  have hdisj := addClusterBorders_links_form _ _ hready.2.2.2.1 _ hmemE
  rcases hdisj with htitled | hlink
  · -- titled edge: endpoint bound contradicts v's freshness
    obtain ⟨htail, hhead⟩ := hbound _ htitled
    have htouch' : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).edges[e]!.tail = v ∨
        (OrderImpl.addClusterBorders (titleReservations
          (sizeProperPorts P labeled)) P.clusterBorderW).edges[e]!.head = v := by
      rw [← heEq]; exact htouch
    obtain ⟨es, hinv⟩ := executed_border_binv P.clusterBorderW hready
    rcases OrderImpl.binv_lookup hinv haddedV with ⟨_, hnodeV⟩ | ⟨hleV, _, _, _⟩
    · have hmemV := List.mem_of_getElem? hnodeV
      rcases hbordV with hs | hs
      · exact ((hready.1 na hmemV).1 hs).elim
      · exact ((hready.1 na hmemV).2 hs).elim
    · have hF : False := by omega
      exact hF.elim
  · -- link edge: the links half
    have htouch' : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPorts P labeled)) P.clusterBorderW).edges[e]!.tail = v ∨
        (OrderImpl.addClusterBorders (titleReservations
          (sizeProperPorts P labeled)) P.clusterBorderW).edges[e]!.head = v := by
      rw [← heEq]; exact htouch
    have hclose := shapeIncidentLinksOfForm (_k := k) hgraph hcomp hrun hside hpos
      hcoordL hready hv hlink htouch'
    rw [← heEq] at hclose
    exact hclose

/-! ## Executed-run closures: the three residuals and the shape assembly. -/

/-- Executed `rank_inj`: two same-side, same-declaration markers on one pass
rank are the same node. -/
theorem shapeRankInj_executed {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeRankInjResidual P run side decl pos k :=
  shapeRankInjResidual hgraph hcomp hrun hside hpos

/-- Executed `rank_consec`: pass ranks of one side chain form an interval
with no gaps. -/
theorem shapeRankConsec_executed {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeRankConsecResidual P run side decl pos k :=
  shapeRankConsec hgraph hcomp hrun hside hpos

/-- Executed inherited half of `incident_border`: the titled-edge endpoint
bound is discharged by `borderInnerTitledBound_executed` on the same ranked
source the readiness bundle comes from. -/
theorem shapeIncidentInherited_executed {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeIncidentInheritedResidual P run side decl := by
  obtain ⟨_, _, labeled, _, hn, hl, hcoordL, _⟩ :=
    componentRun_ranked_source hrun
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun index node hnode => componentCandidate_marker_shape hgraph hnode
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)) :=
    titled_border_ready hkeys hshape hmarkers haligned
  exact shapeIncidentInherited_of_parts (k := k) hgraph hcomp hrun hside hpos
    hcoordL hready (borderInnerTitledBound_executed hn hl)

/-- Executed side-chain shape: the three executed fields close
`foreignSideChainShape` with execution evidence only. -/
theorem foreignSideChainShape_executed {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ForeignSideChainShape P run side decl pos k :=
  foreignSideChainShape hgraph hcomp hrun hside hpos
    (shapeRankInj_executed hgraph hcomp hrun hside hpos)
    (shapeIncidentInherited_executed (k := k) hgraph hcomp hrun hside hpos)
    (shapeRankConsec_executed hgraph hcomp hrun hside hpos)

end Elegant.Layered.PipelineImpl