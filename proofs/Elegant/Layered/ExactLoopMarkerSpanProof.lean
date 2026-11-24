import Elegant.Layered.ExactMarkerBracketProof
import Elegant.Layered.ExactBorderDivergeProof

/-!
The four clauses of `embLoopMarkerSpanX` hold on well-formed exact runs with
framed parents. The alignment clause needs both admission premises.

Counterexample: cell profile, TB, no exact IDs, no labels, plain edges,
box texts equal to IDs. Declare boxes in this order:
`a`, `b`, `d` (group under `a`), `e` (group under `b`), `d1`, `e1`,
`d2`, `e2`, `d3`, `e3`. The numbered boxes belong to their respective
groups; all nongroup boxes are exclusive. Use routes `d → d`,
`d2 → d3`, `e2 → e3`, then 12 pairs of `d1 → e2`, `e1 → d2`, with
distinct route IDs.

`layoutX []` succeeds. Component `[2,3,4,5,6,7,8,9,10,11]`, candidate 0,
has a looping top at index 0 with declaration 2. Its markers 12 and 14
are both left markers, yet their intervals are `[7,8]` and `[18,19]`.
Markers 13 and 15 are both right markers, with `[18,19]` and `[36,37]`.
The input is well formed and within limits, but `framedParents` is false.
`layoutFamilyX` rejects the input, and validating the flat result reports
`parent: box outside its parent`.

Framed parents alone do not suffice. Append two root groups named `a` and
`b` after the ten boxes. `framedParents` becomes true, but duplicate
IDs make the model ill formed and the path still resolves to the earlier
nongroup parents. Candidate 0 in `[2,3,4,5,6,7,8,9,12,13]` has the same
misaligned marker intervals.
-/

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open CoordsImpl

private theorem cross_centers_nonneg {gap pad : Int} {p : Proper}
    {layers : List (List Nat)} {xs : List Int}
    (hcross : crossCoordsClusterWith gap pad p layers = .ok xs) (v : Nat) :
    0 ≤ xs.getD v 0 := by
  obtain ⟨_, _, hempty | ⟨y0, y1, y2, y3, h0, h1, h2, h3, hbalance⟩⟩ :=
    Elegant.Layered.crossCoordsClusterWith_ok hcross
  · rw [hempty.2]
    exact Int.le_refl 0
  · rw [balance_ok hbalance]
    by_cases hv : v < p.nodes.length
    · rw [balanceValues_getD _ _ _ _ _ hv]
      have h0' := fbs_cluster_pass_nonneg h0
      have h1' := fbs_cluster_pass_nonneg h1
      have h2' := fbs_cluster_pass_nonneg h2
      have h3' := fbs_cluster_pass_nonneg h3
      obtain ⟨o0, o1, o2, o3⟩ := fbs_balanceOffsets_nonneg y0 y1 y2 y3
      exact fbs_bal4_nonneg (by have := h0'.2 v (by rw [h0'.1]; exact hv); omega)
        (by have := h1'.2 v (by rw [h1'.1]; exact hv); omega)
        (by have := h2'.2 v (by rw [h2'.1]; exact hv); omega)
        (by have := h3'.2 v (by rw [h3'.1]; exact hv); omega)
    · have hlen : (balanceValues p.nodes.length y0 y1 y2 y3).length = p.nodes.length := by
        simp [balanceValues]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact Int.le_refl 0

theorem xleg_rightMarker_edge_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {m : Nat} {nd : ProperNode} (hnode : run.coordinateProper.nodes[m]? = some nd)
    (hborder : nd.node.border = 1) :
    0 ≤ RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m := by
  obtain ⟨_, _, _, q, _, _, _, _, hcross, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hrec, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 m nd hnode (by rw [hborder]; decide)
  have hproper : run.proper.nodes[m]? = some nd := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    exact hrec
  have hw := (componentRunX_dims_nonneg hrun m nd hproper).1
  have hc := cross_centers_nonneg hcross m
  simp only [RouteImpl.leftOf, RouteImpl.nodeW, RouteImpl.xAt,
    List.getD_eq_getElem?_getD, hproper, hx, Option.getD_some,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hc ⊢
  omega

theorem xleg_rightMarker_later_gap {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {m b : Nat} {nd other : ProperNode} (hm : run.coordinateProper.nodes[m]? = some nd)
    (hborder : nd.node.border = 1) (hb : run.coordinateProper.nodes[b]? = some other)
    {layer : List Nat} (hlayer : layer ∈ run.layers) {j iv : Nat}
    (hj : layer[j]? = some m) (hiv : layer[iv]? = some b) (hlt : j < iv) :
    Int.fdiv (nd.node.w + 2 * (nd.node.loopExtent : Int)) 2 +
      Int.fdiv (other.node.w + 2 * (other.node.loopExtent : Int)) 2 + 1 ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD m 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRunX_spec hrun
  obtain ⟨hgap, hpad, _, hs, _⟩ := crossCoordsClusterWith_spec hcross
  have hj1 : j + 1 < layer.length := by
    have := (List.getElem?_eq_some_iff.mp hiv).1
    omega
  let next := layer[j + 1]
  have hnext : layer[j + 1]? = some next := List.getElem?_eq_getElem hj1
  have hnoTitle : ownTitleAnchor run.coordinateProper m next = false := by
    cases h : run.coordinateProper.nodes[next]? <;> simp [CoordsImpl.ownTitleAnchor, hm, hborder, h]
  have hfirst := cluster_balance_separated hcross layer hlayer j m next hj hnext
  have hminimum := clusterGap_ge_min (ng := P.nodeGap) (cp := P.clusterPad) _ _ _ hnoTitle
  unfold CoordsImpl.clusterSep CoordsImpl.coordSep at hfirst
  have hwM : CoordsImpl.nodeW run.coordinateProper m =
      nd.node.w + 2 * (nd.node.loopExtent : Int) := by simp only [CoordsImpl.nodeW, hm]
  have hwB : CoordsImpl.nodeW run.coordinateProper b =
      other.node.w + 2 * (other.node.loopExtent : Int) := by simp only [CoordsImpl.nodeW, hb]
  rw [← hwM, ← hwB]
  by_cases heq : j + 1 = iv
  · have he : next = b := Option.some.inj (hnext.symm.trans (heq ▸ hiv))
    rw [he] at hfirst hminimum
    omega
  · have htail := cluster_zero_pairs_separated hcross layer hlayer (j + 1) iv next b
      (by omega) hnext hiv
    have hwidth : 0 ≤ Int.fdiv (CoordsImpl.nodeW run.coordinateProper next) 2 :=
      Int.fdiv_nonneg (CoordsImpl.nodeW_nonneg hs next) (by decide)
    omega

private theorem sideMarker_origin (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source) {marker : ProperNode}
    (hmarker : marker ∈ (OrderImpl.addClusterBorders source width).nodes)
    (hborder : marker.node.border = -1 ∨ marker.node.border = 1) :
    ∃ (top : ProperNode) (i : Nat),
      source.nodes[i]? = some top ∧ top.node.border = -2 ∧
      marker.node.clusterPath = top.node.clusterPath ∧
      (marker.node.border = 1 → marker.node.loopExtent = top.node.loopExtent) := by
  let invariant := fun current : Proper =>
    ∀ marker ∈ current.nodes, marker.node.border = -1 ∨ marker.node.border = 1 →
      ∃ (top : ProperNode) (i : Nat),
        source.nodes[i]? = some top ∧ top.node.border = -2 ∧
        marker.node.clusterPath = top.node.clusterPath ∧
        (marker.node.border = 1 → marker.node.loopExtent = top.node.loopExtent)
  have h : invariant (OrderImpl.addClusterBorders source width) := by
    unfold invariant
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv invariant
    · intro node hn hb
      exact (hb.elim (hready.1 node hn).1 (hready.1 node hn).2).elim
    · intro current hcurrent top htop
      obtain ⟨htopZip, htopBorder⟩ := List.mem_filter.mp htop
      unfold OrderImpl.borderStep
      split
      · exact hcurrent
      · apply OrderImpl.foldl_inv invariant
        · exact hcurrent
        · intro state hstate offset _
          intro node hn hb
          change node ∈ state.nodes ++
            [OrderImpl.borderLeft top width, OrderImpl.borderRight top width] at hn
          rcases List.mem_append.mp hn with hn | hn
          · exact hstate node hn hb
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl
            · exact ⟨top.1, top.2, List.mem_zipIdx_iff_getElem?.mp htopZip,
                beq_iff_eq.mp htopBorder, rfl, fun h => by simp [OrderImpl.borderLeft] at h⟩
            · exact ⟨top.1, top.2, List.mem_zipIdx_iff_getElem?.mp htopZip,
                beq_iff_eq.mp htopBorder, rfl, fun _ => rfl⟩
  exact h marker hmarker hborder

theorem xleg_rightMarker_copies_extent {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {t m : Nat} {nt : Node} {nd : ProperNode}
    (ht : (componentCandidate graph comp candidate).nodes[t]? = some nt)
    (hTop : nt.border = -2)
    (hm : run.coordinateProper.nodes[m]? = some nd)
    (hRight : nd.node.border = 1)
    (hLast : nd.node.clusterPath.getLast? = some nt.decl) :
    nd.node.loopExtent = nt.loopExtent := by
  obtain ⟨_, labeled, _, hcoord, hkeys, hready, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 hG hcomp hrun
  have hm' : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[m]? = some nd := by
    rw [hcoord]
    exact hm
  have hb := X_side_original hready hm' (Or.inr hRight)
  obtain ⟨top, i, hi, htopBorder, hpath, hloop⟩ :=
    sideMarker_origin _ _ hready (List.mem_of_getElem? hb) (Or.inr hRight)
  have htitled := X_titled_marker_record (P := P) (exact := exactDecls exactIds inp)
    (hrecords t nt ht) (Or.inl hTop)
  obtain ⟨box, _, hpathTop⟩ := X_cg_group_box h0 hG ht hTop
  have htitleBorder : (titleF ⟨nt, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hTop
  have htitleLast : (titleF ⟨nt, false, none, false⟩).node.clusterPath.getLast? =
      some nt.decl := by
    rw [(titleF_keys _).2.2.1, hpathTop]
    simp
  have howner : top.node.clusterPath.getLast? =
      (titleF ⟨nt, false, none, false⟩).node.clusterPath.getLast? := by
    rw [← hpath, hLast, htitleLast]
  have hiEq := X_titled_group_owner_unique h0 hG hcomp hkeys hrecords
    hi htitled htopBorder htitleBorder howner
  subst i
  have hrecord := Option.some.inj (hi.symm.trans htitled)
  rw [hloop hRight, hrecord]
  simp [titleF, hTop]

private theorem selected_index {α : Type} (nodes : List α) (keep : α → Bool) (i : Nat) :
    (nodes.zipIdx.filterMap (fun q => if keep q.1 then some q.2 else none)).contains i =
      true ↔ ∃ node, nodes[i]? = some node ∧ keep node = true := by
  rw [List.contains_iff_mem, List.mem_filterMap]
  constructor
  · rintro ⟨⟨node, key⟩, hzip, hselected⟩
    cases hkeep : keep node with
    | false => simp [hkeep] at hselected
    | true =>
      have hkey : key = i := by simpa [hkeep] using hselected
      subst key
      exact ⟨node, List.mem_zipIdx_iff_getElem?.mp hzip, hkeep⟩
  · rintro ⟨node, hnode, hkeep⟩
    exact ⟨(node, i), List.mem_zipIdx_iff_getElem?.mpr hnode, by simp [hkeep]⟩

private theorem exact_run_indices {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.exact = cg.nodes.zipIdx.filterMap
      (fun q => if exact.contains q.1.decl then some q.2 else none) := by
  unfold componentRunX at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  rw [← Except.ok.inj h]

private theorem prepared_group_lookup (inp : Input) {u : Nat} {group : ModelBox}
    (hgroup : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[u]? = some group)
    (hrole : group.role = .group) :
    inp.boxes[u]? = some group ∧
      (inp.fixedSizes.any fun fixed => fixed.1 == group.id) = false := by
  rw [List.getElem?_map] at hgroup
  obtain ⟨box, hbox, hgroup⟩ := Option.map_eq_some_iff.mp hgroup
  cases h : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) with
  | false =>
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hgroup
    subst group
    exact ⟨hbox, h⟩
  | true =>
    simp only [h, ↓reduceIte] at hgroup
    have he := congrArg ModelBox.role hgroup
    rw [hrole] at he
    cases he

private theorem measured_top_extent {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {u : Nat} {node : Node} (hnode : execution.graph0.nodes[u]? = some node)
    (hborder : node.border = -2) :
    node.loopExtent = (Loops.extent execution.graph0.slot
      (loopSizes execution.graph0.edges execution.measured u execution.graph0.slot)).toNat := by
  obtain ⟨hdecl, box, hbox, hrole, _⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnode hborder
  rw [hdecl] at hbox
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  have hbox' : boxes[u]? = some box := hbox
  have hboxLen := (List.getElem?_eq_some_iff.mp hbox').1
  have hlines : execution.lines.length = boxes.length := by
    have hl := execution.lines_eq
    unfold boxLines at hl
    simpa only [List.length_zipIdx, boxes, List.length_map] using
      Sequence.mapM_ok_length _ _ _ hl
  have hu : u < execution.lines.length := hlines ▸ hboxLen
  have h := execution.graph0_eq
  unfold measuredGraph at h
  obtain ⟨initial, hini, h⟩ := bind_ok' h
  obtain ⟨edges, _, h⟩ := bind_ok' h
  obtain ⟨metric, hmetric, h⟩ := bind_ok' h
  obtain ⟨labels, hlabels, h⟩ := bind_ok' h
  have hmEq := Except.ok.inj (hmetric.symm.trans execution.metric_eq)
  have hmLabels : measureLabels execution.params metric
      (Measure.wrapTarget metric.profile execution.params.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0)) inp o.direction =
      .ok execution.measured := by rw [hmEq]; exact execution.measured_eq
  have hlabelsEq := Except.ok.inj (hlabels.symm.trans hmLabels)
  have h' := h
  rw [hlabelsEq] at h'
  obtain ⟨nodes, hnodes, h⟩ := bind_ok' h'
  let raw : Graph := { nodes := nodes, edges := edges, slot := execution.params.slot }
  let titles := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  have hgraph : execution.graph0 = Compound.prepare boxes execution.params.clusterPad titles raw :=
    (Except.ok.inj h).symm
  have hslot : execution.graph0.slot = execution.params.slot := by rw [hgraph]; rfl
  change (execution.lines.zipIdx).mapM
    (fun q => sizedNode execution.params q.2 q.1) = .ok initial at hini
  obtain ⟨before, _, hbefore⟩ := (mapM_getElem? _ _ _ hini).2 u (execution.lines[u], u)
    (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hu, Option.map_some, Nat.zero_add])
  obtain ⟨after, hstep, hafter⟩ := (mapM_getElem? _ _ _ hnodes).2 u
    (orientNode o.direction before, u)
    (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore, Option.map_some, Nat.zero_add])
  obtain ⟨hboxRaw, hfixed⟩ := prepared_group_lookup inp hbox hrole
  have hfind : (inp.fixedSizes.find? fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  have hextent : after.loopExtent = (Loops.extent execution.params.slot
      (loopSizes edges execution.measured u execution.params.slot)).toNat := by
    dsimp only at hstep
    simp only [hboxRaw, hfind, Option.any_some, hrole, hfixed, beq_self_eq_true,
      Bool.not_false, Bool.true_and, ↓reduceIte, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · rw [← Except.ok.inj hstep]
  have hrawLen : u < raw.nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hrawNode : raw.nodes[u] = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hprepared := Compound.prepare_group_title_record boxes execution.params.clusterPad
    titles raw hrawLen hbox' hrole
  rw [← hgraph, hnode] at hprepared
  have hloop : node.loopExtent = raw.nodes[u].loopExtent := by
    have he := Option.some.inj hprepared
    have hext := congrArg Node.loopExtent he
    exact hext
  have hsize := prepare_loopSizes_preserved boxes execution.params.clusterPad
    titles raw u hboxLen execution.measured execution.params.slot
  rw [← hgraph] at hsize
  rw [hloop, hrawNode, hextent, hslot, hsize]

private theorem exactGraph_group_top_unselected {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {u : Nat} {node : Node} (hnode : graph0.nodes[u]? = some node)
    (hborder : node.border = -2) :
    graph.nodes[u]? = some node ∧ (exactDecls exactIds inp).contains node.decl = false := by
  obtain ⟨_, box, hgroup, hrole, _⟩ := measuredGraph_group_origin h0 hnode hborder
  obtain ⟨hbox, hfixed⟩ := prepared_group_lookup inp hgroup hrole
  have hfind : (inp.fixedSizes.find? fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  unfold exactGraph at hG
  obtain ⟨nodes, hmap, hG⟩ := bind_ok hG
  obtain ⟨dest, hstep, hdest⟩ := (mapM_getElem? _ _ _ hmap).2 u node hnode
  have hnotExact : exactIds.contains box.id = false := by
    cases h : exactIds.contains box.id with
    | false => rfl
    | true =>
      simp only [hbox, h, hfind, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at hstep
      cases hstep
  have hsame : node = dest := by
    apply Except.ok.inj
    simpa only [hbox, hnotExact, hfixed, Bool.not_false, Bool.and_false,
      Bool.true_and, ↓reduceIte, pure, Except.pure] using hstep
  refine ⟨?_, Bool.eq_false_iff.mpr ?_⟩
  · rw [← Except.ok.inj hG, hsame]
    exact hdest
  · intro h
    obtain ⟨other, ho, hselected⟩ := (selected_index inp.boxes
      (fun b => exactIds.contains b.id ||
        (b.role == .group && inp.fixedSizes.any (·.1 == b.id))) node.decl).mp h
    have he : other = box := Option.some.inj (ho.symm.trans hbox)
    simp only [he, hnotExact, hfixed, Bool.and_false, Bool.false_or,
      Bool.false_eq_true] at hselected

private theorem exactGraph_slot_kept {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph) :
    graph.slot = graph0.slot := by
  unfold exactGraph at hG
  obtain ⟨_, _, hG⟩ := bind_ok hG
  rw [← Except.ok.inj hG]

private theorem candidate_slot_kept (graph : Graph) (comp : List Nat) (candidate : Nat) :
    (componentCandidate graph comp candidate).slot = graph.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

theorem xleg_rightMarker_extent_ge {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t m : Nat} {nt : Node} {nd : ProperNode}
    (ht : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (hTop : nt.border = -2) (hm : run.coordinateProper.nodes[m]? = some nd)
    (hRight : nd.node.border = 1) (hLast : nd.node.clusterPath.getLast? = some nt.decl) :
    (nd.node.loopExtent : Int) ≥
      (if run.exact.contains t then Loops.exactExtent
        (componentCandidate execution.graph comp candidate).slot
        (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured t
          (componentCandidate execution.graph comp candidate).slot)
       else Loops.extent (componentCandidate execution.graph comp candidate).slot
        (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured t
          (componentCandidate execution.graph comp candidate).slot)) := by
  have hcopy := xleg_rightMarker_copies_extent execution.graph0_eq execution.graph_eq
    hcomp hrun ht hTop hm hRight hLast
  obtain ⟨u, hu, hnode⟩ := componentCandidate_nonplain_source ht (by omega)
  have hu0 : u < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hnode).1
  obtain ⟨n, hn⟩ : ∃ n, execution.graph0.nodes[u]? = some n :=
    ⟨_, List.getElem?_eq_getElem hu0⟩
  obtain ⟨n', hn', hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hn
  have he := Option.some.inj (hn'.symm.trans hnode)
  have hborder0 : n.border = -2 := hborder.symm.trans (he ▸ hTop)
  obtain ⟨hnodeUnchanged, hdeclNotExact⟩ :=
    exactGraph_group_top_unselected execution.graph0_eq execution.graph_eq hn hborder0
  have heq : nt = n := Option.some.inj (hnode.symm.trans hnodeUnchanged)
  have hnotExact : run.exact.contains t = false := by
    rw [exact_run_indices hrun]
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨nt', ht', hsel⟩ := (selected_index _ (fun n : Node =>
      (exactDecls exactIds inp).contains n.decl) t).mp h
    have he' : nt' = nt := Option.some.inj (ht'.symm.trans ht)
    rw [he', heq, hdeclNotExact] at hsel
    cases hsel
  have hs := (candidate_slot_kept execution.graph comp candidate).trans
    (exactGraph_slot_kept execution.graph_eq)
  have htLen := (List.getElem?_eq_some_iff.mp hu).1
  have hindex := (List.getElem?_eq_some_iff.mp hu).2
  have hsize := componentCandidate_loopSizes_preserved execution.graph comp
    (components_nodup _ _ hcomp) candidate t htLen execution.measured execution.graph0.slot
  rw [hindex, exactGraph_edges execution.graph_eq] at hsize
  have hextent := measured_top_extent execution hn hborder0
  simp only [hnotExact, Bool.false_eq_true, ↓reduceIte]
  rw [hs, hsize, hcopy, heq, hextent]
  omega

private theorem candidate_top_last {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate i : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some node)
    (hborder : node.border = -2) :
    node.clusterPath.getLast? = some node.decl := by
  obtain ⟨_, _, hpath⟩ := X_cg_group_box h0 hG hnode hborder
  rw [hpath]
  simp

private theorem candidate_top_of_side {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {m : Nat} {nd : ProperNode} (hm : run.coordinateProper.nodes[m]? = some nd)
    (hside : nd.node.border = -1 ∨ nd.node.border = 1) :
    ∃ (i : Nat) (top : Node), (componentCandidate graph comp candidate).nodes[i]? = some top ∧
      top.border = -2 ∧ nd.node.clusterPath = top.clusterPath := by
  obtain ⟨_, labeled, _, hcoord, hkeys, hready, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 hG hcomp hrun
  have hm' : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[m]? = some nd := by
    rw [hcoord]
    exact hm
  have hb := X_side_original hready hm' hside
  obtain ⟨top, i, hi, hb, hpath, _⟩ :=
    sideMarker_origin _ _ hready (List.mem_of_getElem? hb) hside
  obtain ⟨original, ho, he, htop⟩ :=
    X_titled_marker_source_record hkeys hrecords hi (Or.inl hb)
  refine ⟨i, original, ho, he.symm.trans hb, ?_⟩
  rw [hpath, htop, (titleF_keys _).2.2.1]

private theorem coordinate_paths_functional {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    OrderImpl.ClusterPathsFunctional run.coordinateProper := by
  intro a b na nb ha hb hba hbb hlast
  obtain ⟨i, topA, hi, hborderA, hpathA⟩ :=
    candidate_top_of_side h0 hG hcomp hrun ha (Or.inl hba)
  obtain ⟨j, topB, hj, hborderB, hpathB⟩ :=
    candidate_top_of_side h0 hG hcomp hrun hb (Or.inl hbb)
  rw [hpathA, hpathB, candidate_top_last h0 hG hi hborderA,
    candidate_top_last h0 hG hj hborderB] at hlast
  rw [hpathA, hpathB]
  exact (X_group_path_iff_decl h0 hG hi hj hborderA hborderB).mpr (Option.some.inj hlast)

private theorem candidate_top_of_prefix {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {pre : List Nat} (hpre : pre ≠ []) :
    ∀ (fuel : Nat) {i : Nat} {top : Node},
      (componentCandidate graph comp candidate).nodes[i]? = some top →
      top.border = -2 → ∀ suffix, top.clusterPath = pre ++ suffix →
      suffix.length ≤ fuel →
      ∃ (j : Nat) (outer : Node),
        (componentCandidate graph comp candidate).nodes[j]? = some outer ∧
          outer.border = -2 ∧ outer.clusterPath = pre := by
  intro fuel
  induction fuel with
  | zero =>
    intro i top hi hb suffix hpath hlen
    have he : suffix = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨i, top, hi, hb, by simpa only [he, List.append_nil] using hpath⟩
  | succ fuel ih =>
    intro i top hi hb suffix hpath hlen
    by_cases hs : suffix = []
    · exact ⟨i, top, hi, hb, by simpa only [hs, List.append_nil] using hpath⟩
    have hlt : pre.length < top.clusterPath.length := by
      rw [hpath, List.length_append]
      have : suffix.length ≠ 0 := fun h => hs (List.length_eq_zero_iff.mp h)
      omega
    obtain ⟨parent, hparent⟩ := X_candidate_parent_top_exists h0 hG hlines hwf hfp
      hcomp candidate (x := (top, i)) (List.mem_zipIdx_iff_getElem?.mpr hi) hb
      ⟨suffix, hpath.symm⟩ hlt hpre
    have hparentLookup := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hparent)
    have hselected := List.find?_some
      (p := fun entry : Node × Nat => entry.1.border == -2 &&
        entry.1.clusterPath == top.clusterPath.dropLast) hparent
    obtain ⟨hparentBorder, hparentPath⟩ := Bool.and_eq_true_iff.mp hselected
    refine ih hparentLookup (beq_iff_eq.mp hparentBorder) suffix.dropLast ?_ ?_
    · rw [beq_iff_eq.mp hparentPath, hpath, List.dropLast_append_of_ne_nil hs]
    · rw [List.length_dropLast]
      omega

private theorem candidate_top_left_marker {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {i : Nat} {top : Node}
    (htop : (componentCandidate graph comp candidate).nodes[i]? = some top)
    (hborder : top.border = -2) :
    ∃ m, OrderImpl.LeftBorderOf run.coordinateProper m top.clusterPath := by
  obtain ⟨_, labeled, _, hcoord, _, hready, hrecords, _, haligned⟩ :=
    X_cg_run_bundle h0 hG hcomp hrun
  let anchor := titleF (⟨top, false, none, false⟩ : ProperNode)
  let proxy := clearF anchor
  have hproxy : run.coordinateProper.nodes[i]? = some proxy := by
    rw [← hcoord]
    exact X_coordinateGraph_marker_record (hrecords i top htop) (Or.inl hborder) rfl
  have hkeys := titleF_keys (⟨top, false, none, false⟩ : ProperNode)
  have hclear := clearF_keys anchor
  have hborderProxy : proxy.node.border = -2 := hclear.2.1.trans (hkeys.2.1.trans hborder)
  have hpathProxy : proxy.node.clusterPath = top.clusterPath :=
    hclear.2.2.1.trans hkeys.2.2.1
  obtain ⟨owner, side, nd, howner, hside, hs, hlast, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hborderProxy)
  obtain ⟨j, other, hj, hbo, hndPath⟩ :=
    candidate_top_of_side h0 hG hcomp hrun hside hs
  have hlastEq := hlast.trans howner.symm
  rw [hndPath, hpathProxy, candidate_top_last h0 hG hj hbo,
    candidate_top_last h0 hG htop hborder] at hlastEq
  have hndTop : nd.node.clusterPath = top.clusterPath := hndPath.trans
    ((X_group_path_iff_decl h0 hG hj htop hbo hborder).mpr (Option.some.inj hlastEq))
  have hside' : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[side]? = some nd := by
    rw [hcoord]
    exact hside
  let titled := titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)
  have hbordered := X_side_original hready hside' hs
  obtain ⟨entry, hentry, bottom, hbottom, hndEntry, hbounds⟩ :=
    addClusterBorders_side_range_source titled P.clusterBorderW hready
      (List.mem_of_getElem? hbordered) hs
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp hentry
  obtain ⟨left, _, hleft, _, _, _⟩ := emb_rank_pair P (exactDecls exactIds inp) labeled
    (X_titleReservations_node_rank_alignment P haligned) hmem (beq_iff_eq.mp hcond)
    hbottom (Nat.le_refl _) hbounds
  rw [hcoord] at hleft
  exact ⟨left, _, hleft, rfl, hndEntry.symm.trans hndTop⟩

theorem xleg_framed_divergent_markers_stable {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hG : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
    ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      run.coordinateProper.nodes[a']? = some na' →
      run.coordinateProper.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      Divergent na.node.clusterPath nb.node.clusterPath →
      ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
        l2[i']? = some a' → l2[j']? = some b' →
        (i < j ↔ i' < j') := by
  intro l1 l2 hl1 hl2 a b a' b' na nb na' nb' ha hb hsa hsb ha' hb' hsa' hsb' hpa hpb hdiv
  apply X_foreignBorderDivergeStableSeparated_holds exactIds h0 hG hcomp hrun hl1 hl2
    ha hb hsa hsb ha' hb' hsa' hsb' hpa hpb hdiv
  intro pre A B tailA tailB hA hB _
  have headMarker :
      ∀ {idx : Nat} {node : ProperNode}, run.coordinateProper.nodes[idx]? = some node →
      (node.node.border = -1 ∨ node.node.border = 1) →
      ∀ (key : Nat) (tail : List Nat), node.node.clusterPath = pre ++ key :: tail →
        ∃ m, OrderImpl.LeftBorderOf run.coordinateProper m (pre ++ [key]) := by
    intro idx node hnode hside key tail hpath
    obtain ⟨t, top, ht, hborder, htopPath⟩ :=
      candidate_top_of_side h0 hG hcomp hrun hnode hside
    have hpre : pre ++ [key] ≠ [] := by simp
    have htopPath' : top.clusterPath = (pre ++ [key]) ++ tail := by
      rw [← htopPath, hpath, List.append_assoc, List.singleton_append]
    obtain ⟨u, outer, hu, houter, houterPath⟩ :=
      candidate_top_of_prefix h0 hG hlines hwf hfp hcomp hpre
        tail.length ht hborder tail htopPath' (Nat.le_refl _)
    rw [← houterPath]
    exact candidate_top_left_marker h0 hG hcomp hrun hu houter
  obtain ⟨mA, ndA, hmA, hbA, hpA⟩ := headMarker ha hsa A tailA hA
  obtain ⟨mB, ndB, hmB, hbB, hpB⟩ := headMarker hb hsb B tailB hB
  have hf := coordinate_paths_functional h0 hG hcomp hrun
  exact ⟨OrderImpl.clusterIds_mem hmA hbA hpA, OrderImpl.clusterIds_mem hmB hbB hpB,
    (OrderImpl.parentOf_eq hf hmA hbA hpA).trans (OrderImpl.parentOf_eq hf hmB hbB hpB).symm⟩

private theorem marker_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {m : Nat} {nd : ProperNode} (hrec : run.proper.nodes[m]? = some nd)
    (hside : nd.node.border = -1 ∨ nd.node.border = 1) :
    run.coordinateProper.nodes[m]? = some nd := by
  obtain ⟨_, _, _, q, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hq : q.nodes[m]? = some nd := by
    rw [← OrderImpl.dropSynthetic_nodes, hdrop]
    exact hrec
  obtain ⟨_, _, hlen, _, hfields, hpreserved⟩ := proxyWidths_rel hproxy
  have hlt : m < run.coordinateProper.nodes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hq).1
  obtain ⟨original, horiginal⟩ : ∃ n, run.coordinateProper.nodes[m]? = some n :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨after, hafter, _, hborder, _⟩ := hfields m original horiginal
  have he : after = nd := Option.some.inj (hafter.symm.trans hq)
  have hnotProxy : ¬ (original.node.border = -2 ∨ original.node.border = 2) := by
    rw [← hborder, he]
    rcases hside with h | h <;> rw [h] <;> decide
  have hs := (hpreserved m original horiginal hnotProxy).1
  rwa [Option.some.inj (hs.symm.trans hq)] at horiginal

theorem xleg_loopMarkerSpanX_holds (exactIds : List String) : embLoopMarkerSpanX exactIds := by
  intro inp o res execution hwf hfp comp _ candidate run orderOptions cg hcomp hcg hrun
    t nt ht _ hTop mL mR nL nR hcoordL hcoordR hleft hright hlastL hlastR
  subst cg
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h
  have haligned := @X_foreignBorderChainXAligned_of_local_stable execution.params exactIds inp o
    execution.lines execution.measured execution.graph0 execution.graph
    execution.graph0_eq execution.graph_eq comp hcomp candidate run execution.measured
    orderOptions hrun
    (xleg_framed_divergent_markers_stable execution.graph0_eq execution.graph_eq
      hlines hwf hfp hcomp hrun)
    (X_foreignSideChainShapeClosed_holds exactIds execution.graph0_eq execution.graph_eq hcomp hrun)
  refine ⟨?_, xleg_rightMarker_extent_ge execution hcomp hrun ht hTop hcoordR hright hlastR,
    xleg_rightMarker_edge_nonneg hrun hcoordR hright, ?_⟩
  · intro q nd hq hlastQ
    constructor
    · intro hside
      have hm := marker_coordinate_record hrun hq (Or.inl hside)
      exact haligned hm hcoordL (Or.inl hside) (Or.inl hleft)
        (hside.trans hleft.symm) (hlastQ.trans hlastL.symm)
    · intro hside
      have hm := marker_coordinate_record hrun hq (Or.inr hside)
      exact haligned hm hcoordR (Or.inr hside) (Or.inr hright)
        (hside.trans hright.symm) (hlastQ.trans hlastR.symm)
  · intro b nd hb _ layer hlayer j iv hj hiv hlt
    exact xleg_rightMarker_later_gap hrun hcoordR hright hb hlayer hj hiv hlt

end Elegant.Layered.PipelineImpl
