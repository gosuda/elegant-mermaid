import Elegant.Layered.GroupWidthFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem checked_exact {value result : Int}
    (h : FramePorts.checked value = .ok result) : result = value := by
  unfold FramePorts.checked at h
  split at h
  · cases h
  · exact (Except.ok.inj h).symm

theorem proxyWidths_proxy_interval {p q : Proper} {xs ys : List Int}
    (h : proxyWidths p xs = .ok (q, ys)) {index : Nat} {node : ProperNode}
    (hnode : p.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan p xs owner index = .ok span ∧
      q.nodes[index]? = some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf q ys index = span.lo ∧
      RouteImpl.leftOf q ys index + RouteImpl.nodeW q index = span.hi := by
  unfold proxyWidths at h
  obtain ⟨updated, hupdated, hfinal⟩ := bind_ok h
  have finalEq := Except.ok.inj hfinal
  have nodeMap : q.nodes = updated.map Prod.fst := by
    have eq := congrArg (fun pair : Proper × List Int => pair.1.nodes) finalEq
    exact eq.symm
  have xsMap : ys = updated.map Prod.snd := (congrArg Prod.snd finalEq).symm
  obtain ⟨_, records⟩ := mapM_getElem? _ _ _ hupdated
  obtain ⟨record, hrecord, recordLookup⟩ := records index (node, index)
    (by simp only [List.getElem?_zipIdx, hnode, Option.map_some, Nat.zero_add])
  dsimp only at hrecord
  have proxy : (node.node.border == -2 || node.node.border == 2) = true := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  simp only [proxy, ↓reduceIte] at hrecord
  cases ownerEq : node.node.clusterPath.getLast? with
  | none =>
    simp only [ownerEq] at hrecord
    change Except.error LayoutError.domain = Except.ok record at hrecord
    cases hrecord
  | some owner =>
    simp only [ownerEq] at hrecord
    obtain ⟨span, hspan, hrecord⟩ := bind_ok hrecord
    obtain ⟨width, hwidth, hrecord⟩ := bind_ok hrecord
    have widthEq := checked_exact hwidth
    by_cases negative : width < 0
    · simp only [negative, ↓reduceIte] at hrecord
      change Except.error LayoutError.domain = Except.ok record at hrecord
      cases hrecord
    · simp only [negative, ↓reduceIte] at hrecord
      obtain ⟨center, hcenter, hrecord⟩ := bind_ok hrecord
      have centerEq := checked_exact hcenter
      have recordEq := Except.ok.inj hrecord
      have recordNode : record.1 = { node with node := { node.node with w := width } } :=
        (congrArg Prod.fst recordEq).symm
      have recordX : record.2 = center := (congrArg Prod.snd recordEq).symm
      have outputNode : q.nodes[index]? =
          some { node with node := { node.node with w := width } } := by
        simp only [nodeMap, List.getElem?_map, recordLookup, Option.map_some, recordNode]
      have outputX : ys.getD index 0 = center := by
        simp only [xsMap, List.getD_eq_getElem?_getD, List.getElem?_map,
          recordLookup, Option.map_some, Option.getD_some, recordX]
      have left : RouteImpl.leftOf q ys index = span.lo := by
        simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, outputNode,
          outputX, centerEq]
        omega
      refine ⟨owner, span, rfl, hspan, ?_, ?_, left, ?_⟩
      · simpa only [widthEq] using outputNode
      · omega
      · simp only [left, RouteImpl.nodeW, outputNode]
        omega

theorem componentRun_proxy_interval {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
      run.proper.nodes[index]? =
        some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf run.proper run.xs index = span.lo ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _⟩ := componentRun_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

private theorem mapM_output_source {α β : Type} (f : α → Except LayoutError β)
    (source : List α) (output : List β) (decoded : source.mapM f = .ok output)
    (value : β) (member : value ∈ output) :
    ∃ entry ∈ source, f entry = .ok value := by
  obtain ⟨length, records⟩ := mapM_getElem? f source output decoded
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  have sourceBound : i < source.length := by omega
  have sourceLookup : source[i]? = some source[i] :=
    List.getElem?_eq_getElem sourceBound
  obtain ⟨actual, mapped, outputLookup⟩ := records i source[i] sourceLookup
  have equal : actual = value := Option.some.inj (outputLookup.symm.trans lookup)
  subst actual
  exact ⟨source[i], List.getElem_mem sourceBound, mapped⟩

private theorem borderSpan_endpoints {center width : Int} {span : FramePorts.Span}
    (h : FramePorts.borderSpan center width = .ok span) :
    span.lo = center - Int.fdiv width 2 ∧ span.hi = span.lo + width := by
  unfold FramePorts.borderSpan at h
  split at h
  · change Except.error LayoutError.domain = Except.ok span at h
    cases h
  · obtain ⟨lo, hlo, h⟩ := bind_ok h
    obtain ⟨hi, hhi, h⟩ := bind_ok h
    have low := checked_exact hlo
    have high := checked_exact hhi
    have equal := Except.ok.inj h
    have lowField := congrArg FramePorts.Span.lo equal
    have highField := congrArg FramePorts.Span.hi equal
    change lo = span.lo at lowField
    change hi = span.hi at highField
    exact ⟨by omega, by omega⟩

private theorem span_envelope_extrema (first : FramePorts.Span)
    (rest : List FramePorts.Span) :
    let result := rest.foldl
      (fun a b => (⟨min a.lo b.lo, max a.hi b.hi⟩ : FramePorts.Span)) first
    (∃ low ∈ first :: rest, result.lo = low.lo) ∧
      (∃ high ∈ first :: rest, result.hi = high.hi) := by
  constructor
  · apply OrderImpl.foldl_inv
      (fun acc : FramePorts.Span => ∃ low ∈ first :: rest, acc.lo = low.lo)
      _ rest first
    · exact ⟨first, List.mem_cons_self, rfl⟩
    · intro acc previous entry member
      obtain ⟨low, present, equal⟩ := previous
      by_cases left : acc.lo ≤ entry.lo
      · refine ⟨low, present, ?_⟩
        change min acc.lo entry.lo = low.lo
        omega
      · refine ⟨entry, List.mem_cons_of_mem first member, ?_⟩
        change min acc.lo entry.lo = entry.lo
        omega
  · apply OrderImpl.foldl_inv
      (fun acc : FramePorts.Span => ∃ high ∈ first :: rest, acc.hi = high.hi)
      _ rest first
    · exact ⟨first, List.mem_cons_self, rfl⟩
    · intro acc previous entry member
      obtain ⟨high, present, equal⟩ := previous
      by_cases left : entry.hi ≤ acc.hi
      · refine ⟨high, present, ?_⟩
        change max acc.hi entry.hi = high.hi
        omega
      · refine ⟨entry, List.mem_cons_of_mem first member, ?_⟩
        change max acc.hi entry.hi = entry.hi
        omega

theorem proxySpan_endpoint_sources {p : Proper} {xs : List Int}
    {owner index : Nat} {span : FramePorts.Span}
    (h : proxySpan p xs owner index = .ok span) :
    ∃ (leftIndex rightIndex : Nat) (left right : ProperNode),
      p.nodes[leftIndex]? = some left ∧ p.nodes[rightIndex]? = some right ∧
      (left.node.border = -1 ∨ left.node.border = 1) ∧
      (right.node.border = -1 ∨ right.node.border = 1) ∧
      left.node.clusterPath.getLast? = some owner ∧
      right.node.clusterPath.getLast? = some owner ∧
      rk p.rank leftIndex = rk p.rank index ∧
      rk p.rank rightIndex = rk p.rank index ∧
      span.lo = xs.getD leftIndex 0 - Int.fdiv left.node.w 2 ∧
      span.hi = xs.getD rightIndex 0 - Int.fdiv right.node.w 2 + right.node.w := by
  let selected := p.nodes.zipIdx.filter (fun entry =>
    (entry.1.node.border == -1 || entry.1.node.border == 1) &&
      entry.1.node.clusterPath.getLast? == some owner &&
      rk p.rank entry.2 == rk p.rank index)
  unfold proxySpan at h
  split at h
  · cases h
  · obtain ⟨spans, hspans, h⟩ := bind_ok h
    change selected.mapM (fun entry =>
      FramePorts.borderSpan (xs.getD entry.2 0) entry.1.node.w) = .ok spans at hspans
    cases spans with
    | nil => cases h
    | cons first rest =>
      have equal : rest.foldl
          (fun a b => (⟨min a.lo b.lo, max a.hi b.hi⟩ : FramePorts.Span)) first = span :=
        Except.ok.inj h
      obtain ⟨⟨low, lowMember, lowEq⟩, ⟨high, highMember, highEq⟩⟩ :=
        span_envelope_extrema first rest
      obtain ⟨left, leftMember, leftSpan⟩ :=
        mapM_output_source _ selected (first :: rest) hspans low lowMember
      obtain ⟨right, rightMember, rightSpan⟩ :=
        mapM_output_source _ selected (first :: rest) hspans high highMember
      have leftInfo := List.mem_filter.mp leftMember
      have rightInfo := List.mem_filter.mp rightMember
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at leftInfo rightInfo
      have lowEnds := borderSpan_endpoints leftSpan
      have highEnds := borderSpan_endpoints rightSpan
      refine ⟨left.2, right.2, left.1, right.1,
        List.mem_zipIdx_iff_getElem?.mp leftInfo.1,
        List.mem_zipIdx_iff_getElem?.mp rightInfo.1,
        leftInfo.2.1.1, rightInfo.2.1.1, leftInfo.2.1.2, rightInfo.2.1.2,
        leftInfo.2.2, rightInfo.2.2, ?_, ?_⟩
      · rw [equal] at lowEq
        exact lowEq.trans lowEnds.1
      · rw [equal] at highEq
        exact highEq.trans (highEnds.2.trans (by rw [highEnds.1]))

theorem componentRun_nonproxy_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _⟩ := componentRun_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

theorem componentRun_proxy_border_extrema {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner leftIndex rightIndex : Nat) (left right : ProperNode),
      node.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[leftIndex]? = some left ∧
      run.coordinateProper.nodes[rightIndex]? = some right ∧
      run.proper.nodes[leftIndex]? = some left ∧
      run.proper.nodes[rightIndex]? = some right ∧
      (left.node.border = -1 ∨ left.node.border = 1) ∧
      (right.node.border = -1 ∨ right.node.border = 1) ∧
      left.node.clusterPath.getLast? = some owner ∧
      right.node.clusterPath.getLast? = some owner ∧
      rk run.coordinateProper.rank leftIndex = rk run.coordinateProper.rank index ∧
      rk run.coordinateProper.rank rightIndex = rk run.coordinateProper.rank index ∧
      RouteImpl.leftOf run.proper run.xs index =
        RouteImpl.leftOf run.proper run.xs leftIndex ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index =
        RouteImpl.leftOf run.proper run.xs rightIndex + RouteImpl.nodeW run.proper rightIndex := by
  obtain ⟨owner, span, ownerEq, hspan, outputNode, width, proxyLeft, proxyRight⟩ :=
    componentRun_proxy_interval h hnode hborder
  obtain ⟨leftIndex, rightIndex, left, right, leftSource, rightSource,
    leftBorder, rightBorder, leftOwner, rightOwner, leftRank, rightRank, lowEq, highEq⟩ :=
    proxySpan_endpoint_sources hspan
  obtain ⟨leftProper, leftX⟩ := componentRun_border_record h leftSource leftBorder
  obtain ⟨rightProper, rightX⟩ := componentRun_border_record h rightSource rightBorder
  have finalLeft : RouteImpl.leftOf run.proper run.xs leftIndex = span.lo := by
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, leftProper, leftX]
    exact lowEq.symm
  have finalRight : RouteImpl.leftOf run.proper run.xs rightIndex +
      RouteImpl.nodeW run.proper rightIndex = span.hi := by
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, rightProper, rightX]
    exact highEq.symm
  exact ⟨owner, leftIndex, rightIndex, left, right, ownerEq, leftSource, rightSource,
    leftProper, rightProper, leftBorder, rightBorder, leftOwner, rightOwner,
    leftRank, rightRank, proxyLeft.trans finalLeft.symm, proxyRight.trans finalRight.symm⟩

theorem componentRun_nonproxy_ordered_intervals
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {first second : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hfirst : run.coordinateProper.nodes[a]? = some first)
    (hsecond : run.coordinateProper.nodes[b]? = some second)
    (hfirstBorder : ¬(first.node.border = -2 ∨ first.node.border = 2))
    (hsecondBorder : ¬(second.node.border = -2 ∨ second.node.border = 2)) :
    RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
      RouteImpl.leftOf run.proper run.xs b := by
  obtain ⟨_, _, _, hcoordinate, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (measuredGraph_shape hgraph) candidate
  have huniq : ∀ (u v : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[v]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = v := by
    intro u v left right hleft hright hleftBorder hrightBorder hpath
    apply pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hleft)
      (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  have hsep := cluster_all_pairs_separated hcross huniq layer hlayer i j a b
    first second hij ha hb hfirst hsecond
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨hfinalFirst, hxa⟩ := componentRun_nonproxy_record hrun hfirst hfirstBorder
  obtain ⟨hfinalSecond, hxb⟩ := componentRun_nonproxy_record hrun hsecond hsecondBorder
  have hwa : RouteImpl.nodeW run.proper a =
      RouteImpl.nodeW run.coordinateProper a := by
    simp only [RouteImpl.nodeW, hfinalFirst, hfirst]
  have hwb : RouteImpl.nodeW run.proper b =
      RouteImpl.nodeW run.coordinateProper b := by
    simp only [RouteImpl.nodeW, hfinalSecond, hsecond]
  have hga : RouteImpl.nodeW run.coordinateProper a ≤
      CoordsImpl.nodeW run.coordinateProper a := CoordsImpl.nodeW_ge_width _ _
  have hgb : RouteImpl.nodeW run.coordinateProper b ≤
      CoordsImpl.nodeW run.coordinateProper b := CoordsImpl.nodeW_ge_width _ _
  have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
    fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
  unfold CoordsImpl.coordSep at hsep
  simp only [e] at hsep
  simp only [RouteImpl.leftOf, RouteImpl.xAt, hxa, hxb, hwa, hwb, e]
  omega

theorem componentRun_proxy_left_alternatives
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {t v : Nat} {proxy other : ProperNode}
    (ht : run.coordinateProper.nodes[t]? = some proxy)
    (hv : run.coordinateProper.nodes[v]? = some other)
    (htBorder : proxy.node.border = -2 ∨ proxy.node.border = 2)
    (hvBorder : ¬(other.node.border = -2 ∨ other.node.border = 2))
    (hrank : rk run.coordinateProper.rank v = rk run.coordinateProper.rank t) :
    RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
        RouteImpl.leftOf run.proper run.xs t ∨
      RouteImpl.leftOf run.proper run.xs t ≤ RouteImpl.leftOf run.proper run.xs v := by
  obtain ⟨_, side, _, sideNode, _, _, hside, _, hfinalSide, _, hsideBorder, _,
    _, _, hsideRank, _, hleft, _⟩ := componentRun_proxy_border_extrema hrun ht htBorder
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, hcross, _⟩ :=
    componentRun_spec hrun
  have hlay : OrderImpl.lay run.coordinateProper v =
      OrderImpl.lay run.coordinateProper side := by
    unfold OrderImpl.lay
    rw [hrank, hsideRank]
  obtain ⟨hsideBound, hsideMem⟩ :=
    ExecutedBorderOrder.node_layer _ _ ord horder hside
  have hotherMem := (ExecutedBorderOrder.node_layer _ _ ord horder hv).2
  rw [hlay] at hotherMem
  let layer := ord.layers.getD (OrderImpl.lay run.coordinateProper side) []
  have hlayerOrd : layer ∈ ord.layers := by
    have heq : layer = ord.layers[OrderImpl.lay run.coordinateProper side] := by
      simp [layer, List.getD_eq_getElem?_getD, hsideBound]
    rw [heq]
    exact List.getElem_mem hsideBound
  have hlayer : layer ∈ run.layers := by
    rw [← hlayers]
    exact hlayerOrd
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hsideMem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hotherMem
  have hsideNotProxy : ¬(sideNode.node.border = -2 ∨ sideNode.node.border = 2) := by
    rcases hsideBorder with hb | hb <;> omega
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayer
      hij hi hj hside hv hsideNotProxy hvBorder
    obtain ⟨_, _, _, hs, _⟩ := crossCoordsClusterWith_spec hcross
    have hsize : 0 ≤ sideNode.node.w ∧ 0 ≤ sideNode.node.h :=
      of_decide_eq_true (List.all_eq_true.mp hs sideNode (List.mem_of_getElem? hside))
    have hw : 0 ≤ RouteImpl.nodeW run.proper side := by
      simpa only [RouteImpl.nodeW, hfinalSide] using hsize.1
    right
    rw [hleft]
    omega
  · have hsame : side = v := by
      rw [hij] at hi
      exact Option.some.inj (hi.symm.trans hj)
    right
    simpa only [hleft, hsame] using
      (Int.le_refl (RouteImpl.leftOf run.proper run.xs v))
  · have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayer
      hij hj hi hv hside hvBorder hsideNotProxy
    left
    rw [hleft]
    exact hsep

theorem componentRun_top_clearance
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) :
    ∀ layer ∈ run.layers, ∀ t v : Nat, t ∈ layer → v ∈ layer →
      RouteImpl.IsTop run.proper t → v ≠ t → ¬ RouteImpl.IsFrame run.proper v →
      0 < RouteImpl.nodeH run.proper v →
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs t ∨
        RouteImpl.leftOf run.proper run.xs t ≤ RouteImpl.leftOf run.proper run.xs v := by
  obtain ⟨_, _, _, routed, _, _, hcoordinate, _, _, hproxy, hdrop,
    hroute, _⟩ := componentRun_spec hrun
  obtain ⟨_, hrank, hlength, _, hrecords, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact hrank
  have source : ∀ index, index < run.proper.nodes.length →
      ∃ original final : ProperNode,
        run.coordinateProper.nodes[index]? = some original ∧
        run.proper.nodes[index]? = some final ∧
        final.node.border = original.node.border ∧ final.node.h = original.node.h := by
    intro index hindex
    have hsourceIndex : index < run.coordinateProper.nodes.length := by
      rw [hnodes] at hindex
      omega
    have hsource : run.coordinateProper.nodes[index]? =
        some (run.coordinateProper.nodes[index]'hsourceIndex) :=
      List.getElem?_eq_getElem hsourceIndex
    obtain ⟨final, hfinal, _, hborder, hheight⟩ := hrecords index _ hsource
    exact ⟨_, final, hsource, by rw [hnodes]; exact hfinal, hborder, hheight⟩
  have hmembers := (RouteImpl.layersOk_spec
    (RouteImpl.routeWithLanes_geometry hroute).1).2.2.1
  intro layer hlayer t v htmem hvmem htop _ _ hheight
  obtain ⟨layerIndex, hlayerIndex⟩ := List.mem_iff_getElem?.mp hlayer
  obtain ⟨htbound, htrank⟩ := hmembers layerIndex layer hlayerIndex t htmem
  obtain ⟨hvbound, hvrank⟩ := hmembers layerIndex layer hlayerIndex v hvmem
  obtain ⟨proxy, finalProxy, ht, htfinal, htborder, _⟩ := source t htbound
  obtain ⟨other, finalOther, hv, hvfinal, _, hvheight⟩ := source v hvbound
  have htBorder : proxy.node.border = -2 ∨ proxy.node.border = 2 := by
    left
    rw [← htborder]
    exact ((isTop_iff htfinal).mp htop).2
  have hvBorder : ¬(other.node.border = -2 ∨ other.node.border = 2) := by
    intro hborder
    have hzero := pc_frame_flat (by rw [hcoordinate]; exact hv) hborder
    have hheightValue : RouteImpl.nodeH run.proper v = finalOther.node.h := by
      simp only [RouteImpl.nodeH, hvfinal]
    rw [hheightValue, hvheight, hzero] at hheight
    omega
  apply componentRun_proxy_left_alternatives hgraph hcomp hrun ht hv htBorder hvBorder
  rw [← hranks, hvrank, htrank]

private theorem normalize_chain_rank_positions {graph : Graph} {ranks : List Int}
    {normalized : Proper} (hnormalize : normalize graph ranks = .ok normalized)
    {index : Nat} {edge : Edge} {chain : List Nat}
    (hedge : graph.edges[index]? = some edge)
    (hchain : normalized.chains[index]? = some chain) :
    ∀ position (hposition : position < chain.length),
      rk normalized.rank (chain[position]'hposition) =
        rk normalized.rank edge.tail + (position : Int) := by
  have hindex := (List.getElem?_eq_some_iff.mp hedge).1
  have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
  by_cases hself : edge.tail = edge.head
  · have hempty : chain = [] := by
      have h := hfact.2
      simp only [hself, ↓reduceIte] at h
      exact Option.some.inj (hchain.symm.trans h)
    intro position hposition
    simp only [hempty, List.length_nil] at hposition
    omega
  · obtain ⟨actual, hactual, _, hhead, _, hadjacent⟩ :
        ∃ actual, normalized.chains[index]? = some actual ∧
          2 ≤ actual.length ∧ actual.head? = some edge.tail ∧
          actual.getLast? = some edge.head ∧
          ∀ (j : Nat) (hj : j < actual.length) (hj1 : j + 1 < actual.length),
            ∃ pe ∈ normalized.edges, pe.original = index ∧ pe.decl = edge.decl ∧
              pe.tail = actual[j] ∧ pe.head = actual[j + 1] := by
      simpa only [hself, ↓reduceIte] using hfact.2
    have hactualEq : chain = actual := Option.some.inj (hchain.symm.trans hactual)
    subst actual
    intro position
    induction position with
    | zero =>
      intro hposition
      have hzero : chain[0]? = some edge.tail := by
        rw [← List.head?_eq_getElem?]
        exact hhead
      have hfirst : chain[0]'hposition = edge.tail :=
        Option.some.inj ((List.getElem?_eq_getElem hposition).symm.trans hzero)
      rw [hfirst]
      change rk normalized.rank edge.tail = rk normalized.rank edge.tail + (0 : Int)
      omega
    | succ position ih =>
      intro hposition
      have hprevious : position < chain.length := by omega
      obtain ⟨pe, hpe, _, _, htail, hnext⟩ := hadjacent position hprevious hposition
      have hstep := normalize_proper graph ranks normalized hnormalize pe hpe
      unfold Proper.span at hstep
      rw [htail, hnext] at hstep
      have hprefix := ih hprevious
      omega

theorem componentRun_labeled_chain_rank_positions
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      ∀ (index : Nat) (edge : Edge) (chain : List Nat),
        cg.edges[index]? = some edge → labeled.chains[index]? = some chain →
        ∀ position (hposition : position < chain.length),
          rk labeled.rank (chain[position]'hposition) =
            rk labeled.rank edge.tail + (position : Int) := by
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, _⟩ :=
    componentRun_ranked_source hrun
  refine ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, ?_⟩
  intro index edge chain hedge hchain position hposition
  have metadata := Labels.addLabelNodes_metadata hlabels
  rw [metadata.2.2.1] at hchain
  rw [metadata.2.1]
  exact normalize_chain_rank_positions hnormalize hedge hchain position hposition

theorem componentRun_dummy_path_chain_source
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v owner : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hdummy : node.dummy = true) (howner : owner ∈ node.node.clusterPath) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper)
      (index : Nat) (edge : Edge) (chain : List Nat) (position : Nat),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      cg.edges[index]? = some edge ∧ labeled.chains[index]? = some chain ∧
      chain[position]? = some v ∧ chain.head? = some edge.tail ∧
      chain.getLast? = some edge.head ∧
      rk labeled.rank v = rk labeled.rank edge.tail + (position : Int) ∧
      let prepared := clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)
      prepared.chains.find? (fun members => members.contains v) = some chain ∧
      owner ∈ (prepared.nodes.getD (chain.headD v) default).node.clusterPath ∧
      owner ∈ (prepared.nodes.getD (chain.getLastD v) default).node.clusterPath := by
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, hpositions⟩ :=
    componentRun_labeled_chain_rank_positions hrun
  let prepared := clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)
  have hmaterialized : (materializeDummyPaths prepared).nodes[v]? = some node := by
    rw [← hcoordinate] at hv
    exact hv
  obtain ⟨before, hbefore, hd, _, _, _⟩ := materialize_lookup prepared hmaterialized
  have hbeforeDummy : before.dummy = true := hd.symm.trans hdummy
  have hpath : node.node.clusterPath = OrderImpl.nodePath prepared v := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
      hbefore, Option.map_some, hbeforeDummy, ↓reduceIte, Option.some.injEq] at hmaterialized
    rw [← hmaterialized]
    simp only [Nat.zero_add]
  have hselected : node.node.clusterPath =
      match prepared.chains.find? (fun members => members.contains v) with
      | none => []
      | some chain => OrderImpl.commonPath
          ((prepared.nodes.getD (chain.headD v) default).node.clusterPath)
          ((prepared.nodes.getD (chain.getLastD v) default).node.clusterPath) := by
    rw [hpath]
    simp [OrderImpl.nodePath, List.getD_eq_getElem?_getD, hbefore, hbeforeDummy]
    rfl
  cases hfind : prepared.chains.find? (fun members => members.contains v) with
  | none =>
    simp only [hfind] at hselected
    rw [hselected] at howner
    exact False.elim (List.not_mem_nil howner)
  | some chain =>
    have hchains : prepared.chains = labeled.chains := by
      exact (OrderImpl.addClusterBorders_metadata
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW).2.1
    have hchainMember : chain ∈ prepared.chains := List.mem_of_find?_eq_some hfind
    rw [hchains] at hchainMember
    obtain ⟨index, hchain⟩ := List.mem_iff_getElem?.mp hchainMember
    have hnormalizedChain : normalized.chains[index]? = some chain := by
      rw [← (Labels.addLabelNodes_metadata hlabels).2.2.1]
      exact hchain
    have hindex : index < cg.edges.length := by
      have hbound := (List.getElem?_eq_some_iff.mp hnormalizedChain).1
      rw [normalize_chains_length hnormalize] at hbound
      exact hbound
    have hedge : cg.edges[index]? = some (cg.edges[index]'hindex) :=
      List.getElem?_eq_getElem hindex
    have hmember : v ∈ chain := by
      simpa only [List.contains_iff_mem] using List.find?_some hfind
    obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hmember
    have hpositionBound := (List.getElem?_eq_some_iff.mp hposition).1
    have hpositionValue : chain[position]'hpositionBound = v :=
      Option.some.inj ((List.getElem?_eq_getElem hpositionBound).symm.trans hposition)
    have hfact := (normalize_ok hnormalize).2.2 index hindex _ hedge
    by_cases hself : (cg.edges[index]'hindex).tail = (cg.edges[index]'hindex).head
    · have hempty : chain = [] := by
        have h := hfact.2
        simp only [hself, ↓reduceIte] at h
        exact Option.some.inj (hnormalizedChain.symm.trans h)
      rw [hempty] at hmember
      exact False.elim (List.not_mem_nil hmember)
    · obtain ⟨actual, hactual, _, hhead, hlast, _⟩ := by
        simpa only [hself, ↓reduceIte] using hfact.2
      have hactualEq : chain = actual :=
        Option.some.inj (hnormalizedChain.symm.trans hactual)
      subst actual
      have hrank := hpositions index _ chain hedge hchain position hpositionBound
      rw [hpositionValue] at hrank
      have hownerCommon := howner
      rw [hselected, hfind] at hownerCommon
      obtain ⟨hleftOwner, hrightOwner⟩ := commonPath_member_both _ _ hownerCommon
      exact ⟨rr, normalized, labeled, index, _, chain, position, hrr, hnormalize,
        hlabels, hcoordinate, hedge, hchain, hposition, hhead, hlast, hrank,
        hfind, hleftOwner, hrightOwner⟩

end Elegant.Layered.PipelineImpl
