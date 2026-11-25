import Elegant.Layered.PipelineFacts
import Elegant.Layered.RouteTransport
import Elegant.Layered.SizingFacts
import Elegant.Layered.GroupFrameSizingFacts

set_option autoImplicit false

namespace Elegant.Layered.Loops

private theorem fraction_bounds (height : Int) (count index : Nat)
    (offset : Int) (hh : 0 ≤ height) (hi : index < count)
    (ho : 1 ≤ offset ∧ offset ≤ 2) :
    0 ≤ Int.fdiv ((2 * (index : Int) + offset) * height) (2 * (count : Int) + 1) ∧
    Int.fdiv ((2 * (index : Int) + offset) * height) (2 * (count : Int) + 1) ≤ height := by
  have hd : 0 < 2 * (count : Int) + 1 := by omega
  have hn : 0 ≤ 2 * (index : Int) + offset := by omega
  have hu : 2 * (index : Int) + offset ≤ 2 * (count : Int) + 1 := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  constructor
  · exact Int.ediv_nonneg (Int.mul_nonneg hn hh) (by omega)
  · have hm := Int.mul_le_mul_of_nonneg_right hu hh
    have he := Int.ediv_le_ediv (c := 2 * (count : Int) + 1) hd hm
    simpa only [Int.mul_comm (2 * (count : Int) + 1) height,
      Int.mul_ediv_cancel _ (by omega : 2 * (count : Int) + 1 ≠ 0)] using he

theorem exactPlacement_boundary (node : Rect) (slot loopBand : Int)
    (count index : Nat) (label : LoopLabel)
    (hw : 0 ≤ node.w) (hh : 0 ≤ node.h) (hi : index < count) :
    ∃ start finish : Point,
      (exactPlacement node slot loopBand count index label).points.head? = some start ∧
      (exactPlacement node slot loopBand count index label).points.getLast? = some finish ∧
      Validator.onBoundary start node ∧ Validator.onBoundary finish node := by
  have ha := fraction_bounds node.h count index 1 hh hi ⟨by omega, by omega⟩
  have hb := fraction_bounds node.h count index 2 hh hi ⟨by omega, by omega⟩
  refine ⟨⟨node.x + node.w,
      node.y + Int.fdiv ((2 * (index : Int) + 1) * node.h) (2 * (count : Int) + 1)⟩,
    ⟨node.x + node.w,
      node.y + Int.fdiv ((2 * (index : Int) + 2) * node.h) (2 * (count : Int) + 1)⟩,
    rfl, rfl, ?_, ?_⟩ <;>
    simp only [Validator.onBoundary] <;>
    exact ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inl True.intro)⟩

theorem placement_boundary (node : Rect) (slot loopBand : Int)
    (count index : Nat) (label : LoopLabel) (hw : 0 ≤ node.w)
    (hlo : 0 ≤ (index : Int) * loopBand + Int.fdiv loopBand 2 - slot)
    (hhi : (index : Int) * loopBand + Int.fdiv loopBand 2 + slot ≤ node.h)
    (hs : 0 ≤ slot) :
    ∃ start finish : Point,
      (placement node slot loopBand count index label).points.head? = some start ∧
      (placement node slot loopBand count index label).points.getLast? = some finish ∧
      Validator.onBoundary start node ∧ Validator.onBoundary finish node := by
  obtain ⟨ha, hb⟩ := placement_ports node slot loopBand count index label
  refine ⟨_, _, ha, hb, ?_, ?_⟩ <;>
    simp only [Validator.onBoundary] <;>
    exact ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inl True.intro)⟩

private theorem fold_max_ge (labels : List LoopLabel) (initial : Int) :
    initial ≤ labels.foldl (fun h l => max h l.height) initial := by
  induction labels generalizing initial with
  | nil => exact Int.le_refl _
  | cons label rest ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem placement_boundary_of_reservation (node : Rect) (slot : Int)
    (labels : List LoopLabel) (index : Nat) (label : LoopLabel)
    (hw : 0 ≤ node.w) (hs : 0 ≤ slot) (hi : index < labels.length)
    (hh : requiredHeight slot labels ≤ node.h) :
    ∃ start finish : Point,
      (placement node slot (band slot labels) labels.length index label).points.head? = some start ∧
      (placement node slot (band slot labels) labels.length index label).points.getLast? = some finish ∧
      Validator.onBoundary start node ∧ Validator.onBoundary finish node := by
  have hb : 2 * slot ≤ band slot labels := fold_max_ge labels (2 * slot)
  have hb0 : 0 ≤ band slot labels := by omega
  have hm0 := Int.mul_nonneg (Int.natCast_nonneg index) hb0
  have hm := Int.mul_le_mul_of_nonneg_right
    (show (index : Int) + 1 ≤ 2 * (labels.length : Int) by omega) hb0
  have hhalf : slot ≤ Int.fdiv (band slot labels) 2 := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  have hhalf' : Int.fdiv (band slot labels) 2 + slot ≤ band slot labels := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  apply placement_boundary node slot (band slot labels) labels.length index label hw
  · omega
  · simp only [requiredHeight] at hh
    rw [Int.add_mul, Int.one_mul] at hm
    omega
  · exact hs

theorem exactLoops_boundary {node : Rect} {slot : Int} {labels : List LoopLabel}
    {out : List LoopPlacement} (h : exactLoops node slot labels = .ok out)
    {p : LoopPlacement} (hp : p ∈ out) :
    ∃ start finish : Point, p.points.head? = some start ∧
      p.points.getLast? = some finish ∧
      Validator.onBoundary start node ∧ Validator.onBoundary finish node := by
  unfold exactLoops at h
  dsimp only at h
  split at h
  · contradiction
  · next hn =>
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · cases h
          obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hp
          have hi := List.snd_lt_of_mem_zipIdx he
          have hv : node.Valid := by omega
          exact exactPlacement_boundary node slot (band slot labels) labels.length
            entry.2 entry.1 hv.1 hv.2.1 (by simpa using hi)
        · contradiction

theorem loops_boundary_of_reservation {node : Rect} {slot : Int}
    {labels : List LoopLabel} {out : List LoopPlacement}
    (h : loops node slot labels = .ok out)
    (hh : requiredHeight slot labels ≤ node.h)
    {p : LoopPlacement} (hp : p ∈ out) :
    ∃ start finish : Point, p.points.head? = some start ∧
      p.points.getLast? = some finish ∧
      Validator.onBoundary start node ∧ Validator.onBoundary finish node := by
  unfold loops at h
  dsimp only at h
  split at h
  · contradiction
  · next hn =>
    split at h
    · contradiction
    · next hs =>
      split at h
      · contradiction
      · split at h
        · cases h
          obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hp
          have hi := List.snd_lt_of_mem_zipIdx he
          have hv : node.Valid := by omega
          exact placement_boundary_of_reservation node slot labels entry.2 entry.1
            hv.1 (by omega) (by simpa using hi) hh
        · contradiction

end Elegant.Layered.Loops

namespace Elegant.Layered.PipelineImpl

private theorem mapM_member_origin {α β : Type} (f : α → Except LayoutError β)
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    have he : [] = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst ys
    simp at hy
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    have he : b :: bs = ys := Except.ok.inj h
    subst ys
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, by simp, hb⟩
    · obtain ⟨a, ha, he⟩ := ih hbs hy
      exact ⟨a, List.mem_cons_of_mem _ ha, he⟩

theorem measuredGraph_loop_reservation_before_prepare
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) :
    ∃ (metric : Measure.Metric) (labels : List MeasuredLabel) (raw : Graph),
      metricOf o.profile o.fontFamily = .ok metric ∧
      measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp o.direction = .ok labels ∧
      graphEdges inp = .ok raw.edges ∧ raw.slot = P.slot ∧
      g = Compound.prepare
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
        P.clusterPad
        (lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * P.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height)) raw ∧
      ∀ (i : Nat) (node : Node), raw.nodes[i]? = some node →
        Loops.requiredHeight P.slot (loopSizes raw.edges labels i P.slot) ≤ node.h := by
  unfold measuredGraph at hg
  obtain ⟨initial, _, hg⟩ := bind_ok hg
  obtain ⟨edges, he, hg⟩ := bind_ok hg
  obtain ⟨metric, hm, hg⟩ := bind_ok hg
  obtain ⟨labels, hl, hg⟩ := bind_ok hg
  obtain ⟨nodes, hn, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  refine ⟨metric, labels, { nodes := nodes, edges := edges, slot := P.slot },
    hm, hl, he, rfl, hgraph.symm, ?_⟩
  intro i node hnode
  change nodes[i]? = some node at hnode
  obtain ⟨hlen, hprocessed⟩ := mapM_getElem? _ _ _ hn
  have hi : i < initial.length := by
    have hi := (List.getElem?_eq_some_iff.mp hnode).1
    simp only [List.length_zipIdx, List.length_map] at hlen
    omega
  have hbefore : initial[i]? = some initial[i] := List.getElem?_eq_getElem hi
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed i (orientNode o.direction initial[i], i)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have heq : after = node := Option.some.inj (hafter.symm.trans hnode)
  subst after
  dsimp only at hstep
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hstep
  repeat' (first | split at hstep | contradiction)
  all_goals
    have heq := Except.ok.inj hstep
    subst node
    dsimp only
    first | exact Int.le_refl _ | exact Int.le_max_right _ _

theorem componentLoops_entry_origin
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {out : List (Nat × LoopPlacement)}
    (h : componentLoops P cg run labels = .ok out)
    {q : Nat × LoopPlacement} (hq : q ∈ out) :
    ∃ v, v < cg.nodes.length ∧ ∃ placements : List LoopPlacement,
      (if run.exact.contains v then Loops.exactLoops else Loops.loops)
        (frameRect P cg run v) cg.slot (loopSizes cg.edges labels v cg.slot) =
          .ok placements ∧
      ∃ edge : Edge, (edge, q.2) ∈ (loopEdges cg.edges v).zip placements ∧
        q.1 = edge.decl ∧ edge.tail = v ∧ edge.head = v := by
  unfold componentLoops at h
  obtain ⟨groups, hg, h⟩ := bind_ok h
  have he : groups.flatten = out := Except.ok.inj h
  subst out
  obtain ⟨group, hm, hq⟩ := List.mem_flatten.mp hq
  obtain ⟨v, hv, hgroup⟩ := mapM_member_origin _ hg hm
  obtain ⟨placements, hp, hgroup⟩ := bind_ok hgroup
  have he := Except.ok.inj hgroup
  subst group
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hq
  have hedge : entry.1 ∈ loopEdges cg.edges v := (List.of_mem_zip hentry).1
  have hfilter := (List.mem_filter.mp hedge).2
  have hend : entry.1.tail = v ∧ entry.1.head = v := by simpa only [Bool.and_eq_true, beq_iff_eq] using hfilter
  cases heq
  exact ⟨v, List.mem_range.mp hv, placements, hp, entry.1, hentry, rfl, hend⟩

theorem componentLoops_entry_misses_owner
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops)
    {entry : Nat × LoopPlacement} (hentry : entry ∈ loops) :
    ∃ v, v < cg.nodes.length ∧ ∃ edge ∈ loopEdges cg.edges v,
      entry.1 = edge.decl ∧ edge.tail = v ∧ edge.head = v ∧
      ¬ Polyline.hitsRect entry.2.points (frameRect P cg run v) := by
  obtain ⟨v, hv, placements, hp, edge, hzip, hdecl, htail, hhead⟩ :=
    componentLoops_entry_origin hloops hentry
  have hm := (List.of_mem_zip hzip).2
  have hmiss : ¬ Polyline.hitsRect entry.2.points (frameRect P cg run v) := by
    split at hp
    · exact Loops.exactLoops_result_outside_node hp entry.2 hm
    · exact Loops.loops_result_outside_node hp entry.2 hm
  exact ⟨v, hv, edge, (List.of_mem_zip hzip).1, hdecl, htail, hhead, hmiss⟩

theorem componentLoops_excludes_ordinary_decl
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops)
    (hdecls : (cg.edges.map Edge.decl).Nodup)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∀ l ∈ loops, l.1 ≠ edge.decl := by
  intro l hl heq
  obtain ⟨v, _, placements, _, loop, hzip, hdecl, htail, hhead⟩ :=
    componentLoops_entry_origin hloops hl
  have hmem : loop ∈ cg.edges :=
    (List.mem_filter.mp (List.of_mem_zip hzip).1).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hmap : (cg.edges.map Edge.decl)[i]? =
      (cg.edges.map Edge.decl)[j]? := by
    simp only [List.getElem?_map, hedge, hj, Option.map_some]
    exact congrArg some (heq.symm.trans hdecl)
  have hi : i < (cg.edges.map Edge.decl).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
  have hij : i = j := (hdecls.getElem?_inj hi).mp hmap
  have hedgeloop : edge = loop := by
    subst j
    exact Option.some.inj (hedge.symm.trans hj)
  apply hne
  rw [hedgeloop, htail, hhead]

theorem componentLoops_exact_entry_attachment
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {out : List (Nat × LoopPlacement)}
    (h : componentLoops P cg run labels = .ok out)
    {q : Nat × LoopPlacement} (hq : q ∈ out)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ v, v < cg.nodes.length ∧ ∃ placements : List LoopPlacement,
      ∃ edge : Edge, (edge, q.2) ∈ (loopEdges cg.edges v).zip placements ∧
      q.1 = edge.decl ∧ edge.tail = v ∧ edge.head = v ∧
      (run.exact.contains v = true →
        ∃ start finish : Point,
          q.2.points.head? = some start ∧ q.2.points.getLast? = some finish ∧
          let bounds := placeBounds P cg run labels out
          let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
          let rect := shiftRect margin margin (orientRect direction canvasH
            (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) (frameRect P cg run v)))
          Validator.onBoundary (transport start) rect ∧
            Validator.onBoundary (transport finish) rect) := by
  obtain ⟨v, hv, placements, hp, edge, he, hdecl, htail, hhead⟩ :=
    componentLoops_entry_origin h hq
  refine ⟨v, hv, placements, edge, he, hdecl, htail, hhead, ?_⟩
  intro hexact
  rw [hexact, ite_eq_left rfl] at hp
  obtain ⟨start, finish, hs, ht, hsb, htb⟩ :=
    Loops.exactLoops_boundary hp (List.of_mem_zip he).2
  refine ⟨start, finish, hs, ht, ?_⟩
  dsimp only
  constructor
  · apply (onBoundary_shift _ _ _ _).mpr
    apply (onBoundary_orient _ _ _ _).mpr
    exact (onBoundary_shift _ _ _ _).mpr hsb
  · apply (onBoundary_shift _ _ _ _).mpr
    apply (onBoundary_orient _ _ _ _).mpr
    exact (onBoundary_shift _ _ _ _).mpr htb

private theorem compound_endpoint_self (boxes : List ModelBox) (source : Bool) (v : Nat) :
    Compound.endpoint boxes source v v = v := by
  cases hb : boxes[v]? <;> simp [Compound.endpoint, hb]

private theorem compound_endpoint_preimage (boxes : List ModelBox)
    (source : Bool) (index other v : Nat) (hv : v < boxes.length)
    (h : Compound.endpoint boxes source index other = v) : index = v := by
  cases hi : boxes[index]? <;> cases ho : boxes[other]?
  all_goals simp only [Compound.endpoint, hi, ho] at h
  all_goals first
    | exact h
    | split at h
      · exact h
      · split at h
        · exact h
        · unfold Compound.bottomIndex at h
          omega

theorem prepare_loopEdges_preserved (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (raw : Graph) (v : Nat) (hv : v < boxes.length) :
    loopEdges (Compound.prepare boxes pad titles raw).edges v = loopEdges raw.edges v := by
  have hlist : ∀ edges : List Edge,
      loopEdges (edges.map (Compound.aliasEdge boxes)) v = loopEdges edges v := by
    intro edges
    induction edges with
    | nil => rfl
    | cons edge edges ih =>
      have hiff :
          ((Compound.aliasEdge boxes edge).tail == v &&
            (Compound.aliasEdge boxes edge).head == v) = true ↔
          (edge.tail == v && edge.head == v) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]
        constructor
        · intro h
          exact ⟨compound_endpoint_preimage boxes true edge.tail edge.head v hv h.1,
            compound_endpoint_preimage boxes false edge.head edge.tail v hv h.2⟩
        · rintro ⟨ht, hh⟩
          simp [Compound.aliasEdge, ht, hh, compound_endpoint_self]
      by_cases he : (edge.tail == v && edge.head == v) = true
      · have hend : edge.tail = v ∧ edge.head = v := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using he
        have hid : Compound.aliasEdge boxes edge = edge := by
          cases edge
          simp_all only [Compound.aliasEdge, compound_endpoint_self]
        simp only [loopEdges, List.map_cons, List.filter_cons, he,
          ↓reduceIte, hid] at ih ⊢
        exact congrArg (List.cons edge) ih
      · have ha : ((Compound.aliasEdge boxes edge).tail == v &&
            (Compound.aliasEdge boxes edge).head == v) = false :=
          Bool.eq_false_iff.mpr (fun h => he (hiff.mp h))
        have he' : (edge.tail == v && edge.head == v) = false := Bool.eq_false_iff.mpr he
        simpa only [loopEdges, List.map_cons, List.filter_cons, ha, he',
          Bool.false_eq_true, ↓reduceIte] using ih
  exact hlist raw.edges

theorem prepare_loopSizes_preserved (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (raw : Graph) (v : Nat) (hv : v < boxes.length)
    (labels : List MeasuredLabel) (slot : Int) :
    loopSizes (Compound.prepare boxes pad titles raw).edges labels v slot =
      loopSizes raw.edges labels v slot := by
  unfold loopSizes
  rw [prepare_loopEdges_preserved boxes pad titles raw v hv]

private theorem measuredGraph_node_count
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) :
    let boxes := inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box
    g.nodes.length = lines.length +
      (boxes.zipIdx.filter (fun q => q.1.role == .group)).length := by
  unfold measuredGraph at hg
  obtain ⟨initial, hi, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hn, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  subst g
  have hfirst := (mapM_getElem? _ _ _ hi).1
  have hsecond := (mapM_getElem? _ _ _ hn).1
  simp only [List.length_zipIdx, List.length_map] at hfirst hsecond
  dsimp only [Compound.prepare]
  rw [Compound.markNodes_length]
  omega

theorem measuredGraph_ordinary_loop_reservation
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} (hi : i < lines.length)
    {box : ModelBox} (hb : inp.boxes[i]? = some box) (hrole : box.role = .node) :
    ∃ (metric : Measure.Metric) (labels : List MeasuredLabel) (node : Node),
      metricOf o.profile o.fontFamily = .ok metric ∧
      measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp o.direction = .ok labels ∧
      g.nodes[i]? = some node ∧
      Loops.requiredHeight g.slot (loopSizes g.edges labels i g.slot) ≤ node.h := by
  obtain ⟨metric, labels, raw, hm, hl, _, hslot, hprepare, hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare hg
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  change g = Compound.prepare boxes P.clusterPad titles raw at hprepare
  have hcount := measuredGraph_node_count hg
  change g.nodes.length = lines.length +
    (boxes.zipIdx.filter (fun q => q.1.role == .group)).length at hcount
  have hrawlen : raw.nodes.length = lines.length := by
    rw [hprepare] at hcount
    change (Compound.markNodes boxes P.clusterPad titles raw.nodes).length = _ at hcount
    rw [Compound.markNodes_length] at hcount
    omega
  have hiraw : i < raw.nodes.length := by omega
  have hraw : raw.nodes[i]? = some raw.nodes[i] := List.getElem?_eq_getElem hiraw
  let sourceBox := if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
    { box with role := .node } else box
  have hbox : boxes[i]? = some sourceBox := by
    simp only [boxes, sourceBox, List.getElem?_map, hb, Option.map_some]
  have hsource : sourceBox.role = .node := by
    dsimp only [sourceBox]
    split <;> simp_all
  have hrecord := prepare_node_record boxes P.clusterPad titles raw hraw hbox hsource
  refine ⟨metric, labels,
    { raw.nodes[i] with clusterPath := Compound.path boxes sourceBox }, hm, hl, ?_, ?_⟩
  · rw [hprepare]
    exact hrecord
  · rw [hprepare]
    change Loops.requiredHeight raw.slot
      (loopSizes (Compound.prepare boxes P.clusterPad titles raw).edges labels i raw.slot) ≤
        raw.nodes[i].h
    rw [prepare_loopSizes_preserved boxes P.clusterPad titles raw i
      (by simpa only [boxes, List.length_map] using
        (List.getElem?_eq_some_iff.mp hb).1) labels raw.slot, hslot]
    exact hreserve i raw.nodes[i] hraw

private theorem component_idxOf_eq_iff {component : List Nat}
    (hn : component.Nodup) (v : Nat) (hv : v < component.length) (source : Nat) :
    component.idxOf source = v ↔ source = component[v] := by
  constructor
  · intro he
    have hb : component.idxOf source < component.length := by omega
    have hget := List.getElem_idxOf hb
    simpa only [he] using hget.symm
  · intro he
    subst source
    exact hn.idxOf_getElem v hv

theorem componentGraph_loopEdges_preserved (g : Graph) (component : List Nat)
    (hn : component.Nodup) (v : Nat) (hv : v < component.length) :
    loopEdges (componentGraph g component).edges v =
      (loopEdges g.edges component[v]).map fun edge =>
        { edge with tail := v, head := v } := by
  let renumber := fun edge : Edge =>
    { edge with tail := component.idxOf edge.tail, head := component.idxOf edge.head }
  have hlist : ∀ edges : List Edge,
      loopEdges ((edges.filter fun edge => component.contains edge.tail).map renumber) v =
      (loopEdges edges component[v]).map (fun edge => { edge with tail := v, head := v }) := by
    intro edges
    induction edges with
    | nil => rfl
    | cons edge edges ih =>
      have hiff :
          ((renumber edge).tail == v && (renumber edge).head == v) = true ↔
          (edge.tail == component[v] && edge.head == component[v]) = true := by
        simp only [renumber, Bool.and_eq_true, beq_iff_eq,
          component_idxOf_eq_iff hn v hv]
      by_cases he : (edge.tail == component[v] && edge.head == component[v]) = true
      · have hend : edge.tail = component[v] ∧ edge.head = component[v] := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using he
        have hcontains : component.contains edge.tail = true := by
          rw [List.contains_iff_mem, hend.1]
          exact List.getElem_mem hv
        have hrenumber : renumber edge = { edge with tail := v, head := v } := by
          simp only [renumber, hend.1, hend.2, hn.idxOf_getElem v hv]
        simp only [List.filter_cons, hcontains, ↓reduceIte, List.map_cons, loopEdges,
          he, hrenumber] at ih ⊢
        simpa using congrArg (List.cons { edge with tail := v, head := v }) ih
      · have hlocal : ((renumber edge).tail == v && (renumber edge).head == v) = false :=
          Bool.eq_false_iff.mpr (fun h => he (hiff.mp h))
        have he' : (edge.tail == component[v] && edge.head == component[v]) = false :=
          Bool.eq_false_iff.mpr he
        cases hc : component.contains edge.tail <;>
          simpa only [List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte, List.map_cons,
            loopEdges, hlocal, he'] using ih
  exact hlist g.edges

theorem componentGraph_loopSizes_preserved (g : Graph) (component : List Nat)
    (hn : component.Nodup) (v : Nat) (hv : v < component.length)
    (labels : List MeasuredLabel) (slot : Int) :
    loopSizes (componentGraph g component).edges labels v slot =
      loopSizes g.edges labels component[v] slot := by
  unfold loopSizes
  rw [componentGraph_loopEdges_preserved g component hn v hv, List.map_map]
  rfl

private theorem loopSizes_original (edges : List Edge) (labels : List MeasuredLabel)
    (v : Nat) (slot : Int) :
    loopSizes (edges.map Edge.original) labels v slot = loopSizes edges labels v slot := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
    by_cases ht : edge.tail = v <;> by_cases hh : edge.head = v <;>
      cases hr : edge.reversed <;>
      simp [loopSizes, loopEdges, Edge.original, hr, ht, hh] at ih ⊢ <;>
      exact ih

private theorem loopSizes_of_originals {left right : List Edge}
    (h : left.map Edge.original = right.map Edge.original)
    (labels : List MeasuredLabel) (v : Nat) (slot : Int) :
    loopSizes left labels v slot = loopSizes right labels v slot := by
  rw [← loopSizes_original left labels v slot, h, loopSizes_original right labels v slot]

private theorem loopSizes_cycleGraph (g : Graph) (labels : List MeasuredLabel)
    (v : Nat) (slot : Int) :
    loopSizes (cycleGraph g).edges labels v slot = loopSizes g.edges labels v slot := by
  unfold cycleGraph
  split
  · exact loopSizes_of_originals
      (ProtectedCycles.semantic_identity g (Compound.constraints g)) labels v slot
  · apply loopSizes_of_originals ?_ labels v slot
    rw [breakCycles_edges_eq, List.map_map]
    apply List.map_congr_left
    intro edge _
    change (g.orient edge).original = edge.original
    unfold Graph.orient
    split
    · exact Edge.reverse_original edge
    · rfl

theorem componentCandidate_loopSizes_preserved (g : Graph) (component : List Nat)
    (hn : component.Nodup) (candidate v : Nat) (hv : v < component.length)
    (labels : List MeasuredLabel) (slot : Int) :
    loopSizes (componentCandidate g component candidate).edges labels v slot =
      loopSizes g.edges labels component[v] slot := by
  rw [← componentGraph_loopSizes_preserved g component hn v hv labels slot]
  unfold componentCandidate
  dsimp only
  split
  · split
    · apply Eq.trans (loopSizes_of_originals
        (ProtectedCycles.semantic_identity _ _) labels v slot)
      exact (loopSizes_of_originals (breakCyclesGreedy_semantic_identity _) labels v slot).trans
        (loopSizes_original _ labels v slot)
    · exact (loopSizes_of_originals (breakCyclesGreedy_semantic_identity _) labels v slot).trans
        (loopSizes_original _ labels v slot)
  · exact (loopSizes_cycleGraph _ labels v slot).trans (loopSizes_original _ labels v slot)

private theorem componentCandidate_slot (g : Graph) (component : List Nat) (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

theorem SceneExecution.ordinary_candidate_loop_reservation
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .node) :
    ∃ node : Node,
      (componentCandidate execution.graph component candidate).nodes[v]? = some node ∧
      Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
        (loopSizes (componentCandidate execution.graph component candidate).edges
          execution.measured v (componentCandidate execution.graph component candidate).slot) ≤ node.h := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hi : component[v] < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨metric, labels, node, hm, hl, hnode, hheight⟩ :=
    measuredGraph_ordinary_loop_reservation execution.graph_eq hi hb hrole
  have hemetric : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst metric
  have helabels : labels = execution.measured := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst labels
  refine ⟨node, ?_, ?_⟩
  · rw [componentCandidate_nodes]
    change (component.map (fun source => execution.graph.nodes.getD source default))[v]? = some node
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  · rw [componentCandidate_slot,
      componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv]
    exact hheight

theorem measuredGraph_ordinary_node_border_zero
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} (hi : i < lines.length) {box : ModelBox}
    (hb : inp.boxes[i]? = some box) (hrole : box.role = .node)
    {node : Node} (hnode : g.nodes[i]? = some node) : node.border = 0 := by
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  subst g
  have hall : ∀ n ∈ nodes, n.border = 0 := by
    intro n hn
    obtain ⟨entry, hentry, hstep⟩ := mapM_member_origin _ hnodes hn
    have hmem := List.fst_mem_of_mem_zipIdx hentry
    obtain ⟨before, hbefore, heq⟩ := List.mem_map.mp hmem
    have hzero := sizedNodes_border hinitial before hbefore
    have hentryzero : entry.1.border = 0 := by
      rw [← heq, orientNode_border]
      exact hzero
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    repeat' (first | split at hstep | contradiction)
    all_goals
      have he := Except.ok.inj hstep
      subst n
      simpa only [orientNode_border] using hentryzero
  have hfirst := (mapM_getElem? _ _ _ hinitial).1
  have hsecond := (mapM_getElem? _ _ _ hnodes).1
  simp only [List.length_zipIdx, List.length_map] at hfirst hsecond
  have hi' : i < nodes.length := by omega
  have hn : nodes[i]? = some nodes[i] := List.getElem?_eq_getElem hi'
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  let sourceBox := if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
    { box with role := .node } else box
  have hbox : boxes[i]? = some sourceBox := by
    simp only [boxes, sourceBox, List.getElem?_map, hb, Option.map_some]
  have hs : sourceBox.role = .node := by
    dsimp only [sourceBox]
    split
    · rfl
    · exact hrole
  have hrecord := prepare_node_record boxes P.clusterPad titles
    { nodes := nodes, edges := edges, slot := P.slot } hn hbox hs
  change (Compound.prepare boxes P.clusterPad titles
    { nodes := nodes, edges := edges, slot := P.slot }).nodes[i]? = some node at hnode
  have he := Option.some.inj (hnode.symm.trans hrecord)
  rw [he]
  exact hall nodes[i] (List.getElem_mem hi')

theorem SceneExecution.ordinary_candidate_node_border_zero
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (candidate v : Nat) (hv : v < component.length)
    {box : ModelBox} (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .node)
    {node : Node}
    (hnode : (componentCandidate execution.graph component candidate).nodes[v]? = some node) :
    node.border = 0 := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hi : component[v] < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨_, _, source, _, _, hsource, _⟩ :=
    measuredGraph_ordinary_loop_reservation execution.graph_eq hi hb hrole
  have hlocal : (componentCandidate execution.graph component candidate).nodes[v]? =
      some source := by
    rw [componentCandidate_nodes]
    change (component.map (fun source => execution.graph.nodes.getD source default))[v]? = some source
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
      List.getD_eq_getElem?_getD, hsource, Option.getD_some]
  have he : node = source := Option.some.inj (hnode.symm.trans hlocal)
  rw [he]
  exact measuredGraph_ordinary_node_border_zero execution.graph_eq hi hb hrole hsource

theorem SceneExecution.ordinary_candidate_frame_loop_reservation
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .node)
    {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  obtain ⟨node, hnode, hheight⟩ :=
    execution.ordinary_candidate_loop_reservation component hn candidate v hv hb hrole
  have hborder := execution.ordinary_candidate_node_border_zero component candidate v hv hb hrole hnode
  exact Int.le_trans hheight (componentRun_original_frame_minimum_dims hrun hnode hborder).2

theorem SceneExecution.componentLoops_ordinary_attachment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hcomponent : component ∈ components execution.graph)
    (candidate : Nat) {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph component candidate) run execution.measured = .ok loops)
    {q : Nat × LoopPlacement} (hq : q ∈ loops)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ v, ∃ hv : v < component.length, ∃ placements : List LoopPlacement, ∃ edge : Edge,
      (edge, q.2) ∈
        (loopEdges (componentCandidate execution.graph component candidate).edges v).zip placements ∧
      q.1 = edge.decl ∧ edge.tail = v ∧ edge.head = v ∧
      (∀ box : ModelBox, inp.boxes[component[v]]? = some box → box.role = .node →
        ∃ start finish : Point,
          q.2.points.head? = some start ∧ q.2.points.getLast? = some finish ∧
          let bounds := placeBounds execution.params
            (componentCandidate execution.graph component candidate) run execution.measured loops
          let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
          let rect := shiftRect margin margin (orientRect direction canvasH
            (shiftRect (boxX - bounds.minX) (boxY - bounds.minY)
              (frameRect execution.params (componentCandidate execution.graph component candidate) run v)))
          Validator.onBoundary (transport start) rect ∧
            Validator.onBoundary (transport finish) rect) := by
  obtain ⟨v, hv, placements, hp, edge, he, hdecl, htail, hhead⟩ :=
    componentLoops_entry_origin hloops hq
  have hv' : v < component.length := by
    rw [componentCandidate_nodes] at hv
    simpa only [componentGraph, List.length_map] using hv
  refine ⟨v, hv', placements, edge, he, hdecl, htail, hhead, ?_⟩
  intro box hb hrole
  have hboundary : ∃ start finish : Point,
      q.2.points.head? = some start ∧ q.2.points.getLast? = some finish ∧
      Validator.onBoundary start
        (frameRect execution.params (componentCandidate execution.graph component candidate) run v) ∧
      Validator.onBoundary finish
        (frameRect execution.params (componentCandidate execution.graph component candidate) run v) := by
    split at hp
    · exact Loops.exactLoops_boundary hp (List.of_mem_zip he).2
    · exact Loops.loops_boundary_of_reservation hp
        (execution.ordinary_candidate_frame_loop_reservation component
          (components_nodup execution.graph component hcomponent) candidate v hv' hb hrole hrun)
        (List.of_mem_zip he).2
  obtain ⟨start, finish, hs, ht, hsb, htb⟩ := hboundary
  refine ⟨start, finish, hs, ht, ?_⟩
  dsimp only
  constructor
  · apply (onBoundary_shift _ _ _ _).mpr
    apply (onBoundary_orient _ _ _ _).mpr
    exact (onBoundary_shift _ _ _ _).mpr hsb
  · apply (onBoundary_shift _ _ _ _).mpr
    apply (onBoundary_orient _ _ _ _).mpr
    exact (onBoundary_shift _ _ _ _).mpr htb

private theorem native_loop_result_length (exact : Bool)
    {node : Rect} {slot : Int} {labels : List LoopLabel} {out : List LoopPlacement}
    (h : (if exact then Loops.exactLoops else Loops.loops) node slot labels = .ok out) :
    out.length = labels.length := by
  cases exact with
  | false =>
    change Loops.loops node slot labels = .ok out at h
    unfold Loops.loops at h
    dsimp only at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · cases h
            simp only [List.length_map, List.length_zipIdx]
          · contradiction
  | true =>
    change Loops.exactLoops node slot labels = .ok out at h
    unfold Loops.exactLoops at h
    dsimp only at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · cases h
            simp only [List.length_map, List.length_zipIdx]
          · contradiction

theorem componentLoops_entry_of_self_edge
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops)
    {edge : Edge} (hedge : edge ∈ cg.edges)
    (hv : edge.tail < cg.nodes.length) (hself : edge.tail = edge.head) :
    ∃ placement : LoopPlacement, (edge.decl, placement) ∈ loops := by
  unfold componentLoops at hloops
  obtain ⟨groups, hgroups, hflat⟩ := bind_ok hloops
  have heflat : groups.flatten = loops := Except.ok.inj hflat
  obtain ⟨_, hindexed⟩ := mapM_getElem? _ _ _ hgroups
  obtain ⟨group, hgroup, hgroupIndex⟩ :=
    hindexed edge.tail edge.tail (List.getElem?_range hv)
  obtain ⟨placements, hplacements, hgroup⟩ := bind_ok hgroup
  have hegroup := Except.ok.inj hgroup
  have hlength := native_loop_result_length (run.exact.contains edge.tail) hplacements
  simp only [loopSizes, List.length_map] at hlength
  have heloop : edge ∈ loopEdges cg.edges edge.tail := by
    apply List.mem_filter.mpr
    exact ⟨hedge, by simp [hself]⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp heloop
  have hjbound : j < placements.length := by
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    omega
  have hplacement : placements[j]? = some placements[j] := List.getElem?_eq_getElem hjbound
  have hzip := zip_mem_of_getElem? hj hplacement
  refine ⟨placements[j], ?_⟩
  rw [← heflat]
  apply List.mem_flatten.mpr
  refine ⟨group, List.mem_of_getElem? hgroupIndex, ?_⟩
  rw [← hegroup]
  exact List.mem_map.mpr ⟨(edge, placements[j]), hzip, rfl⟩

theorem componentLoops_emitted_self_edge
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hv : edge.tail < cg.nodes.length) (hself : edge.tail = edge.head)
    (cursor : Int) :
    ∃ q ∈ loops,
      loops.find? (fun loop => loop.1 == edge.decl) = some q ∧ q.1 = edge.decl ∧
      (placeComponent P cg run cursor labels loops).routes[i]? =
        some (edge.decl, q.2.points.map
          (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
            (0 - (placeBounds P cg run labels loops).minY))) := by
  obtain ⟨placement, hplacement⟩ := componentLoops_entry_of_self_edge hloops
    (List.mem_of_getElem? hedge) hv hself
  cases hfind : loops.find? (fun loop => loop.1 == edge.decl) with
  | none =>
    have hn := List.find?_eq_none.mp hfind (edge.decl, placement) hplacement
    simp only [beq_self_eq_true, not_true_eq_false] at hn
  | some q =>
    have hq := List.mem_of_find?_eq_some hfind
    have hdecl : q.1 = edge.decl := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    refine ⟨q, hq, rfl, hdecl, ?_⟩
    unfold placeComponent placeBounds
    dsimp only
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some,
      hfind, Option.getD_some]

theorem measuredGraph_fixed_loop_reservation
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} (hi : i < lines.length) {box : ModelBox}
    (hb : inp.boxes[i]? = some box) {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry) :
    ∃ (metric : Measure.Metric) (labels : List MeasuredLabel) (node : Node),
      metricOf o.profile o.fontFamily = .ok metric ∧
      measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp o.direction = .ok labels ∧
      g.nodes[i]? = some node ∧ node.border = 0 ∧
      Loops.requiredHeight g.slot (loopSizes g.edges labels i g.slot) ≤ node.h := by
  obtain ⟨metric, labels, raw, hm, hl, _, hslot, hprepare, hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare hg
  obtain ⟨node, hnode, _, hborder, _, _⟩ :=
    measuredGraph_fixed_node_dims hg (List.getElem?_eq_getElem hi) hb hfixed
  have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
    List.any_eq_true.mpr
      ⟨entry, List.mem_of_find?_eq_some hfixed, by simpa using List.find?_some hfixed⟩
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  change g = Compound.prepare boxes P.clusterPad titles raw at hprepare
  have hcount := measuredGraph_node_count hg
  change g.nodes.length = lines.length +
    (boxes.zipIdx.filter (fun q => q.1.role == .group)).length at hcount
  have hrawlen : raw.nodes.length = lines.length := by
    rw [hprepare] at hcount
    change (Compound.markNodes boxes P.clusterPad titles raw.nodes).length = _ at hcount
    rw [Compound.markNodes_length] at hcount
    omega
  have hiraw : i < raw.nodes.length := by omega
  have hraw : raw.nodes[i]? = some raw.nodes[i] := List.getElem?_eq_getElem hiraw
  have hbox : boxes[i]? = some { box with role := .node } := by
    simp only [boxes, List.getElem?_map, hb, Option.map_some, hany, ↓reduceIte]
  have hprepared : (Compound.prepare boxes P.clusterPad titles raw).nodes[i]? = some node := by
    rw [← hprepare]
    exact hnode
  have hdims := Compound.prepare_node_dims_decl boxes P.clusterPad titles raw
    hiraw hprepared hbox (by change BoxRole.node ≠ BoxRole.group; decide)
  refine ⟨metric, labels, node, hm, hl, hnode, hborder, ?_⟩
  rw [hdims.2.2.1, hprepare]
  change Loops.requiredHeight raw.slot
    (loopSizes (Compound.prepare boxes P.clusterPad titles raw).edges labels i raw.slot) ≤ raw.nodes[i].h
  rw [prepare_loopSizes_preserved boxes P.clusterPad titles raw i
    (by simpa only [boxes, List.length_map] using
      (List.getElem?_eq_some_iff.mp hb).1) labels raw.slot, hslot]
  exact hreserve i raw.nodes[i] hraw

theorem SceneExecution.fixed_candidate_frame_loop_reservation
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry)
    {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hi : component[v] < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨metric, labels, node, hm, hl, hnode, hborder, hheight⟩ :=
    measuredGraph_fixed_loop_reservation execution.graph_eq hi hb hfixed
  have hemetric : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst metric
  have helabels : labels = execution.measured := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst labels
  have hlocal : (componentCandidate execution.graph component candidate).nodes[v]? =
      some node := by
    rw [componentCandidate_nodes]
    change (component.map (fun source => execution.graph.nodes.getD source default))[v]? = some node
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hframe := (componentRun_original_frame_minimum_dims hrun hlocal hborder).2
  rw [componentCandidate_slot,
    componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv]
  exact Int.le_trans hheight hframe

private theorem nonempty_loop_extent_pos (slot : Int) (labels : List LoopLabel)
    (hs : 0 < slot) (hn : labels ≠ []) (hw : ∀ label ∈ labels, 0 ≤ label.width) :
    0 < Loops.extent slot labels := by
  cases labels with
  | nil => contradiction
  | cons label rest =>
    have he := Loops.outer_label_extent slot (label :: rest) (by omega) hw label (by simp)
    have hp := Int.mul_pos hs
      (show 0 < ((label :: rest).length : Int) + 1 by omega)
    have hl := hw label (by simp)
    omega

theorem SceneExecution.nonfixed_group_node_loop_reservation
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {i : Nat} {box : ModelBox} (hb : inp.boxes[i]? = some box)
    (hrole : box.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    (hloop : loopEdges execution.graph.edges i ≠ []) :
    ∃ top : Node, execution.graph.nodes[i]? = some top ∧ top.border = -2 ∧
      0 < top.loopExtent ∧
      Loops.requiredHeight execution.graph.slot
        (loopSizes execution.graph.edges execution.measured i execution.graph.slot) ≤ top.h := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hi : i < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have hslot : 0 < execution.params.slot := by
    have h := (checkedParams_valid execution.checked).2.2.1
    omega
  have hg := execution.graph_eq
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, hm, hg⟩ := bind_ok hg
  obtain ⟨labels, hl, hg⟩ := bind_ok hg
  have hemetric : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst metric
  have helabels : labels = execution.measured := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst labels
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hprepare := (Except.ok.inj hg).symm
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  let raw : Graph := { nodes := nodes, edges := edges, slot := execution.params.slot }
  change execution.graph = Compound.prepare boxes execution.params.clusterPad titles raw at hprepare
  have hiboxes : i < boxes.length := by
    simpa only [boxes, List.length_map] using (List.getElem?_eq_some_iff.mp hb).1
  have hrawloops : loopEdges edges i ≠ [] := by
    have hp := prepare_loopEdges_preserved boxes execution.params.clusterPad titles raw i hiboxes
    rw [hprepare, hp] at hloop
    exact hloop
  have hsizes : loopSizes edges execution.measured i execution.params.slot ≠ [] := by
    intro he
    exact hrawloops (List.map_eq_nil_iff.mp he)
  have hwidth : ∀ label ∈ loopSizes edges execution.measured i execution.params.slot,
      0 ≤ label.width := by
    intro label hlabel
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hlabel
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hextent := nonempty_loop_extent_pos execution.params.slot
    (loopSizes edges execution.measured i execution.params.slot) hslot hsizes hwidth
  have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, _, hbefore⟩ :=
    hinit i (execution.lines[i], i)
      (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
        Option.map_some, Nat.zero_add])
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed i (orientNode o.direction before, i)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have hprops :
      after.h = Loops.requiredHeight execution.params.slot
        (loopSizes edges execution.measured i execution.params.slot) ∧
      0 < after.loopExtent := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    simp [hb, hfind, hrole, hfixed] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        constructor
        · rfl
        · dsimp only
          omega
  have hinodes : i < nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hget : nodes[i]'hinodes = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hbox : boxes[i]? = some box := by
    simp only [boxes, List.getElem?_map, hb, Option.map_some, hfixed,
      Bool.false_eq_true, ↓reduceIte]
  have hrecord := Compound.prepare_group_title_record boxes execution.params.clusterPad
    titles raw hinodes hbox hrole
  have hrecord' : execution.graph.nodes[i]? =
      some { after with
        clusterPath := Compound.path boxes box ++ [i]
        border := -2
        w := (titles.getD i (0, 0)).1
        h := max ((titles.getD i (0, 0)).2 + execution.params.clusterPad) after.h } := by
    rw [hprepare]
    have hnonzero : (after.loopExtent == 0) = false :=
      Bool.eq_false_iff.mpr (by
        intro he
        have hz : after.loopExtent = 0 := beq_iff_eq.mp he
        omega)
    simpa only [raw, hget, hnonzero, Bool.false_eq_true, ↓reduceIte] using hrecord
  refine ⟨_, hrecord', rfl, hprops.2, ?_⟩
  rw [hprepare]
  change Loops.requiredHeight execution.params.slot
    (loopSizes (Compound.prepare boxes execution.params.clusterPad titles raw).edges
      execution.measured i execution.params.slot) ≤
    max ((titles.getD i (0, 0)).2 + execution.params.clusterPad) after.h
  rw [prepare_loopSizes_preserved boxes execution.params.clusterPad titles raw i hiboxes]
  rw [← hprops.1]
  exact Int.le_max_right _ _

theorem SceneExecution.nonfixed_group_candidate_frame_loop_reservation
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    (hloop : loopEdges (componentCandidate execution.graph component candidate).edges v ≠ [])
    {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  have hglobal : loopEdges execution.graph.edges component[v] ≠ [] := by
    intro he
    have hlen := congrArg List.length
      (componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv
        execution.measured execution.graph.slot)
    simp only [loopSizes, List.length_map] at hlen
    rw [he, List.length_nil] at hlen
    exact hloop (List.length_eq_zero_iff.mp hlen)
  obtain ⟨top, htop, hborder, _, hheight⟩ :=
    execution.nonfixed_group_node_loop_reservation hb hrole hfixed hglobal
  have hlocal : (componentCandidate execution.graph component candidate).nodes[v]? =
      some top := by
    rw [componentCandidate_nodes]
    change (component.map (fun source => execution.graph.nodes.getD source default))[v]? = some top
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
      List.getD_eq_getElem?_getD, htop, Option.getD_some]
  have hbox : inp.boxes[component.getD v 0]? = some box := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
      Option.getD_some] using hb
  have hmember := actual_group_self_membership execution.graph_eq hlocal hborder hbox
  have hframe : top.h ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
    have h := componentRun_group_frame_height_ge hrun hlocal hborder hmember
      (th := top.h - execution.params.clusterPad) (by omega)
    simpa only [Int.sub_add_cancel] using h
  rw [componentCandidate_slot,
    componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv]
  exact Int.le_trans hheight hframe

theorem SceneExecution.componentLoops_group_emitted_attachment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hcomponent : component ∈ components execution.graph)
    (candidate : Nat) {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph component candidate) run execution.measured = .ok loops)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph component candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) {source : ModelBox}
    (hsource : inp.boxes[component.getD edge.tail 0]? = some source)
    (hrole : source.role = .group) :
    ∃ loop ∈ loops,
      loops.find? (fun q => q.1 == edge.decl) = some loop ∧ loop.1 = edge.decl ∧
      let bounds := placeBounds execution.params
        (componentCandidate execution.graph component candidate) run execution.measured loops
      let points := loop.2.points.map (shiftPoint (0 - bounds.minX) (0 - bounds.minY))
      let rect := shiftRect (0 - bounds.minX) (0 - bounds.minY)
        (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail)
      (placeComponent execution.params (componentCandidate execution.graph component candidate)
        run 0 execution.measured loops).routes[i]? = some (edge.decl, points) ∧
      ∃ start finish : Point, points.head? = some start ∧ points.getLast? = some finish ∧
        Validator.onBoundary start rect ∧ Validator.onBoundary finish rect := by
  obtain ⟨_, _, _, _, hnormalize, _⟩ := componentRun_spec hrun
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hnormalize).2
    edge (List.mem_of_getElem? hedge)
  have hv : edge.tail < component.length := by
    have h := hbounds.1
    rw [componentCandidate_nodes] at h
    simpa only [componentGraph, List.length_map] using h
  have hbox : inp.boxes[component[edge.tail]]? = some source := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
      Option.getD_some] using hsource
  obtain ⟨loop, hloop, hfind, hdecl, hemitted⟩ :=
    componentLoops_emitted_self_edge hloops hedge hbounds.1 hself 0
  obtain ⟨v, _, placements, hp, loopEdge, hzip, hloopDecl, htail, _⟩ :=
    componentLoops_entry_origin hloops hloop
  have hloopEdge : loopEdge ∈
      (componentCandidate execution.graph component candidate).edges :=
    (List.mem_filter.mp (List.of_mem_zip hzip).1).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hloopEdge
  have hdecls := componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq
    component candidate
  have hmap :
      ((componentCandidate execution.graph component candidate).edges.map Edge.decl)[i]? =
      ((componentCandidate execution.graph component candidate).edges.map Edge.decl)[j]? := by
    simp only [List.getElem?_map, hedge, hj, Option.map_some]
    exact congrArg some (hdecl.symm.trans hloopDecl)
  have hi : i < ((componentCandidate execution.graph component candidate).edges.map Edge.decl).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
  have hij : i = j := (hdecls.getElem?_inj hi).mp hmap
  have he : edge = loopEdge := by
    subst j
    exact Option.some.inj (hedge.symm.trans hj)
  subst loopEdge
  subst v
  have hboundary : ∃ start finish : Point,
      loop.2.points.head? = some start ∧ loop.2.points.getLast? = some finish ∧
      Validator.onBoundary start
        (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail) ∧
      Validator.onBoundary finish
        (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail) := by
    split at hp
    · exact Loops.exactLoops_boundary hp (List.of_mem_zip hzip).2
    · have hreservation : Loops.requiredHeight
          (componentCandidate execution.graph component candidate).slot
          (loopSizes (componentCandidate execution.graph component candidate).edges
            execution.measured edge.tail (componentCandidate execution.graph component candidate).slot) ≤
          (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail).h := by
        cases hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) with
        | none =>
          have hany : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false :=
            List.any_eq_false.mpr (List.find?_eq_none.mp hfixed)
          have hnonempty : loopEdges
              (componentCandidate execution.graph component candidate).edges edge.tail ≠ [] := by
            intro hempty
            have hm := (List.of_mem_zip hzip).1
            rw [hempty] at hm
            cases hm
          exact execution.nonfixed_group_candidate_frame_loop_reservation component
            (components_nodup execution.graph component hcomponent) candidate edge.tail hv
            hbox hrole hany hnonempty hrun
        | some entry =>
          exact execution.fixed_candidate_frame_loop_reservation component
            (components_nodup execution.graph component hcomponent) candidate edge.tail hv
            hbox hfixed hrun
      exact Loops.loops_boundary_of_reservation hp hreservation (List.of_mem_zip hzip).2
  obtain ⟨start, finish, hs, ht, hsb, htb⟩ := hboundary
  refine ⟨loop, hloop, hfind, hdecl, hemitted, ?_⟩
  let bounds := placeBounds execution.params
    (componentCandidate execution.graph component candidate) run execution.measured loops
  refine ⟨shiftPoint (0 - bounds.minX) (0 - bounds.minY) start,
    shiftPoint (0 - bounds.minX) (0 - bounds.minY) finish, ?_, ?_, ?_, ?_⟩
  · simp only [List.head?_map, hs, Option.map_some, bounds]
  · simp only [List.getLast?_map, ht, Option.map_some, bounds]
  · exact (onBoundary_shift _ _ _ _).mpr hsb
  · exact (onBoundary_shift _ _ _ _).mpr htb

end Elegant.Layered.PipelineImpl
