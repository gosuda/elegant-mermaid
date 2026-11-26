import Elegant.Layered.RegionC7LoopBranches
import Elegant.Layered.RegionC7BridgeAssembly
import Elegant.Layered.RegionActiveOrderProof

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem r7LoopRawSizing {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) :
    ∃ (metric : Measure.Metric) (labels : List MeasuredLabel) (raw : Graph)
      (titles : List (Int × Int)),
      metricOf o.profile o.fontFamily = .ok metric ∧
      measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        inp o.direction = .ok labels ∧
      raw.slot = P.slot ∧ raw.nodes.length = lines.length ∧
      g = Compound.prepare
        (inp.boxes.map fun box => if inp.fixedSizes.any (·.1 == box.id)
          then { box with role := .node } else box) P.clusterPad titles raw ∧
      ∀ {i : Nat} {node : Node}, raw.nodes[i]? = some node →
        Loops.extent P.slot (loopSizes raw.edges labels i P.slot) ≤ (node.loopExtent : Int) ∧
        Loops.requiredHeight P.slot (loopSizes raw.edges labels i P.slot) ≤ node.h := by
  unfold measuredGraph at hg
  obtain ⟨initial, hi, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, hm, hg⟩ := bind_ok hg
  obtain ⟨labels, hl, hg⟩ := bind_ok hg
  obtain ⟨nodes, hn, hg⟩ := bind_ok hg
  have hcount₀ := (mapM_getElem? _ _ _ hi).1
  obtain ⟨hcount₁, hprocessed⟩ := mapM_getElem? _ _ _ hn
  simp only [List.length_zipIdx, List.length_map] at hcount₀ hcount₁
  refine ⟨metric, labels, { nodes := nodes, edges := edges, slot := P.slot }, _,
    hm, hl, rfl, hcount₁.trans hcount₀, (Except.ok.inj hg).symm, ?_⟩
  intro i node hnode
  change nodes[i]? = some node at hnode
  have hi₀ : i < initial.length := by
    have hi₁ := (List.getElem?_eq_some_iff.mp hnode).1
    omega
  have hbefore : initial[i]? = some initial[i] := List.getElem?_eq_getElem hi₀
  obtain ⟨after, hstep, ha⟩ := hprocessed i (orientNode o.direction initial[i], i)
    (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
      Option.map_some, Nat.zero_add])
  have heq : after = node := Option.some.inj (ha.symm.trans hnode)
  subst after
  dsimp only at hstep
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hstep
  repeat' (first | split at hstep | contradiction)
  all_goals
    have heq := Except.ok.inj hstep
    subst node
    dsimp only
    constructor
    · omega
    · first | exact Int.le_refl _ | exact Int.le_max_right _ _

private theorem r7LoopMeasuredPlain {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {i : Nat} {node : Node} (hi : execution.graph0.nodes[i]? = some node)
    (hb : node.border = 0) :
    ∃ box, inp.boxes[i]? = some box ∧ node.decl = i ∧
      Loops.extent execution.params.slot
        (loopSizes execution.graph0.edges execution.measured i execution.params.slot) ≤
          (node.loopExtent : Int) ∧
      Loops.requiredHeight execution.params.slot
        (loopSizes execution.graph0.edges execution.measured i execution.params.slot) ≤ node.h := by
  have hl := execution.lines_eq
  unfold boxLines at hl
  have hlines : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hl).1
  obtain ⟨metric, labels, raw, titles, hm, hlabels, _, hrawLen, hprep, hrawSize⟩ :=
    r7LoopRawSizing execution.graph0_eq
  have he : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst metric
  have he : labels = execution.measured := Except.ok.inj (hlabels.symm.trans execution.measured_eq)
  subst labels
  let boxes := inp.boxes.map fun box => if inp.fixedSizes.any (·.1 == box.id)
    then { box with role := .node } else box
  change execution.graph0 = Compound.prepare boxes execution.params.clusterPad titles raw at hprep
  have hprepared := hi
  rw [hprep] at hprepared
  have hraw : i < raw.nodes.length := by
    by_cases h : i < raw.nodes.length
    · exact h
    · have hborder := (Compound.prepare_bottom_of_index boxes execution.params.clusterPad titles
        raw i (by omega) hprepared).1
      omega
  have hiBox : i < inp.boxes.length := by omega
  let box := inp.boxes[i]
  have hbox : inp.boxes[i]? = some box := List.getElem?_eq_getElem hiBox
  let effective := if inp.fixedSizes.any (·.1 == box.id) then { box with role := .node } else box
  have hboxEff : boxes[i]? = some effective := by
    simp only [boxes, effective, List.getElem?_map, hbox, Option.map_some]
  have hgroup : effective.role ≠ .group := by
    intro hg
    have hh := Compound.prepare_group_title_record boxes execution.params.clusterPad titles raw
      hraw hboxEff hg
    have hh := congrArg Node.border (Option.some.inj (hprepared.symm.trans hh))
    change node.border = -2 at hh
    omega
  obtain ⟨_, _, hh, hw⟩ := Compound.prepare_node_dims_decl boxes execution.params.clusterPad titles raw
    hraw hprepared hboxEff hgroup
  have hsizes := prepare_loopSizes_preserved boxes execution.params.clusterPad titles raw i
    (by simpa only [boxes, List.length_map] using hiBox) execution.measured execution.params.slot
  have hdecl : node.decl = i := by
    obtain ⟨_, _, _, hprep', _, hmetadata⟩ :=
      measuredGraph_prepared_source execution.graph0_eq
    rw [hprep'] at hi
    exact (prepare_plain_path_origin _ _ _ _ hmetadata hi hb hboxEff).1
  have hsize := hrawSize (List.getElem?_eq_getElem hraw)
  refine ⟨box, hbox, hdecl, ?_, ?_⟩
  · rw [hprep, hsizes, hw]
    exact hsize.1
  · rw [hprep, hsizes, hh]
    exact hsize.2

private theorem r7LoopCandidateNodes (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (candidate : Nat) :
    (componentCandidateR spec g comp candidate).nodes = (componentGraph g comp).nodes := by
  cases spec with
  | none => exact componentCandidate_nodes g comp candidate
  | some _ => rfl

private theorem r7LoopCandidateSlot (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (candidate : Nat) :
    (componentCandidateR spec g comp candidate).slot = g.slot := by
  cases spec with
  | none =>
    unfold componentCandidateR componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  | some _ => rfl

private theorem r7LoopRewrittenHeader {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    cg'.nodes = cg.nodes ∧ cg'.slot = cg.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, h⟩
  · rw [he]
    exact ⟨rfl, rfl⟩
  · refine ⟨rankEquivalentR_nodes_eq h, ?_⟩
    unfold rankEquivalentR at h
    dsimp only at h
    split at h
    · simp only [bind, Except.bind] at h
      cases h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      exact (congrArg (fun q : List Int × Graph × Bool => q.2.1.slot) (Except.ok.inj h)).symm

theorem r7ComponentRun_slot_of_scene {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec : Option RegionSpec}
    {cg : Graph} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec inp
      (componentCandidateR spec execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg, run)) :
    cg.slot = execution.params.slot := by
  obtain ⟨nodes, _, he⟩ := bind_ok execution.graph_eq
  have he₁ : execution.graph = { execution.graph0 with nodes := nodes } :=
    (Except.ok.inj he).symm
  obtain ⟨_, _, _, he₂, _, _⟩ := measuredGraph_prepared_source execution.graph0_eq
  rw [(r7LoopRewrittenHeader hrun).2, r7LoopCandidateSlot, he₁, he₂] <;> rfl

private theorem r7LoopRunExact {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {u : Nat} {node : Node} (hu : cg'.nodes[u]? = some node) :
    run.exact.contains u = true ↔ exact.contains node.decl = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rw [List.contains_iff_mem, stages.hExact, List.mem_filterMap]
  constructor
  · rintro ⟨⟨n, j⟩, hmem, ht⟩
    have hj : cg'.nodes[j]? = some n := List.mem_zipIdx_iff_getElem?.mp hmem
    dsimp only at ht
    split at ht
    · next hn =>
        have hj' : j = u := Option.some.inj ht
        subst j
        have he := Option.some.inj (hj.symm.trans hu)
        simpa only [he] using hn
    · cases ht
  · intro h
    refine ⟨(node, u), List.mem_zipIdx_iff_getElem?.mpr hu, ?_⟩
    simp only [h, ↓reduceIte]

private theorem r7LoopExactDecl {exactIds : List String} {inp : Input}
    {i : Nat} {box : ModelBox} (hi : inp.boxes[i]? = some box) :
    (exactDecls exactIds inp).contains i = true ↔
      (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true := by
  rw [List.contains_iff_mem, exactDecls, List.mem_filterMap]
  constructor
  · rintro ⟨⟨b, j⟩, hm, hout⟩
    have hj : inp.boxes[j]? = some b := List.mem_zipIdx_iff_getElem?.mp hm
    dsimp only at hout
    split at hout
    · next h =>
        have he : j = i := Option.some.inj hout
        subst j
        have hb := Option.some.inj (hj.symm.trans hi)
        simpa only [hb] using h
    · cases hout
  · intro h
    refine ⟨(box, i), List.mem_zipIdx_iff_getElem?.mpr hi, ?_⟩
    simp only [h, ↓reduceIte]

private theorem r7LoopExactGraphSize {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {labels : List MeasuredLabel} {g₀ g : Graph}
    (hgraph : exactGraph P exactIds inp o labels g₀ = .ok g)
    {i : Nat} {node₀ node : Node} {box : ModelBox}
    (h₀ : g₀.nodes[i]? = some node₀) (h : g.nodes[i]? = some node)
    (hbox : inp.boxes[node₀.decl]? = some box) :
    (if (exactDecls exactIds inp).contains node₀.decl then
      Loops.exactExtent P.slot (loopSizes g₀.edges labels node₀.decl P.slot) ≤
        (node.loopExtent : Int)
     else node = node₀) := by
  obtain ⟨nodes, hnodes, hd⟩ := bind_ok hgraph
  have he : g = { g₀ with nodes := nodes } := (Except.ok.inj hd).symm
  have hx : nodes[i]? = some node := by rwa [he] at h
  obtain ⟨out, hstep, hout⟩ := (mapM_getElem? _ _ _ hnodes).2 i node₀ h₀
  have heq : out = node := Option.some.inj (hout.symm.trans hx)
  subst out
  have hflag := r7LoopExactDecl (exactIds := exactIds) hbox
  simp only [hbox] at hstep
  by_cases hc : (exactDecls exactIds inp).contains node₀.decl = true
  · have hcond : (!exactIds.contains box.id &&
        !(box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = false := by
      have ht := hflag.mp hc
      cases ha : exactIds.contains box.id <;>
        cases hb : (box.role == .group && inp.fixedSizes.any (·.1 == box.id)) <;>
        simp_all
    simp only [hc, ↓reduceIte]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hstep
    cases hf : inp.fixedSizes.find? (·.1 == box.id) with
    | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at hstep
    | some _ =>
      simp only [hf] at hstep
      split at hstep
      · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hstep
        cases hstep
      · split at hstep
        · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hstep
          cases hstep
        · simp only [pure, Except.pure] at hstep
          have heq := Except.ok.inj hstep
          subst node
          dsimp only
          omega
  · have hcond : (!exactIds.contains box.id &&
        !(box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true := by
      have hf : ¬ ((exactIds.contains box.id ||
          (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true) :=
        fun h => hc (hflag.mpr h)
      cases ha : exactIds.contains box.id <;>
        cases hb : (box.role == .group && inp.fixedSizes.any (·.1 == box.id)) <;>
        simp_all
    simp only [ite_eq_right hc]
    simp only [hcond, ↓reduceIte, pure, Except.pure] at hstep
    exact (Except.ok.inj hstep).symm

private theorem r7LoopCoordinateExtent (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) {p : Proper} {i : Nat} {node : ProperNode}
    (hn : p.nodes[i]? = some node) (hb : node.node.border = 0) :
    ∃ nd, (coordinateGraphR P exact spec p).nodes[i]? = some nd ∧
      nd.node.loopExtent = node.node.loopExtent := by
  let sized := sizeProperPortsX P exact p
  obtain ⟨nd, hs, hborder, he⟩ : ∃ nd, sized.nodes[i]? = some nd ∧
      nd.node.border = 0 ∧ nd.node.loopExtent = node.node.loopExtent := by
    simp only [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx,
      hn, Option.map_some, Nat.zero_add]
    split <;> exact ⟨_, rfl, hb, rfl⟩
  let titled := match spec with
    | none => titleReservations sized
    | some s => titleReservationsR s.titles P.clusterPad sized
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have ht : titled.nodes[i]? = some nd := by
    cases spec with
    | none =>
      change (titleReservations sized).nodes[i]? = some nd
      rw [titleReservations_nodes, List.getElem?_append_left (by
        simpa only [List.length_map] using hi)]
      simp [List.getElem?_map, hs, titleF, hborder]
    | some s =>
      change (titleReservationsR s.titles P.clusterPad sized).nodes[i]? = some nd
      unfold titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by simpa only [List.length_map] using hi)]
      simp [List.getElem?_map, hs, hborder]
  obtain ⟨_, hnodes, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hadd : (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[i]? = some nd := by
    rw [hnodes, List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1]
    exact ht
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[i]? =
      some nd := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hadd, clearF, hborder]
  have hcoord : coordinateGraphR P exact spec p =
      materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)) := by
    cases spec <;> rfl
  rw [hcoord]
  simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hclear,
    Option.map_some, Nat.zero_add]
  split <;> exact ⟨_, rfl, he⟩

private theorem r7LoopPortsKeepExtent {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x x' : List Int} {out : Proper} {i : Nat}
    {nd : ProperNode} (h : reservedPortsR pl cg labels x = .ok (x', out))
    (hn : pl.p.nodes[i]? = some nd) :
    ∃ n, out.nodes[i]? = some n ∧ n.node.loopExtent = nd.node.loopExtent := by
  unfold reservedPortsR at h
  obtain ⟨result, hfold, hdone⟩ := bind_ok h
  let step : (List Int × Array ProperNode) → (RegionCluster × Nat) →
      Except LayoutError (List Int × Array ProperNode) := fun acc q => do
    let c := q.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      let nodes := acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
      pure (x, nodes)
  let keeps (acc : List Int × Array ProperNode) : Prop :=
    ∃ n, acc.2[i]? = some n ∧ n.node.loopExtent = nd.node.loopExtent
  have foldKeeps : ∀ (rows : List (RegionCluster × Nat)) (start finish : List Int × Array ProperNode),
      rows.foldlM step start = .ok finish → keeps start → keeps finish := by
    intro rows
    induction rows with
    | nil =>
      intro start finish hnil hkeep
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hnil
      rwa [← hnil]
    | cons q rest ih =>
      intro start finish hcons hkeep
      simp only [List.foldlM_cons] at hcons
      obtain ⟨next, hnext, hrest⟩ := bind_ok hcons
      apply ih next finish hrest
      obtain ⟨cur, hcur, he⟩ := hkeep
      dsimp only [step] at hnext
      split at hnext
      · simp [throw, throwThe, MonadExceptOf.throw] at hnext
      · obtain ⟨_, _, hnext⟩ := bind_ok hnext
        obtain ⟨_, _, hnext⟩ := bind_ok hnext
        rw [← Except.ok.inj hnext]
        change ∃ n, (start.2.set! q.1.top _)[i]? = some n ∧
          n.node.loopExtent = nd.node.loopExtent
        by_cases heq : q.1.top = i
        · have hbound := (Array.getElem?_eq_some_iff.mp hcur).1
          have hread : start.2.getD i default = cur := by
            rw [Array.getD_eq_getD_getElem?, hcur, Option.getD_some]
          rw [heq, getElem?_set!_self hbound, hread]
          exact ⟨_, rfl, he⟩
        · exact ⟨cur, (getElem?_set!_ne heq _).trans hcur, he⟩
  have hbase : keeps (x, pl.p.nodes.toArray) :=
    ⟨nd, by simpa only [List.getElem?_toArray] using hn, rfl⟩
  have hnodes : out.nodes = result.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hdone)).symm
  obtain ⟨n, hget, he⟩ := foldKeeps _ _ _ hfold hbase
  exact ⟨n, by rw [hnodes, Array.getElem?_toList]; exact hget, he⟩


private theorem r7LoopRunExtent {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions = .ok (cg', run))
    {u : Nat} {node : Node} (hu : cg'.nodes[u]? = some node) (hplain : node.border = 0) :
    (run.coordinateProper.nodes.getD u default).node.loopExtent = node.loopExtent := by
  obtain ⟨_, _, _, _, _, pCoord, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  obtain ⟨n, hn, he⟩ := r7LoopCoordinateExtent P (exactDecls exactIds inp) spec
    (addLabelNodes_untouched_node stages.hLabels (normalize_node_record stages.hNorm hu) rfl) hplain
  rw [stages.hCoord] at hn
  rw [stages.hCoordProper]
  rcases stages.hPlaced with ⟨_, _, _, _, heq⟩ | ⟨_, _, _, _, hcross⟩
  · rw [heq]
    simpa only [List.getD_eq_getElem?_getD, hn, Option.getD_some] using he
  · obtain ⟨allocation⟩ := crossCoordsR_allocation_stages hcross
    have hp : allocation.placement.p = pCoord := by rw [allocation.hPlacement]
    have hnp : allocation.placement.p.nodes[u]? = some n := by rwa [hp]
    obtain ⟨out, hout, houtExtent⟩ := r7LoopPortsKeepExtent allocation.hFramesAndPorts hnp
    simpa only [List.getD_eq_getElem?_getD, hout, Option.getD_some] using houtExtent.trans he

theorem r7_loopPlainSizing_of_run {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec : Option RegionSpec}
    {cg cg' : Graph} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidateR spec execution.graph comp candidate)
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec
      inp cg execution.measured orderOptions = .ok (cg', run))
    {u : Nat} {node : Node} (hu : cg'.nodes[u]? = some node) (hb : node.border = 0) :
    (loopFootprintExt cg' run execution.measured u).w ≤
        ((run.coordinateProper.nodes.getD u default).node.loopExtent : Int) ∧
    (run.exact.contains u = false →
      Loops.requiredHeight cg'.slot (loopSizes cg'.edges execution.measured u cg'.slot) ≤ node.h) := by
  have hheader := r7LoopRewrittenHeader hrun
  have hlocal : cg.nodes[u]? = some node := by rwa [hheader.1] at hu
  have hlen : cg.nodes.length = comp.length := by
    rw [hcg, r7LoopCandidateNodes]
    exact List.length_map ..
  have huComp : u < comp.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hlocal).1
  let key := comp[u]
  have hkey : comp[u]? = some key := List.getElem?_eq_getElem huComp
  have hkeyG : key < execution.graph.nodes.length := by
    have hm : key ∈ comp := List.mem_of_getElem? hkey
    unfold components at hcomp
    dsimp only at hcomp
    obtain ⟨_, _, he⟩ := List.mem_map.mp hcomp
    rw [← he] at hm
    exact List.mem_range.mp (List.mem_filter.mp hm).1
  have hkey₀ : key < execution.graph0.nodes.length := by
    rwa [← exactGraph_length execution.graph_eq]
  let node₀ := execution.graph0.nodes[key]
  have hnode₀ : execution.graph0.nodes[key]? = some node₀ :=
    List.getElem?_eq_getElem hkey₀
  obtain ⟨global, hglobal, hborder, _, hdecl⟩ :=
    exactGraph_node_key execution.graph_eq hnode₀
  have hlookup := component_node_lookupR (spec := spec) (cand := candidate) hkey hglobal
  rw [← hcg] at hlookup
  have he : global = node := Option.some.inj (hlookup.symm.trans hlocal)
  subst global
  obtain ⟨box, hbox, hkeyDecl, hwidth₀, hheight₀⟩ :=
    r7LoopMeasuredPlain execution hnode₀ (hborder.symm.trans hb)
  have hslot : cg'.slot = execution.params.slot :=
    r7ComponentRun_slot_of_scene execution (comp := comp) (candidate := candidate)
      (by simpa only [hcg] using hrun)
  have hsizes : loopSizes cg'.edges execution.measured u cg'.slot =
      loopSizes execution.graph0.edges execution.measured key execution.params.slot := by
    rw [componentRunR_loopSizes_eq hrun u cg'.slot, hcg]
    rw [componentCandidateR_loopSizes_preserved spec execution.graph comp
      (components_nodup _ _ hcomp) candidate u huComp]
    rw [exactGraph_edges execution.graph_eq, hslot]
  have hsrc : inp.boxes[node₀.decl]? = some box := by rwa [hkeyDecl]
  have hexSize := r7LoopExactGraphSize execution.graph_eq hnode₀ hglobal hsrc
  have hexFlag := r7LoopRunExact hrun hu
  have hcoord := r7LoopRunExtent hrun hu hb
  constructor
  · change (if run.exact.contains u then Loops.exactExtent else Loops.extent) cg'.slot
        (loopSizes cg'.edges execution.measured u cg'.slot) ≤ _
    rw [hcoord, hsizes, hslot]
    by_cases ht : run.exact.contains u = true
    · have hex : (exactDecls exactIds inp).contains node₀.decl = true := by
        rw [← hdecl]
        exact hexFlag.mp ht
      rw [ite_eq_left hex, hkeyDecl] at hexSize
      rw [ite_eq_left ht]
      exact hexSize
    · have hf : (exactDecls exactIds inp).contains node₀.decl = false :=
        Bool.eq_false_iff.mpr (fun hex => ht (hexFlag.mpr (by rwa [hdecl])))
      have heq : node = node₀ := by simpa only [hf, Bool.false_eq_true, ↓reduceIte] using hexSize
      rw [ite_eq_right ht, heq]
      exact hwidth₀
  · intro hf
    have hex : (exactDecls exactIds inp).contains node₀.decl = false :=
      Bool.eq_false_iff.mpr (fun ht => by
        have he := hexFlag.mpr (by rwa [hdecl])
        rw [hf] at he
        cases he)
    have heq : node = node₀ := by simpa only [hex, Bool.false_eq_true, ↓reduceIte] using hexSize
    rw [hsizes, hslot, heq]
    exact hheight₀

private theorem r7_loopMiss_plain_earlier {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {u v : Nat} {nu nv : Node} (hu : cg'.nodes[u]? = some nu) (hv : cg'.nodes[v]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0)
    (hrank : (rk run.proper.rank v).toNat < (rk run.proper.rank u).toNat) :
    ¬ (loopFootprintExt cg' run labels u).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨layerU, hlookupU, _, hloU, _⟩ := hband hu hbu
  obtain ⟨layerV, hlookupV, _, _, hhiV⟩ := hband hv hbv
  have hvlen := componentRunR_original_nodes_covered hrun v (List.getElem?_eq_some_iff.mp hv).1
  have hvb : (cg'.nodes.getD v default).border ≠ -2 := by
    simp [List.getD_eq_getElem?_getD, hv, hbv]
  have hframe := plain_frame_eq_boxRect P cg' run v hvlen hvb
  rw [hframe] at hhiV
  have hgap := hsep hrank hlookupV hlookupU
  have hfootY : (loopFootprintExt cg' run labels u).y = (frameRect P cg' run u).y := rfl
  unfold Rect.meetsInterior
  omega

def R7_SettledPlainLoopPair (spec : Option RegionSpec) (cg : Graph)
    (run : Run) (u v : Nat) : Prop :=
  ∃ nu nv : Node, cg.nodes[u]? = some nu ∧ cg.nodes[v]? = some nv ∧
    nu.border = 0 ∧ nv.border = 0 ∧
    (v = u ∨
     (rk run.proper.rank v).toNat < (rk run.proper.rank u).toNat ∨
     ((rk run.proper.rank u).toNat = (rk run.proper.rank v).toNat ∧
       (spec.isSome = true → nu.clusterPath.getLast? = nv.clusterPath.getLast?)) ∨
     ((rk run.proper.rank u).toNat < (rk run.proper.rank v).toNat ∧
       run.exact.contains u = false))

theorem r7_loopEnvelopeMiss_of_settledPlainPair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec : Option RegionSpec}
    {cg cg' : Graph} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidateR spec execution.graph comp candidate)
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec
      inp cg execution.measured orderOptions = .ok (cg', run))
    {u v : Nat} (hpair : R7_SettledPlainLoopPair spec cg' run u v) :
    ¬ (loopFootprintExt cg' run execution.measured u).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨nu, nv, hu, hv, hbu, hbv, hs⟩ := hpair
  rcases hs with rfl | hlt | ⟨hrank, howner⟩ | ⟨hlt, hnonexact⟩
  · exact componentRunR_loopFootprint_miss_plain_self hrun hu hbu
  · exact r7_loopMiss_plain_earlier hrun hu hv hbu hbv hlt
  · obtain ⟨hband, _⟩ := componentRunR_plain_rank_bands hrun
    obtain ⟨layerU, hlookupU, hmemU, _, _⟩ := hband hu hbu
    obtain ⟨layerV, hlookupV, hmemV, _, _⟩ := hband hv hbv
    rw [← hrank] at hlookupV
    have hsame : layerU = layerV := Option.some.inj (hlookupU.symm.trans hlookupV)
    have hsizing := r7_loopPlainSizing_of_run execution hcomp hcg hrun hu hbu
    exact componentRunR_loopFootprint_miss_plain_same_rank hrun hu hv hbu hbv howner
      (List.mem_of_getElem? hlookupU) hmemU (hsame.symm ▸ hmemV) hsizing.1
  · have hsizing := r7_loopPlainSizing_of_run execution hcomp hcg hrun hu hbu
    have hnodes := (r7LoopRewrittenHeader hrun).1
    have hlocal : cg.nodes[u]? = some nu := by rwa [hnodes] at hu
    have hpos := componentRunR_slot_pos hrun
    have hcgSlot : cg'.slot = execution.params.slot :=
      r7ComponentRun_slot_of_scene execution (comp := comp) (candidate := candidate)
        (by simpa only [hcg] using hrun)
    have hnn : 0 ≤ cg'.slot := by omega
    have hreserve := componentRunR_loopFootprint_rank_cap_of_requiredHeight
      hrun hlocal hbu hnn (hsizing.2 hnonexact)
    exact componentRunR_loopFootprint_miss_plain_other_rank hrun hu hv hbu hbv
      (by omega) hreserve

end Elegant.Layered.PipelineImpl
