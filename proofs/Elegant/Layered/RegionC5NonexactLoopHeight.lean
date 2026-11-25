import Elegant.Layered.RegionFlatC6Selected
import Elegant.Layered.RegionC7SettledPlainLoops
import Elegant.Layered.ExactFlatC5SelfRoutes
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

elab "rC5RunHeader%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC7SettledPlainLoops
    `Elegant.Layered.PipelineImpl.r7LoopRewrittenHeader))
elab "rC5CandidateSlot%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC7SettledPlainLoops
    `Elegant.Layered.PipelineImpl.r7LoopCandidateSlot))
elab "rC5RunExact%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC7SettledPlainLoops
    `Elegant.Layered.PipelineImpl.r7LoopRunExact))
elab "rC5ExactGraphSize%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC7SettledPlainLoops
    `Elegant.Layered.PipelineImpl.r7LoopExactGraphSize))
elab "rC5RawSize%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC7SettledPlainLoops
    `Elegant.Layered.PipelineImpl.r7LoopRawSizing))
elab "rC5PlainSource%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionFlatC6
    `Elegant.Layered.PipelineImpl.r6c6_plain_graph_node))
elab "rC5GroupSource%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionFlatC6
    `Elegant.Layered.PipelineImpl.r6c6_nonfixed_group_graph_node))
elab "rC5SourceDecl%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionFlatC6
    `Elegant.Layered.PipelineImpl.r6c6_graphNodeDeclOfBox))
elab "rC5CandidateRegions%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionFlatC6Selected
    `Elegant.Layered.PipelineImpl.regionCandidate_resolution))
elab "rC5FallbackGroupHeight%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.ExactFlatC5SelfRoutes
    `Elegant.Layered.PipelineImpl.X_self_componentRunX_group_frame_height_ge))
elab "rC5LoopExtentPos%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.ExactFlatC5SelfRoutes
    `Elegant.Layered.PipelineImpl.X_self_nonempty_loop_extent_pos))
elab "rC5CandidateDeclNodup%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionFlatC7
    `Elegant.Layered.PipelineImpl.r7_candidateR_decls_nodup))

private theorem c5HeightBind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem c5FirstGroupDecl {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) (used : Option RegionSpec) (k : Nat)
    {v key : Nat} {source : ModelBox} {node : Node}
    (hkey : comp[v]? = some key) (hsource : inp.boxes[key]? = some source)
    (hn : (componentCandidateR used e.graph comp k).nodes[v]? = some node)
    (hd : node.decl = key) :
    ((componentCandidateR used e.graph comp k).nodes.zipIdx.find?
      (fun q => q.1.decl == node.decl)) = some (node, v) := by
  let ns := (componentCandidateR used e.graph comp k).nodes
  have hcompOrd : comp.Pairwise (· < ·) := by
    obtain ⟨_, he⟩ := mem_components_eq hcomp
    rw [he]
    exact List.Pairwise.sublist List.filter_sublist List.pairwise_lt_range
  obtain ⟨hv, hvEq⟩ := List.getElem?_eq_some_iff.mp hkey
  have hzip : ns.zipIdx[v]? = some (node, v) := by
    simp only [ns, List.getElem?_zipIdx, hn, Option.map_some, Nat.zero_add]
  obtain ⟨hvz, hget⟩ := List.getElem?_eq_some_iff.mp hzip
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp, v, hvz, hget, ?_⟩
  intro j hj
  have hjc : j < comp.length := Nat.lt_trans hj hv
  have hjkey : comp[j]'hjc < key := by
    rw [← hvEq]
    exact List.Pairwise.rel_getElem_of_lt hjc hv hcompOrd hj
  have hjbox : comp[j]'hjc < inp.boxes.length :=
    Nat.lt_trans hjkey (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨prior, hprior, hdecl⟩ := rC5SourceDecl% e (List.getElem?_eq_getElem hjbox)
  have hpriorLocal : ns[j]? = some prior :=
    component_node_lookupR (List.getElem?_eq_getElem hjc) hprior
  obtain ⟨hjns, hjget⟩ := List.getElem?_eq_some_iff.mp hpriorLocal
  have hne : prior.decl ≠ node.decl := by rw [hdecl, hd]; exact Nat.ne_of_lt hjkey
  simp only [List.getElem_zipIdx, Bool.not_eq_eq_eq_not, Bool.not_true]
  change ((ns[j]'hjns).decl == node.decl) = false
  rw [hjget]
  exact beq_eq_false_iff_ne.mpr hne

private theorem c5ResolvedClusters {spec : RegionSpec} {P : Params} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some spec) P inp cg = .ok (some rm)) :
    rm.clusters = clusterRows inp spec cg := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := c5HeightBind h
    split at h
    · cases h
    · exact (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm

private theorem c5ClusterTop {inp : Input} {spec : RegionSpec} {cg : Graph}
    {v : Nat} {node : Node} (hn : cg.nodes[v]? = some node) (hb : node.border = -2)
    (hfirst : (cg.nodes.zipIdx.find? (fun q => q.1.decl == node.decl)) = some (node, v)) :
    (∃ c ∈ clusterRows inp spec cg, c.top = v) ∧
    (∀ c ∈ clusterRows inp spec cg, c.top = v → c.node = v) := by
  let bottom := match cg.nodes.zipIdx.find? (fun b =>
      b.1.border == 2 && b.1.decl == node.decl) with
    | some b => b.2
    | none => v
  let titles := spec.titles.getD node.decl (0, 0)
  let row : RegionCluster := ⟨boxId inp node.decl, node.decl, v, v, bottom,
    node.w, titles.2, node.loopExtent⟩
  refine ⟨⟨row, ?_, rfl⟩, ?_⟩
  · unfold clusterRows
    apply List.mem_filterMap.mpr
    refine ⟨(node, v), List.mem_zipIdx_iff_getElem?.mpr hn, ?_⟩
    simp [row, bottom, titles, hb, hfirst]
    rfl
  · intro c hc htop
    unfold clusterRows at hc
    obtain ⟨q, hq, hc⟩ := List.mem_filterMap.mp hc
    dsimp only at hc
    split at hc
    · cases hc
    · have hrow := Option.some.inj hc
      have hv : q.2 = v := (congrArg RegionCluster.top hrow).trans htop
      have hlookup := List.mem_zipIdx_iff_getElem?.mp hq
      rw [hv, hn] at hlookup
      have hval := Option.some.inj hlookup
      rw [← hrow]
      change (match cg.nodes.zipIdx.find? (fun b => b.1.decl == q.1.decl) with
        | some b => b.2
        | none => q.2) = v
      rw [← hval, hfirst]

private theorem c5CoordGroupTop {P : Params} {exact : List Nat} {spec : RegionSpec}
    {p : Proper} {v : Nat} {node : Node}
    (hn : p.nodes[v]? = some ⟨node, false, none, false⟩) (hb : node.border = -2) :
    ∃ n, (coordinateGraphR P exact (some spec) p).nodes[v]? = some n ∧
      n.node.clusterPath = node.clusterPath := by
  let original : ProperNode := ⟨node, false, none, false⟩
  let zero : ProperNode := { original with node := { node with w := 0, h := 0 } }
  let sized := sizeProperPortsX P exact p
  let titled := titleReservationsR spec.titles P.clusterPad sized
  have hs : sized.nodes[v]? = some original := by
    simp [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hn, hb, original]
  have hv := (List.getElem?_eq_some_iff.mp hs).1
  have ht : titled.nodes[v]? = some zero := by
    unfold titled titleReservationsR
    dsimp only
    rw [List.getElem?_append_left (by simpa only [List.length_map] using hv)]
    simp [List.getElem?_map, hs, original, zero, hb]
  obtain ⟨_, he, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have ha : (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[v]? = some zero := by
    rw [he, List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1]
    exact ht
  have hc : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
      some (clearF zero) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, ha, Option.map_some]
  refine ⟨clearF zero, ?_, (clearF_keys zero).2.2.1⟩
  change (materializeDummyPaths (clearProxyExtents
    (OrderImpl.addClusterBorders titled P.clusterBorderW))).nodes[v]? = _
  have hd : (clearF zero).dummy = false := (clearF_keys zero).1
  simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hc,
    Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]

private theorem c5ReservedTopHeight {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs outXs : List Int} {out : Proper}
    (h : reservedPortsR pl cg labels xs = .ok (outXs, out)) {v : Nat} {n : ProperNode}
    (hn : pl.p.nodes[v]? = some n) (hvisit : ∃ c ∈ pl.rm.clusters, c.top = v)
    (howner : ∀ c ∈ pl.rm.clusters, c.top = v → c.node = v) :
    ∃ actual, out.nodes[v]? = some actual ∧ actual.node.clusterPath = n.node.clusterPath ∧
      Loops.requiredHeight cg.slot (loopSizes cg.edges labels v cg.slot) ≤ actual.node.h := by
  let need := Loops.requiredHeight cg.slot (loopSizes cg.edges labels v cg.slot)
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  have foldLaw (rows : List (RegionCluster × Nat)) (start finish : List Int × Array ProperNode)
      (src : ProperNode) (hsrc : start.2[v]? = some src)
      (hfold : rows.foldlM step start = .ok finish)
      (hrows : ∀ q ∈ rows, q.1.top = v → q.1.node = v) :
      ∃ dst, finish.2[v]? = some dst ∧ dst.node.clusterPath = src.node.clusterPath ∧
        ((need ≤ src.node.h ∨ ∃ q ∈ rows, q.1.top = v) → need ≤ dst.node.h) := by
    induction rows generalizing start src with
    | nil =>
      change Except.ok start = Except.ok finish at hfold
      rw [← Except.ok.inj hfold]
      exact ⟨src, hsrc, rfl, by simp⟩
    | cons q rest ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hmid, htail⟩ := c5HeightBind hfold
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨_, _, hmid⟩ := c5HeightBind hmid
        obtain ⟨_, _, hmid⟩ := c5HeightBind hmid
        have hentry : ∃ m, mid.2[v]? = some m ∧ m.node.clusterPath = src.node.clusterPath ∧
            (q.1.top = v → need ≤ m.node.h) ∧ (q.1.top ≠ v → m = src) := by
          rw [← Except.ok.inj hmid]
          dsimp only
          rw [Array.set!_eq_setIfInBounds]
          by_cases ht : q.1.top = v
          · have hs : start.2.getD v default = src := by
              rw [Array.getD_eq_getD_getElem?, hsrc, Option.getD_some]
            have hb := (Array.getElem?_eq_some_iff.mp hsrc).1
            have hd := hrows q List.mem_cons_self ht
            rw [ht, Array.getElem?_setIfInBounds_self_of_lt hb, hs, hd]
            refine ⟨_, rfl, rfl, fun _ => ?_, fun hne => (hne rfl).elim⟩
            exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
          · rw [Array.getElem?_setIfInBounds_ne ht]
            exact ⟨src, hsrc, rfl, fun he => (ht he).elim, fun _ => rfl⟩
        obtain ⟨m, hm, hp, hh, hkeep⟩ := hentry
        obtain ⟨dst, hdst, hpath, hbound⟩ := ih mid m hm htail
          (fun r hr => hrows r (List.mem_cons_of_mem _ hr))
        refine ⟨dst, hdst, hpath.trans hp, fun hneed => hbound ?_⟩
        by_cases ht : q.1.top = v
        · exact Or.inl (hh ht)
        · have heq := hkeep ht
          rcases hneed with hs | ⟨r, hr, hrt⟩
          · exact Or.inl (heq.symm ▸ hs)
          · rcases List.mem_cons.mp hr with rfl | hr
            · exact (ht hrt).elim
            · exact Or.inr ⟨r, hr, hrt⟩
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨finish, hfold, hret⟩ := c5HeightBind h
  obtain ⟨c, hc, htop⟩ := hvisit
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  have hq : (c, i) ∈ pl.rm.clusters.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  obtain ⟨actual, ha, hp, hbound⟩ := foldLaw _ _ _ n
    (by simpa only [List.getElem?_toArray] using hn) hfold
    (fun q hq => howner q.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)))
  have hnodes : out.nodes = finish.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hret)).symm
  exact ⟨actual, by rw [hnodes, Array.getElem?_toList]; exact ha, hp,
    hbound (Or.inr ⟨(c, i), hq, htop⟩)⟩

private theorem c5ActiveGroupHeight {P : Params} {inp : Input} {spec : RegionSpec}
    {exact : List Nat} {candidate cg : Graph} {labels : List MeasuredLabel}
    {run : Run} {order : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some spec) inp candidate labels order = .ok (cg, run))
    (hrm : newComponentRegions (some spec) P inp candidate = .ok (some rm))
    {v : Nat} {node : Node} (hn : candidate.nodes[v]? = some node) (hb : node.border = -2)
    (hfirst : (candidate.nodes.zipIdx.find? (fun q => q.1.decl == node.decl)) = some (node, v))
    (hmember : node.clusterPath.contains node.decl = true) :
    Loops.requiredHeight cg.slot (loopSizes cg.edges labels v cg.slot) ≤ (frameRect P cg run v).h := by
  obtain ⟨_, _, labeled, p, _, _, _, _, _, hnorm, hlabels, hcoord, _, _, ⟨allocation⟩⟩ :=
    componentRunR_active_allocation_stages hrun hrm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hfinal : cg.nodes[v]? = some node := by rw [(rC5RunHeader% hrun).1]; exact hn
  have hfrom : labeled.nodes[v]? = some ⟨node, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hfinal) rfl
  obtain ⟨top, htop, hpath⟩ := c5CoordGroupTop (P := P) (exact := exact) (spec := spec) hfrom hb
  have hp : allocation.placement.p = p := by rw [allocation.hPlacement]
  have hregions : allocation.placement.rm = rm := by rw [allocation.hPlacement]
  have ht : allocation.placement.p.nodes[v]? = some top := by rw [hp, ← hcoord]; exact htop
  have hc := c5ClusterTop (inp := inp) (spec := spec) hn hb hfirst
  rw [← c5ResolvedClusters hrm, ← hregions] at hc
  obtain ⟨reserved, hreserved, hpRes, hh⟩ :=
    c5ReservedTopHeight allocation.hFramesAndPorts ht hc.1 hc.2
  rw [stages.hCoordProper] at hreserved
  obtain ⟨actual, ha, _, _, hActual⟩ := (proxyWidths_rel stages.hProxy).2.2.2.2.1 v _ hreserved
  obtain ⟨same, hsame, _, _, _, hActualPath⟩ := proxyWidths_decl_path stages.hProxy hreserved
  have he : same = actual := Option.some.inj (hsame.symm.trans ha)
  rw [he] at hActualPath
  have haFinal : run.proper.nodes[v]? = some actual := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    exact ha
  have hf : (cg.nodes.getD v default).border = -2 := by
    simp only [List.getD_eq_getElem?_getD, hfinal, Option.getD_some, hb]
  have hm : actual.node.clusterPath.contains (cg.nodes.getD v default).decl = true := by
    simpa only [hActualPath, hpRes, hpath, List.getD_eq_getElem?_getD, hfinal, Option.getD_some]
      using hmember
  have hy :
      (frameRect P cg run v).y ≤ (Labels.rectAt run.proper run.xs run.ys v).y ∧
      (Labels.rectAt run.proper run.xs run.ys v).y +
        (Labels.rectAt run.proper run.xs run.ys v).h ≤
          (frameRect P cg run v).y + (frameRect P cg run v).h :=
    frameRect_member_vertical (q := (actual, v)) hf
      (List.mem_zipIdx_iff_getElem?.mpr haFinal) hm
  have hrect : (Labels.rectAt run.proper run.xs run.ys v).h = reserved.node.h := by
    change RouteImpl.nodeH run.proper v = _
    rw [RouteImpl.nodeH, haFinal]
    exact hActual
  obtain ⟨hTop, hBottom⟩ := hy
  rw [hrect] at hBottom
  omega

private theorem c5FallbackMeasuredGroupHeight {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) {v key : Nat} {source : ModelBox} {prior : Node}
    (hkey : part.1[v]? = some key) (hsource : inp.boxes[key]? = some source)
    (hrole : source.role = .group) (hfixed : inp.fixedSizes.any (·.1 == source.id) = false)
    (hprior : e.graph0.nodes[key]? = some prior) (hloop : loopEdges s.cg.edges v ≠ []) :
    Loops.requiredHeight s.cg.slot (loopSizes s.cg.edges e.measured v s.cg.slot) ≤ prior.h := by
  obtain ⟨metric, measured, raw, titles, hm, hmeas, hslot, hlen, hprep, hsize⟩ := rC5RawSize% e.graph0_eq
  have heq := Except.ok.inj (hm.symm.trans e.metric_eq)
  subst metric
  have heq := Except.ok.inj (hmeas.symm.trans e.measured_eq)
  subst measured
  let boxes := preparedBoxes inp
  change e.graph0 = Compound.prepare boxes e.params.clusterPad titles raw at hprep
  have hboxes := (List.getElem?_eq_some_iff.mp hsource).1
  have hbs : key < boxes.length := by simpa only [boxes, preparedBoxes, List.length_map] using hboxes
  have hlines := e.lines_eq
  unfold boxLines at hlines
  have hlineCount : e.lines.length = inp.boxes.length :=
    (mapM_getElem? _ _ _ hlines).1.trans List.length_zipIdx
  have hk : key < raw.nodes.length := by rw [hlen, hlineCount]; exact hboxes
  have hbefore := hsize (List.getElem?_eq_getElem hk)
  have hgraphSlot : e.graph.slot = e.graph0.slot := by
    have hg := e.graph_eq
    unfold exactGraph at hg
    obtain ⟨_, _, h⟩ := c5HeightBind hg
    exact (congrArg Graph.slot (Except.ok.inj h)).symm
  have hslot' : s.cg.slot = e.params.slot := by
    rw [(rC5RunHeader% s.hRun).2, rC5CandidateSlot% s.used e.graph part.1 s.candidate,
      hgraphSlot, hprep]
    exact hslot
  have hv := (List.getElem?_eq_some_iff.mp hkey).1
  have hsizes : loopSizes s.cg.edges e.measured v s.cg.slot =
      loopSizes raw.edges e.measured key e.params.slot := by
    rw [hslot', componentRunR_loopSizes_eq s.hRun,
      componentCandidateR_loopSizes_preserved s.used e.graph part.1
        (components_nodup _ _ s.hComp) s.candidate v hv,
      (List.getElem?_eq_some_iff.mp hkey).2, exactGraph_edges e.graph_eq, hprep,
      prepare_loopSizes_preserved boxes e.params.clusterPad titles raw key hbs]
  have hnonempty : loopSizes raw.edges e.measured key e.params.slot ≠ [] := by
    rw [← hsizes]
    exact fun hempty => hloop (List.map_eq_nil_iff.mp hempty)
  have hwidth : ∀ label ∈ loopSizes raw.edges e.measured key e.params.slot, 0 ≤ label.width := by
    intro label hmemb
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hmemb
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hpos : 0 < e.params.slot := by
    have hp := (checkedParams_valid e.checked).2.2.1
    omega
  have hextent := rC5LoopExtentPos% e.params.slot _ hpos hnonempty hwidth
  have hnotZero : (raw.nodes[key].loopExtent == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hzero := beq_iff_eq.mp ht
    have hle := hbefore.1
    omega
  have heff : boxes[key]? = some source := by
    simpa only [hfixed, Bool.false_eq_true, ↓reduceIte] using preparedBoxes_lookup hsource
  have hrecord := Compound.prepare_group_title_record boxes e.params.clusterPad titles raw hk heff hrole
  rw [← hprep, hprior] at hrecord
  have hh := congrArg Node.h (Option.some.inj hrecord)
  change prior.h = (if raw.nodes[key].loopExtent == 0 then _ else _) at hh
  rw [hnotZero] at hh
  change prior.h = max ((titles.getD key (0, 0)).2 + e.params.clusterPad) raw.nodes[key].h at hh
  rw [hsizes, hslot', hh]
  exact Int.le_trans hbefore.2 (Int.le_max_right _ _)

/-- The selected nonexact loop owner's actual local frame reserves its entire measured loop band. -/
theorem R6_SelectedLoopPartR.nonexactLoopHeight {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) {v key : Nat} {source : ModelBox} {edge : Edge}
    (hkey : part.1[v]? = some key) (hsource : inp.boxes[key]? = some source)
    (hedge : edge ∈ loopEdges s.cg.edges v) (hnonexact : s.run.exact.contains v = false) :
    Loops.requiredHeight s.cg.slot (loopSizes s.cg.edges e.measured v s.cg.slot) ≤
      (frameRect e.params s.cg s.run v).h := by
  have hheader := rC5RunHeader% s.hRun
  by_cases hgroup : source.role = .group ∧ inp.fixedSizes.any (·.1 == source.id) = false
  · obtain ⟨prior, hprior, hb, hd⟩ := rC5GroupSource% e hsource hgroup.1 hgroup.2
    obtain ⟨node, hnode, hb', hp, hd'⟩ := exactGraph_node_key e.graph_eq hprior
    have hcand := component_node_lookupR (spec := s.used) (cand := s.candidate) hkey hnode
    have hfinal : s.cg.nodes[v]? = some node := by rw [hheader.1]; exact hcand
    have hborder := hb'.trans hb
    obtain ⟨_, _, _, _, hpath⟩ := measuredGraph_group_origin e.graph0_eq hprior hb
    have hmember : node.clusterPath.contains node.decl = true := by rw [hp, hd', hpath]; simp
    cases hu : s.used with
    | none =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hedge).1
      rcases s.dispatch hi with ⟨_, _, hx⟩ | ⟨_, _, _, hactive, _⟩
      · have hflag : (exactDecls exactIds inp).contains prior.decl = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          have he := (rC5RunExact% s.hRun hfinal).mpr (by rwa [hd'])
          rw [hnonexact] at he
          cases he
        have hsource' : inp.boxes[prior.decl]? = some source := by rwa [hd]
        have he := rC5ExactGraphSize% e.graph_eq hprior hnode hsource'
        have hsame : node = prior := by simpa only [hflag, Bool.false_eq_true, ↓reduceIte] using he
        have hframe := rC5FallbackGroupHeight% hx hfinal hborder hmember
          (th := node.h - e.params.clusterPad) (by omega)
        have hh : node.h ≤ (frameRect e.params s.cg s.run v).h := by
          simpa only [Int.sub_add_cancel] using hframe
        rw [hsame] at hh
        exact Int.le_trans (c5FallbackMeasuredGroupHeight s hkey hsource hgroup.1 hgroup.2 hprior
          (fun hnil => by rw [hnil] at hedge; exact List.not_mem_nil hedge)) hh
      · rw [hu] at hactive
        cases hactive
    | some spec =>
      obtain ⟨rs, hr, hused⟩ := s.hResolved
      have hactive : ∃ rm, newComponentRegions (some spec) e.params inp
          (componentCandidateR (some spec) e.graph part.1 s.candidate) = .ok (some rm) := by
        cases rs with
        | none => simp [hu] at hused
        | some rm =>
          have hs : some spec = r7Spec idSets o e.params e.lines := by simpa [hu] using hused
          refine ⟨rm, ?_⟩
          rw [rC5CandidateRegions%, hs]
          exact hr
      obtain ⟨rm, hrm⟩ := hactive
      have hrun := s.hRun
      rw [hu] at hrun hcand
      exact c5ActiveGroupHeight hrun hrm hcand hborder
        (c5FirstGroupDecl e s.hComp (some spec) s.candidate hkey hsource hcand (hd'.trans hd)) hmember
  · obtain ⟨prior, hprior, hb, _, _⟩ := rC5PlainSource% e hsource hgroup
    obtain ⟨node, hnode, hb', _, _⟩ := exactGraph_node_key e.graph_eq hprior
    have hcand := component_node_lookupR (spec := s.used) (cand := s.candidate) hkey hnode
    have hfinal : s.cg.nodes[v]? = some node := by rw [hheader.1]; exact hcand
    have hborder := hb'.trans hb
    exact Int.le_trans
      ((r7_loopPlainSizing_of_run e s.hComp rfl s.hRun hfinal hborder).2 hnonexact)
      (regionRunFrameDims s.hRun hcand hborder).2

/-- Use the lookup of the emitted loop and the unique semantic edge declaration to select the very
frame passed to `Loops.loops`. The result is in local coordinates for final C5 transport. -/
theorem R6_SelectedLoopPartR.nonexactLoopBoundary {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) {i key : Nat} {source : ModelBox}
    {edge : Edge} {entry : Nat × LoopPlacement}
    (hedge : s.cg.edges[i]? = some edge)
    (hfound : s.loops.find? (fun l => l.1 == edge.decl) = some entry)
    (hkey : part.1[edge.tail]? = some key) (hsource : inp.boxes[key]? = some source)
    (hnonexact : s.run.exact.contains edge.tail = false) :
    (Loops.requiredHeight s.cg.slot (loopSizes s.cg.edges e.measured edge.tail s.cg.slot) ≤
      (frameRect e.params s.cg s.run edge.tail).h) ∧
    ∃ start finish, entry.2.points.head? = some start ∧ entry.2.points.getLast? = some finish ∧
      Validator.onBoundary start (frameRect e.params s.cg s.run edge.tail) ∧
      Validator.onBoundary finish (frameRect e.params s.cg s.run edge.tail) := by
  obtain ⟨v, _, out, hplaced, origin, hzip, hdecl, htail, _⟩ :=
    componentLoops_entry_origin s.hLoops (List.mem_of_find?_eq_some hfound)
  have hdecl' : entry.1 = edge.decl :=
    beq_iff_eq.mp (List.find?_some (p := fun l : Nat × LoopPlacement => l.1 == edge.decl) hfound)
  have horigin : origin ∈ loopEdges s.cg.edges v := (List.of_mem_zip hzip).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp horigin).1
  have hnd : (s.cg.edges.map Edge.decl).Nodup := by
    rw [componentRunR_edges_declsR s.hRun]
    exact rC5CandidateDeclNodup% s.used e.graph part.1 s.candidate
      (exactGraph_decls_nodup e.graph0_eq e.graph_eq)
  have hi : i < (s.cg.edges.map Edge.decl).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
  have hmap : (s.cg.edges.map Edge.decl)[i]? = (s.cg.edges.map Edge.decl)[j]? := by
    simp only [List.getElem?_map, hedge, hj, Option.map_some]
    exact congrArg some (hdecl'.symm.trans hdecl)
  have hij := (hnd.getElem?_inj hi).mp hmap
  subst j
  have heq : origin = edge := Option.some.inj (hj.symm.trans hedge)
  subst origin
  subst v
  have hheight := s.nonexactLoopHeight hkey hsource horigin hnonexact
  have hresult : Loops.loops (frameRect e.params s.cg s.run edge.tail) s.cg.slot
      (loopSizes s.cg.edges e.measured edge.tail s.cg.slot) = .ok out := by
    simpa only [hnonexact, Bool.false_eq_true, ↓reduceIte] using hplaced
  exact ⟨hheight, Loops.loops_boundary_of_reservation hresult hheight (List.of_mem_zip hzip).2⟩

end Elegant.Layered.PipelineImpl
