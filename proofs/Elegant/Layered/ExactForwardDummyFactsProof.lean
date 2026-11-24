import Elegant.Layered.ExactRouteForwardClearProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.RunLocalSeparationsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact forward dummy facts (`XFR_*X_holds`)

Proves three premises of `XF_routeForwardClearX_holds`
(`ExactRouteForwardClearProof.lean:309`): `XFR_StrictDummyLinkedX`,
`XFR_RouteLabelInDummyX`, `XFR_DummyExLabeledX`.

Plain path replayed (`route_run_clear_closed`, `RouteRunClearClosed.lean:76`,
which gets each fact from its `of_run` lemma):

* `routeLabelInDummy_of_run` (`RouteRunClearCases.lean:525`): placed forward
  labels lie in their dummy rect. Reads the run spec only through
  `forward_anchor_full` (`RunLocalSeparationsProof.lean:148`) and the shared
  envelope equation `forward_envelope_eq` (`RunLocalSeparationsProof.lean:268`).
  Exact anchor: `xfd_forward_anchor_core` below (copies `X_forward_anchor_full`,
  `ExactFlatC7Forward.lean:84`, over `componentRunX_spec`).
* `dummy_ex_labeled_of_run` (`RouteRunClearCases.lean:780`): every labeled
  forward edge has its mid-rank anchor dummy. Reads the run spec only through
  `forward_anchor_full` and shared `labelAnchorIndex_eq`. Same exact anchor.
* `strictDummyFrame_of_run` (`StrictDummyFrameProof.lean:1091`): the linked
  strict dummy frame. Reads the run spec through the rank straddle and the
  order-stage `DummyMarkerBracket` seam (`StrictDummyFrameProof.lean:51`).
  Reduced below to four narrow side residuals following the plain proof's
  four-side assembly (`StrictDummyFrameProof.lean:1115-1124`).

The label dummy of a forward edge is created by `addLabelNodes` and
`materializeDummyPaths` before the exact size hook matters; the exact anchor
keeps its fixed size, which already covers its own measured stack
(`componentRunX_forward_anchor_size`, `ExactPartBounded.lean:240`).

Probe: `proofs/wip/Probe/ExactRouteFwdClearTProbe.lean` evaluates the three
conclusions on exact runs (`strict`, `inDummy`, `dummyEx`) over flat,
self-loop-on-fixed, reversed-pair-into-group, and wider-than-slot fixed
inputs; `proofs/wip/Probe/ExactFwdDummyFactsTProbe.lean` checks the four
strict sides separately on the same inputs.
-/

/-- Copy of the private `findIdxHitElem'` (`RouteNonforwardLabelClearProof.lean:85`,
itself a copy of the private helper in `RouteRunClearCases.lean`): a `findIdx?`
hit carries its element and the satisfied predicate. -/
private theorem xfd_findIdxHitElem {α : Type} {l : List α} (p : α → Bool) (j : Nat)
    (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

/-- Dummy flags survive the exact coordinate-graph construction at a fixed
index (copy of `X_coordinateGraphX_dummy_at`, `ExactFlatC7Forward.lean:31`,
with the `sizeProperPortsX` first step; all later steps are shared). -/
private theorem xfd_coord_dummy_at {P : Params} {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (h : p.nodes[i]? = some nd) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.dummy = nd.dummy := by
  have hlen : (sizeProperPortsX P exact p).nodes.length = p.nodes.length :=
    sizeProperPortsX_length P exact p
  have hi : i < (sizeProperPortsX P exact p).nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    omega
  obtain ⟨sized, hsized⟩ : ∃ sized,
      (sizeProperPortsX P exact p).nodes[i]? = some sized :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  have hkey := sizeProperPortsX_key P exact p i
  rw [h, hsized] at hkey
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
  have hd_sized : sized.dummy = nd.dummy := hkey.1
  obtain ⟨titled, htitled, hd_titled⟩ :
      ∃ titled, (titleReservations (sizeProperPortsX P exact p)).nodes[i]? =
        some titled ∧ titled.dummy = nd.dummy := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by
        have hlt := (List.getElem?_eq_some_iff.mp hsized).1
        simpa using hlt)]
    simp only [List.getElem?_map, hsized, Option.map_some]
    obtain ⟨ha1, -, -, -⟩ := titleF_keys sized
    exact ⟨_, rfl, by rw [ha1, hd_sized]⟩
  obtain ⟨bordered, hbordered, hd_bordered⟩ :
      ∃ bordered, (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
          some bordered ∧ bordered.dummy = nd.dummy := by
    obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
    have hlen2 : i < (titleReservations (sizeProperPortsX P exact p)).nodes.length :=
      (List.getElem?_eq_some_iff.mp htitled).1
    rw [hnodes, List.getElem?_append_left hlen2, htitled]
    exact ⟨_, rfl, hd_titled⟩
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
      (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]?.map
        clearF := by
    rw [clearProxyExtents_nodes, List.getElem?_map]
  obtain ⟨ha1, -, -, -⟩ := clearF_keys bordered
  simp only [coordinateGraphX, materializeDummyPaths, List.getElem?_map,
    List.getElem?_zipIdx, hclear, hbordered, Option.map_some]
  split
  · exact ⟨_, rfl, by simp [hd_bordered, ha1]⟩
  · exact ⟨_, rfl, by simp [hd_bordered, ha1]⟩
/-- The exact executed run carries the selected forward label stack at the
exact anchor the forward envelope uses (copies `X_forward_anchor_full`,
`ExactFlatC7Forward.lean:84`, over `componentRunX_spec`, with the dummy flag
kept through `xfd_coord_dummy_at`; the coordinate-proper lookup is dropped
since only the proper lookup is consumed below). -/
private theorem xfd_forward_anchor_core {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {k : Nat} {edge : Edge} {first : MeasuredLabel}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
    (hfirst : (routeLabels labels edge.decl).head? = some first) :
    ∃ index nd,
      labelAnchorIndex run.proper k
        (rk run.proper.rank edge.tail +
          Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
          some index ∧
      run.proper.nodes[index]? = some nd ∧
      nd.edge = some k ∧ nd.dummy = true ∧ nd.node.border = 0 ∧
      (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter ≤
        nd.node.w ∧
      nd.node.h = (stackSize cg.slot (routeLabels labels edge.decl)).height := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hc, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨halign0, hwf⟩ := normalize_node_rank_alignment hn
  obtain ⟨hlrank, hlkeys⟩ := addLabelNodes_anchor_keys hl
  have hlen : labeled.nodes.length = p0.nodes.length := by
    have he := congrArg List.length hlkeys
    simpa only [List.length_map] using he
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [hlen, hlrank, halign0]
  have hedgeBounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hk)
  have htailBound : edge.tail < labeled.rank.length := by
    rw [hlrank]
    have hlt : edge.tail < cg.nodes.length := hedgeBounds.1
    have hle := normalize_nodes_length_le hn
    omega
  have hheadBound : edge.head < labeled.rank.length := by
    rw [hlrank]
    have hlt : edge.head < cg.nodes.length := hedgeBounds.2.1
    have hle := normalize_nodes_length_le hn
    omega
  obtain ⟨index, nd, hi, hnode, hw, hh⟩ :=
    componentLabels_selected_size hk hne hfirst hl
  have hedge : nd.edge = some k := labelAnchorIndex_node_edge hi hnode
  have hplain : EdgeAnchorsPlain labeled :=
    addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hn) hl
  have hborder : nd.node.border = 0 :=
    hplain nd (List.mem_of_getElem? hnode) (by rw [hedge]; simp)
  have hdummy : nd.dummy = true := labeled_anchor_plain hn hl hnode hedge
  obtain ⟨out, hout, hedgeOut, hborderOut, hwOut, hhOut⟩ :=
    coordinateGraphX_plain_anchor_dims P hnode hborder
  obtain ⟨dout, hdout, hd_dout⟩ := xfd_coord_dummy_at hnode
  have houtEq : dout = out := Option.some.inj (hdout.symm.trans hout)
  subst dout
  have hkeysPrefix := (coordinateGraphX_anchor_prefix P exact labeled).1
  have hrankPrefix := (coordinateGraphX_anchor_prefix P exact labeled).2
  have hicoord := labelAnchorIndex_prefix halign hkeysPrefix hrankPrefix hi
  rw [hc] at hout hicoord hrankPrefix
  obtain ⟨_hedges, hprank, _hprolen, _, _, hpreserve⟩ := proxyWidths_rel hproxy
  have hne2 : ¬ (out.node.border = -2 ∨ out.node.border = 2) := by
    rw [hborderOut]
    omega
  obtain ⟨hpnode, _hxs⟩ := hpreserve index out hout hne2
  have hlookup : run.proper.nodes[index]? = some out := by
    rw [← hdrop]
    exact hpnode
  obtain ⟨_extraRanks, hcrank⟩ := hrankPrefix
  have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact hprank
  have htail : rk run.proper.rank edge.tail = rk labeled.rank edge.tail := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left htailBound]
  have hhead : rk run.proper.rank edge.head = rk labeled.rank edge.head := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left hheadBound]
  have hanchor : labelAnchorIndex run.proper k
      (rk run.proper.rank edge.tail +
        Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
        some index := by
    rw [htail, hhead, ← hdrop]
    change labelAnchorIndex q0 k _ = some index
    unfold labelAnchorIndex
    rw [proxyWidths_edge_keys hproxy, hprank]
    exact hicoord
  have hedgeP : out.edge = some k := hedgeOut.trans hedge
  have hborderP : out.node.border = 0 := hborderOut
  have hdummyP : out.dummy = true := hd_dout.trans hdummy
  refine ⟨index, out, hanchor, hlookup, hedgeP, hdummyP, hborderP, ?_, ?_⟩
  · rw [← hw]
    exact hwOut
  · exact hhOut.trans hh
/-- Exact labeled-edge dummy existence: every forward edge carrying a label
has its mid-rank anchor dummy. Replay of `dummy_ex_labeled_of_run`
(`RouteRunClearCases.lean:780`) over `componentRunX`: the labeled edge has a
head label, hence an anchor by `xfd_forward_anchor_core`, which is the `find?`
witness by shared `labelAnchorIndex_eq`. -/
theorem XFR_dummyExLabeledX_holds (exactIds : List String) :
    XFR_DummyExLabeledX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
    edge e he hne _hrev hlabeled
  obtain ⟨l, hlm, hledge⟩ := hlabeled
  have hbe : (l.edge == e.decl) = true := by simp [hledge]
  have hmem_f : l ∈ routeLabels execution.measured e.decl :=
    List.mem_filter.mpr ⟨hlm, hbe⟩
  obtain ⟨first, hfirst⟩ : ∃ first,
      (routeLabels execution.measured e.decl).head? = some first := by
    cases hcon : routeLabels execution.measured e.decl with
    | nil => rw [hcon] at hmem_f; simp at hmem_f
    | cons f r => exact ⟨f, rfl⟩
  obtain ⟨aindex, and, hanchor, hnodeA, _hedgeA, hdummyA, _hborderA, _hwA, _hhA⟩ :=
    xfd_forward_anchor_core hrun he hne hfirst
  rw [labelAnchorIndex_eq] at hanchor
  cases hfq : run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge &&
      rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv
        (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) with
  | none => rw [hfq] at hanchor; simp at hanchor
  | some q =>
    obtain ⟨qd, d⟩ := q
    have hd_eq : d = aindex := Option.some.inj (by rw [hfq] at hanchor; simpa using hanchor)
    have hmemq : run.proper.nodes[d]? = some qd :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfq)
    have hqd : qd = and := by
      rw [hd_eq] at hmemq
      exact Option.some.inj (hmemq.symm.trans hnodeA)
    have hqdum : qd.dummy = true := by rw [hqd]; exact hdummyA
    exact ⟨qd, d, hqdum, rfl⟩
/-- Link the `find?` witness of a placed forward label to its exact anchor
(step of `routeLabelInDummy_of_run`, `RouteRunClearCases.lean:568-616`, over
`componentRunX`): the envelope inversion `forward_envelope_eq` (shared) feeds
`xfd_forward_anchor_core`, and the two `find?` hits coincide. -/
private theorem xfd_anchor_link {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {edge : Nat} {e : Edge} {env : Rect} {nd : ProperNode} {d : Nat}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (he : cg.edges[edge]? = some e) (hne : e.tail ≠ e.head)
    (hrev : e.reversed = false)
    (henv : labelEnvelope P cg run labels edge e = some env)
    (hfindd : run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge &&
      rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv
        (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d)) :
    ∃ (first : MeasuredLabel) (and : ProperNode),
      (routeLabels labels e.decl).head? = some first ∧
      run.proper.nodes[d]? = some nd ∧
      (stackSize cg.slot (routeLabels labels e.decl)).width + first.gutter ≤ and.node.w ∧
      and.node.h = (stackSize cg.slot (routeLabels labels e.decl)).height ∧
      nd = and ∧ env = Labels.textRectAt run.proper run.xs run.ys d first.gutter := by
  obtain ⟨first, q, hfirst, hqfind, hqenv⟩ := forward_envelope_eq hne hrev henv
  obtain ⟨aindex, and, hanchor, hnodeA, _hedgeA, _hdummyA, _hborderA, hwA, hhA⟩ :=
    xfd_forward_anchor_core hrun he hne hfirst
  rw [labelAnchorIndex_eq] at hanchor
  have hu : q.2 = aindex := by
    rw [hqfind] at hanchor
    exact Option.some.inj hanchor
  have hqq : q = (nd, d) := Option.some.inj (hqfind.symm.trans hfindd)
  have hq2 : q.2 = d := congrArg Prod.snd hqq
  have hq1a : q.1 = nd := congrArg Prod.fst hqq
  have hmemq : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hqfind)
  have hmemd : run.proper.nodes[d]? = some nd := by
    rw [← hq2, ← hq1a]
    exact hmemq
  have hnodeA' : run.proper.nodes[q.2]? = some and := by
    rw [hu]
    exact hnodeA
  have hq1b : q.1 = and := Option.some.inj (hmemq.symm.trans hnodeA')
  have hndand : nd = and := hq1a.symm.trans hq1b
  have he2 : env = Labels.textRectAt run.proper run.xs run.ys d first.gutter := by
    rw [hqenv, hq2]
  exact ⟨first, and, hfirst, hmemd, hwA, hhA, hndand, he2⟩
/-- Exact placed-in-dummy: every placed forward label lies in its dummy rect.
Replay of `routeLabelInDummy_of_run` (`RouteRunClearCases.lean:525`) over
`componentRunX`: placed-pair inversion, measured-index injectivity, and edge
identity are run-generic (reused outright); the anchor and envelope steps go
through `xfd_anchor_link` (exact anchor plus shared `forward_envelope_eq`);
the stack containment is run-generic. -/
theorem XFR_routeLabelInDummyX_holds (exactIds : List String) :
    XFR_RouteLabelInDummyX exactIds := by
  intro inp o res execution comp _hcomp candidate run orderOptions hrun
    k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev d nd _hdummy hfindd
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
    placedLabels_pair_inv hnd hmem
  have hml : ml = l₀ :=
    measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := xfd_findIdxHitElem _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdeclsNodup : ((componentCandidate execution.graph comp candidate).edges.map
      (·.decl)).Nodup := by
    have hndE := exactGraph_decls_nodup execution.graph0_eq execution.graph_eq
    exact componentCandidate_decls_nodup _ _ _ hndE
  have heq : edge = edge' := by
    have hmap : ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl)[edge]? =
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl).length := by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdeclsNodup.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  have hne' : e'.tail ≠ e'.head := by
    intro hcon
    rw [← hEE] at hcon
    exact hne hcon
  have hrev' : e'.reversed = false := by
    rw [← hEE]
    exact hrev
  rw [hEE] at hfindd
  obtain ⟨first, and, hfirst, hmemd, hwA', hhA', hndand, he2⟩ :=
    xfd_anchor_link hrun he' hne' hrev' henv hfindd
  have hlab := execution.measured_nonneg
  have hfm : first ∈ routeLabels execution.measured e'.decl := by
    cases hrfl : routeLabels execution.measured e'.decl with
    | nil => rw [hrfl] at hfirst; simp at hfirst
    | cons hd tl =>
      have heq2 : hd = first := by
        have h2 := hfirst
        rw [hrfl] at h2
        simpa using h2
      subst heq2
      exact List.mem_cons_self
  have hg0 : 0 ≤ first.gutter := (hlab first (List.mem_filter.mp hfm).1).2.2
  have hsizes : ∀ s ∈ (routeLabels execution.measured e'.decl).map
      fun l => (l.width, l.height), 0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1,
      (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  have hslot := componentRunX_slot_nonneg hrun
  have hWd : RouteImpl.nodeW run.proper d = nd.node.w := by
    unfold RouteImpl.nodeW
    rw [hmemd]
  have hHd : RouteImpl.nodeH run.proper d = nd.node.h := by
    unfold RouteImpl.nodeH
    rw [hmemd]
  have henvW : env.w = nd.node.w - first.gutter := by
    simp only [he2, Labels.textRectAt, Labels.rectAt, Labels.labelRect, hWd, hHd]
  have henvH : env.h = nd.node.h := by
    simp only [he2, Labels.textRectAt, Labels.rectAt, Labels.labelRect, hWd, hHd]
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hw : Labels.stackWidth
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.w := by
    have hwA'' : Labels.stackWidth
        ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤
        and.node.w - first.gutter := by
      rw [stackSize_width_eq] at hwA'
      omega
    rw [henvW, hndand]
    exact hwA''
  have hh : Labels.stackHeight
      ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.h := by
    rw [henvH, hndand, hhA', stackSize_height_eq]
    exact Int.le_refl _
  obtain ⟨_, _, hcont⟩ := Labels.stackRects_contained env
      ((componentCandidate execution.graph comp candidate).slot) hslot hsizes hw hh
      rect hmemstk
  have hsub : (Labels.rectAt run.proper run.xs run.ys d).Contained env := by
    have hex : env.x = (Labels.rectAt run.proper run.xs run.ys d).x + first.gutter := by
      rw [he2]
      rfl
    have hey : env.y = (Labels.rectAt run.proper run.xs run.ys d).y := by
      rw [he2]
      rfl
    have how : (Labels.rectAt run.proper run.xs run.ys d).w = nd.node.w := by
      unfold Labels.rectAt Labels.labelRect
      exact hWd
    have hoh : (Labels.rectAt run.proper run.xs run.ys d).h = nd.node.h := by
      unfold Labels.rectAt Labels.labelRect
      exact hHd
    unfold Rect.Contained
    omega
  exact Rect.Contained.trans hsub hcont
/-- Exact strict-dummy left edge: every linked dummy rect starts strictly
right of its group frame's left edge. Mirror of the conclusion of
`dummyFrameLeftXStrict` (`StrictDummyFrameProof.lean:935`), which the plain
proof takes through the order-stage `DummyMarkerBracket` seam
(`StrictDummyFrameProof.lean:51`) via same-rank separation. Strictly narrower
than `XFR_StrictDummyLinkedX` (one of its four edge inequalities), over exact
runs only. Probe: `ExactFwdDummyFactsTProbe.lean` checks each side separately
on flat, nested, sane-fixed, and wider-than-slot inputs. -/
def XFD_StrictLeftX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {gpos : Nat} {gn : Node},
      (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn →
      gn.border = -2 →
      ∀ {d : Nat} {nd : ProperNode}, run.proper.nodes[d]? = some nd →
        nd.dummy = true → gn.decl ∈ nd.node.clusterPath →
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run gpos).x <
          (Labels.rectAt run.proper run.xs run.ys d).x

/-- Exact strict-dummy right edge: every linked dummy rect ends strictly left
of its group frame's right edge. Mirror of the conclusion of
`dummyFrameRightXStrict` (`StrictDummyFrameProof.lean:1012`), through the same
`DummyMarkerBracket` seam as the left edge. Strictly narrower than
`XFR_StrictDummyLinkedX` (one of its four edge inequalities), over exact runs
only. Same probe as `XFD_StrictLeftX`. -/
def XFD_StrictRightX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {gpos : Nat} {gn : Node},
      (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn →
      gn.border = -2 →
      ∀ {d : Nat} {nd : ProperNode}, run.proper.nodes[d]? = some nd →
        nd.dummy = true → gn.decl ∈ nd.node.clusterPath →
        (Labels.rectAt run.proper run.xs run.ys d).x +
          (Labels.rectAt run.proper run.xs run.ys d).w <
          (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run gpos).x +
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run gpos).w
/-- Exact strict-dummy top edge: every linked dummy rect starts strictly below
its group frame's top edge. Mirror of the conclusion of `dummyFrameTopYStrict`
(`StrictDummyFrameProof.lean:606`), which the plain proof takes through the
strict dummy rank straddle (`dummyTopRankStrict`, `StrictDummyFrameProof.lean:492`,
from chain interior and the closed top closure) transported through the rank
tops. Strictly narrower than `XFR_StrictDummyLinkedX` (one of its four edge
inequalities), over exact runs only. Same probe as `XFD_StrictLeftX`. -/
def XFD_StrictTopX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {gpos : Nat} {gn : Node},
      (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn →
      gn.border = -2 →
      ∀ {d : Nat} {nd : ProperNode}, run.proper.nodes[d]? = some nd →
        nd.dummy = true → gn.decl ∈ nd.node.clusterPath →
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run gpos).y <
          (Labels.rectAt run.proper run.xs run.ys d).y

/-- Exact strict-dummy bottom edge: every linked dummy rect ends strictly
above its group frame's bottom edge. Mirror of the conclusion of
`dummyFrameBotYStrict` (`StrictDummyFrameProof.lean:692`), through the strict
dummy bottom rank straddle (`dummyBottomRankStrict`,
`StrictDummyFrameProof.lean:542`). Strictly narrower than
`XFR_StrictDummyLinkedX` (one of its four edge inequalities), over exact runs
only. Same probe as `XFD_StrictLeftX`. -/
def XFD_StrictBottomX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {gpos : Nat} {gn : Node},
      (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn →
      gn.border = -2 →
      ∀ {d : Nat} {nd : ProperNode}, run.proper.nodes[d]? = some nd →
        nd.dummy = true → gn.decl ∈ nd.node.clusterPath →
        (Labels.rectAt run.proper run.xs run.ys d).y +
          (Labels.rectAt run.proper run.xs run.ys d).h <
          (frameRect execution.params
            (componentCandidate execution.graph comp candidate) run gpos).y +
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run gpos).h
/-- Exact strict linked dummy frame from its four narrow sides: replay of the
assembly at the end of `strictDummyFrame_of_run`
(`StrictDummyFrameProof.lean:1115-1124`), which builds the same four-tuple
from the four side lemmas. Each side is a strictly narrower residual above;
`Rect.StrictInside` is exactly their conjunction. -/
theorem XFR_strictDummyLinkedX_holds (exactIds : List String)
    (hL : XFD_StrictLeftX exactIds) (hR : XFD_StrictRightX exactIds)
    (hT : XFD_StrictTopX exactIds) (hB : XFD_StrictBottomX exactIds) :
    XFR_StrictDummyLinkedX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  exact ⟨hL execution hcomp hrun hg hgroup hnd hdum hpath,
    hR execution hcomp hrun hg hgroup hnd hdum hpath,
    hT execution hcomp hrun hg hgroup hnd hdum hpath,
    hB execution hcomp hrun hg hgroup hnd hdum hpath⟩
end PipelineImpl
end Layered
end Elegant
