import Elegant.Layered.FamilyC5
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.GroupEndpointC5

set_option autoImplicit false

/-! ### Group endpoint attachment (C5, flat group-endpoint case)

`componentRun_group_route_attachment` discharges the flat group-endpoint fact
`PipelineImpl.GroupAttach` from one named bundle of per-endpoint facts,
`GroupTopEndpointData`.  The data records, for a `border = -2` top proxy: the
coordinate-graph mirror of the border, the coordinate cluster-path owner, the
executed member containment, the executed member routing bound (`hlow` of
`componentRun_group_frame_boundary`), and the two port-form facts
(`frameKind = -2`, zero proxy height).

The assembly itself is complete: it routes the first/last points through the
stored port forms of `route_endpoints_on_ports`, replaces each `-2` endpoint's
frame by the transported `frameRect` and every other endpoint by the
transported `boxRect`, and transports both through
`onBoundary_shift`/`onBoundary_orient`, exactly as
`componentRun_ordinary_route_attachment` does for plain endpoints. -/

namespace Elegant.Layered.PipelineImpl

/-- The per-endpoint facts for a `border = -2` group top proxy.  The first six
conjuncts are the premises of `componentRun_group_frame_boundary` in their
executed forms; the last two state that the endpoint's port form is the frame
top (`frameKind = -2`, proxy height zero), which collapses both stored port
forms of `route_endpoints_on_ports` to `⟨px, run.ys.getD v 0⟩`. -/
def GroupTopEndpointData (cg : Graph) (run : Run) (v : Nat) : Prop :=
  (cg.nodes.getD v default).border = -2 ∧
    run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default) ∧
    (run.coordinateProper.nodes.getD v default).node.border = -2 ∧
    (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl ∧
    (run.proper.nodes.getD v default).node.clusterPath.contains
      (cg.nodes.getD v default).decl = true ∧
    v < run.proper.nodes.length ∧
    (∀ q : ProperNode × Nat, q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains (cg.nodes.getD v default).decl = true →
        run.ys.getD v 0 ≤ run.ys.getD q.2 0) ∧
    RouteImpl.frameKind run.proper v = -2 ∧
    RouteImpl.nodeH run.proper v = 0

/-- Universal form of the group-endpoint data: every `-2` top proxy of a
successful flat execution satisfies it.  This is the single remaining fact of
the group-endpoint attachment proof. -/
def GroupTopEndpointFacts : Prop :=
  ∀ {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRun P cg labels orderOptions = .ok run →
    ∀ v : Nat, (cg.nodes.getD v default).border = -2 → GroupTopEndpointData cg run v

/-- Candidate-graph specialization of `GroupTopEndpointFacts`: the remaining
obligation in its provable form.  Measured candidate graphs carry unique
`border = -2` declarations ending their cluster paths, which is exactly what
the unrestricted form lacks: on a hand-built graph with two `-2` markers that
share a declaration and are not ancestor/descendant, `componentRun` succeeds
and the second marker's frame top lies strictly below its own port, so the
unrestricted bundle (and `GroupAttach` at that graph) is refuted. -/
def GroupTopEndpointFactsCandidate : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
      componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run →
      ∀ v : Nat,
        ((componentCandidate graph comp candidate).nodes.getD v default).border = -2 →
        GroupTopEndpointData (componentCandidate graph comp candidate) run v

/-- The routed port point of a group top proxy lies on the group frame
boundary, from the bundled endpoint facts. -/
theorem group_top_boundary
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} (hdata : GroupTopEndpointData cg run v) (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run v) := by
  obtain ⟨hcborder, hnode, hborder, howner, hcontains, hv, hlow, _, _⟩ := hdata
  exact componentRun_group_frame_boundary hrun hnode hborder hcborder howner hcontains
    hv hlow px hpx

/-- Two conjuncts of `GroupTopEndpointData` follow from the run alone: a
coordinate node carrying a `-2` border is a non-dummy frame top with zero
height in the executed graph. -/
theorem group_top_frame_facts
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hb : (run.coordinateProper.nodes.getD v default).node.border = -2) :
    RouteImpl.frameKind run.proper v = -2 ∧ RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  obtain ⟨labeled, hcoord, hkeys, _, _⟩ := componentRun_coordinate_source_alignment hrun
  have hrel := proxyWidths_rel hproxy
  obtain ⟨nd', hnd', hdummy, hborder', hheight⟩ := hrel.2.2.2.2.1 v _ hnode
  have hproper : run.proper.nodes[v]? = some nd' := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    exact hnd'
  have hcoord' : (coordinateGraph P labeled).nodes[v]? =
      some (run.coordinateProper.nodes.getD v default) := by
    rw [hcoord]
    exact hnode
  have hd : (run.coordinateProper.nodes.getD v default).dummy = false := by
    cases hdv : (run.coordinateProper.nodes.getD v default).dummy with
    | false => rfl
    | true =>
      have h0 := pc_plain hkeys hcoord' hdv
      rw [h0] at hb
      exact absurd hb (by decide)
  refine ⟨(isTop_iff hproper).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [hdummy]; exact hd
  · rw [hborder']; exact hb
  · have hzero : nd'.node.h = 0 := by
      rw [hheight]
      exact pc_frame_flat hcoord' (Or.inl hb)
    simp only [RouteImpl.nodeH, hproper, hzero]

/-- A `-2` graph node's frame kind is `-2` whenever the endpoint data says so;
the `ite` form of the stored port therefore selects the frame top. -/
theorem group_top_port_eq_ys
    {cg : Graph} {run : Run} {v : Nat} (_hdata : GroupTopEndpointData cg run v) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).y = run.ys.getD v 0 := by
  simp only [RouteImpl.boxRect, RouteImpl.yAt]

/-- The frame-top port form coincides with the frame's vertical top. -/
theorem group_top_frame_y_eq_ys
    {cg : Graph} {run : Run} {v : Nat} (hdata : GroupTopEndpointData cg run v) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).y +
        (RouteImpl.boxRect run.proper run.xs run.ys v).h = run.ys.getD v 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hnh⟩ := hdata
  simp only [RouteImpl.boxRect, RouteImpl.yAt]
  rw [hnh]
  exact Int.add_zero _

/-- Flat group-endpoint attachment: every route whose first or last point is a
group top proxy attaches to the transported frame of that endpoint, and every
other endpoint attaches to the transported box rectangle.  Conditional on the
bundled group-endpoint facts. -/
theorem componentRun_group_route_attachment_of_facts
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < cg.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    (hsrc : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = -2 →
      GroupTopEndpointData cg run (RouteImpl.edgeAt run.proper first).tail)
    (htgt : (cg.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border = -2 →
      GroupTopEndpointData cg run (RouteImpl.edgeAt run.proper last).head)
    (cursor : Int) (loops : List (Nat × LoopPlacement))
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ rt : EdgeRoute, ∃ start finish : Point,
      run.routes[i]? = some rt ∧ rt.original = i ∧
      (placeComponent P cg run cursor labels loops).routes[i]? =
        some ((cg.edges[i]).decl, rt.points.map
          (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
            (0 - (placeBounds P cg run labels loops).minY))) ∧
      rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
      let source := frameRect P cg run (RouteImpl.edgeAt run.proper first).tail
      let target := frameRect P cg run (RouteImpl.edgeAt run.proper last).head
      let reversed := (cg.edges.map (·.reversed)).getD i false
      let bounds := placeBounds P cg run labels loops
      let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
      let transportRect := fun rect => shiftRect margin margin
        (orientRect direction canvasH
          (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) rect))
      Validator.onBoundary (transport start) (transportRect (if reversed then target else source)) ∧
      Validator.onBoundary (transport finish) (transportRect (if reversed then source else target)) := by
  obtain ⟨rt, hrt, horiginal, _⟩ := componentRun_route_of_index hrun hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, _, _, hroutes⟩ :=
    componentRun_spec hrun
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    simpa only [horiginal] using hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    simpa only [horiginal] using hlast
  obtain ⟨px, qx, _, _, hpx0, hpx1, hqx0, hqx1, hend⟩ :=
    Elegant.Layered.route_endpoints_on_ports hrouting hroutes rt hm first last hfirst' hlast'
  rw [horiginal] at hend
  have hgeometry := RouteImpl.routeWithLanes_geometry hrouting
  obtain ⟨_, hdims, _, _, hedge⟩ := RouteImpl.layersOk_spec hgeometry.1
  have hf := hedge first (RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' hfirst))
  have hl := hedge last (RouteImpl.mem_edgesOf (List.mem_of_getLast? hlast))
  have hsh := (hdims _ hf.1).2
  have hth := (hdims _ hl.2.1).2
  -- plain box-rectangle boundaries at both ends
  have hsPlain : Validator.onBoundary
      ⟨px, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (RouteImpl.boxRect run.proper run.xs run.ys (RouteImpl.edgeAt run.proper first).tail) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inr True.intro))⟩
  have htPlain : Validator.onBoundary
      ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).y⟩
      (RouteImpl.boxRect run.proper run.xs run.ys (RouteImpl.edgeAt run.proper last).head) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hqx0, hqx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
  -- non-reversed head point on the source frame
  have hsb : Validator.onBoundary
      ⟨px, if RouteImpl.frameKind run.proper (RouteImpl.edgeAt run.proper first).tail = -2 then
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y else
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (frameRect P cg run (RouteImpl.edgeAt run.proper first).tail) := by
    by_cases hg : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = -2
    · obtain ⟨-, -, -, -, -, -, -, hfk, -⟩ := hsrc hg
      simp only [hfk, ↓reduceIte]
      simpa only [RouteImpl.boxRect, RouteImpl.yAt] using
        group_top_boundary hrun (hsrc hg) px ⟨hpx0, hpx1⟩
    · rw [plain_frame_eq_boxRect' P cg run _ hf.1 hg]
      by_cases hfk : RouteImpl.frameKind run.proper
          (RouteImpl.edgeAt run.proper first).tail = -2
      · simp only [hfk, ↓reduceIte, Validator.onBoundary, RouteImpl.boxRect]
        exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
      · simp only [hfk, ↓reduceIte]
        exact hsPlain
  -- reversed last point on the source frame
  have hsbRev : Validator.onBoundary
      ⟨px, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (frameRect P cg run (RouteImpl.edgeAt run.proper first).tail) := by
    by_cases hg : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = -2
    · have hdata := hsrc hg
      have hy := group_top_frame_y_eq_ys (cg := cg) (run := run) hdata
      rw [hy]
      exact group_top_boundary hrun hdata px ⟨hpx0, hpx1⟩
    · rw [plain_frame_eq_boxRect' P cg run _ hf.1 hg]
      exact hsPlain
  -- head point on the target frame
  have htb : Validator.onBoundary
      ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).y⟩
      (frameRect P cg run (RouteImpl.edgeAt run.proper last).head) := by
    by_cases hg : (cg.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border = -2
    · have hdata := htgt hg
      have hy := group_top_port_eq_ys (cg := cg) (run := run) hdata
      rw [hy]
      exact group_top_boundary hrun hdata qx ⟨hqx0, hqx1⟩
    · rw [plain_frame_eq_boxRect' P cg run _ hl.2.1 hg]
      exact htPlain
  have hplaced := placeComponent_route_entry_of_producer hrun cursor loops i hi hloop
  have hget : run.routes[i]'(by
      rw [componentRun_routes_length hrun, componentRun_proper_chains_length hrun]
      exact hi) = rt := (List.getElem?_eq_some_iff.mp hrt).2
  rw [hget] at hplaced
  split at hend
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev, ↓reduceIte]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htb
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsbRev
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsb
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htb

/-- The flat group-endpoint attachment fact `GroupAttach`, conditional on the
bundled group-endpoint facts. -/
theorem componentRun_group_route_attachment
    (hfacts : GroupTopEndpointFacts) :
    GroupAttach := by
  intro P cg run labels orderOptions hrun i hi first last hfirst hlast cursor loops hloop
    margin direction canvasH boxX boxY
  exact componentRun_group_route_attachment_of_facts hrun hi hfirst hlast
    (fun hg => hfacts hrun _ hg) (fun hg => hfacts hrun _ hg)
    cursor loops hloop margin direction canvasH boxX boxY

/-- The per-graph form of `GroupAttach`: one explicit `P cg` pair, all other
binders and the conclusion byte-identical to `GroupAttach`'s. -/
def GroupAttachAt (P : Params) (cg : Graph) : Prop :=
  ∀ {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRun P cg labels orderOptions = .ok run →
    ∀ {i : Nat} (hi : i < cg.edges.length) {first last : Nat}
      (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
      (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
      (cursor : Int) (loops : List (Nat × LoopPlacement))
      (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
      (margin : Int) (direction : Direction) (canvasH boxX boxY : Int),
      ∃ rt : EdgeRoute, ∃ start finish : Point,
        run.routes[i]? = some rt ∧ rt.original = i ∧
        (placeComponent P cg run cursor labels loops).routes[i]? =
          some ((cg.edges[i]).decl, rt.points.map
            (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
              (0 - (placeBounds P cg run labels loops).minY))) ∧
        rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
        let source := frameRect P cg run (RouteImpl.edgeAt run.proper first).tail
        let target := frameRect P cg run (RouteImpl.edgeAt run.proper last).head
        let reversed := (cg.edges.map (·.reversed)).getD i false
        let bounds := placeBounds P cg run labels loops
        let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
        let transportRect := fun rect => shiftRect margin margin
          (orientRect direction canvasH
            (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) rect))
        Validator.onBoundary (transport start)
          (transportRect (if reversed then target else source)) ∧
        Validator.onBoundary (transport finish)
          (transportRect (if reversed then source else target))

/-- `GroupAttach` holds exactly at every params/graph pair iff it holds as
stated: the restriction changes no binder and no conclusion, it only scopes
the graph quantifier. -/
theorem groupAttach_iff_attach_at :
    GroupAttach ↔ ∀ (P : Params) (cg : Graph), GroupAttachAt P cg := by
  constructor
  · intro hall P cg
    intro run labels orderOptions hrun i hi first last hfirst hlast cursor loops
      hloop margin direction canvasH boxX boxY
    exact hall (P := P) (cg := cg) (run := run) (labels := labels)
      (orderOptions := orderOptions) hrun hi hfirst hlast cursor loops
      hloop margin direction canvasH boxX boxY
  · intro hall P cg run labels orderOptions hrun i hi first last hfirst hlast cursor
      loops hloop margin direction canvasH boxX boxY
    exact hall P cg hrun hi hfirst hlast cursor loops hloop margin
      direction canvasH boxX boxY

/-- The minimal true replacement for the false unrestricted `GroupAttach`:
the same fact restricted to graphs that arise as `componentCandidate` of a
measured graph.  Every `layoutFamily`/`layoutRecursive` consumer applies
`GroupAttach` only at `componentCandidate execution.graph comp candidate` for a
`SceneExecution`, whose `graph_eq` field makes exactly these premises
dischargeable (the line-count premise follows from `execution.lines_eq` via
`mapM_getElem?`/`List.length_zipIdx`, as in `CaptionWidthFacts`).  The
unrestricted form is refutable: on the hand-built graph with `-2` markers
`decl 0, clusterPath [0]` and `decl 0, clusterPath [0,0,0]`, `componentRun`
succeeds and the second marker's route endpoint misses its own frame boundary,
because the declaration-sharing membership premise of the member routing bound
(`hlow`) is violated — measured graphs give every `-2` node its own group
declaration and end its cluster path with it. -/
def GroupAttachMeasured : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ candidate : Nat, GroupAttachAt P (componentCandidate graph comp candidate)

/-- `GroupAttachMeasured` from the candidate-graph endpoint facts: the single
remaining obligation is `GroupTopEndpointFactsCandidate` itself (the member
routing bound over measured candidate graphs). -/
theorem groupAttachMeasured_of_candidate_facts
    (hfacts : GroupTopEndpointFactsCandidate) : GroupAttachMeasured := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate
  intro run labels orderOptions hrun i hi first last hfirst hlast cursor loops hloop
    margin direction canvasH boxX boxY
  exact componentRun_group_route_attachment_of_facts hrun hi hfirst hlast
    (fun hg => hfacts hgraph hlines hwf hfp hcomp hrun _ hg)
    (fun hg => hfacts hgraph hlines hwf hfp hcomp hrun _ hg)
    cursor loops hloop margin direction canvasH boxX boxY

end Elegant.Layered.PipelineImpl
