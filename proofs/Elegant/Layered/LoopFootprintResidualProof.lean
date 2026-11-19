import Elegant.Layered.LoopFootprintFactsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

 /-- Narrow residual, proved below, general over `orderOptions`: an in-range
    non-plain candidate node has border `-2` (group top) or `2` (group
    bottom). Side (`±1`), title-copy (`3`) and other borders are created later
    in the coordinate phases, never in a component candidate. The probe census
    over all executed runs and all six orderings shows only borders `0`,
    `-2`, `2`; zero other-border nodes. `loopFootprintOtherBorder_candidate`
    is the `candidateOrder` instance. -/
 def LoopFootprintOtherBorder (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v : Nat),
    comp ∈ components e.graph →
     componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border ≠ 0 →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 ∨
      ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 2

 /-- Narrow residual about `loopSizes`, proved below, general over
    `orderOptions` (the conclusion never mentions the run): an in-range
    `border = 2` (group bottom) candidate node owns no loop sizes. Bottom
    nodes are appended after the original nodes and no aliased raw edge maps
    to them. The probe census shows `0` loops on every bottom node of every
    executed run and ordering. `loopFootprintBottomEmpty_candidate` is the
    `candidateOrder` instance. -/
 def LoopFootprintBottomEmpty (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v : Nat),
    comp ∈ components e.graph →
     componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 2 →
    loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
      (componentCandidate e.graph comp candidate).slot = []

 /-- Narrow residual about `loopFootprint`, still open, general over
    `orderOptions`: the footprint of an in-range `border = -2` (group top) node
    separates from every plain box frame. A nonfixed group's self-loop attaches
    to its top node, so tops may own loops. The plain-pair core uses `border = 0`
    for the owner `v` in two places that fail for tops: the same-rank gap, which
    for a plain owner is discharged by `componentRun_original_plain_record` and
    the coordinate gap that reserves the owner's own loop extent (a top's extent
    is zeroed by `clearProxyExtents`, and the group frame's right edge is a
    per-rank maximum, so a marker-anchored gap does not cover the footprint's
    full width). The probe shows `sep = true` for every top-vs-plain pair on
    all executed runs and orderings, including looping tops, and no falsifying
    witness was found; the same-rank right-outsider case stays open.
    `loopFootprintTopSeparation_candidate` is the `candidateOrder` instance. -/
def LoopFootprintTopSeparation (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v b : Nat),
    comp ∈ components e.graph →
    ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0 →
     componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 →
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b

 /-- Narrow residual about `frameRect` at beyond-candidate indices, still open,
    general over `orderOptions`: when `b` lies past the candidate nodes but
    inside the proper nodes, `frameRect` takes the `nodeRect` branch (the `getD`
    default node has border `0 ≠ -2`) over the proper node at `b` — a title
    copy, border marker, or routing dummy. The probe evaluates every sliver
    pair in both directions, under every ordering, with zero failures.
    `loopFootprintBeyondProper_candidate` is the `candidateOrder` instance. -/
def LoopFootprintBeyondProper (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v b : Nat),
    comp ∈ components e.graph →
     componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    (componentCandidate e.graph comp candidate).nodes.length ≤ b →
    b < run.proper.nodes.length →
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`. -/
private theorem candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Endpoint projection of the pristine form of an edge. -/
private theorem edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Endpoint projection of the pristine form of an edge. -/
private theorem edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Every edge of a component candidate keeps both endpoints below the
candidate's node count. -/
private theorem candidate_edge_endpoints_bounded (g : Graph) (comp : List Nat) (index : Nat)
    (hcomp : comp ∈ components g)
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    {edge : Edge} (hedge : edge ∈ (componentCandidate g comp index).edges) :
    edge.tail < (componentCandidate g comp index).nodes.length ∧
      edge.head < (componentCandidate g comp index).nodes.length := by
  have hlen : (componentCandidate g comp index).nodes.length = comp.length :=
    candidate_nodes_length g comp index
  have hmem : edge.original ∈ (componentCandidate g comp index).edges.map Edge.original :=
    List.mem_map_of_mem hedge
  rw [componentCandidate_semantic_edges g comp index] at hmem
  obtain ⟨e₁, he₁, heq⟩ := List.mem_map.mp hmem
  have he₁mem : e₁ ∈ (componentGraph g comp).edges := he₁
  change e₁ ∈ ((g.edges.filter fun e => comp.contains e.tail).map fun e =>
    { e with tail := comp.idxOf e.tail, head := comp.idxOf e.head }) at he₁mem
  obtain ⟨e₀, he₀filter, he₁def⟩ := List.mem_map.mp he₁mem
  obtain ⟨he₀mem, he₀tail⟩ := List.mem_filter.mp he₀filter
  have he₀tailmem : e₀.tail ∈ comp := List.contains_iff_mem.mp he₀tail
  obtain ⟨comp', hcomp'mem, htail', hhead'⟩ :=
    components_edge_endpoints hbd (List.mem_append_left _ he₀mem)
  have hsame : comp = comp' :=
    components_shared_member_eq hcomp hcomp'mem he₀tailmem htail'
  have he₁tail : e₁.tail = comp.idxOf e₀.tail := congrArg Edge.tail he₁def.symm
  have he₁head : e₁.head = comp.idxOf e₀.head := congrArg Edge.head he₁def.symm
  have htailLt : comp.idxOf e₀.tail < comp.length := List.idxOf_lt_length_of_mem he₀tailmem
  have hheadLt : comp.idxOf e₀.head < comp.length :=
    List.idxOf_lt_length_of_mem (hsame ▸ hhead')
  have he₁tailLt : e₁.tail < comp.length := by rw [he₁tail]; exact htailLt
  have he₁headLt : e₁.head < comp.length := by rw [he₁head]; exact hheadLt
  have ht := congrArg Edge.tail heq
  have hh := congrArg Edge.head heq
  rw [edge_original_tail e₁, edge_original_tail edge] at ht
  rw [edge_original_head e₁, edge_original_head edge] at hh
  rw [hlen]
  cases h₁ : e₁.reversed <;> cases h₂ : edge.reversed <;>
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at ht hh <;>
    constructor <;> omega

/-- An executed component run has no exact ports. -/
private theorem exact_nil_of_run {P : Params} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (h : componentRun P cg labels orderOptions = .ok run) : run.exact = [] := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, _, h⟩ := bind_ok h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have hfin := Except.ok.inj h
  subst hfin
  rfl

/-- The loop extent of an empty size list is zero. -/
private theorem extent_empty (slot : Int) : Loops.extent slot [] = 0 := by
  simp [Loops.extent]

/-- Separation with an empty loop-size list: the footprint has zero width, so
it meets no frame interior. -/
private theorem sep_of_empty_loops {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {v b : Nat}
    (hempty : loopSizes cg.edges labels v cg.slot = [])
    (hexact : run.exact = []) :
    LoopFootprintSeparation cg run labels v b := by
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hext : (if run.exact.contains v then Loops.exactExtent else Loops.extent)
      cg.slot (loopSizes cg.edges labels v cg.slot) = 0 := by
    have h1 : (if run.exact.contains v then Loops.exactExtent else Loops.extent) =
        Loops.extent := by simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    rw [h1, hempty]
    exact extent_empty _
  unfold LoopFootprintSeparation loopFootprint
  rw [hext]
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- An out-of-range position owns no self-loops in an executed candidate. -/
private theorem loopEdges_empty_of_oob {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate v : Nat)
    (hcomp : comp ∈ components e.graph)
    (hv : ¬ v < (componentCandidate e.graph comp candidate).nodes.length) :
    loopEdges (componentCandidate e.graph comp candidate).edges v = [] := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨ed, hmem⟩ : ∃ ed, ed ∈ loopEdges (componentCandidate e.graph comp candidate).edges v := by
    cases h : loopEdges (componentCandidate e.graph comp candidate).edges v with
    | nil => exact absurd h hne
    | cons ed _ => exact ⟨ed, List.mem_cons.mpr (Or.inl rfl)⟩
  have hpair := List.mem_filter.mp (by simpa only [loopEdges] using hmem)
  obtain ⟨hedges, hflt⟩ := hpair
  have hflt' : (ed.tail == v && ed.head == v) = true := hflt
  rw [Bool.and_eq_true] at hflt'
  have hTailEq : ed.tail = v := beq_iff_eq.mp hflt'.1
  have hbd := sceneExecution_edges_bounded e
  have hbnd := candidate_edge_endpoints_bounded e.graph comp candidate hcomp hbd hedges
  omega

/-- An out-of-range position has an empty loop-size list. -/
private theorem loopSizes_empty_of_oob {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate v : Nat)
    (hcomp : comp ∈ components e.graph)
    (hv : ¬ v < (componentCandidate e.graph comp candidate).nodes.length) :
    loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
      (componentCandidate e.graph comp candidate).slot = [] := by
  have hempty := loopEdges_empty_of_oob e comp candidate v hcomp hv
  simp only [loopSizes, hempty, List.map_nil]

/-- The frame at an out-of-range proper index is degenerate: both `getD`
defaults apply, so the node rect has zero width and height. -/
private theorem frameRect_width_zero_of_oob {cg : Graph} {run : Run} {b : Nat}
    (hcg : cg.nodes.getD b default = default)
    (hproper : run.proper.nodes.getD b default = default) :
    (frameRect default cg run b).w = 0 := by
  have hcond : (default : Node).border != -2 := by decide
  have hframe : frameRect default cg run b = nodeRect cg run b := by
    unfold frameRect
    dsimp only
    rw [hcg]
    simp only [hcond, ↓reduceIte]
  rw [hframe]
  unfold nodeRect
  dsimp only
  rw [hproper]
  rfl

/-- Separation with a degenerate out-of-range frame. -/
private theorem sep_of_frame_oob {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {v b : Nat}
    (hw : (frameRect default cg run b).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A candidate node record is the executed-graph record at the mapped index. -/
private theorem candidate_node_lookup {g : Graph} {comp : List Nat} {candidate v : Nat}
    (hv : v < comp.length) {nodeV : Node}
    (hnodeV : (componentCandidate g comp candidate).nodes[v]? = some nodeV) :
    nodeV = g.nodes.getD (comp.getD v 0) default := by
  have hcc : (componentCandidate g comp candidate).nodes =
      comp.map fun key => g.nodes.getD key default := by
    rw [componentCandidate_nodes]
    unfold componentGraph
    rfl
  rw [hcc, List.getElem?_map] at hnodeV
  have h2 : comp[v]? = some (comp.getD v 0) := by
    have h3 := List.getElem?_eq_getElem hv
    have h4 : (comp[v]?).getD 0 = comp.getD v 0 := (List.getD_eq_getElem?_getD).symm
    rw [h3] at h4
    simp only [Option.getD_some] at h4
    rw [h3, h4]
  rw [h2, Option.map_some] at hnodeV
  exact (Option.some.inj hnodeV).symm

/-- Executed lines cover exactly the input boxes. -/
private theorem resid_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- The pre-prepare nodes of an executed measured graph cover exactly the
input boxes, and the graph is their `Compound.prepare` image. -/
private theorem measured_raw_graph {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    (hlines : lines.length = inp.boxes.length) :
    ∃ raw : Graph, raw.nodes.length = inp.boxes.length ∧
      g = Compound.prepare (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) P.clusterPad (lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * P.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height)) raw := by
  unfold measuredGraph at hg
  obtain ⟨nodes0, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have h0 : nodes0.length = lines.length := by
    have h := (mapM_getElem? _ _ _ hinitial).1
    simpa only [List.length_zipIdx] using h
  have h1 : nodes.length = nodes0.length := by
    have h := (mapM_getElem? _ _ _ hnodes).1
    simpa only [List.length_zipIdx, List.length_map] using h
  refine ⟨{ nodes := nodes, edges := edges, slot := P.slot }, ?_, ?_⟩
  · show nodes.length = inp.boxes.length
    omega
  · have hfin := Except.ok.inj hg
    exact hfin.symm

/-- A prepared node below the box count is a top (`-2`) or a plain (`0`)
record: fixed groups and plain boxes keep border `0`, nonfixed groups become
tops. Side (`±1`) and title-copy (`3`) markers only appear later in the
proper graph. -/
private theorem border_of_lt_boxes {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {boxes' : List ModelBox} {pad : Int} {titles : List (Int × Int)} {raw : Graph}
    (hraw : e.graph = Compound.prepare boxes' pad titles raw)
    (hrawlen : raw.nodes.length = inp.boxes.length)
    (hlines : e.lines.length = inp.boxes.length)
    {m : Nat} (hmlt : m < inp.boxes.length)
    (hmap : boxes'[m]? = some (inp.boxes[m]'hmlt))
    {nodeV : Node} (hgetm : e.graph.nodes.getD m default = nodeV) :
    nodeV.border = -2 ∨ nodeV.border = 0 := by
  have hbox : inp.boxes[m]? = some (inp.boxes[m]'hmlt) := List.getElem?_eq_getElem hmlt
  have hlen : m < e.graph.nodes.length := by
    have hle : raw.nodes.length ≤ e.graph.nodes.length := by
      rw [hraw]
      exact Compound.prepare_nodes_length_ge _ _ _ _
    omega
  have hsome : e.graph.nodes[m]? = some (e.graph.nodes[m]'hlen) :=
    List.getElem?_eq_getElem hlen
  have hgetm' : e.graph.nodes.getD m default = e.graph.nodes[m]'hlen := by
    simp only [List.getD_eq_getElem?_getD, hsome, Option.getD_some]
  have hnv : nodeV = e.graph.nodes[m]'hlen := by rw [← hgetm, hgetm']
  match hrole : (inp.boxes[m]'hmlt).role with
    | BoxRole.group =>
      have hmlen : m < raw.nodes.length := by rw [hrawlen]; exact hmlt
      have hrec2 := Compound.prepare_group_title_record boxes' pad titles raw hmlen hmap hrole
      rw [← hraw] at hrec2
      have h2 := Option.some.inj (hsome.symm.trans hrec2)
      left
      simp [hnv, h2]
    | BoxRole.node =>
      have hroleN : (inp.boxes[m]'hmlt).role = BoxRole.node := hrole
      have hmlines : m < e.lines.length := by rw [hlines]; exact hmlt
      have hnode : e.graph.nodes[m]? = some nodeV := by rw [hnv]; exact hsome
      have hb0 := measuredGraph_ordinary_node_border_zero e.graph_eq hmlines hbox hroleN hnode
      right
      exact hb0

/-- Local copy of the private `findIdx?_lt_length` bound. -/
private theorem resid_findIdx_lt_length {α : Type} {p : α → Bool} :
    ∀ (l : List α) (i : Nat), l.findIdx? p = some i → i < l.length := by
  intro l
  induction l with
  | nil =>
    intro i h
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons x xs ih =>
    intro i h
    rw [List.findIdx?_cons] at h
    split at h
    · simp at h
      subst h
      simp
    · cases hx : xs.findIdx? p with
      | none => rw [hx] at h; simp at h
      | some j =>
        rw [hx] at h
        simp at h
        have hbound := ih j hx
        have hlen : (x :: xs).length = xs.length + 1 := List.length_cons ..
        omega

/-- Local copy of the private raw-edge endpoint bound. -/
private theorem resid_edgeOf_tail_head_lt {inp : Input} {r : ModelRoute} {i : Nat} {e : Edge}
    (h : edgeOf inp r i = .ok e) :
    e.tail < inp.boxes.length ∧ e.head < inp.boxes.length := by
  unfold edgeOf at h
  cases h1 : inp.boxes.findIdx? (fun b => b.id == r.fromId) with
  | none => rw [h1] at h; simp at h
  | some a =>
    cases h2 : inp.boxes.findIdx? (fun b => b.id == r.toId) with
    | none => rw [h1, h2] at h; simp at h
    | some b =>
      rw [h1, h2] at h
      simp at h
      cases h
      exact ⟨resid_findIdx_lt_length inp.boxes a h1,
        resid_findIdx_lt_length inp.boxes b h2⟩

/-- Local copy of the private graph-edge bound. -/
private theorem resid_graphEdges_mem_bounds (inp : Input) :
    ∀ (rs : List ModelRoute) (k : Nat) (es : List Edge),
      graphEdgesFrom inp k rs = .ok es →
      ∀ e ∈ es, e.tail < inp.boxes.length ∧ e.head < inp.boxes.length := by
  intro rs
  induction rs with
  | nil =>
    intro k es h e he
    simp only [graphEdgesFrom] at h
    simp at h
    subst h
    simp at he
  | cons r rs ih =>
    intro k es h e he
    unfold graphEdgesFrom at h
    obtain ⟨edge, hedge, h⟩ := bind_ok h
    obtain ⟨edges, hedges, h⟩ := bind_ok h
    have hr := Except.ok.inj h
    subst hr
    rcases List.mem_cons.mp he with rfl | he'
    · exact resid_edgeOf_tail_head_lt hedge
    · exact ih (k + 1) edges hedges e he'

/-- Local copy of the private self-loop endpoint identity. -/
private theorem resid_compound_endpoint_self (boxes : List ModelBox) (source : Bool) (v : Nat) :
    Compound.endpoint boxes source v v = v := by
  cases hb : boxes[v]? <;> simp [Compound.endpoint, hb]

/-- Local copy of the private `bottomIndex` strict monotonicity. -/
private theorem resid_selfBottomIndex_lt {boxes : List ModelBox} {i j : Nat} (hij : i < j)
    (_hi : i < boxes.length) {bi : ModelBox} (hbi : boxes[i]? = some bi)
    (hg : bi.role == .group) :
    Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
  unfold Compound.bottomIndex
  have h1 : (boxes.take j).take i ++ (boxes.take j).drop i = boxes.take j :=
    List.take_append_drop i (boxes.take j)
  have h2 : (boxes.take j).take i = boxes.take i := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have h3 := congrArg (List.filter (fun box : ModelBox => box.role == .group)) h1
  rw [List.filter_append, h2] at h3
  have hmem : bi ∈ (boxes.take j).drop i := by
    have h0 : ((boxes.take j).drop i)[0]? = some bi := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_take, ite_eq_left hij, hbi]
    exact List.mem_of_getElem? h0
  have hfilter : 0 < (((boxes.take j).drop i).filter
      (fun box : ModelBox => box.role == .group)).length := by
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hmem, hg⟩
  rw [h3.symm, List.length_append]
  omega

set_option maxHeartbeats 1000000 in
/-- Local copy of the private bottom-alias impossibility. -/
private theorem resid_selfBottom_ne {boxes : List ModelBox} {a b k : Nat}
    (ha : a < boxes.length) (hb : b < boxes.length) (hab : a ≠ b)
    (ea : Compound.endpoint boxes true a b = k)
    (eb : Compound.endpoint boxes false b a = k)
    (hk : ¬ k < boxes.length) : False := by
  cases hma : boxes[a]? with
  | none =>
    simp only [Compound.endpoint, hma] at ea
    exact hk (by rw [← ea]; exact ha)
  | some ba =>
    cases hmb : boxes[b]? with
    | none =>
      simp only [Compound.endpoint, hma, hmb] at ea eb
      exact hk (by rw [← eb]; exact hb)
    | some bb =>
      simp only [Compound.endpoint, hma, hmb] at ea eb
      split at ea
      · exact hk (by rw [← ea]; exact ha)
      · split at ea
        · exact hk (by rw [← ea]; exact ha)
        · rename_i hc1 hc2
          split at eb
          · exact hk (by rw [← eb]; exact hb)
          · split at eb
            · exact hk (by rw [← eb]; exact hb)
            · rename_i hc3 _
              have hgrpA : (ba.role == .group) = true := by
                have hf := Bool.eq_false_iff.mpr hc1
                have hp := (Bool.or_eq_false_iff.mp hf).1
                simpa using hp.symm
              have hgrpB : (bb.role == .group) = true := by
                have hf := Bool.eq_false_iff.mpr hc3
                have hp := (Bool.or_eq_false_iff.mp hf).1
                simpa using hp.symm
              rcases Nat.lt_or_ge a b with hcmp | hcmp
              · have hbound := resid_selfBottomIndex_lt hcmp ha hma hgrpA
                rw [ea, eb] at hbound
                exact absurd hbound (Nat.lt_irrefl k)
              · have hblt : b < a := by omega
                have hbound := resid_selfBottomIndex_lt hblt hb hmb hgrpB
                rw [eb, ea] at hbound
                exact absurd hbound (Nat.lt_irrefl k)

/-- Local copy of the private bottom-loop emptiness: a bottom index owns no
self-loops in an executed component candidate. -/
private theorem resid_bottomLoopEmpty {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (v : Nat)
    (hcomp : comp ∈ components e.graph) (hv : v < comp.length)
    (hge : inp.boxes.length ≤ comp.getD v 0) :
    loopEdges (componentCandidate e.graph comp candidate).edges v = [] := by
  apply Classical.byContradiction
  intro hne
  have hn := components_nodup e.graph comp hcomp
  have hpres := componentCandidate_loopSizes_preserved e.graph comp hn candidate v hv
    e.measured (componentCandidate e.graph comp candidate).slot
  have hSizesNe : loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot ≠ [] := by
    intro he
    have hempty : loopEdges (componentCandidate e.graph comp candidate).edges v = [] :=
      List.map_eq_nil_iff.mp he
    exact hne hempty
  have hsEq : comp.getD v 0 = comp[v]'hv := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
  have hLoopGNe : loopEdges e.graph.edges (comp[v]'hv) ≠ [] := by
    intro he
    have hSizesG : loopSizes e.graph.edges e.measured (comp[v]'hv) e.graph.slot = [] := by
      simp only [loopSizes, he, List.map_nil]
    have hEq : loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot =
        loopSizes e.graph.edges e.measured (comp[v]'hv) e.graph.slot := by
      rw [hpres]
      have hcslot : (componentCandidate e.graph comp candidate).slot = e.graph.slot := by
        unfold componentCandidate
        dsimp only
        split
        · split <;> rfl
        · unfold cycleGraph
          split <;> rfl
      rw [hcslot]
    rw [hEq] at hSizesNe
    rw [hSizesG] at hSizesNe
    exact hSizesNe rfl
  obtain ⟨metric, labels, raw, hm, hl, heRaw, _hslot, hprepare, _hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare e.graph_eq
  have hemetric : metric = e.metric := Except.ok.inj (hm.symm.trans e.metric_eq)
  subst hemetric
  have helabels : labels = e.measured := Except.ok.inj (hl.symm.trans e.measured_eq)
  subst helabels
  have hGraphEdges : graphEdges inp = .ok raw.edges := heRaw
  have hRawBounds := resid_graphEdges_mem_bounds inp inp.routes 0 raw.edges
    (by simpa only [graphEdges] using hGraphEdges)
  have hMappedLen : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box).length = inp.boxes.length := by simp
  have hLoopGNe2 : loopEdges e.graph.edges (comp[v]'hv) ≠ [] := hLoopGNe
  have hExists : ∃ eprime ∈ e.graph.edges,
      (eprime.tail == (comp[v]'hv) && eprime.head == (comp[v]'hv)) = true := by
    have hne2 : (e.graph.edges.filter fun e =>
        e.tail == (comp[v]'hv) && e.head == (comp[v]'hv)) ≠ [] := hLoopGNe2
    cases hfilter : (e.graph.edges.filter fun e =>
        e.tail == (comp[v]'hv) && e.head == (comp[v]'hv)) with
    | nil => exact absurd hfilter hne2
    | cons eprime _ =>
      have hmem : eprime ∈ (e.graph.edges.filter fun e =>
          e.tail == (comp[v]'hv) && e.head == (comp[v]'hv)) := by
        rw [hfilter]
        simp
      exact ⟨eprime, (List.mem_filter.mp hmem).1, (List.mem_filter.mp hmem).2⟩
  obtain ⟨eprime, hmem, hfilter⟩ := hExists
  have hAnd : (eprime.tail == (comp[v]'hv) && eprime.head == (comp[v]'hv)) = true :=
    hfilter
  simp only [Bool.and_eq_true] at hAnd
  obtain ⟨hTailBeq, hHeadBeq⟩ := hAnd
  have hTailEq : eprime.tail = (comp[v]'hv) := beq_iff_eq.mp hTailBeq
  have hHeadEq : eprime.head = (comp[v]'hv) := beq_iff_eq.mp hHeadBeq
  have hInRaw : ∃ e ∈ raw.edges, Compound.aliasEdge
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) e = eprime := by
    rw [hprepare] at hmem
    dsimp only [Compound.prepare] at hmem
    exact List.mem_map.mp hmem
  obtain ⟨e, hmemRaw, hAlias⟩ := hInRaw
  have hBounds := hRawBounds e hmemRaw
  have hTailLt : e.tail < inp.boxes.length := hBounds.1
  have hHeadLt : e.head < inp.boxes.length := hBounds.2
  have hTailLtM : e.tail <
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box).length := by omega
  have hHeadLtM : e.head <
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box).length := by omega
  have hGeM : ¬ (comp[v]'hv) <
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box).length := by
    have hge2 : inp.boxes.length ≤ (comp[v]'hv) := by
      rw [← hsEq]
      exact hge
    omega
  by_cases hEqTailHead : e.tail = e.head
  · have hSelfTail : Compound.endpoint
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box) true e.tail e.head = e.tail := by
      rw [← hEqTailHead]
      exact resid_compound_endpoint_self _ true e.tail
    have hSelfHead : Compound.endpoint
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box) false e.head e.tail = e.head := by
      rw [hEqTailHead]
      exact resid_compound_endpoint_self _ false e.head
    have hTailAlias : eprime.tail = e.tail := by
      have h1 : eprime.tail = Compound.endpoint
          (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
            else box) true e.tail e.head := by
        rw [← hAlias]
        rfl
      rw [h1, hSelfTail]
    have hHeadAlias : eprime.head = e.head := by
      have h1 : eprime.head = Compound.endpoint
          (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
            else box) false e.head e.tail := by
        rw [← hAlias]
        rfl
      rw [h1, hSelfHead]
    rw [hTailAlias] at hTailEq
    rw [hHeadAlias] at hHeadEq
    have hgeComp : inp.boxes.length ≤ (comp[v]'hv) := by
      rw [hsEq] at hge
      exact hge
    omega
  · have hNe : e.tail ≠ e.head := hEqTailHead
    have hEpTail : Compound.endpoint
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box) true e.tail e.head = (comp[v]'hv) := by
      have h1 : eprime.tail = Compound.endpoint
          (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
            else box) true e.tail e.head := by
        rw [← hAlias]
        rfl
      rw [← h1, hTailEq]
    have hEpHead : Compound.endpoint
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box) false e.head e.tail = (comp[v]'hv) := by
      have h1 : eprime.head = Compound.endpoint
          (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
            else box) false e.head e.tail := by
        rw [← hAlias]
        rfl
      rw [← h1, hHeadEq]
    exact resid_selfBottom_ne hTailLtM hHeadLtM hNe hEpTail hEpHead hGeM

/-- The other-border residual holds unconditionally: candidate borders are
`0`, `-2`, or `2`. -/
 theorem LoopFootprintOtherBorder_holds {inp : Input} {o : Options} {res : FamilyResult} :
    LoopFootprintOtherBorder inp o res := by
  intro e comp candidate run orderOptions v _hcomp _hrun hvlen hne0
  have hv : v < comp.length := by
    rw [← candidate_nodes_length e.graph comp candidate]
    exact hvlen
  obtain ⟨nodeV, hnodeV⟩ : ∃ n, (componentCandidate e.graph comp candidate).nodes[v]? = some n :=
    ⟨_, List.getElem?_eq_getElem hvlen⟩
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default = nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  rw [hgetV] at hne0 ⊢
  have hrec := candidate_node_lookup hv hnodeV
  have hlines : e.lines.length = inp.boxes.length := resid_lines_len e
  obtain ⟨raw, hrawlen, hraw⟩ := measured_raw_graph e.graph_eq hlines
  have hgetm : e.graph.nodes.getD (comp.getD v 0) default = nodeV := hrec.symm
  rcases Nat.lt_or_ge (comp.getD v 0) inp.boxes.length with hmlt | hmge
  · by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) = true
    · obtain ⟨entry, hfind⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) = some entry := by
        cases hf : inp.fixedSizes.find?
            (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) with
        | none =>
          obtain ⟨entry, hmemF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf entry hmemF) (by rw [hid]; decide)
        | some entry => exact ⟨entry, rfl⟩
      have hbox : inp.boxes[comp.getD v 0]? = some (inp.boxes[comp.getD v 0]'hmlt) :=
        List.getElem?_eq_getElem hmlt
      have hmlines : comp.getD v 0 < e.lines.length := by rw [hlines]; exact hmlt
      have hls : e.lines[comp.getD v 0]? = some (e.lines[comp.getD v 0]'hmlines) :=
        List.getElem?_eq_getElem hmlines
      obtain ⟨node, hnode, _, hborder0, _, _⟩ :=
        measuredGraph_fixed_node_dims e.graph_eq hls hbox hfind
      have hcomp : comp.getD v 0 = comp[v]'hv := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
      rw [hcomp] at hnode
      have hgetnode : e.graph.nodes.getD (comp.getD v 0) default = node := by
        rw [hcomp]
        simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
      have hnn : nodeV = node := hgetm.symm.trans hgetnode
      rw [hnn] at hne0
      exact absurd hborder0 hne0
    · have hfixedF : inp.fixedSizes.any
          (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hbox : inp.boxes[comp.getD v 0]? = some (inp.boxes[comp.getD v 0]'hmlt) :=
        List.getElem?_eq_getElem hmlt
      have hmap : (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)[comp.getD v 0]? = some (inp.boxes[comp.getD v 0]'hmlt) := by
        simp only [List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      rcases border_of_lt_boxes e hraw hrawlen hlines hmlt hmap hgetm with htop | hplain
      · exact Or.inl htop
      · exact absurd hplain hne0
  · have hj : raw.nodes.length ≤ comp.getD v 0 := by omega
    have hlen : comp.getD v 0 < e.graph.nodes.length := by
      apply Classical.byContradiction
      intro hcon
      have hnone : e.graph.nodes[comp.getD v 0]? = none :=
        List.getElem?_eq_none (by omega)
      have hgetd : e.graph.nodes.getD (comp.getD v 0) default = default := by
        rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
      have hdef : default = nodeV := hgetd.symm.trans hgetm
      have h0 : (default : Node).border = 0 := rfl
      rw [← hdef] at hne0
      exact hne0 h0
    have hsome : e.graph.nodes[comp.getD v 0]? = some nodeV := by
      have h1 : e.graph.nodes[comp.getD v 0]? = some (e.graph.nodes[comp.getD v 0]'hlen) :=
        List.getElem?_eq_getElem hlen
      have hgetd : e.graph.nodes.getD (comp.getD v 0) default =
          e.graph.nodes[comp.getD v 0]'hlen := by
        rw [List.getD_eq_getElem?_getD, h1, Option.getD_some]
      have hnv : nodeV = e.graph.nodes[comp.getD v 0]'hlen := by
        rw [← hgetm, hgetd]
      rw [hnv]
      exact h1
    have hlook : (Compound.prepare (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) e.params.clusterPad (e.lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * e.params.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height)) raw).nodes[comp.getD v 0]? = some nodeV := by
      rw [← hraw]
      exact hsome
    have hbot := Compound.prepare_bottom_of_index _ _ _ raw _ hj hlook
    exact Or.inr hbot.1

/-- The bottom-empty residual holds unconditionally: border-`2` indices sit
past the box count, hence own no loops. -/
 theorem LoopFootprintBottomEmpty_holds {inp : Input} {o : Options} {res : FamilyResult} :
    LoopFootprintBottomEmpty inp o res := by
  intro e comp candidate run orderOptions v hcomp _hrun hvlen hborder
  have hv : v < comp.length := by
    rw [← candidate_nodes_length e.graph comp candidate]
    exact hvlen
  obtain ⟨nodeV, hnodeV⟩ : ∃ n, (componentCandidate e.graph comp candidate).nodes[v]? = some n :=
    ⟨_, List.getElem?_eq_getElem hvlen⟩
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default = nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  rw [hgetV] at hborder
  have hrec := candidate_node_lookup hv hnodeV
  have hlines : e.lines.length = inp.boxes.length := resid_lines_len e
  obtain ⟨raw, hrawlen, hraw⟩ := measured_raw_graph e.graph_eq hlines
  have hgetm : e.graph.nodes.getD (comp.getD v 0) default = nodeV := hrec.symm
  have hge : inp.boxes.length ≤ comp.getD v 0 := by
    apply Classical.byContradiction
    intro hcon
    have hmlt : comp.getD v 0 < inp.boxes.length := by omega
    by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) = true
    · obtain ⟨entry, hfind⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) = some entry := by
        cases hf : inp.fixedSizes.find?
            (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) with
        | none =>
          obtain ⟨entry, hmemF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf entry hmemF) (by rw [hid]; decide)
        | some entry => exact ⟨entry, rfl⟩
      have hbox : inp.boxes[comp.getD v 0]? = some (inp.boxes[comp.getD v 0]'hmlt) :=
        List.getElem?_eq_getElem hmlt
      have hmlines : comp.getD v 0 < e.lines.length := by rw [hlines]; exact hmlt
      have hls : e.lines[comp.getD v 0]? = some (e.lines[comp.getD v 0]'hmlines) :=
        List.getElem?_eq_getElem hmlines
      obtain ⟨node, hnode, _, hborder0, _, _⟩ :=
        measuredGraph_fixed_node_dims e.graph_eq hls hbox hfind
      have hcomp : comp.getD v 0 = comp[v]'hv := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
      rw [hcomp] at hnode
      have hgetnode : e.graph.nodes.getD (comp.getD v 0) default = node := by
        rw [hcomp]
        simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
      have hnn : nodeV = node := hgetm.symm.trans hgetnode
      rw [hnn] at hborder
      omega
    · have hfixedF : inp.fixedSizes.any
          (fun fixed => fixed.1 == (inp.boxes[comp.getD v 0]'hmlt).id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hbox : inp.boxes[comp.getD v 0]? = some (inp.boxes[comp.getD v 0]'hmlt) :=
        List.getElem?_eq_getElem hmlt
      have hmap : (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)[comp.getD v 0]? = some (inp.boxes[comp.getD v 0]'hmlt) := by
        simp only [List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      rcases border_of_lt_boxes e hraw hrawlen hlines hmlt hmap hgetm with htop | hplain
      · omega
      · omega
  have hempty := resid_bottomLoopEmpty e comp candidate v hcomp hv hge
  simp only [loopSizes, hempty, List.map_nil]

 /-- Candidate instance of the general other-border residual. -/
 theorem loopFootprintOtherBorder_candidate {inp : Input} {o : Options} {res : FamilyResult}
    (h : LoopFootprintOtherBorder inp o res) :
    ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (v : Nat),
      comp ∈ components e.graph →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      v < (componentCandidate e.graph comp candidate).nodes.length →
      ((componentCandidate e.graph comp candidate).nodes.getD v default).border ≠ 0 →
      ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 ∨
        ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 2 :=
   fun e comp candidate run v hcomp hrun hvlen hne0 =>
    h e comp candidate run (candidateOrder candidate) v hcomp hrun hvlen hne0

 /-- Candidate instance of the general bottom-empty residual. -/
 theorem loopFootprintBottomEmpty_candidate {inp : Input} {o : Options} {res : FamilyResult}
    (h : LoopFootprintBottomEmpty inp o res) :
    ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (v : Nat),
      comp ∈ components e.graph →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      v < (componentCandidate e.graph comp candidate).nodes.length →
      ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 2 →
      loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot = [] :=
   fun e comp candidate run v hcomp hrun hvlen hbord =>
    h e comp candidate run (candidateOrder candidate) v hcomp hrun hvlen hbord

 /-- Candidate instance of the general top-separation residual. -/
 theorem loopFootprintTopSeparation_candidate {inp : Input} {o : Options} {res : FamilyResult}
    (h : LoopFootprintTopSeparation inp o res) :
    ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (v b : Nat),
      comp ∈ components e.graph →
      ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      v < (componentCandidate e.graph comp candidate).nodes.length →
      ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 →
      LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
        e.measured v b :=
   fun e comp candidate run v b hcomp hbord hrun hvlen htop =>
    h e comp candidate run (candidateOrder candidate) v b hcomp hbord hrun hvlen htop

 /-- Candidate instance of the general beyond-proper residual. -/
 theorem loopFootprintBeyondProper_candidate {inp : Input} {o : Options} {res : FamilyResult}
    (h : LoopFootprintBeyondProper inp o res) :
    ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (v b : Nat),
      comp ∈ components e.graph →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      v < (componentCandidate e.graph comp candidate).nodes.length →
      (componentCandidate e.graph comp candidate).nodes.length ≤ b →
      b < run.proper.nodes.length →
      LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
        e.measured v b :=
   fun e comp candidate run v b hcomp hrun hvlen hle hlt =>
    h e comp candidate run (candidateOrder candidate) v b hcomp hrun hvlen hle hlt
/-- The broad residual follows from the two proved narrow results plus the two
remaining hypotheses. Out-of-range `v` has no loops, hence a zero-width
footprint; out-of-range `b` past the proper nodes has a degenerate frame,
while the sliver inside the proper nodes is the `LoopFootprintBeyondProper`
residual; an in-range non-plain `v` is a top, a bottom, or excluded by
`LoopFootprintOtherBorder`. -/
theorem loopFootprintSeparationResidual {inp : Input} {o : Options}
    {res : FamilyResult}
    (htop : LoopFootprintTopSeparation inp o res)
    (hbeyond : LoopFootprintBeyondProper inp o res) :
    LoopFootprintSeparationResidual inp o res := by
  intro e comp candidate run v b hcomp hbord hrun hdisj
  rcases hdisj with hne0 | hvnlen | hbnlen
  · by_cases hvlen : v < (componentCandidate e.graph comp candidate).nodes.length
    · rcases LoopFootprintOtherBorder_holds e comp candidate run (candidateOrder candidate) v hcomp hrun hvlen hne0 with htop2 | hbot2
      · exact htop e comp candidate run (candidateOrder candidate) v b hcomp hbord hrun hvlen htop2
      · have hempty := LoopFootprintBottomEmpty_holds e comp candidate run (candidateOrder candidate) v hcomp hrun hvlen hbot2
        exact sep_of_empty_loops hempty (exact_nil_of_run hrun)
    · exact sep_of_empty_loops (loopSizes_empty_of_oob e comp candidate v hcomp hvlen)
        (exact_nil_of_run hrun)
  · exact sep_of_empty_loops (loopSizes_empty_of_oob e comp candidate v hcomp hvnlen)
      (exact_nil_of_run hrun)
  · by_cases hvlen : v < (componentCandidate e.graph comp candidate).nodes.length
    · by_cases hbproper : b < run.proper.nodes.length
      · exact hbeyond e comp candidate run (candidateOrder candidate) v b hcomp hrun hvlen
          (Nat.le_of_not_lt hbnlen) hbproper
      · have hnone : (componentCandidate e.graph comp candidate).nodes[b]? = none :=
          List.getElem?_eq_none (by omega)
        have hcg : (componentCandidate e.graph comp candidate).nodes.getD b default =
            default := by
          rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
        have hnoneP : run.proper.nodes[b]? = none :=
          List.getElem?_eq_none (by omega)
        have hproper : run.proper.nodes.getD b default = default := by
          rw [List.getD_eq_getElem?_getD, hnoneP, Option.getD_none]
        exact sep_of_frame_oob (frameRect_width_zero_of_oob hcg hproper)
    · exact sep_of_empty_loops (loopSizes_empty_of_oob e comp candidate v hcomp hvlen)
        (exact_nil_of_run hrun)

/-- Executed loop footprint separation for plain boxes, modulo only the two
remaining narrow residuals. -/
theorem loopFootprintSeparation_executed' {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run)
    (v b : Nat)
    (hcomp : comp ∈ components e.graph)
    (hbord : ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      (candidateOrder candidate) = .ok run)
    (htop : LoopFootprintTopSeparation inp o res)
    (hbeyond : LoopFootprintBeyondProper inp o res) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b :=
  loopFootprintSeparation_executed e comp candidate run v b hcomp hbord hrun
    (loopFootprintSeparationResidual htop hbeyond)

end PipelineImpl
end Layered
end Elegant
