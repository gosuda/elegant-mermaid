import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.GroupFrameSizingFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # General-order loop footprint facts

Order-dependence audit for the loop chain (see `RunLocalSeparationsProof.lean:966`
`RunLocalLoopFootprint`, which quantifies over an arbitrary `orderOptions`).

Places that mention the order, and why none of them needs `candidateOrder`:

* `loopReservation_executed` (`LoopFootprintFactsProof.lean:547`) and
  `loopFootprintSeparation_executed` (`:1256`) take
  `hrun : componentRun … (candidateOrder candidate) = .ok run`, but feed `hrun`
  only to order-general helpers: `componentRun_spec`,
  `componentRun_original_nodes_covered`, `componentRun_dims_nonneg`,
  `componentRun_original_plain_record`, `componentRun_nonproxy_record`,
  `componentRun_prepared_titled_source`, `componentRun_original_frame_minimum_dims`,
  `componentRun_group_frame_height_ge` (all quantify over an implicit
  `orderOptions`), plus the order-free `executed_candidate_slot_pos` (which
  takes no `hrun` at all) and order-free graph facts.
* `frame_h_nonneg` (private, `:491`) pins `candidateOrder` in `hrun` but uses
  only the three general helpers above; the general form below replays it.
* `separation_plain_pair` (private, `:966`) pins `candidateOrder` in `hrun`
  but uses only the general helpers above (plus `graph_node_loopExtent_eq`
  and `bottomLoopEmpty_holds`, which take no `hrun`); the general form below
  replays it.
* The three `SceneExecution.*_candidate_frame_loop_reservation` methods
  (`ExecutedLoopPortsFacts.lean`) pin `candidateOrder` in `hrun`, but each
  body feeds `hrun` only to a general helper (`componentRun_original_frame_minimum_dims`
  or `componentRun_group_frame_height_ge`); the general analogues below replay them.
* The narrow residuals `LoopFootprintOtherBorder`, `LoopFootprintBottomEmpty`,
  `LoopFootprintTopSeparation`, `LoopFootprintBeyondProper`
  (`LoopFootprintResidualProof.lean`) already bind an explicit `orderOptions`
  (the first two are proved unconditionally; the last two stay hypotheses).
  Only `LoopFootprintSeparationResidual` (`LoopFootprintFactsProof.lean:922`)
  pins `candidateOrder`; its proof applies the already-general inputs at the
  candidate order, so the general form below replays it with `orderOptions`.
* The actual pipeline (`Pipeline.lean:905` `componentTrial`) only ever runs
  `componentRun P cg labels (candidateOrder index)`, and the FlatC6 assembly
  consumers (`FlatC6Assembly.lean`, `ExpandChildFrameLiftProof.lean:69-89`)
  pin `candidateOrder` — already discharged by the existing candidate-order
  facts. The label seam (`RunLocalLoopFootprint`) quantifies generally and its
  consumer `runLocalLoopSeparation` passes `orderOptions` through, so the seam
  needs the general forms proved here — no seam restriction is required.

This file therefore redoes exactly the order-mentioning steps with a general
`(orderOptions : OrderOptions)` binder. Everything else is an order-free copy
of a private helper that cannot be imported.
-/

/-- General-order alias of `LoopFootprintTopSeparation`: the tracked def already
binds `orderOptions`, so this is the same statement under the name the seam
proof takes its hypothesis at. -/
abbrev LoopFootprintTopSeparationG (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  LoopFootprintTopSeparation inp o res

/-- General-order alias of `LoopFootprintBeyondProper`: the tracked def already
binds `orderOptions`, so this is the same statement under the name the seam
proof takes its hypothesis at. -/
abbrev LoopFootprintBeyondProperG (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  LoopFootprintBeyondProper inp o res

private theorem bind_ok_general {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => simp [hx, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Except.bind] using h⟩

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`. -/
private theorem candidate_nodes_length_general (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Endpoint projection of the pristine form of an edge. -/
private theorem edge_original_tail_general (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Endpoint projection of the pristine form of an edge. -/
private theorem edge_original_head_general (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Every edge of a component candidate keeps both endpoints below the
candidate's node count. Order-free copy of the private helper in
`LoopFootprintFactsProof.lean`; public so the seam proof can bound the loop
owner. -/
theorem candidate_edge_endpoints_bounded_general (g : Graph) (comp : List Nat)
    (index : Nat)
    (hcomp : comp ∈ components g)
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    {edge : Edge} (hedge : edge ∈ (componentCandidate g comp index).edges) :
    edge.tail < (componentCandidate g comp index).nodes.length ∧
      edge.head < (componentCandidate g comp index).nodes.length := by
  have hlen : (componentCandidate g comp index).nodes.length = comp.length :=
    candidate_nodes_length_general g comp index
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
  rw [edge_original_tail_general e₁, edge_original_tail_general edge] at ht
  rw [edge_original_head_general e₁, edge_original_head_general edge] at hh
  rw [hlen]
  cases h₁ : e₁.reversed <;> cases h₂ : edge.reversed <;>
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at ht hh <;>
    constructor <;> omega

private theorem foldl_add_zero_general (a : Int) :
    ∀ l : List Int, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  intro l
  induction l generalizing a with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (a + x), ih x]
    omega
private theorem loop_width_sum_ge_general (slot : Int) (hs : 0 ≤ slot)
    (labels : List LoopLabel) (hw : ∀ l ∈ labels, 0 ≤ l.width) (start : Nat) :
    2 * slot * (labels.length : Int) ≤
      ((labels.zipIdx start).map
        (fun q => slot * ((q.2 : Int) + 2) + q.1.width)).foldl (· + ·) 0 := by
  induction labels generalizing start with
  | nil => simp [List.map_nil, List.foldl_nil]
  | cons l ls ih =>
    have hls := ih (fun a ha => hw a (by simp [ha]))
    have hl := hw l (by simp)
    have hstart : 0 ≤ (start : Int) := by omega
    have hterm : 2 * slot ≤ slot * ((start : Int) + 2) + l.width := by
      have hmul := Int.mul_nonneg hs hstart
      rw [Int.mul_add]
      omega
    rw [Int.mul_add] at hterm
    rw [List.zipIdx_cons, List.map_cons, List.foldl_cons, Int.zero_add]
    simp only [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one,
      List.length_cons]
    rw [foldl_add_zero_general]
    have htail := hls (start + 1)
    simp only [Int.mul_add] at htail
    omega
private theorem extent_ge_two_mul_general (slot : Int) (hs : 0 ≤ slot)
    (labels : List LoopLabel) (hw : ∀ l ∈ labels, 0 ≤ l.width) :
    2 * slot * (labels.length : Int) ≤ Loops.extent slot labels := by
  have heq : Loops.extent slot labels =
      ((labels.zipIdx 0).map
        (fun q => slot * ((q.2 : Int) + 2) + q.1.width)).foldl (· + ·) 0 := rfl
  rw [heq]
  exact loop_width_sum_ge_general slot hs labels hw 0

private theorem band_ge_two_slot_general (slot : Int) (sizes : List LoopLabel) :
    2 * slot ≤ Loops.band slot sizes := by
  have key : ∀ (l : List LoopLabel) (init : Int),
      init ≤ l.foldl (fun h l => max h l.height) init := by
    intro l
    induction l with
    | nil => intro init; exact Int.le_refl init
    | cons a rest ih =>
      intro init
      rw [List.foldl_cons]
      exact Int.le_trans (Int.le_max_left init a.height) (ih (max init a.height))
  exact key sizes (2 * slot)

private theorem extent_nonneg_of_slot_nonneg_general {slot : Int} (hs : 0 ≤ slot)
    (sizes : List LoopLabel) (hw : ∀ l ∈ sizes, 0 ≤ l.width) :
    0 ≤ Loops.extent slot sizes := by
  have h1 := extent_ge_two_mul_general slot hs sizes hw
  have h2 : 0 ≤ 2 * slot * (sizes.length : Int) :=
    Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
  omega

private theorem loopSizes_width_nonneg_general {cg : Graph} {labels : List MeasuredLabel}
    {v : Nat} {slot : Int} {label : LoopLabel}
    (hm : label ∈ loopSizes cg.edges labels v slot) :
    0 ≤ label.width := by
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hm
  rw [stackSize_width_eq]
  exact Labels.stackWidth_nonneg _

private theorem findIdx_lt_length_general {α : Type} {p : α → Bool} :
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

private theorem edgeOf_tail_head_lt_general {inp : Input} {r : ModelRoute} {i : Nat}
    {e : Edge} (h : edgeOf inp r i = .ok e) :
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
      exact ⟨findIdx_lt_length_general inp.boxes a h1,
        findIdx_lt_length_general inp.boxes b h2⟩

private theorem graphEdges_mem_bounds_general (inp : Input) :
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
    obtain ⟨edge, hedge, h⟩ := bind_ok_general h
    obtain ⟨edges, hedges, h⟩ := bind_ok_general h
    have hr := Except.ok.inj h
    subst hr
    rcases List.mem_cons.mp he with rfl | he'
    · exact edgeOf_tail_head_lt_general hedge
    · exact ih (k + 1) edges hedges e he'

private theorem compound_endpoint_self_general (boxes : List ModelBox)
    (source : Bool) (v : Nat) :
    Compound.endpoint boxes source v v = v := by
  cases hb : boxes[v]? <;> simp [Compound.endpoint, hb]

/-- `bottomIndex` is strictly increasing past a group box. -/
private theorem selfBottomIndex_lt_general {boxes : List ModelBox} {i j : Nat}
    (hij : i < j) (_hi : i < boxes.length) {bi : ModelBox} (hbi : boxes[i]? = some bi)
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
private theorem selfBottom_ne_general {boxes : List ModelBox} {a b k : Nat}
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
              · have hbound := selfBottomIndex_lt_general hcmp ha hma hgrpA
                rw [ea, eb] at hbound
                exact absurd hbound (Nat.lt_irrefl k)
              · have hblt : b < a := by omega
                have hbound := selfBottomIndex_lt_general hblt hb hmb hgrpB
                rw [eb, ea] at hbound
                exact absurd hbound (Nat.lt_irrefl k)

private theorem bottomLoopEmpty_general {inp : Input} {o : Options}
    {res : FamilyResult}
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
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
      Option.getD_some]
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
  have hRawBounds := graphEdges_mem_bounds_general inp inp.routes 0 raw.edges
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
      exact compound_endpoint_self_general _ true e.tail
    have hSelfHead : Compound.endpoint
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box) false e.head e.tail = e.head := by
      rw [hEqTailHead]
      exact compound_endpoint_self_general _ false e.head
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
    exact selfBottom_ne_general hTailLtM hHeadLtM hNe hEpTail hEpHead hGeM

/-- Frame height is nonnegative for every index of an executed run, at any
order options. General form of the private `frame_h_nonneg`: the proof feeds
`hrun` only to the general `componentRun_dims_nonneg`,
`componentRun_original_nodes_covered`, and `frameRect_dims_nonneg`. -/
private theorem frame_h_nonneg_general {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions)
    (_hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run) (v : Nat) :
    0 ≤ (frameRect default (componentCandidate e.graph comp candidate) run v).h := by
  have hdim := componentRun_dims_nonneg hrun
  have hcov := componentRun_original_nodes_covered hrun
  by_cases hv : v < run.proper.nodes.length
  · have hpair := frameRect_dims_nonneg default
      (componentCandidate e.graph comp candidate) run v hdim hv
    exact hpair.2
  · have hcglen : (componentCandidate e.graph comp candidate).nodes.length = comp.length :=
      candidate_nodes_length_general e.graph comp candidate
    have hle : (componentCandidate e.graph comp candidate).nodes.length ≤
        run.proper.nodes.length := by
      rw [hcglen]
      by_cases h0 : 0 < comp.length
      · have hlt : comp.length - 1 <
          (componentCandidate e.graph comp candidate).nodes.length := by omega
        have := hcov (comp.length - 1) hlt
        omega
      · omega
    have hcg : (componentCandidate e.graph comp candidate).nodes.getD v default =
        default := by
      have hnone : (componentCandidate e.graph comp candidate).nodes[v]? = none :=
        List.getElem?_eq_none (by omega)
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    have hcond : (default : Node).border != -2 := by decide
    have hframe : frameRect default (componentCandidate e.graph comp candidate) run v =
        nodeRect (componentCandidate e.graph comp candidate) run v := by
      unfold frameRect
      dsimp only
      rw [hcg]
      simp only [hcond, ↓reduceIte]
    rw [hframe]
    unfold nodeRect
    dsimp only
    have hnone : run.proper.nodes[v]? = none := List.getElem?_eq_none (by omega)
    have hget : run.proper.nodes.getD v default = default := by
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [hget]
    exact Int.le_refl _

private theorem lines_len_general {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

private theorem componentCandidate_slot_general (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- Ordinary-node frame reservation at general order options. The tracked
`SceneExecution.ordinary_candidate_frame_loop_reservation` pins
`candidateOrder` in `hrun` but feeds it only to the general
`componentRun_original_frame_minimum_dims`; this replays it. -/
private theorem ordinary_candidate_frame_loop_reservation_general
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .node)
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      orderOptions = .ok run) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  obtain ⟨node, hnode, hheight⟩ :=
    execution.ordinary_candidate_loop_reservation component hn candidate v hv hb hrole
  have hborder := execution.ordinary_candidate_node_border_zero component candidate v hv hb hrole hnode
  exact Int.le_trans hheight (componentRun_original_frame_minimum_dims hrun hnode hborder).2

/-- Fixed-node frame reservation at general order options. The tracked
`SceneExecution.fixed_candidate_frame_loop_reservation` pins `candidateOrder`
in `hrun` but feeds it only to the general
`componentRun_original_frame_minimum_dims`; this replays it. -/
private theorem fixed_candidate_frame_loop_reservation_general
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry)
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      orderOptions = .ok run) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  have hlines : execution.lines.length = inp.boxes.length :=
    lines_len_general execution
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
  rw [componentCandidate_slot_general,
    componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv]
  exact Int.le_trans hheight hframe

/-- Group-node frame reservation at general order options. The tracked
`SceneExecution.nonfixed_group_candidate_frame_loop_reservation` pins
`candidateOrder` in `hrun` but feeds it only to the general
`componentRun_group_frame_height_ge`; this replays it. -/
private theorem nonfixed_group_candidate_frame_loop_reservation_general
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    (hloop : loopEdges (componentCandidate execution.graph component candidate).edges v ≠ [])
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph component candidate) execution.measured
      orderOptions = .ok run) :
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
  rw [componentCandidate_slot_general,
    componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv]
  exact Int.le_trans hheight hframe

/-- Executed loop reservation at any order options: every component node has a
positive slot and enough frame height for its loop band. General form of
`loopReservation_executed` — the only order-mentioning inputs are the three
frame reservations above, replayed generally. -/
theorem loopReservation_general {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run) (v : Nat)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run) :
    LoopReservation (componentCandidate e.graph comp candidate) run e.measured v := by
  have hn : comp.Nodup := components_nodup e.graph comp hcomp
  have hslotpos := executed_candidate_slot_pos e comp candidate
  unfold LoopReservation
  refine ⟨hslotpos, ?_⟩
  have hband2 : 2 * (componentCandidate e.graph comp candidate).slot ≤
      Loops.band (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) :=
    band_ge_two_slot_general _ _
  have hslotnn : 0 ≤ (componentCandidate e.graph comp candidate).slot := by omega
  have hbandnn : 0 ≤ Loops.band (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot) := by omega
  have hlenNn : 0 ≤ (((loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot).length : Int)) :=
    Int.natCast_nonneg _
  have hreq : Loops.requiredHeight (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot) ≤
      (frameRect default (componentCandidate e.graph comp candidate) run v).h := by
    by_cases hnil : loopSizes (componentCandidate e.graph comp candidate).edges
        e.measured v (componentCandidate e.graph comp candidate).slot = []
    · have hR0 : Loops.requiredHeight
          (componentCandidate e.graph comp candidate).slot
          (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
            (componentCandidate e.graph comp candidate).slot) = 0 := by
        simp [hnil, Loops.requiredHeight]
      rw [hR0]
      exact frame_h_nonneg_general e comp candidate run orderOptions hcomp hrun v
    · have hloop : loopEdges (componentCandidate e.graph comp candidate).edges v ≠ [] := by
        intro he
        exact hnil (by simp only [loopSizes, he, List.map_nil])
      obtain ⟨edge, hmem⟩ : ∃ edg, edg ∈
          loopEdges (componentCandidate e.graph comp candidate).edges v := by
        cases h : loopEdges (componentCandidate e.graph comp candidate).edges v with
        | nil => exact absurd h hloop
        | cons edg _ => exact ⟨edg, by simp⟩
      obtain ⟨hmem', hfilter⟩ :=
        List.mem_filter.mp (by simpa only [loopEdges] using hmem)
      have hAnd := hfilter
      simp only [Bool.and_eq_true] at hAnd
      obtain ⟨hTailBeq, hHeadBeq⟩ := hAnd
      have hTailEq : edge.tail = v := beq_iff_eq.mp hTailBeq
      have hbd := sceneExecution_edges_bounded e
      have hbnd :=
        candidate_edge_endpoints_bounded_general e.graph comp candidate hcomp hbd hmem'
      have hlen : (componentCandidate e.graph comp candidate).nodes.length =
          comp.length :=
        candidate_nodes_length_general _ _ _
      have hv : v < comp.length := by
        have h1 := hbnd.1
        rw [hlen, hTailEq] at h1
        exact h1
      have hlines : e.lines.length = inp.boxes.length := lines_len_general e
      by_cases hm : comp[v]'hv < e.lines.length
      · have hblt : comp[v]'hv < inp.boxes.length := by
          rw [← hlines]; exact hm
        have hbox : inp.boxes[comp[v]'hv]? = some (inp.boxes[comp[v]'hv]) :=
          List.getElem?_eq_getElem hblt
        by_cases hfixed : inp.fixedSizes.any
            (fun fixed => fixed.1 == (inp.boxes[comp[v]'hv]).id) = true
        · obtain ⟨entry, hfind⟩ : ∃ entry, inp.fixedSizes.find?
              (fun fixed => fixed.1 == (inp.boxes[comp[v]'hv]).id) = some entry := by
            cases hf : inp.fixedSizes.find?
                (fun fixed => fixed.1 == (inp.boxes[comp[v]'hv]).id) with
            | none =>
              obtain ⟨entry, hmemF, hid⟩ := List.any_eq_true.mp hfixed
              exact absurd (List.find?_eq_none.mp hf entry hmemF)
                (by rw [hid]; decide)
            | some entry => exact ⟨entry, rfl⟩
          exact fixed_candidate_frame_loop_reservation_general e comp hn candidate v
            hv hbox hfind hrun
        · have hfixedF : inp.fixedSizes.any
              (fun fixed => fixed.1 == (inp.boxes[comp[v]'hv]).id) = false :=
            Bool.eq_false_iff.mpr hfixed
          by_cases hrole : (inp.boxes[comp[v]'hv]).role = .group
          · exact nonfixed_group_candidate_frame_loop_reservation_general e comp hn
              candidate v hv hbox hrole hfixedF hloop hrun
          · have hroleN : (inp.boxes[comp[v]'hv]).role = .node := by
              match h : (inp.boxes[comp[v]'hv]).role with
              | .node => rfl
              | .group => exact absurd h hrole
            exact ordinary_candidate_frame_loop_reservation_general e comp hn candidate v
              hv hbox hroleN hrun
      · have hle : e.lines.length ≤ comp[v]'hv := by omega
        have hget : comp.getD v 0 = comp[v]'hv := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
            Option.getD_some]
        have hge : inp.boxes.length ≤ comp.getD v 0 := by
          rw [hget, ← hlines]; exact hle
        have hempty := bottomLoopEmpty_general e comp candidate v hcomp hv hge
        have hnil' : loopSizes (componentCandidate e.graph comp candidate).edges
            e.measured v (componentCandidate e.graph comp candidate).slot = [] := by
          simp only [loopSizes, hempty, List.map_nil]
        exact absurd hnil' hnil
  have h2len : ((loopSizes (componentCandidate e.graph comp candidate).edges e.measured
      v (componentCandidate e.graph comp candidate).slot).length : Int) ≤
      2 * (((loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot).length : Int)) := by omega
  have hle2 := Int.mul_le_mul_of_nonneg_right h2len hbandnn
  have hreqH : 2 * (((loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot).length : Int)) *
      Loops.band (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) ≤
      (frameRect default (componentCandidate e.graph comp candidate) run v).h := hreq
  exact Int.le_trans hle2 hreqH

/-- An executed component run has no exact ports, at any order options.
General form of the private `componentRun_exact_nil'`: `componentRun` is
unfolded and every phase is general. -/
private theorem componentRun_exact_nil_general {P : Params} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (h : componentRun P cg labels orderOptions = .ok run) : run.exact = [] := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := bind_ok_general h
  obtain ⟨p0, _, h⟩ := bind_ok_general h
  obtain ⟨p, _, h⟩ := bind_ok_general h
  obtain ⟨ord, _, h⟩ := bind_ok_general h
  obtain ⟨xs, _, h⟩ := bind_ok_general h
  obtain ⟨routed, _, h⟩ := bind_ok_general h
  obtain ⟨lanes, _, h⟩ := bind_ok_general h
  obtain ⟨yt, _, h⟩ := bind_ok_general h
  obtain ⟨routes, _, h⟩ := bind_ok_general h
  have hfin := Except.ok.inj h
  subst hfin
  rfl

/-- The loop footprint starts at the right edge of its own frame, so it is
disjoint from that frame regardless of extent. Order-free. -/
private theorem loopFootprint_self_disjoint_general (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (v : Nat) :
    Disjoint (loopFootprint cg run labels v) (frameRect default cg run v) := by
  unfold loopFootprint
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- Sizing-phase loop extent: an executed graph node stores the exact loop
extent of its own loop sizes. Order-free copy of the private
`graph_node_loopExtent_eq` (no `hrun` is used). -/
private theorem graph_node_loopExtent_general {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecution inp o res) {m : Nat}
    (hm : m < e.lines.length) {gnode : Node}
    (hg : e.graph.nodes[m]? = some gnode) :
    gnode.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
  have hlines : e.lines.length = inp.boxes.length := lines_len_general e
  have hmB : m < inp.boxes.length := by rw [← hlines]; exact hm
  obtain ⟨box, hbox⟩ : ∃ box, inp.boxes[m]? = some box :=
    ⟨_, List.getElem?_eq_getElem hmB⟩
  have hgE := e.graph_eq
  unfold measuredGraph at hgE
  obtain ⟨initial, hinitial, hgE⟩ := bind_ok_general hgE
  obtain ⟨edges, _, hgE⟩ := bind_ok_general hgE
  obtain ⟨metric, hmM, hgE⟩ := bind_ok_general hgE
  obtain ⟨labels, hlL, hgE⟩ := bind_ok_general hgE
  obtain ⟨nodes, hnodes, hgE⟩ := bind_ok_general hgE
  have hprepare := (Except.ok.inj hgE).symm
  let raw : Graph := { nodes := nodes, edges := edges, slot := e.params.slot }
  change e.graph = Compound.prepare _ e.params.clusterPad _ raw at hprepare
  have hemetric : metric = e.metric := Except.ok.inj (hmM.symm.trans e.metric_eq)
  subst hemetric
  have helabels : labels = e.measured :=
    Except.ok.inj (hlL.symm.trans e.measured_eq)
  subst helabels
  have hslotG : e.graph.slot = e.params.slot := by rw [hprepare]; exact rfl
  have hslotnn : 0 ≤ e.params.slot := by
    have hvalid := checkedParams_valid e.checked
    have h1 : 1 ≤ e.params.slot := hvalid.2.2.1
    omega
  have hwidths : ∀ l ∈ loopSizes edges e.measured m e.params.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hextnn : 0 ≤ Loops.extent e.params.slot
      (loopSizes edges e.measured m e.params.slot) :=
    extent_nonneg_of_slot_nonneg_general hslotnn _ hwidths
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, _, hbefore⟩ :=
    hinit m (e.lines[m], m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hm,
        Option.map_some, Nat.zero_add])
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed m (orientNode o.direction before, m)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have hloop : after.loopExtent =
      (Loops.extent e.params.slot
        (loopSizes edges e.measured m e.params.slot)).toNat := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    by_cases hfixed : inp.fixedSizes.any
        (fun fixed => fixed.1 == box.id) = true
    · obtain ⟨entry, hfindE⟩ : ∃ entry, inp.fixedSizes.find?
          (fun fixed => fixed.1 == box.id) = some entry := by
        cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
        | none =>
          obtain ⟨e2, hmF, hid⟩ := List.any_eq_true.mp hfixed
          exact absurd (List.find?_eq_none.mp hf e2 hmF) (by rw [hid]; decide)
        | some e2 => exact ⟨e2, rfl⟩
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
        hfixed
      simp [hbox, hfindE, hany] at hstep
      split at hstep
      · cases hstep
      · split at hstep
        · cases hstep
        · have he := Except.ok.inj hstep
          subst after
          rfl
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hfindN : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
        List.find?_eq_none.mpr (List.any_eq_false.mp hfixedF)
      by_cases hrole : box.role = .group
      · simp [hbox, hfindN, hrole, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
      · have hroleN : box.role = .node := by
          match h : box.role with
          | .node => rfl
          | .group => exact absurd h hrole
        simp [hbox, hfindN, hroleN, hfixedF] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · have he := Except.ok.inj hstep
            subst after
            rfl
  have hinodes : m < nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hget : nodes[m]'hinodes = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hraw : raw.nodes[m]? = some after := by
    simpa only [raw, List.getElem?_eq_getElem hinodes] using congrArg some hget
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := e.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * e.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  have hprepEq : e.graph = Compound.prepare boxes e.params.clusterPad titles raw :=
    hprepare
  have hbound : m < boxes.length := by
    simpa only [boxes, List.length_map] using hmB
  have hpe := prepare_loopSizes_preserved boxes e.params.clusterPad titles raw m
    hbound e.measured e.params.slot
  have heg : (Compound.prepare boxes e.params.clusterPad titles raw).edges =
      e.graph.edges := by
    rw [hprepEq]
  rw [heg] at hpe
  have hrawE : raw.edges = edges := rfl
  have hsizeq : loopSizes edges e.measured m e.params.slot =
      loopSizes e.graph.edges e.measured m e.graph.slot := by
    rw [hrawE] at hpe
    rw [← hpe, hslotG]
  have hloopG : after.loopExtent = (Loops.extent e.graph.slot
      (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
    rw [hloop, hsizeq, hslotG]
  have hclose : gnode.loopExtent = after.loopExtent →
      gnode.loopExtent = (Loops.extent e.graph.slot
        (loopSizes e.graph.edges e.measured m e.graph.slot)).toNat := by
    intro hll
    rw [hll, hloopG]
  by_cases hrole : box.role = .group
  · by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := Compound.prepare_group_title_record boxes e.params.clusterPad
        titles raw hinodes hboxM hrole
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = (raw.nodes[m]'hinodes).loopExtent := by
        rw [h2]
      have hRl : (raw.nodes[m]'hinodes).loopExtent = after.loopExtent := by
        simp only [raw, hget]
      exact hclose (hloopR.trans hRl)
  · have hroleN : box.role = .node := by
      match h : box.role with
      | .node => rfl
      | .group => exact absurd h hrole
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
    · have hmapped : boxes[m]? = some { box with role := .node } := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixed,
          ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hmapped rfl
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        Bool.eq_false_iff.mpr hfixed
      have hboxM : boxes[m]? = some box := by
        simp only [boxes, List.getElem?_map, hbox, Option.map_some, hfixedF,
          Bool.false_eq_true, ↓reduceIte]
      have hrec := prepare_node_record boxes e.params.clusterPad titles raw hraw
        hboxM hroleN
      have h1 : some gnode =
          (Compound.prepare boxes e.params.clusterPad titles raw).nodes[m]? := by
        rw [← hg, hprepEq]
      rw [hrec] at h1
      have h2 := Option.some.inj h1
      have hloopR : gnode.loopExtent = after.loopExtent := by rw [h2]
      exact hclose hloopR

/-- `coordinateGraph` preserves the loop extent of a plain anchor. Order-free
copy of the private `coordinateGraph_loopExtent`. -/
private theorem coordinateGraph_loopExtent_general {P : Params} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraph P p).nodes[i]? = some out ∧
      out.node.loopExtent = nd.node.loopExtent := by
  obtain ⟨sized, hs, hb', hle⟩ :
      ∃ sized, (sizeProperPorts P p).nodes[i]? = some sized ∧
        sized.node.border = 0 ∧ sized.node.loopExtent = nd.node.loopExtent := by
    unfold sizeProperPorts
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, hb, rfl⟩
    · refine ⟨_, rfl, hb, rfl⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPorts P p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[i]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · refine ⟨_, rfl, ?_⟩
    show sized.node.loopExtent = nd.node.loopExtent
    exact hle
  · exact ⟨_, rfl, hle⟩

/-- Separation for two distinct in-range plain nodes, at any order options.
General form of the private `separation_plain_pair`: the proof feeds `hrun`
only to order-general helpers. -/
private theorem separation_plain_pair_general {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    {v b : Nat} {nodeV nodeB : Node}
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hblen : b < (componentCandidate e.graph comp candidate).nodes.length)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hvB0 : nodeV.border = 0) (hbB0 : nodeB.border = 0) (hne : v ≠ b) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hrunU := hrun
  have hexact : run.exact = [] := componentRun_exact_nil_general hrunU
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hcovered := componentRun_original_nodes_covered hrun
  have huP : v < run.proper.nodes.length := hcovered v hvlen
  have hfp : loopFootprint (componentCandidate e.graph comp candidate) run e.measured v =
      ⟨(frameRect default (componentCandidate e.graph comp candidate) run v).x +
        (frameRect default (componentCandidate e.graph comp candidate) run v).w,
       (frameRect default (componentCandidate e.graph comp candidate) run v).y,
       Loops.extent (componentCandidate e.graph comp candidate).slot
         (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
           (componentCandidate e.graph comp candidate).slot),
       (frameRect default (componentCandidate e.graph comp candidate) run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
  have hvP : b < run.proper.nodes.length := hcovered b hblen
  obtain ⟨actualV, hcoordV, hpropV, _, hbV0', _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeV hvB0
  obtain ⟨actualB, hcoordB, hpropB, _, hbB0', _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeB hbB0
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    rw [List.getD_eq_getElem?_getD, hnodeB]
    rfl
  have hframeV : frameRect default (componentCandidate e.graph comp candidate) run v =
      nodeRect (componentCandidate e.graph comp candidate) run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hvB0]
    rfl
  have hframeB : frameRect default (componentCandidate e.graph comp candidate) run b =
      nodeRect (componentCandidate e.graph comp candidate) run b := by
    unfold frameRect
    simp only []
    rw [hgetB, hbB0]
    rfl
  have hrectV : nodeRect (componentCandidate e.graph comp candidate) run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      ⟨run.xs.getD b 0 - Int.fdiv actualB.node.w 2, run.ys.getD b 0,
        actualB.node.w, actualB.node.h⟩ := by
    simp [nodeRect, hpropB]
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute,
    hlanes, hry, hys, hroutes⟩ := componentRun_spec hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : v < run.coordinateProper.nodes.length := by omega
  have hvC : b < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  obtain ⟨hrg, hslot, hslotslen, hslotsnn, hsizes, htop, hy⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hy]; simp
  have huCy : v < run.coordinateYs.length := by omega
  have hvCy : b < run.coordinateYs.length := by omega
  have hysEqV : run.ys.getD v 0 = run.coordinateYs.getD v 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordV huCy, hbV0']
    rfl
  have hysEqB : run.ys.getD b 0 = run.coordinateYs.getD b 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordB hvCy, hbB0']
    rfl
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v huP
  obtain ⟨lB, hlyB, hbIn, hrkB⟩ := hcov b hvP
  let rV : Nat := (rk run.proper.rank v).toNat
  let rB : Nat := (rk run.proper.rank b).toNat
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkB' : rk run.proper.rank b = (rB : Int) := by
    have h := Int.toNat_of_nonneg hrkB
    exact h.symm
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hrkCoordB : rk run.coordinateProper.rank b = (rB : Int) := by
    rw [← hranks]; exact hrkB'
  have hlyV' : run.layers[rV]? = some lV := hlyV
  have hlyB' : run.layers[rB]? = some lB := hlyB
  rcases Nat.lt_trichotomy rV rB with hlt | heq | hgt
  · have hbandV := CoordsImpl.rankAxis_node_in_band hry hlyV' hvIn huC hrkCoordV
    have hbandB := CoordsImpl.rankAxis_node_in_band hry hlyB' hbIn hvC hrkCoordB
    have hbands := CoordsImpl.rankAxis_bands_disjoint hry rV rB lV lB hlt hlyV' hlyB'
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    have hnodeHB : CoordsImpl.nodeH run.coordinateProper b = actualB.node.h := by
      simp [CoordsImpl.nodeH, hcoordB]
    rw [hnodeHV] at hbandV
    rw [hnodeHB] at hbandB
    unfold LoopFootprintSeparation
    rw [hfp, hframeV, hrectV, hframeB, hrectB]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · rw [heq] at hlyV'
    obtain hlBVeq : lB = lV := Option.some.inj (hlyB'.symm.trans hlyV')
    rw [hlBVeq] at hbIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp hvIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hbIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lV ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyV'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    have hfbV : ¬(actualV.node.border = -2 ∨ actualV.node.border = 2) := by
      simp [hbV0']
    have hfbB : ¬(actualB.node.border = -2 ∨ actualB.node.border = 2) := by
      simp [hbB0']
    obtain ⟨_, hxV⟩ := componentRun_nonproxy_record hrun hcoordV hfbV
    obtain ⟨_, hxB⟩ := componentRun_nonproxy_record hrun hcoordB hfbB
    obtain ⟨_, _, _, hcoordinate, hkeys, _, hrecords, _⟩ :=
      componentRun_prepared_titled_source e.graph_eq hcomp hrun
    have hshape := componentCandidate_shape (components_nodup e.graph comp hcomp)
      (measuredGraph_shape e.graph_eq) candidate
    have huniq : ∀ (u w : Nat) (left right : ProperNode),
        run.coordinateProper.nodes[u]? = some left →
        run.coordinateProper.nodes[w]? = some right →
        left.node.border = 3 → right.node.border = 3 →
        left.node.clusterPath = right.node.clusterPath → u = w := by
      intro u w left right hleft hright hleftBorder hrightBorder hpath
      apply pc_title_unique hkeys hshape
        (by rw [hcoordinate]; exact hleft)
        (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
    have hslotpos := executed_candidate_slot_pos e comp candidate
    have hslotnn : 0 ≤ (componentCandidate e.graph comp candidate).slot := by omega
    have hwidths : ∀ l ∈ loopSizes (componentCandidate e.graph comp candidate).edges
        e.measured v (componentCandidate e.graph comp candidate).slot, 0 ≤ l.width := by
      intro l hl
      obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
      rw [stackSize_width_eq]
      exact Labels.stackWidth_nonneg _
    have hextnn : 0 ≤ Loops.extent (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot) :=
      extent_nonneg_of_slot_nonneg_general hslotnn _ hwidths
    have hLvGe : ((actualV.node.loopExtent : Int)) ≥
        Loops.extent (componentCandidate e.graph comp candidate).slot
          (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
            (componentCandidate e.graph comp candidate).slot) := by
      by_cases hnil : loopSizes (componentCandidate e.graph comp candidate).edges
          e.measured v (componentCandidate e.graph comp candidate).slot = []
      · have hExt0 : Loops.extent (componentCandidate e.graph comp candidate).slot
            (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
              (componentCandidate e.graph comp candidate).slot) = 0 := by
          simp [hnil, Loops.extent]
        rw [hExt0]
        exact Int.natCast_nonneg _
      · have hvl : v < comp.length := by
          have hlen : (componentCandidate e.graph comp candidate).nodes.length =
              comp.length := candidate_nodes_length_general _ _ _
          omega
        have hget : comp.getD v 0 = comp[v]'hvl := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvl,
            Option.getD_some]
        have hmlin : comp.getD v 0 < e.lines.length := by
          by_cases hcon : comp.getD v 0 < e.lines.length
          · exact hcon
          have hle : e.lines.length ≤ comp[v]'hvl := by omega
          have hge : inp.boxes.length ≤ comp.getD v 0 := by
            have hlines : e.lines.length = inp.boxes.length := lines_len_general e
            rw [hget, ← hlines]; exact hle
          have hempty := bottomLoopEmpty_general e comp candidate v hcomp hvl hge
          have hnil' : loopSizes (componentCandidate e.graph comp candidate).edges
              e.measured v (componentCandidate e.graph comp candidate).slot = [] := by
            simp only [loopSizes, hempty, List.map_nil]
          exact absurd hnil' hnil
        have hgnlen : comp.getD v 0 < e.graph.nodes.length := by
          have h1 := measuredGraph_nodes_length_ge e.graph_eq (lines_len_general e)
          have hlines : e.lines.length = inp.boxes.length := lines_len_general e
          omega
        obtain ⟨gnodeM, hgm⟩ : ∃ g, e.graph.nodes[comp.getD v 0]? = some g :=
          ⟨_, List.getElem?_eq_getElem hgnlen⟩
        have hloopM := graph_node_loopExtent_general e hmlin hgm
        have hcslot : (componentCandidate e.graph comp candidate).slot =
            e.graph.slot := componentCandidate_slot_general e.graph comp candidate
        have hpres := componentCandidate_loopSizes_preserved e.graph comp
          (components_nodup e.graph comp hcomp) candidate v hvl e.measured
          (componentCandidate e.graph comp candidate).slot
        have e2 : nodeV = e.graph.nodes.getD (comp.getD v 0) default := by
          have hcc : (componentCandidate e.graph comp candidate).nodes =
              comp.map (fun key => e.graph.nodes.getD key default) := by
            rw [componentCandidate_nodes]
            unfold componentGraph
            rfl
          have h1 : (comp.map (fun key => e.graph.nodes.getD key default))[v]? =
              some nodeV := by
            rw [← hcc]; exact hnodeV
          rw [List.getElem?_map] at h1
          have h2 : comp[v]? = some (comp.getD v 0) := by
            have h3 := List.getElem?_eq_getElem hvl
            rwa [← hget] at h3
          rw [h2, Option.map_some] at h1
          have h3 := Option.some.inj h1
          exact h3.symm
        have e1 : e.graph.nodes.getD (comp.getD v 0) default = gnodeM := by
          rw [List.getD_eq_getElem?_getD, hgm]
          rfl
        have hnodeVloop : nodeV.loopExtent = gnodeM.loopExtent := by rw [e2, e1]
        have hlabV := hrecords v nodeV hnodeV
        obtain ⟨outV, houtV, hloopV⟩ := coordinateGraph_loopExtent_general hlabV
          (by simpa using hvB0)
        rw [hcoordinate] at houtV
        have houtVeq : outV = actualV :=
          Option.some.inj (houtV.symm.trans hcoordV)
        have hLvEq : ((actualV.node.loopExtent : Int)) =
            Loops.extent (componentCandidate e.graph comp candidate).slot
              (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
                (componentCandidate e.graph comp candidate).slot) := by
          have h1 : actualV.node.loopExtent = nodeV.loopExtent := by
            rw [← houtVeq]; exact hloopV
          rw [h1, hnodeVloop, hloopM, ← hcslot, hget, ← hpres]
          exact Int.toNat_of_nonneg hextnn
        omega
    have hLwNN : (0 : Int) ≤ ((actualB.node.loopExtent : Int)) :=
      Int.natCast_nonneg _
    have hWvNN : (0 : Int) ≤ actualV.node.w := by
      have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
      have hsizesNN := hcs.2.2.2.1
      exact (sizesNonneg_lookup hsizesNN v actualV hcoordV).1
    have hgap : 1 ≤ min e.params.nodeGap e.params.clusterPad := by
      have hcs := CoordsImpl.crossCoordsClusterWith_spec hcross
      omega
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq lV hlayerMem
        pu pv v b actualV actualB hplt hpu hpv hcoordV hcoordB
        (by simp [hbV0']) (by simp [hbV0']) (by simp [hbB0']) (by simp [hbB0'])
      simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordV, hcoordB] at hsep
      unfold LoopFootprintSeparation
      rw [hfp, hframeV, hrectV, hframeB, hrectB]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
      omega
    · have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq lV hlayerMem
        pv pu b v actualB actualV hpgt hpv hpu hcoordB hcoordV
        (by simp [hbB0']) (by simp [hbB0']) (by simp [hbV0']) (by simp [hbV0'])
      simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordV, hcoordB] at hsep
      unfold LoopFootprintSeparation
      rw [hfp, hframeV, hrectV, hframeB, hrectB]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
      omega
  · have hbandV := CoordsImpl.rankAxis_node_in_band hry hlyV' hvIn huC hrkCoordV
    have hbandB := CoordsImpl.rankAxis_node_in_band hry hlyB' hbIn hvC hrkCoordB
    have hbands := CoordsImpl.rankAxis_bands_disjoint hry rB rV lB lV hgt hlyB' hlyV'
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    have hnodeHB : CoordsImpl.nodeH run.coordinateProper b = actualB.node.h := by
      simp [CoordsImpl.nodeH, hcoordB]
    rw [hnodeHV] at hbandV
    rw [hnodeHB] at hbandB
    unfold LoopFootprintSeparation
    rw [hfp, hframeV, hrectV, hframeB, hrectB]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

/-- The loop extent of an empty size list is zero. Order-free. -/
private theorem extent_empty_general (slot : Int) : Loops.extent slot [] = 0 := by
  simp [Loops.extent]

/-- Separation with an empty loop-size list. Order-free copy. -/
private theorem sep_of_empty_loops_general {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hempty : loopSizes cg.edges labels v cg.slot = [])
    (hexact : run.exact = []) :
    LoopFootprintSeparation cg run labels v b := by
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hext : (if run.exact.contains v then Loops.exactExtent else Loops.extent)
      cg.slot (loopSizes cg.edges labels v cg.slot) = 0 := by
    have h1 : (if run.exact.contains v then Loops.exactExtent else Loops.extent) =
        Loops.extent := by simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    rw [h1, hempty]
    exact extent_empty_general _
  unfold LoopFootprintSeparation loopFootprint
  rw [hext]
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- An out-of-range position owns no self-loops in an executed candidate.
Order-free copy (no `hrun`). -/
private theorem loopEdges_empty_of_oob_general {inp : Input} {o : Options}
    {res : FamilyResult}
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
  have hbnd := candidate_edge_endpoints_bounded_general e.graph comp candidate hcomp hbd hedges
  omega

/-- An out-of-range position has an empty loop-size list. Order-free copy. -/
private theorem loopSizes_empty_of_oob_general {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate v : Nat)
    (hcomp : comp ∈ components e.graph)
    (hv : ¬ v < (componentCandidate e.graph comp candidate).nodes.length) :
    loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
      (componentCandidate e.graph comp candidate).slot = [] := by
  have hempty := loopEdges_empty_of_oob_general e comp candidate v hcomp hv
  simp only [loopSizes, hempty, List.map_nil]

/-- The frame at an out-of-range proper index is degenerate. Order-free copy. -/
private theorem frameRect_width_zero_of_oob_general {cg : Graph} {run : Run} {b : Nat}
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

/-- Separation with a degenerate out-of-range frame. Order-free copy. -/
private theorem sep_of_frame_oob_general {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {v b : Nat}
    (hw : (frameRect default cg run b).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A candidate node record is the executed-graph record at the mapped index.
Order-free copy. -/
private theorem candidate_node_lookup_general {g : Graph} {comp : List Nat}
    {candidate v : Nat} (hv : v < comp.length) {nodeV : Node}
    (hnodeV : (componentCandidate g comp candidate).nodes[v]? = some nodeV) :
    nodeV = g.nodes.getD (comp.getD v 0) default := by
  have hcc : (componentCandidate g comp candidate).nodes =
      comp.map fun key => g.nodes.getD key default := by
    rw [componentCandidate_nodes]
    unfold componentGraph
    rfl
  have h2 : comp[v]? = some (comp.getD v 0) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
      Option.getD_some]
  rw [hcc, List.getElem?_map] at hnodeV
  rw [h2, Option.map_some] at hnodeV
  have hcon : g.nodes.getD (comp.getD v 0) default = nodeV := Option.some.inj hnodeV
  exact hcon.symm

/-- The broad residual at any order options, from the two proved narrow
results plus the two remaining hypotheses. General form of
`loopFootprintSeparationResidual`: the proof applies the already-general
inputs at `orderOptions` instead of `candidateOrder candidate`. -/
private theorem loopFootprintSeparationResidual_general {inp : Input} {o : Options}
    {res : FamilyResult}
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res)
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run) (v b : Nat)
    (hcomp : comp ∈ components e.graph)
    (hbord : ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    (hne0 : ((componentCandidate e.graph comp candidate).nodes.getD v default).border ≠ 0 ∨
      ¬ v < (componentCandidate e.graph comp candidate).nodes.length ∨
      ¬ b < (componentCandidate e.graph comp candidate).nodes.length) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  rcases hne0 with hne0 | hvnlen | hbnlen
  · by_cases hvlen : v < (componentCandidate e.graph comp candidate).nodes.length
    · rcases LoopFootprintOtherBorder_holds e comp candidate run orderOptions v hcomp hrun hvlen hne0 with htop2 | hbot2
      · exact htop e comp candidate run orderOptions v b hcomp hbord hrun hvlen htop2
      · have hempty := LoopFootprintBottomEmpty_holds e comp candidate run orderOptions v hcomp hrun hvlen hbot2
        exact sep_of_empty_loops_general hempty (componentRun_exact_nil_general hrun)
    · exact sep_of_empty_loops_general (loopSizes_empty_of_oob_general e comp candidate v hcomp hvlen)
        (componentRun_exact_nil_general hrun)
  · exact sep_of_empty_loops_general (loopSizes_empty_of_oob_general e comp candidate v hcomp hvnlen)
      (componentRun_exact_nil_general hrun)
  · by_cases hvlen : v < (componentCandidate e.graph comp candidate).nodes.length
    · by_cases hbproper : b < run.proper.nodes.length
      · exact hbeyond e comp candidate run orderOptions v b hcomp hrun hvlen
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
        exact sep_of_frame_oob_general (frameRect_width_zero_of_oob_general hcg hproper)
    · exact sep_of_empty_loops_general (loopSizes_empty_of_oob_general e comp candidate v hcomp hvlen)
        (componentRun_exact_nil_general hrun)

/-- Executed loop footprint separation for plain boxes at any order options,
modulo only the two remaining narrow residuals. General form of
`loopFootprintSeparation_executed`. -/
private theorem loopFootprintSeparation_executed_general {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run) (v b : Nat)
    (hcomp : comp ∈ components e.graph)
    (hbord : ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  by_cases heq : v = b
  · subst heq
    exact loopFootprint_self_disjoint_general _ _ _ _
  · by_cases hvlen : v < (componentCandidate e.graph comp candidate).nodes.length
    · by_cases hblen : b < (componentCandidate e.graph comp candidate).nodes.length
      · obtain ⟨nodeV, hnodeV⟩ :
            ∃ n, (componentCandidate e.graph comp candidate).nodes[v]? = some n :=
          ⟨_, List.getElem?_eq_getElem hvlen⟩
        obtain ⟨nodeB, hnodeB⟩ :
            ∃ n, (componentCandidate e.graph comp candidate).nodes[b]? = some n :=
          ⟨_, List.getElem?_eq_getElem hblen⟩
        have hbB0 : nodeB.border = 0 := by
          have hget : (componentCandidate e.graph comp candidate).nodes.getD b default =
              nodeB := by
            simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
          rw [← hget]; exact hbord
        by_cases hvplain : nodeV.border = 0
        · exact separation_plain_pair_general e comp candidate orderOptions run hcomp hrun hvlen hblen
            hnodeV hnodeB hvplain hbB0 heq
        · have hnb : ((componentCandidate e.graph comp candidate).nodes.getD v
              default).border ≠ 0 := by
            have hget : (componentCandidate e.graph comp candidate).nodes.getD v
                default = nodeV := by
              simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
            rw [hget]; exact hvplain
          exact loopFootprintSeparationResidual_general htop hbeyond e comp candidate
            orderOptions run v b hcomp hbord hrun (Or.inl hnb)
      · exact loopFootprintSeparationResidual_general htop hbeyond e comp candidate
          orderOptions run v b hcomp hbord hrun (Or.inr (Or.inr hblen))
    · exact loopFootprintSeparationResidual_general htop hbeyond e comp candidate
        orderOptions run v b hcomp hbord hrun (Or.inr (Or.inl hvlen))

/-- Public general-order separation: the footprint of any owner misses every
in-range plain box frame, modulo the two narrow residuals. The proved narrow
facts (`OtherBorder`, `BottomEmpty`) discharge the non-plain-owner cases
inside; only `Top`/`Beyond` stay hypotheses. -/
theorem loopFootprintSeparation_general {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run) (v b : Nat)
    (hcomp : comp ∈ components e.graph)
    (hbord : ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b :=
  loopFootprintSeparation_executed_general e comp candidate orderOptions run v b
    hcomp hbord hrun htop hbeyond

/-- Bridge (c): an in-range non-plain candidate node sits under a zero-height
proper box, at any order options. By the proved `LoopFootprintOtherBorder`
its border is `±2`; border is preserved from the candidate record through
`sizeProperPorts` (`sizeProperPorts_key`), `titleReservations` (`titleF_keys`),
`addClusterBorders` (appended extras sit past the base), and `clearProxyExtents`
(`clearF_keys`), while `titleF` zeroes the height of `±2` nodes and the later
maps preserve it; `materialize_lookup` and `run_record_source` carry the
zero height to the proper node, whose height is the box height. -/
theorem loopBoxZero_of_nonplain {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (orderOptions : OrderOptions) (run : Run) (v : Nat)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run)
    (hvlen : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hne0 : ((componentCandidate e.graph comp candidate).nodes.getD v default).border ≠ 0) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).h = 0 := by
  have hb2 : ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 ∨
      ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 2 :=
    LoopFootprintOtherBorder_holds e comp candidate run orderOptions v hcomp hrun hvlen hne0
  obtain ⟨nodeV, hnodeV⟩ :
      ∃ n, (componentCandidate e.graph comp candidate).nodes[v]? = some n :=
    ⟨_, List.getElem?_eq_getElem hvlen⟩
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default = nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hbV : nodeV.border = -2 ∨ nodeV.border = 2 := by
    rw [← hgetV]; exact hb2
  obtain ⟨_, labeled, _, hcoordinate, _, _, hrecords, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hlabV : labeled.nodes[v]? = some ⟨nodeV, false, none, false⟩ :=
    hrecords v nodeV hnodeV
  have hvlab : v < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hlabV).1
  cases hs : (sizeProperPorts e.params labeled).nodes[v]? with
  | none =>
    have hkey := sizeProperPorts_key e.params labeled v
    rw [hs, hlabV] at hkey
    simp at hkey
  | some sized =>
    have hkey := sizeProperPorts_key e.params labeled v
    rw [hs, hlabV] at hkey
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
    obtain ⟨hdum, hbord, -⟩ := hkey
    have hlen_sp : (sizeProperPorts e.params labeled).nodes.length =
        labeled.nodes.length := sizeProperPorts_length _ _
    have htV : (titleReservations (sizeProperPorts e.params labeled)).nodes[v]? =
        some (titleF sized) := by
      rw [titleReservations_nodes,
        List.getElem?_append_left (by rw [List.length_map, hlen_sp]; exact hvlab),
        List.getElem?_map, hs]
      rfl
    have htF := titleF_keys sized
    have hbordS : sized.node.border = -2 ∨ sized.node.border = 2 := by
      rw [hbord]; exact hbV
    have hbordT : (titleF sized).node.border = -2 ∨ (titleF sized).node.border = 2 := by
      rw [htF.2.1]; exact hbordS
    have hhT : (titleF sized).node.h = 0 := htF.2.2.2 hbordS
    obtain ⟨extra, hx, -⟩ := addClusterBorders_extra
      (titleReservations (sizeProperPorts e.params labeled)) e.params.clusterBorderW
    have hlen_tr : labeled.nodes.length ≤
        (titleReservations (sizeProperPorts e.params labeled)).nodes.length := by
      rw [titleReservations_nodes]
      simp only [List.length_append, List.length_map]
      omega
    have haV : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts e.params labeled))
        e.params.clusterBorderW).nodes[v]? = some (titleF sized) := by
      rw [hx, List.getElem?_append_left (by omega), htV]
    have hcV : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts e.params labeled))
        e.params.clusterBorderW)).nodes[v]? = some (clearF (titleF sized)) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, haV]
      rfl
    have hcF := clearF_keys (titleF sized)
    have hhC : (clearF (titleF sized)).node.h = 0 := hcF.2.2.2.trans hhT
    have hbC : (clearF (titleF sized)).node.border = -2 ∨
        (clearF (titleF sized)).node.border = 2 := by
      rw [hcF.2.1]; exact hbordT
    obtain ⟨ndM, hmat⟩ := materialize_exists _ hcV
    obtain ⟨m, hm, -, hbb, hhh, -⟩ := materialize_lookup _ hmat.1
    have hmEq : m = clearF (titleF sized) := Option.some.inj (hm.symm.trans hcV)
    have hhM : ndM.node.h = 0 := by rw [hhh, hmEq]; exact hhC
    have hmat' : (coordinateGraph e.params labeled).nodes[v]? = some ndM := hmat.1
    rw [hcoordinate] at hmat'
    have hvP : v < run.proper.nodes.length := by
      have hcov := componentRun_original_nodes_covered hrun
      have hlen : (componentCandidate e.graph comp candidate).nodes.length = comp.length :=
        candidate_nodes_length_general _ _ _
      have hv : v < comp.length := by omega
      exact hcov v (by omega)
    obtain ⟨nd, hnd⟩ : ∃ nd, run.proper.nodes[v]? = some nd :=
      ⟨_, List.getElem?_eq_getElem hvP⟩
    obtain ⟨cw, hcw, -, hhEq⟩ := run_record_source hrun hnd
    have hcwEq : cw = ndM := Option.some.inj (hcw.symm.trans hmat')
    have hndH : nd.node.h = 0 := by rw [← hhEq, hcwEq]; exact hhM
    have hnh : RouteImpl.nodeH run.proper v = 0 := by
      simp only [RouteImpl.nodeH, hnd]
      exact hndH
    have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).h =
        RouteImpl.nodeH run.proper v := rfl
    rw [hbox, hnh]
