import Elegant.Layered.ExactLoopEnvelopeFootBelowProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.LoopFootprintGroupHullProof
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.SizingFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CoordGraph
import Elegant.Layered.CgShape
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Loops
import Elegant.Layered.Compound

set_option autoImplicit false

open Elegant Layered Layered.PipelineImpl

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Loop-envelope reservation for plain owners, plus the group overlap half.

Target leaf defs (`ExactLoopEnvelopeFootBelowProof.lean`):
`XLEM_PlainReserve` (a self-loop on a non-exact plain owner reserves its band
stack in the owner frame) and `XLEM_GroupOwnerOtherRank` (a looping group top
misses every in-scope other-rank real box).

Probe truth (`proofs/wip/Probe/ExactLoopEnvelopeReserveTProbe.lean`,
`exactIds = ["a"]`, vector profile, declaration order):
- `sib-1loop-big`, `sib-2loop-small`: `resv=true` (`n * band <= fr.h`).
- `fixedself-1loop-zero` (degenerate zero-size fixed owner): `resv=true`.
- `grp-1loop-big`, `grp-2loop-small`, `grp-1loop-long` (huge extent),
  `nest-1loop`, `unrelated-1loop`: every other-rank in-scope real box has
  `disj=true`; every `yOvl=true` row has `xOvl=false`.
  `grp-exact-1loop-big`
  (exact group id, `exactIds = ["g"]`): `prep error LayoutError.domain`
  (`exactGraph` needs a fixed size for exact nodes, so an exact non-fixed
  group top has no execution and the residual holds vacuously there).
- `illformed-dup-id`: `prep error LayoutError.domain` (no execution, so the
  universals hold vacuously; no extra `WellFormed` premise needed).

Plain route: the measured-graph sizing already stores
`requiredHeight <= node.h` for every non-exact node box (ordinary reservation
covers fixed node boxes too, since fixed groups are exact); the exact run
transfers the height through the coordinate phases into `frame.h`, and
`n * band <= 2 * n * band` closes. The candidate self-loop pins a below-boxes
global key (`lh_globalSelfLoopLt`), so no bottom case remains.
Group route: boxes missing the footprint vertically miss outright; the
y-overlapping half stays as the single residual `XLEM_GroupOverlapMiss`,
true on all probes above. All record literals are on one line.
-/

/-- Exact-run index list equation (copy of `XLEMS_run_exact_eq`). -/
private theorem xlemR_run_exact_eq {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.exact = cg.nodes.zipIdx.filterMap
      (fun q : Node × Nat => if exact.contains q.1.decl then some q.2 else none) := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, _, h⟩ := bind_ok h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  rw [← he]

/-- Exact membership forward (copy of `XLEMS_run_exact_mem_of_contains`). -/
private theorem xlemR_run_exact_mem {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < cg.nodes.length)
    (hmem : exact.contains ((cg.nodes[v]'hv).decl) = true) :
    v ∈ run.exact := by
  have heq := xlemR_run_exact_eq h
  rw [heq]
  have hzipmem : ((cg.nodes[v]'hv), v) ∈ cg.nodes.zipIdx := by
    simpa using List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hv)
  apply List.mem_filterMap.mpr
  refine ⟨((cg.nodes[v]'hv), v), hzipmem, ?_⟩
  simp only [hmem, ↓reduceIte]

/-- Exact-index absence (copy of `XLEMS_run_exact_not_mem`). -/
private theorem xlemR_run_exact_not_mem {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < cg.nodes.length)
    (hnot : run.exact.contains v = false) :
    exact.contains ((cg.nodes[v]'hv).decl) = false := by
  cases he : exact.contains ((cg.nodes[v]'hv).decl) with
  | true =>
    have hmem := xlemR_run_exact_mem h hv he
    have hcon2 : run.exact.contains v = true := by
      rw [List.contains_eq_mem]
      simp [hmem]
    rw [hcon2] at hnot
    contradiction
  | false => rfl

/-- Membership characterization of `exactDecls` (copy of
`X_self_exactDecls_contains`). -/
private theorem xlemR_exactDecls_contains {exactIds : List String} {inp : Input}
    {d : Nat} {box : ModelBox} (hb : inp.boxes[d]? = some box) :
    (exactDecls exactIds inp).contains d =
      (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) := by
  have hchar : (d ∈ exactDecls exactIds inp) ↔
      (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true := by
    constructor
    · intro hm
      unfold exactDecls at hm
      obtain ⟨q, hq, hqq⟩ := List.mem_filterMap.mp hm
      have hpred : (exactIds.contains q.1.id || (q.1.role == .group && inp.fixedSizes.any (·.1 == q.1.id))) = true := by
        cases h : (exactIds.contains q.1.id || (q.1.role == .group && inp.fixedSizes.any (·.1 == q.1.id))) with
        | true => rfl
        | false => simp only [h] at hqq; simp at hqq
      have hqd : q.2 = d := by
        simp only [hpred, ↓reduceIte] at hqq
        exact Option.some.inj hqq
      obtain ⟨a, n⟩ := q
      have hmem : inp.boxes[n]? = some a := List.mem_zipIdx_iff_getElem?.mp hq
      have hnd : n = d := hqd
      subst hnd
      have ha : a = box := Option.some.inj (hmem.symm.trans hb)
      subst ha
      exact hpred
    · intro hR
      unfold exactDecls
      apply List.mem_filterMap.mpr
      refine ⟨(box, d), List.mem_zipIdx_iff_getElem?.mpr hb, ?_⟩
      show (if exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id)) then some d else none) = some d
      simp only [hR, ↓reduceIte]
  rw [List.contains_eq_mem]
  cases hR : (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) with
  | true =>
    have hm := hchar.mpr hR
    exact decide_eq_true hm
  | false =>
    have hm : d ∉ exactDecls exactIds inp := by
      intro h
      have ht := hchar.mp h
      rw [ht] at hR
      exact Bool.noConfusion hR
    exact decide_eq_false hm

/-- A non-exact global node survives `exactGraph` unchanged (copy of
`X_self_nonexact_node_eq`). -/
private theorem xlemR_nonexact_node_eq {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {component : List Nat} {candidate v : Nat} {nk node : Node}
    (hv : v < component.length)
    (hk0 : execution.graph0.nodes[component[v]]? = some nk)
    (hnode : (componentCandidate execution.graph component candidate).nodes[v]? = some node)
    (hnexact : (exactDecls exactIds inp).contains node.decl = false) :
    node = nk := by
  have hklt : component[v] < execution.graph.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hk0).1
    rw [exactGraph_length execution.graph_eq]
    exact h1
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq hk0
  have hnode_nd : node = nd' := by
    have hlocal : (component.map fun source => execution.graph.nodes.getD source default)[v]? = some node := by
      have h1 : (componentCandidate execution.graph component candidate).nodes =
          (componentGraph execution.graph component).nodes :=
        componentCandidate_nodes _ _ _
      rw [h1] at hnode
      have h2 : (componentGraph execution.graph component).nodes =
          component.map fun source => execution.graph.nodes.getD source default := rfl
      rw [h2] at hnode
      exact hnode
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
      Option.some.injEq] at hlocal
    have hgetD : execution.graph.nodes.getD component[v] default = nd' := by
      simp only [List.getD_eq_getElem?_getD, hnd', Option.getD_some]
    rw [hgetD] at hlocal
    exact hlocal.symm
  have hnexact_nd : (exactDecls exactIds inp).contains nd'.decl = false := by
    have hde : nd'.decl = node.decl := by rw [hnode_nd]
    rw [hde]; exact hnexact
  obtain ⟨nodes, hnodes, h⟩ := bind_ok execution.graph_eq
  have he : execution.graph = { execution.graph0 with nodes := nodes } := (Except.ok.inj h).symm
  have hnd2 : nodes[component[v]]? = some nd' := by rw [he] at hnd'; exact hnd'
  obtain ⟨b, hfb, hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 component[v] nk hk0
  have hbnd : b = nd' := Option.some.inj (hmem.symm.trans hnd2)
  have hbnk : b = nk := by
    cases hbox' : inp.boxes[nk.decl]? with
    | none =>
      simp only [hbox'] at hfb
      exact (Except.ok.inj hfb).symm
    | some box' =>
      have hchar := xlemR_exactDecls_contains (exactIds := exactIds) (inp := inp) hbox'
      have hnkd : nk.decl = nd'.decl := hnd.symm
      rw [← hnkd, hchar] at hnexact_nd
      have ha : exactIds.contains box'.id = false := by
        cases h1 : exactIds.contains box'.id with
        | true => rw [h1] at hnexact_nd; exact Bool.noConfusion hnexact_nd
        | false => rfl
      have hb2 : (box'.role == .group && inp.fixedSizes.any (·.1 == box'.id)) = false := by
        cases h1 : (box'.role == .group && inp.fixedSizes.any (·.1 == box'.id)) with
        | true => rw [ha, h1] at hnexact_nd; exact Bool.noConfusion hnexact_nd
        | false => rfl
      have hcond : (!exactIds.contains box'.id && !(box'.role == .group && inp.fixedSizes.any (·.1 == box'.id))) = true := by
        rw [ha, hb2]
        decide
      simp only [hbox', hcond] at hfb
      exact (Except.ok.inj hfb).symm
  rw [hnode_nd, ← hbnd, hbnk]

/-- Exact executions cover every input box (copy of `X_self_lines_len`). -/
private theorem xlemR_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have hle := execution.lines_eq
  unfold boxLines at hle
  have hlen := (mapM_getElem? _ _ _ hle).1
  simpa only [List.length_zipIdx] using hlen

/-- The exact graph preserves the slot (copy of `X_self_graph_slot_eq`). -/
private theorem xlemR_graph_slot_eq {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.graph.slot = execution.graph0.slot := by
  obtain ⟨nodes, _, h⟩ := bind_ok execution.graph_eq
  have he := Except.ok.inj h
  rw [← he]

/-- Candidate slots agree with global slots (copy of `componentCandidate_slot`). -/
private theorem xlemR_candidate_slot (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- Band lower bound (copy of `band_ge_two_slot_general`). -/
private theorem xlemR_band_two (slot : Int) (sizes : List LoopLabel) :
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

/-- Exact proper nodes transfer unchanged for non-proxy borders (copy of
`XLEML_nonproxy_record`). -/
private theorem xlemR_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Exact original plain nodes keep their measured record (copy of
`XLEML_original_plain_record`). -/
private theorem xlemR_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := (xlemR_nonproxy_record h hcoordinate (by rw [hborder]; decide)).1
  have hxs := (xlemR_nonproxy_record h hcoordinate (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  exact hxs

/-- A candidate self-loop pins a below-boxes global key (X replay of the
`lh_loopOwnerKey` core over `execution.graph0`). -/
private theorem xlemR_keyLt {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate t : Nat}
    (hv : t < comp.length) (hn : comp.Nodup)
    {k : Nat} {e : Edge} (hedge : (componentCandidate execution.graph comp candidate).edges[k]? = some e)
    (hself : e.tail = e.head) (ht : e.tail = t) :
    ∃ kk, comp[t]? = some kk ∧ kk < inp.boxes.length := by
  have hmem : e ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  have hloop : e ∈ loopEdges (componentCandidate execution.graph comp candidate).edges t := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    have h1 : (e.tail == t) = true := by rw [ht]; simp
    have h2 : (e.head == t) = true := by
      have hht : e.head = t := hself.symm.trans ht
      rw [hht]; simp
    simp [h1, h2]
  have hSizesNe : loopSizes (componentCandidate execution.graph comp candidate).edges
      execution.measured t (componentCandidate execution.graph comp candidate).slot ≠ [] := by
    intro he
    have hempty : loopEdges (componentCandidate execution.graph comp candidate).edges t = [] :=
      List.map_eq_nil_iff.mp he
    rw [hempty] at hloop
    simp at hloop
  have hpres := componentCandidate_loopSizes_preserved execution.graph comp hn candidate t hv
    execution.measured ((componentCandidate execution.graph comp candidate).slot)
  have hSizesGNe : loopSizes execution.graph.edges execution.measured comp[t]
      execution.graph.slot ≠ [] := by
    intro heG
    apply hSizesNe
    rw [hpres, xlemR_candidate_slot execution.graph comp candidate, heG]
  have hLoopGNe : loopEdges execution.graph.edges comp[t] ≠ [] := by
    intro heG
    exact hSizesGNe (by simp only [loopSizes, heG, List.map_nil])
  obtain ⟨e₀, hmem₀⟩ : ∃ e₀, e₀ ∈ loopEdges execution.graph.edges comp[t] := by
    cases h : loopEdges execution.graph.edges comp[t] with
    | nil => exact absurd h hLoopGNe
    | cons e₀ _ => exact ⟨e₀, by simp⟩
  obtain ⟨hmemG, hfilter⟩ := List.mem_filter.mp hmem₀
  obtain ⟨hTeq, hHeq⟩ : e₀.tail = comp[t] ∧ e₀.head = comp[t] := by
    simp only [Bool.and_eq_true] at hfilter
    exact ⟨beq_iff_eq.mp hfilter.1, beq_iff_eq.mp hfilter.2⟩
  have hself₀ : e₀.tail = e₀.head := hTeq.trans hHeq.symm
  have hmemG0 : e₀ ∈ execution.graph0.edges := by
    rw [exactGraph_edges execution.graph_eq] at hmemG
    exact hmemG
  obtain ⟨metric, labels, raw, hm, hl, heRaw, hslot, hprepare, hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph0_eq
  have heRaw' : graphEdgesFrom inp 0 inp.routes = .ok raw.edges := heRaw
  have hbounds : ∀ e ∈ raw.edges,
      e.tail < inp.boxes.length ∧ e.head < inp.boxes.length :=
    fun e he => lh_rawBounds inp inp.routes 0 raw.edges heRaw' e he
  have hmemSrc : e₀ ∈ raw.edges.map (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)) := by
    rw [hprepare] at hmemG0
    dsimp only [Compound.prepare] at hmemG0
    exact hmemG0
  have hkLt : e₀.tail < inp.boxes.length :=
    lh_globalSelfLoopLt (by simp) hbounds hmemSrc hself₀
  refine ⟨e₀.tail, ?_, hkLt⟩
  rw [hTeq]
  exact List.getElem?_eq_getElem hv

/-- A non-exact loop owner with a non-group frame sits over a node box. -/
private theorem xlemR_boxRole {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate t : Nat} (hv : t < comp.length)
    {box : ModelBox} (hb : inp.boxes[comp[t]]? = some box)
    {node nk : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[t]? = some node)
    (hnk : execution.graph0.nodes[comp[t]]? = some nk)
    (hnexact : (exactDecls exactIds inp).contains node.decl = false)
    (hnodeBne : node.border ≠ -2) :
    box.role = .node := by
  have heq0 : node = nk := xlemR_nonexact_node_eq execution hv hnk hnode hnexact
  cases hbr : box.role with
  | node => rfl
  | group =>
    obtain ⟨rawNodes, rawEdges, titles, hprepare, hlength, hmetadata⟩ :=
      measuredGraph_prepared_source execution.graph0_eq
    have hboxLt : comp[t] < inp.boxes.length :=
      (List.getElem?_eq_some_iff.mp hb).1
    have hmapHb : (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)[comp[t]]? =
        some (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) := by
      simp only [List.getElem?_map, hb, Option.map_some]
    by_cases hfixed : (inp.fixedSizes.any fun fixed => fixed.1 == box.id) = true
    · have hmapRole : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then ({ box with role := .node } : ModelBox) else box).role = .node := by
        simp [hfixed]
      have hrawLt : comp[t] < rawNodes.length := by
        have hbl := (List.getElem?_eq_some_iff.mp hb).1
        have hll := xlemR_lines_len execution
        omega
      have hraw : rawNodes[comp[t]]? = some rawNodes[comp[t]] :=
        List.getElem?_eq_getElem hrawLt
      have hrec := prepare_node_record (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)
        execution.params.clusterPad titles
        ({ nodes := rawNodes, edges := rawEdges, slot := execution.params.slot } : Graph)
        hraw hmapHb hmapRole
      have hpred : (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true := by
        simp [hbr, hfixed]
      have hcon : (exactDecls exactIds inp).contains comp[t] = true := by
        rw [xlemR_exactDecls_contains hb]
        exact hpred
      have hnkDecl : nk.decl = comp[t] := by
        rw [← hprepare] at hrec
        have heqnk := Option.some.inj (hnk.symm.trans hrec)
        exact (congrArg Node.decl heqnk).trans (hmetadata _ _ hraw).1
      have hdecl : node.decl = comp[t] := by rw [heq0, hnkDecl]
      rw [hdecl, hcon] at hnexact
      exact Bool.noConfusion hnexact
    · have hfixedF : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false := by
        cases h : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) with
        | true => exact absurd h hfixed
        | false => rfl
      have hlines := xlemR_lines_len execution
      have hi : comp[t] < execution.lines.length := by omega
      have hmapHb' : (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)[comp[t]]? =
          some box := by
        simpa [hfixedF] using hmapHb
      obtain ⟨top, _, htop, _, hbTop, _, _, _, _, _⟩ :=
        measuredGraph_paired_markers execution.graph0_eq hi hmapHb' hbr
      have heqnk := Option.some.inj (hnk.symm.trans htop)
      have hb2 : node.border = -2 := by rw [heq0, heqnk]; exact hbTop
      exact absurd hb2 hnodeBne

/-- Graph reservation reaches the run frame for a non-exact plain owner. -/
private theorem xlemR_heightLe {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate t : Nat} (hv : t < comp.length) (hn : comp.Nodup)
    {box : ModelBox} (hb : inp.boxes[comp[t]]? = some box) (hrole : box.role = .node)
    {node nk : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[t]? = some node)
    (hnk : execution.graph0.nodes[comp[t]]? = some nk)
    (hnexact : (exactDecls exactIds inp).contains node.decl = false) :
    Loops.requiredHeight (componentCandidate execution.graph comp candidate).slot
      (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured t
        (componentCandidate execution.graph comp candidate).slot) ≤ node.h ∧ node.border = 0 := by
  have heq0 : node = nk := xlemR_nonexact_node_eq execution hv hnk hnode hnexact
  have hlines := xlemR_lines_len execution
  have hi : comp[t] < execution.lines.length := by
    have hbl := (List.getElem?_eq_some_iff.mp hb).1
    omega
  obtain ⟨metric, labels, node0, hm, hl, hnode0, hheight0⟩ :=
    measuredGraph_ordinary_loop_reservation execution.graph0_eq hi hb hrole
  have hemetric : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst hemetric
  have helabels : labels = execution.measured := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst helabels
  have heq00 : node0 = nk := Option.some.inj (hnode0.symm.trans hnk)
  have hb00 : node0.border = 0 :=
    measuredGraph_ordinary_node_border_zero execution.graph0_eq hi hb hrole hnode0
  have hb0 : node.border = 0 := by rw [heq0, ← heq00]; exact hb00
  have hslotEq : (componentCandidate execution.graph comp candidate).slot =
      execution.graph0.slot := by
    rw [xlemR_candidate_slot execution.graph comp candidate,
      xlemR_graph_slot_eq execution]
  have hloopEq : loopSizes (componentCandidate execution.graph comp candidate).edges
      execution.measured t (componentCandidate execution.graph comp candidate).slot =
      loopSizes execution.graph0.edges execution.measured comp[t] execution.graph0.slot := by
    rw [componentCandidate_loopSizes_preserved execution.graph comp hn candidate t hv
      execution.measured ((componentCandidate execution.graph comp candidate).slot),
      xlemR_candidate_slot execution.graph comp candidate,
      exactGraph_edges execution.graph_eq, xlemR_graph_slot_eq execution]
  have hheightC : Loops.requiredHeight (componentCandidate execution.graph comp candidate).slot
      (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured t
        (componentCandidate execution.graph comp candidate).slot) ≤ node.h := by
    rw [hloopEq, hslotEq, heq0, ← heq00]
    exact hheight0
  exact ⟨hheightC, hb0⟩

/-- Plain loop reservation holds on exact runs: the looping node's frame
covers its loop band stack. -/
theorem XLEM_plainReserve_holds (exactIds : List String) : XLEM_PlainReserve exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e hcomp hcg hrun hedge hself hbdr hnex
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp candidate hcomp hbd
    (List.mem_of_getElem? hedge)
  have hlenCG : (componentCandidate execution.graph comp candidate).nodes.length = comp.length := by
    rw [componentCandidate_nodes]
    show (comp.map fun source => execution.graph.nodes.getD source default).length = comp.length
    exact List.length_map ..
  have htailCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length := hbnd.1
  have hv : e.tail < comp.length := by omega
  have hn : comp.Nodup := components_nodup _ _ hcomp
  obtain ⟨node, hnode⟩ : ∃ node,
      (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some node :=
    ⟨_, List.getElem?_eq_getElem htailCG⟩
  obtain ⟨gk, hkt, hkLt⟩ := xlemR_keyLt execution hv hn hedge hself rfl
  have htailEq : comp[e.tail] = gk :=
    Option.some.inj ((List.getElem?_eq_getElem hv).symm.trans hkt)
  have hlines := xlemR_lines_len execution
  have hboxLt : comp[e.tail] < inp.boxes.length := by omega
  have hi : comp[e.tail] < execution.lines.length := by omega
  obtain ⟨box, hb⟩ : ∃ box, inp.boxes[comp[e.tail]]? = some box :=
    ⟨_, List.getElem?_eq_getElem hboxLt⟩
  have hnodeBne : node.border ≠ -2 := by
    have h := hbdr
    rwa [List.getD_eq_getElem?_getD, hnode, Option.getD_some] at h
  have hnexact0 : (exactDecls exactIds inp).contains
      ((componentCandidate execution.graph comp candidate).nodes[e.tail]'htailCG).decl = false :=
    xlemR_run_exact_not_mem hrun htailCG hnex
  have hnodeEq : node = (componentCandidate execution.graph comp candidate).nodes[e.tail]'htailCG :=
    Option.some.inj (hnode.symm.trans (List.getElem?_eq_getElem htailCG))
  have hnexact : (exactDecls exactIds inp).contains node.decl = false := by
    rw [hnodeEq]; exact hnexact0
  have hge := measuredGraph_nodes_length_ge execution.graph0_eq
  have hg0len : comp[e.tail] < execution.graph0.nodes.length := by omega
  obtain ⟨nk, hnk⟩ : ∃ nk, execution.graph0.nodes[comp[e.tail]]? = some nk :=
    ⟨_, List.getElem?_eq_getElem hg0len⟩
  have hrole : box.role = .node :=
    xlemR_boxRole execution hv hb hnode hnk hnexact hnodeBne
  obtain ⟨hheightC, hb0⟩ :=
    xlemR_heightLe execution hv hn hb hrole hnode hnk hnexact
  obtain ⟨actual, _, hproper, _, _, hh, _⟩ :=
    xlemR_original_plain_record hrun hnode hb0
  have hFr := frameRect_plain_dims execution.params
    (componentCandidate execution.graph comp candidate) run e.tail actual hbdr hproper
  have hslotNN : 0 ≤ (componentCandidate execution.graph comp candidate).slot :=
    componentRunX_slot_nonneg hrun
  have hband2 : 2 * (componentCandidate execution.graph comp candidate).slot ≤
      Loops.band (componentCandidate execution.graph comp candidate).slot
        (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured e.tail
          (componentCandidate execution.graph comp candidate).slot) :=
    xlemR_band_two _ _
  have hbandNN : 0 ≤ Loops.band (componentCandidate execution.graph comp candidate).slot
      (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured e.tail
        (componentCandidate execution.graph comp candidate).slot) := by omega
  have h2len : ((loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured
      e.tail (componentCandidate execution.graph comp candidate).slot).length : Int) ≤
      2 * (((loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured
        e.tail (componentCandidate execution.graph comp candidate).slot).length : Int)) := by omega
  have hle2 := Int.mul_le_mul_of_nonneg_right h2len hbandNN
  have hreqH : 2 * (((loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured
      e.tail (componentCandidate execution.graph comp candidate).slot).length : Int)) *
      Loops.band (componentCandidate execution.graph comp candidate).slot
        (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured e.tail
          (componentCandidate execution.graph comp candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run e.tail).h := by
    rw [hFr.2, hh]
    exact hheightC
  exact Int.le_trans hle2 hreqH

/-- Y-overlap half of the group-owner other-rank miss: an other-rank in-scope
real box that overlaps the extended footprint vertically still misses it
(x-separated). Strictly narrower than `XLEM_GroupOwnerOtherRank` (one extra
vertical-overlap premise); true on every group probe in
`ExactLoopEnvelopeReserveTProbe.lean` (`disj=true` on every `yOvl=true` row). -/
def XLEM_GroupOverlapMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →
    (cg.nodes.getD e.tail default).border = -2 →
    max (loopFootprintExt cg run execution.measured e.tail).y
        (RouteImpl.boxRect run.proper run.xs run.ys v).y <
      min ((loopFootprintExt cg run execution.measured e.tail).y +
        (loopFootprintExt cg run execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
          (RouteImpl.boxRect run.proper run.xs run.ys v).h) →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Group-owner other-rank miss from the y-split: vertically disjoint boxes
miss outright; the y-overlapping half stays as the residual. -/
theorem XLEM_groupOtherRank_holds (exactIds : List String)
    (hov : XLEM_GroupOverlapMiss exactIds) : XLEM_GroupOwnerOtherRank exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v hcomp hcg hrun hedge hself hv hreal
    hscope0 hscope1 hrank hbdr
  subst hcg
  by_cases hy : max (loopFootprintExt (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).y (RouteImpl.boxRect run.proper run.xs run.ys v).y <
      min ((loopFootprintExt (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).y +
        (loopFootprintExt (componentCandidate execution.graph comp candidate) run
          execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
          (RouteImpl.boxRect run.proper run.xs run.ys v).h)
  · exact hov inp o res execution comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) k e v hcomp rfl hrun hedge hself hv hreal
      hscope0 hscope1 hrank hbdr hy
  · unfold Rect.meetsInterior
    omega
end PipelineImpl
end Layered
end Elegant
