import Elegant.Layered.ExactForwardDummyFactsProof
import Elegant.Layered.ExactCaptionAncestorsProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC5Bottom
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.RouteTransport
import Elegant.Layered.Labels
import Elegant.Layered.Order
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.StrictDummyFrameProof
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.CgShape
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExactFlatC2

set_option autoImplicit false

open Elegant
open Elegant.Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact strict dummy sides (`XFD_Strict*X_holds`)

Proves the four narrow side residuals of `ExactForwardDummyFactsProof.lean`
(`XFD_StrictLeftX`, `XFD_StrictRightX`, `XFD_StrictTopX`, `XFD_StrictBottomX`)
over exact runs, replaying `strictDummyFrame_of_run`
(`StrictDummyFrameProof.lean:1091`) through `componentRunX`:

* top and bottom transport the strict dummy rank straddle (strict chain
  interior plus the closed top closure / bottom closure) through the rank
  tops, exactly as `dummyFrameTopYStrict` / `dummyFrameBotYStrict`;
* left and right transport the exact marker bracket through same-rank
  separation, exactly as `dummyFrameLeftXStrict` / `dummyFrameRightXStrict`.

Admission (`WellFormed`, `framedParents`) rides as the per-execution premises
`XCA_WellFormedX` / `XCA_FramedX`. The order-stage bracket stays as the one
narrow residual `XFD_MarkerBracketX` below.

Probe: `proofs/wip/Probe/ExactStrictDummySidesTProbe.lean` checks all four
sides and the bracket on flat, self-loop-fixed, reversed-pair-into-group,
wider-than-slot, and nested exact runs.
-/

/-- Exact marker bracket residual: the order-stage fact for one exact run,
mirror of `DummyMarkerBracket` (`StrictDummyFrameProof.lean:51`) with the
candidate graph and run coming from `componentRunX`. Strictly narrower than
`XFD_StrictLeftX` / `XFD_StrictRightX` (rank/layer positions and marker
records only, no geometry), one pipeline stage, over executed runs only.
Probe: `ExactStrictDummySidesTProbe` counts bracket satisfaction per linked
pair on flat, self-loop-fixed, reversed-pair, wider-than-slot, and nested
inputs. -/
def XFD_MarkerBracketX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    DummyMarkerBracket (componentCandidate execution.graph comp candidate) run

/-- `xsds_` small utilities: executed-line count, rank transports, list bounds.
Copies of `Xb_prepared_rk`, `X_labeled_rank_aligned`, `X_coord_rank_eq`,
`Xb_filter_ne_nil`, and `X_le_foldr_max` through the public exact prefix
(`coordinateGraphX_anchor_prefix`). -/
private theorem xsds_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := (mapM_getElem? _ _ _ execution.lines_eq).1
  simpa only [List.length_zipIdx] using h

private theorem xsds_prepared_rk {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk run.coordinateProper.rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  have hlabLen : index < labeled.rank.length :=
    (List.getElem?_eq_some_iff.mp hlabLookup).1
  obtain ⟨_, heq⟩ := (coordinateGraphX_anchor_prefix P exact labeled).2
  have hcoordLookup : run.coordinateProper.rank[index]? = some rr.ranks[index] := by
    rw [← hc, heq, List.getElem?_append_left hlabLen]
    exact hlabLookup
  simp only [rk, List.getD_eq_getElem?_getD, hcoordLookup, hrrLookup, Option.getD_some]

private theorem xsds_labeled_aligned {cg : Graph}
    {rr : RankImpl.RankResult} {normalized labeled : Proper}
    {labels : List MeasuredLabel}
    (hnormalize : normalize cg rr.ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
    labeled.nodes.length = labeled.rank.length := by
  have h1 := addLabelNodes_node_length hlabels
  have h2 := congrArg List.length (Labels.addLabelNodes_metadata hlabels).2.1
  have h3 := (normalize_node_rank_alignment hnormalize).1
  omega

private theorem xsds_coord_rank_eq {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run}
    (hcoord : coordinateGraphX P exact labeled = run.coordinateProper)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {x : Nat} (hx : x < labeled.nodes.length) :
    rk run.coordinateProper.rank x = rk labeled.rank x := by
  have hxr : x < labeled.rank.length := by omega
  have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
    List.getElem?_eq_getElem hxr
  have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
    rw [← hcoord]
    obtain ⟨_, heq⟩ := (coordinateGraphX_anchor_prefix P exact labeled).2
    rw [heq, List.getElem?_append_left hxr]
    exact hlab
  simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

/-- Exact coordinate `BordersWellFormed` for one exact run, via the public
run bundle and the shared border-extension composition. -/
private theorem xsds_coord_BWF {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready

/-- An executed exact proper dummy has the same record in the exact
coordinate graph (copy of `X_proper_to_coordinate_dummy`, with the plain
border fact replaced by the exact `BordersWellFormed` above). -/
private theorem xsds_coord_dummy {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hBWF : OrderImpl.BordersWellFormed run.coordinateProper)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
      cn.node.border = pn.node.border ∧ cn.node.clusterPath = pn.node.clusterPath ∧
      cn.node.h = pn.node.h := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
  have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
    (proxyWidths_rel hprox).2.2.1
  have hiC : i < run.coordinateProper.nodes.length := by
    have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
    omega
  obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
    ⟨_, List.getElem?_eq_getElem hiC⟩
  obtain ⟨nd', hnd', hddum, _, _⟩ :=
    (proxyWidths_rel hprox).2.2.2.2.1 i cn hcn
  have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
  have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
  have hbord0 : cn.node.border = 0 := hBWF.2.2 i cn hcn hcnDum
  have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
    rw [hbord0]; decide
  obtain ⟨hsame, _⟩ := (proxyWidths_rel hprox).2.2.2.2.2 i cn hcn hnp
  have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
  exact ⟨cn, hcn, hcnDum, by rw [hcnEq], by rw [hcnEq], by rw [hcnEq]⟩

/-- Exact chain rank positions (copy of `X_normalize_chain_rank_positions`). -/
private theorem xsds_normalize_chain_positions {graph : Graph} {ranks : List Int}
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

/-- Exact bordered-graph node classification (copy of `X_coordinateGraph0_lookupX`). -/
private theorem xsds_coord0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := sizeProperPortsX_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification (copy of `X_coordinateGraph_lookupX`). -/
private theorem xsds_coord_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup (clearProxyExtents
    (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact p))
      P.clusterBorderW)) h
  rcases xsds_coord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · have hpath : m.dummy = false → nd.node.clusterPath = m.node.clusterPath := by
      intro hf
      have hfalse : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd hfalse]
      exact h3
    have hh0 : (nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0 := by
      intro hbd
      rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
    exact Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, hpath, hh0⟩
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · have hpath3 : q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath := by
      intro hf
      have hfalse : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd hfalse]
      exact h3
    exact Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, hpath3⟩)
/-- Tiny list facts (copies of `Xb_filter_ne_nil`, `X_le_foldr_max`,
`Xb_dropLast_is_prefix`). -/
private theorem xsds_filter_ne_nil {α : Type} {l : List α}
    (h : l.isEmpty = false) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

private theorem xsds_le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

private theorem xsds_dropLast_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

/-- Exact prepared nodes keep their labeled cluster path (copy of `X_prepared_path_eq`). -/
private theorem xsds_prepared_path {P : Params} {exact : List Nat} {labeled : Proper}
    {j : Nat} {pn : ProperNode}
    (hlab : labeled.nodes[j]? = some pn) :
    ∃ qn, (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[j]? =
      some qn ∧ qn.node.clusterPath = pn.node.clusterPath := by
  have hj : j < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hlab).1
  have hlen1 : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
    simp [sizeProperPortsX]
  have hs1 := sizeProperPortsX_key P exact labeled j
  rw [hlab] at hs1
  obtain ⟨m1, hm1, htrip⟩ : ∃ m1, (sizeProperPortsX P exact labeled).nodes[j]? = some m1 ∧
      (m1.dummy, m1.node.border, m1.node.clusterPath) =
        (pn.dummy, pn.node.border, pn.node.clusterPath) := by
    cases hs : (sizeProperPortsX P exact labeled).nodes[j]? with
    | none => simp [hs] at hs1
    | some m1 =>
      simp only [hs, Option.map_some, Option.some.injEq] at hs1
      exact ⟨m1, rfl, hs1⟩
  have hp1 : m1.node.clusterPath = pn.node.clusterPath := by
    have h3 := congrArg (fun t : Bool × Int × List Nat => t.2.2) htrip
    simpa using h3
  have hm2 : (titleReservations (sizeProperPortsX P exact labeled)).nodes[j]? =
      some (titleF m1) := by
    have hJ : j < ((sizeProperPortsX P exact labeled).nodes.map titleF).length := by
      rw [List.length_map, hlen1]; exact hj
    rw [titleReservations_nodes, List.getElem?_append_left hJ, List.getElem?_map, hm1,
      Option.map_some]
  have hp2 : (titleF m1).node.clusterPath = pn.node.clusterPath := by
    rw [(titleF_keys m1).2.2.1]; exact hp1
  have hlen2 : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
      (sizeProperPortsX P exact labeled).nodes.length +
        ((titleNodes (sizeProperPortsX P exact labeled)).map copyF).length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
  have hj2 : j < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    omega
  obtain ⟨extra, hx, _⟩ :=
    addClusterBorders_extra (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hm3 : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[j]? =
      (titleReservations (sizeProperPortsX P exact labeled)).nodes[j]? := by
    rw [hx]; exact List.getElem?_append_left hj2
  have hm4 : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[j]? =
      some (clearF (titleF m1)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hm3, hm2, Option.map_some]
  have hp4 : (clearF (titleF m1)).node.clusterPath = pn.node.clusterPath := by
    rw [(clearF_keys (titleF m1)).2.2.1]; exact hp2
  exact ⟨_, hm4, hp4⟩

/-- Exact dummy path chain source (copy of `X_dummy_path_chain_source`). -/
private theorem xsds_chain_fetch {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v owner : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hdummy : node.dummy = true) (howner : owner ∈ node.node.clusterPath) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper)
      (index : Nat) (edge : Edge) (chain : List Nat) (position : Nat),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      cg.edges[index]? = some edge ∧ labeled.chains[index]? = some chain ∧
      chain[position]? = some v ∧ chain.head? = some edge.tail ∧
      chain.getLast? = some edge.head ∧
      rk labeled.rank v = rk labeled.rank edge.tail + (position : Int) ∧
      let prepared := clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
      prepared.chains.find? (fun members => members.contains v) = some chain ∧
      owner ∈ (prepared.nodes.getD (chain.headD v) default).node.clusterPath ∧
      owner ∈ (prepared.nodes.getD (chain.getLastD v) default).node.clusterPath := by
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, _⟩ :=
    X_componentRun_ranked_source hrun
  have hpositions : ∀ (index : Nat) (edge : Edge) (chain : List Nat),
      cg.edges[index]? = some edge → labeled.chains[index]? = some chain →
      ∀ position (hposition : position < chain.length),
        rk labeled.rank (chain[position]'hposition) =
          rk labeled.rank edge.tail + (position : Int) := by
    intro index edge chain hedge hchain position hposition
    have metadata := Labels.addLabelNodes_metadata hlabels
    rw [metadata.2.2.1] at hchain
    rw [metadata.2.1]
    exact xsds_normalize_chain_positions hnormalize hedge hchain position hposition
  let prepared := clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
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
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).2.1
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

/-- Strict chain straddle for executed exact proper dummies (copy of
`dummy_chain_strict` through the exact source lemmas). -/
private theorem xsds_chain_strict {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hdummy : (run.proper.nodes.getD i default).dummy = true)
    {owner : Nat} (howner : owner ∈ (run.proper.nodes.getD i default).node.clusterPath) :
    ∃ (index : Nat) (edge : Edge),
      (componentCandidate graph comp candidate).edges[index]? = some edge ∧
      edge.tail ≠ edge.head ∧
      edge.tail < (componentCandidate graph comp candidate).nodes.length ∧
      edge.head < (componentCandidate graph comp candidate).nodes.length ∧
      rk run.coordinateProper.rank edge.tail < rk run.coordinateProper.rank i ∧
      rk run.coordinateProper.rank i < rk run.coordinateProper.rank edge.head ∧
      ∃ (nA nB : Node),
        (componentCandidate graph comp candidate).nodes[edge.tail]? = some nA ∧
        (componentCandidate graph comp candidate).nodes[edge.head]? = some nB ∧
        nA.clusterPath.contains owner = true ∧ nB.clusterPath.contains owner = true := by
  have hp : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, hi]
  have hBWF := xsds_coord_BWF h0 h hcomp hrun
  obtain ⟨cn, hcn, hcnDum, _, hcnPath, _⟩ := xsds_coord_dummy hrun hBWF hp hdummy
  have hownerC : owner ∈ cn.node.clusterPath := by rw [hcnPath]; exact howner
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordRun, _⟩ :=
    X_componentRun_ranked_source hrun
  have hpositions : ∀ (index : Nat) (edge : Edge) (chain : List Nat),
      (componentCandidate graph comp candidate).edges[index]? = some edge →
      labeled.chains[index]? = some chain →
      ∀ position (hposition : position < chain.length),
        rk labeled.rank (chain[position]'hposition) =
          rk labeled.rank edge.tail + (position : Int) := by
    intro index edge chain hedge hchain position hposition
    have metadata := Labels.addLabelNodes_metadata hlabels
    rw [metadata.2.2.1] at hchain
    rw [metadata.2.1]
    exact xsds_normalize_chain_positions hnormalize hedge hchain position hposition
  have hK : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hnormalize) hlabels
  obtain ⟨rrC, normC, labC, index, edge, chain, position,
      hrrC, hnormC, hlabC, hcoordC, hedge, hchainC, hpos, hhead, hlast, _hrankC,
      _hfind, hleftC, hrightC⟩ :=
    xsds_chain_fetch hrun hcn hcnDum hownerC
  have e1 : rr = rrC := Except.ok.inj (hrr.symm.trans hrrC)
  subst e1
  have e2 : normalized = normC := Except.ok.inj (hnormalize.symm.trans hnormC)
  subst e2
  have e3 : labeled = labC := Except.ok.inj (hlabels.symm.trans hlabC)
  subst e3
  have hindex : index < (componentCandidate graph comp candidate).edges.length :=
    (List.getElem?_eq_some_iff.mp hedge).1
  have hwf : (componentCandidate graph comp candidate).wellformed = true :=
    (normalize_node_rank_alignment hnormalize).2
  have hedgeMem : edge ∈ (componentCandidate graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨htailLt, hheadLt, _⟩ := RankImpl.wellformed_spec hwf edge hedgeMem
  have hchainsEq : labeled.chains = normalized.chains :=
    (Labels.addLabelNodes_metadata hlabels).2.2.1
  have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
  have hne : edge.tail ≠ edge.head := by
    intro heq
    have hif := hfact.2
    simp only [heq, ↓reduceIte] at hif
    rw [← hchainsEq] at hif
    have hempty : chain = [] := Option.some.inj (hchainC.symm.trans hif)
    rw [hempty] at hpos
    simp at hpos
  have hcoordV0 : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
    rw [hcoordRun]; exact hcn
  obtain ⟨mV, hmvV, hdmV⟩ : ∃ m, labeled.nodes[i]? = some m ∧ m.dummy = true := by
    rcases xsds_coord_lookup P exact labeled hcoordV0 with
      ⟨m, hm, h1, _, _, _⟩ | ⟨h1, _⟩ | ⟨tq, q, hq, _, h1, _, _⟩
    · exact ⟨m, hm, h1.symm.trans hcnDum⟩
    · rw [h1] at hcnDum; exact absurd hcnDum (by decide)
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp2 : labeled.nodes[q.2]? with
      | none => simp [hp2] at hk
      | some mp =>
        simp only [hp2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp2 with ⟨n, _, hmd, _, _⟩ | ⟨_, hbB, _⟩
        · rw [h1, hk1, hmd] at hcnDum; exact absurd hcnDum (by decide)
        · rw [hk2] at hbq; rw [hbB] at hbq; exact absurd hbq (by decide)
  obtain ⟨nA, hnA⟩ : ∃ n, (componentCandidate graph comp candidate).nodes[edge.tail]? =
      some n := ⟨_, List.getElem?_eq_getElem htailLt⟩
  obtain ⟨nB, hnB⟩ : ∃ n, (componentCandidate graph comp candidate).nodes[edge.head]? =
      some n := ⟨_, List.getElem?_eq_getElem hheadLt⟩
  have hlabT : labeled.nodes[edge.tail]? = some ⟨nA, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnA
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  have hlabH : labeled.nodes[edge.head]? = some ⟨nB, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnB
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  have hposLen : position < chain.length := (List.getElem?_eq_some_iff.mp hpos).1
  have hposNe0 : position ≠ 0 := by
    intro hz
    have hiv : chain[0]? = some i := by
      have h := hpos
      rw [hz] at h
      exact h
    have h0tail : chain[0]? = some edge.tail := by
      cases chain with
      | nil => simp at hhead
      | cons a as => exact hhead
    have hiEq : i = edge.tail := Option.some.inj (hiv.symm.trans h0tail)
    have hmEq : mV = ⟨nA, false, none, false⟩ := by
      rw [hiEq] at hmvV
      exact Option.some.inj (hmvV.symm.trans hlabT)
    rw [hmEq] at hdmV
    exact Bool.false_ne_true hdmV
  have hlastElem : chain[chain.length - 1]? = some edge.head := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hlastLt : chain.length - 1 < chain.length :=
    (List.getElem?_eq_some_iff.mp hlastElem).1
  have hposNeLast : position ≠ chain.length - 1 := by
    intro hz
    have hiv : chain[chain.length - 1]? = some i := by
      have h := hpos
      rw [hz] at h
      exact h
    have hiEq : i = edge.head := Option.some.inj (hiv.symm.trans hlastElem)
    have hmEq : mV = ⟨nB, false, none, false⟩ := by
      rw [hiEq] at hmvV
      exact Option.some.inj (hmvV.symm.trans hlabH)
    rw [hmEq] at hdmV
    exact Bool.false_ne_true hdmV
  have hposLtLast : position < chain.length - 1 := by omega
  have hpositionValue : chain[position]'hposLen = i :=
    Option.some.inj ((List.getElem?_eq_getElem hposLen).symm.trans hpos)
  have hlastValue : chain[chain.length - 1]'hlastLt = edge.head :=
    Option.some.inj ((List.getElem?_eq_getElem hlastLt).symm.trans hlastElem)
  have hposBase := hpositions index edge chain hedge hchainC position hposLen
  have hlastBase := hpositions index edge chain hedge hchainC (chain.length - 1) hlastLt
  have hrankV : rk labeled.rank i = rk labeled.rank edge.tail + (position : Int) := by
    rw [← hpositionValue]; exact hposBase
  have hrankH : rk labeled.rank edge.head =
      rk labeled.rank edge.tail + ((chain.length - 1 : Nat) : Int) := by
    rw [← hlastValue]; exact hlastBase
  have hltLab1 : rk labeled.rank edge.tail < rk labeled.rank i := by omega
  have hltLab2 : rk labeled.rank i < rk labeled.rank edge.head := by omega
  have hlenN := normalize_nodes_length_le hnormalize
  have hlenL : normalized.nodes.length = labeled.nodes.length :=
    addLabelNodes_node_length hlabels
  have htailL : edge.tail < labeled.nodes.length := by omega
  have hheadL : edge.head < labeled.nodes.length := by omega
  have haligned := xsds_labeled_aligned hnormalize hlabels
  have hiL : i < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hmvV).1
  have hcTail : rk run.coordinateProper.rank edge.tail = rk labeled.rank edge.tail :=
    xsds_coord_rank_eq hcoordRun haligned htailL
  have hcHead : rk run.coordinateProper.rank edge.head = rk labeled.rank edge.head :=
    xsds_coord_rank_eq hcoordRun haligned hheadL
  have hcI : rk run.coordinateProper.rank i = rk labeled.rank i :=
    xsds_coord_rank_eq hcoordRun haligned hiL
  have hltC1 : rk run.coordinateProper.rank edge.tail < rk run.coordinateProper.rank i := by
    rw [hcTail, hcI]; exact hltLab1
  have hltC2 : rk run.coordinateProper.rank i < rk run.coordinateProper.rank edge.head := by
    rw [hcI, hcHead]; exact hltLab2
  obtain ⟨qT, hqT, hpT⟩ := xsds_prepared_path hlabT
  obtain ⟨qH, hqH, hpH⟩ := xsds_prepared_path hlabH
  have hheadD : chain.headD i = edge.tail := by
    cases hcchain : chain with
    | nil => simp [hcchain] at hhead
    | cons a as =>
      simp only [List.headD]
      simpa [hcchain] using hhead
  have hlastD : chain.getLastD i = edge.head := by
    rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
  have hgetDT : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes.getD
      edge.tail default = qT := by
    rw [List.getD_eq_getElem?_getD, hqT, Option.getD_some]
  have hgetDH : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes.getD
      edge.head default = qH := by
    rw [List.getD_eq_getElem?_getD, hqH, Option.getD_some]
  rw [hheadD, hgetDT] at hleftC
  rw [hlastD, hgetDH] at hrightC
  have hcontA : nA.clusterPath.contains owner = true := by
    rw [hpT] at hleftC
    exact List.contains_iff_mem.mpr hleftC
  have hcontB : nB.clusterPath.contains owner = true := by
    rw [hpH] at hrightC
    exact List.contains_iff_mem.mpr hrightC
  exact ⟨index, edge, hedge, hne, htailLt, hheadLt, hltC1, hltC2,
    nA, nB, hnA, hnB, hcontA, hcontB⟩

/-- Strict top rank for exact dummies (copy of `dummyTopRankStrict` through
`xsds_chain_strict` and the closed exact top closure). -/
private theorem xsds_topRank_strict {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hbordV : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
    {d : Nat} (hd : d < run.proper.nodes.length)
    (hpath : (run.proper.nodes.getD d default).node.clusterPath.contains nd.decl = true)
    (hdum : (run.proper.nodes.getD d default).dummy = true) :
    rk run.coordinateProper.rank v < rk run.coordinateProper.rank d := by
  have howner : nd.decl ∈ (run.proper.nodes.getD d default).node.clusterPath :=
    List.contains_iff_mem.mp hpath
  obtain ⟨index, edge, hedge, hne, htailLt, hheadLt, hlt1, hlt2,
      nA, nB, hnA, hnB, hcontA, hcontB⟩ :=
    xsds_chain_strict h0 h hcomp hrun hd hdum howner
  obtain ⟨rr, hrr, hclose⟩ :=
    X_GroupTopSubtreeRankCg_holds h0 h hlines hwf hframed hcomp hrun hvGet hbordV
  have hgetDA : (componentCandidate graph comp candidate).nodes.getD edge.tail default = nA := by
    simp [List.getD_eq_getElem?_getD, hnA]
  have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD edge.tail
      default).clusterPath.contains nd.decl = true := by
    rw [hgetDA]; exact hcontA
  have hleTail : rk rr.ranks v ≤ rk rr.ranks edge.tail :=
    hclose edge.tail htailLt hgetDContains
  obtain ⟨rrS, _, hrrS, hcS, _, _, _, hranksS, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrrEq : rr = rrS := Except.ok.inj (hrr.symm.trans hrrS)
  subst hrrEq
  have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v :=
    xsds_prepared_rk hrr hcS hranksS hvcg
  have hTcoord : rk run.coordinateProper.rank edge.tail = rk rr.ranks edge.tail :=
    xsds_prepared_rk hrr hcS hranksS htailLt
  omega

/-- Original member rank bound by fuel induction (copy of `Xb_origRankLe`
through the exact source lemmas). -/
private theorem xsds_origRankLe {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds) :
    ∀ {idx : Nat} {n : Node},
    (componentCandidate graph comp candidate).nodes[idx]? = some n →
    n.clusterPath.contains ndT.decl = true →
    rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hfindV : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndV.decl) = some (ndV, v) :=
    X_bottom_find_eq h0 h hcomp hvGet hbordV
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
    rw [← hdecl]; exact hfindV
  have htopOuter : ((ndT, t) : Node × Nat) ∈
      (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htGet
  have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := xsds_prepared_rk hrr hc hranks (List.getElem?_eq_some_iff.mp hvGet).1
    exact h1
  let cg := componentCandidate graph comp candidate
  let maxLen := ((cg.nodes.filter fun n => n.border == -2).map
    (fun n => n.clusterPath.length)).foldr max 0
  have hbound : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath.length ≤ maxLen := by
    intro index node hnode hgroup
    have hmem : node ∈ cg.nodes.filter (fun n => n.border == -2) :=
      List.mem_filter.mpr ⟨List.mem_of_getElem? hnode, by simp [hgroup]⟩
    have hmap : node.clusterPath.length ∈
        (cg.nodes.filter fun n => n.border == -2).map
          (fun n => n.clusterPath.length) :=
      List.mem_map_of_mem hmem
    exact xsds_le_foldr_max hmap
  have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath ≠ [] := by
    intro index node hnode hgroup hnil
    exact (X_componentCandidate_marker_shape h0 h hnode).2 hgroup hnil
  have main : ∀ fuel idx n, cg.nodes[idx]? = some n →
      n.clusterPath.contains ndT.decl = true →
      maxLen - n.clusterPath.length = fuel → rk rr.ranks idx ≤ rk rr.ranks v := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro idx n hidx hcontains hfuel
      rcases (X_componentCandidate_marker_shape h0 h hidx).1 with hplain | hgroup | hbottom
      · have hinterval := ranked_compound_member_interval hrr htopOuter hbordT
          hbotFindOuter (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hplain hcontains
        have hle : rk rr.ranks idx + 1 ≤ rk rr.ranks v := hinterval.2
        omega
      · obtain ⟨rrB, labeledB, bottomTB, hrrB, hcB, hkB, hreadyB, hrecordsB, hranksB,
            htitledB, hfindB⟩ :=
          X_group_bottom_source h0 h hcomp hrun hidx hgroup
        obtain ⟨origB, horigB, hborderB, hpathB, hrecordB, hfindCB⟩ :=
          X_bottom_constraint_source h0 h hkB hrecordsB hidx hgroup hfindB
        have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
          rw [hpathB]; exact hcontains
        have resolveB : rk rr.ranks bottomTB.2 ≤ rk rr.ranks v := by
          by_cases hdeq : origB.decl = ndT.decl
          · have hmemB := List.find?_some hfindCB
            simp only [Bool.and_eq_true, beq_iff_eq] at hmemB
            have hndeq : n.decl = ndT.decl := hmemB.2.symm.trans hdeq
            rw [hndeq] at hfindCB
            have heq : (origB, bottomTB.2) = (ndV, v) :=
              Option.some.inj (hfindCB.symm.trans hbotFindOuter)
            have hbv : bottomTB.2 = v := congrArg Prod.snd heq
            rw [hbv]
            exact Int.le_refl _
          · have hleB : rk run.coordinateProper.rank bottomTB.2 ≤
                rk run.coordinateProper.rank v :=
              hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
                horigB hborderB hdeq hpathBmem
            have e1 : rk run.coordinateProper.rank bottomTB.2 =
                rk rr.ranks bottomTB.2 := by
              have h1 := xsds_prepared_rk hrr hc hranks
                (List.getElem?_eq_some_iff.mp horigB).1
              exact h1
            omega
        cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
            entry.1.border == 0 && entry.1.clusterPath.contains n.decl).isEmpty with
        | false =>
          obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
            (xsds_filter_ne_nil hmemCase)
          obtain ⟨hmemberZip, hmemberCond⟩ := List.mem_filter.mp hmember
          obtain ⟨hmemberPlain, hmemberInside⟩ := Bool.and_eq_true_iff.mp hmemberCond
          have hmemberPlain' : member.1.border = 0 := by simpa using hmemberPlain
          have hmemberInside' : member.1.clusterPath.contains n.decl = true := by
            simpa using hmemberInside
          have hinterval := ranked_compound_member_interval hrr
            (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
            hmemberZip hmemberPlain' hmemberInside'
          have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks member.2 := hinterval.1
          have hR : rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottomTB.2 := hinterval.2
          omega
        | true =>
          cases hchildCase : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
              fun entry => entry.1.clusterPath.dropLast == n.clusterPath).isEmpty with
          | false =>
            obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _
              (xsds_filter_ne_nil hchildCase)
            obtain ⟨hchildTop, hchildPathEq⟩ := List.mem_filter.mp hchildMem
            obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
            have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
            have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
            obtain ⟨rrC, labeledC, bottomTC, hrrC, hcC, hkC, hreadyC, hrecordsC, hranksC,
                htitledC, hfindC⟩ :=
              X_group_bottom_source h0 h hcomp hrun hchildIndex hchildGroup'
            obtain ⟨childOriginal, horigC, hborderC, hpathC, hrecordC, hchildFind'⟩ :=
              X_bottom_constraint_source h0 h hkC hrecordsC hchildIndex
                hchildGroup' hfindC
            have hchildPair : cg.nodes.zipIdx.find? (fun entry =>
                entry.1.border == 2 && entry.1.decl == child.1.decl) =
                some (childOriginal, bottomTC.2) := hchildFind'
            have hpathEq : child.1.clusterPath.dropLast = n.clusterPath := by
              simpa using hchildPathEq
            have hdirect := ranked_compound_child_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
              hchildZip hchildGroup' hpathEq hchildPair
            have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks child.2 := hdirect.1
            have hne : n.clusterPath ≠ [] := hnonempty idx n hidx hgroup
            have hchildNonEmpty : child.1.clusterPath ≠ [] := by
              intro hempty
              rw [hempty, List.dropLast_nil] at hpathEq
              exact hne hpathEq.symm
            have hlenC : child.1.clusterPath.length = n.clusterPath.length + 1 := by
              rw [← hpathEq, List.length_dropLast]
              have hchildLen := List.length_pos_iff.mpr hchildNonEmpty
              omega
            have hboundChild := hbound child.2 child.1 hchildIndex hchildGroup'
            have hpos : 0 < fuel := by omega
            have hfuelChild : maxLen - child.1.clusterPath.length = fuel - 1 := by omega
            have hcontainsC : child.1.clusterPath.contains ndT.decl = true := by
              have hsub : n.clusterPath <+: child.1.clusterPath := by
                rw [← hpathEq]; exact xsds_dropLast_prefix _
              have hmemN : ndT.decl ∈ n.clusterPath :=
                List.contains_iff_mem.mp hcontains
              have hmemC : ndT.decl ∈ child.1.clusterPath :=
                List.Sublist.mem hmemN (List.IsPrefix.sublist hsub)
              exact List.contains_iff_mem.mpr hmemC
            have hih := ih (fuel - 1) (by omega) child.2 child.1 hchildIndex
              hcontainsC hfuelChild
            omega
          | true =>
            have hempty := ranked_empty_group_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB hmemCase hchildCase
            have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks bottomTB.2 := hempty
            omega
      · by_cases hdeq : n.decl = ndT.decl
        · have hfindEq : (componentCandidate graph comp candidate).nodes.zipIdx.find?
              (fun entry => entry.1.border == 2 && entry.1.decl == n.decl) =
              some (n, idx) :=
            X_bottom_find_eq h0 h hcomp hidx hbottom
          rw [hdeq] at hfindEq
          have heq : (n, idx) = (ndV, v) :=
            Option.some.inj (hfindEq.symm.trans hbotFindOuter)
          have hiv : idx = v := congrArg Prod.snd heq
          rw [hiv]
          exact Int.le_refl _
        · have hleB : rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v :=
            hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
              hidx hbottom hdeq hcontains
          have e1 : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
            have h1 := xsds_prepared_rk hrr hc hranks
              (List.getElem?_eq_some_iff.mp hidx).1
            exact h1
          omega
  intro idx n hidx hcontains
  have hrr_le := main (maxLen - n.clusterPath.length) idx n hidx hcontains rfl
  have eI : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
    have h1 := xsds_prepared_rk hrr hc hranks
      (List.getElem?_eq_some_iff.mp hidx).1
    exact h1
  omega

/-- Strict bottom rank for exact dummies (copy of `dummyBottomRankStrict`
through `xsds_chain_strict` and `xsds_origRankLe`). -/
private theorem xsds_bottomRank_strict {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    {d : Nat} (hd : d < run.proper.nodes.length)
    (hpath : (run.proper.nodes.getD d default).node.clusterPath.contains ndT.decl = true)
    (hdum : (run.proper.nodes.getD d default).dummy = true) :
    rk run.coordinateProper.rank d < rk run.coordinateProper.rank v := by
  have howner : ndT.decl ∈ (run.proper.nodes.getD d default).node.clusterPath :=
    List.contains_iff_mem.mp hpath
  obtain ⟨index, edge, hedge, hne, htailLt, hheadLt, hlt1, hlt2,
      nA, nB, hnA, hnB, hcontA, hcontB⟩ :=
    xsds_chain_strict h0 h hcomp hrun hd hdum howner
  have hnest : Xb_NestedExact exactIds := Xb_NestedExact_holds exactIds
  have hle := xsds_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet
    hbordV hbordT hdecl hnest hnB hcontB
  omega

/-- Exact proxy span record (copy of `componentRun_proxy_interval` through
`componentRunX_spec`). -/
private theorem xsds_proxy_interval {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
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
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = q0.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

/-- Exact top proper record (copy of `proper_top_proper_clusterPath_copy`). -/
private theorem xsds_top_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath := by
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    xsds_proxy_interval hrun hcoord (Or.inl hb)
  exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

/-- Exact non-proxy record (copy of `componentRun_nonproxy_record`). -/
private theorem xsds_nonproxy {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = q0.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Exact border record (copy of `componentRun_border_record`). -/
private theorem xsds_border_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact top coordinate record (copy of `proper_top_coordinate_record_copy`
through `X_coordinateGraph_marker_record` and the run bundle). -/
private theorem xsds_top_coord {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = -2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact)
    hrec (Or.inl hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inl hgroup))

/-- Exact bottom coordinate record (copy of `proper_bottom_coordinate_record_copy`). -/
private theorem xsds_bottom_coord {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact)
    hrec (Or.inr hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))

/-- Exact bottom proper node (copy of `proper_bottom_proper_node_copy`). -/
private theorem xsds_bottom_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    xsds_proxy_interval hrun hcoord (Or.inr hb)
  refine ⟨_, hproper, rfl, ?_⟩
  simp only [RouteImpl.nodeH, hproper]
  exact hcoordH



/-- Exact pre-reserve coordinates: unfold one `componentRunX` to expose the
rank-axis output (copy of `xcsbb_run_pre`, `ExactCaptionSelfBottomProof.lean:475`). -/
private theorem xsds_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (y_pre top_pre ys_pre : List Int),
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
      proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
      reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
        .ok (run.ys, run.top) ∧
      run.coordinateYs = y_pre := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨routed, hprojection, h⟩ := bind_ok h
  obtain ⟨lanes, hr, h⟩ := bind_ok h
  obtain ⟨yt, hy, h⟩ := bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  cases yt with
  | mk y top =>
    exact ⟨y, top, _, hy, rfl, hres, rfl⟩
private theorem xsds_foldl_preserves (step : List Int → (Node × Nat) → List Int)
    (topLen : Nat)
    (hstep : ∀ acc q, acc.length = topLen → (∀ i, 0 ≤ acc.getD i 0) →
      (step acc q).length = topLen ∧ ∀ i, 0 ≤ (step acc q).getD i 0)
    (xs : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = topLen) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (xs.foldl step acc).length = topLen ∧
      ∀ i, 0 ≤ (xs.foldl step acc).getD i 0 := by
  induction xs generalizing acc with
  | nil => exact ⟨hlen, hpos⟩
  | cons q xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hlen', hpos'⟩ := hstep acc q hlen hpos
    exact ih _ hlen' hpos'

private theorem xsds_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
    (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (acc.set m (max (acc.getD m 0) needed)).length = acc.length ∧
      ∀ i, 0 ≤ (acc.set m (max (acc.getD m 0) needed)).getD i 0 := by
  refine ⟨List.length_set, ?_⟩
  intro i
  have hset : (acc.set m (max (acc.getD m 0) needed))[i]? =
      if m = i then if m < acc.length then some (max (acc.getD m 0) needed) else none
      else acc[i]? :=
    List.getElem?_set
  rw [List.getD_eq_getElem?_getD, hset]
  by_cases heq : m = i
  · subst heq
    by_cases hlt : m < acc.length
    · have h0 : 0 ≤ acc[m] := by
        have h := hpos m
        simpa [hlt] using h
      simp [hlt]
      exact Int.le_trans h0 (Int.le_max_left _ _)
    · simp [hlt]
  · have hne : m ≠ i := heq
    simp [hne]
    exact hpos i

private theorem xsds_extra_step_concrete (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    (acc : List Int) (q : Node × Nat)
    (hlen : acc.length = top.length) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
  by_cases h1 : (!exact.contains q.1.decl) = true
  · rw [ite_eq_left h1]
    exact ⟨hlen, hpos⟩
  · rw [ite_eq_right h1]
    by_cases h2 : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
    · rw [ite_eq_left h2]
      exact ⟨hlen, hpos⟩
    · rw [ite_eq_right h2]
      obtain ⟨hlen', hpos'⟩ := xsds_extra_step_preserves acc _ _ hpos
      exact ⟨hlen'.trans hlen, hpos'⟩

private theorem xsds_extra_fold (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
    let extra := cg.nodes.zipIdx.foldl (fun (acc : List Int) (q : Node × Nat) =>
      if !exact.contains q.1.decl then acc
      else
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        if sizes.isEmpty then acc
        else
          let rank := (p.rank.getD q.2 0).toNat
          let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
          let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
            heights.getD rank 0
          acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))
    extra.length = top.length ∧ ∀ i, 0 ≤ extra.getD i 0 := by
  have hbase : (List.replicate top.length (0 : Int)).length = top.length := by simp
  have hbasePos : ∀ i, 0 ≤ (List.replicate top.length (0 : Int)).getD i 0 := by
    intro i
    by_cases h : i < top.length
    · have hg : (List.replicate top.length (0 : Int))[i]? = some 0 := by
        rw [List.getElem?_eq_getElem (by simpa using h)]
        simp
      rw [List.getD_eq_getElem?_getD, hg]
      simp
    · have hg : (List.replicate top.length (0 : Int))[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt h)
      rw [List.getD_eq_getElem?_getD, hg]
      simp
  have hstep : ∀ (acc : List Int) (q : Node × Nat), acc.length = top.length →
    (∀ i, 0 ≤ acc.getD i 0) →
      (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
            Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
            top.getD ((p.rank.getD q.2 0).toNat) 0 -
            heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
              Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
              top.getD ((p.rank.getD q.2 0).toNat) 0 -
              heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
    intro acc q hlen hpos
    exact xsds_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
  have h := xsds_foldl_preserves (fun (acc : List Int) (q : Node × Nat) =>
    if !exact.contains q.1.decl then acc
    else
      let sizes := loopSizes cg.edges labels q.2 cg.slot
      if sizes.isEmpty then acc
      else
        let rank := (p.rank.getD q.2 0).toNat
        let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
        let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
          heights.getD rank 0
        acc.set rank (max (acc.getD rank 0) needed)) top.length hstep
    cg.nodes.zipIdx (List.replicate top.length (0 : Int)) hbase hbasePos
  exact h

private theorem xsds_prefix_length (es : List Int) (s : Int) (out : List Int) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
      out.length + es.length := by
  induction es generalizing s out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

private theorem xsds_prefix_pairwise (es : List Int) (hpos : ∀ e ∈ es, 0 ≤ e)
    (s : Int) (out : List Int)
    (hm : out.Pairwise (· ≤ ·)) (hle : ∀ x ∈ out, x ≤ s) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).Pairwise
      (· ≤ ·) := by
  induction es generalizing s out with
  | nil => simpa
  | cons e es ih =>
    have he : 0 ≤ e := hpos e List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih
    · intro e' he'
      exact hpos e' (List.mem_cons_of_mem e he')
    · apply List.pairwise_append.mpr
      refine ⟨hm, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      rw [hy]
      exact hle x hx
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := hle x hx
        omega
      · omega

private theorem xsds_pairwise_getD_le {l : List Int} (hp : l.Pairwise (· ≤ ·))
    {i j : Nat} (hij : i < j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := by omega
  have hgi : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  have hgj : l[j]? = some l[j] := List.getElem?_eq_getElem hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hgi, hgj]
  simp only [Option.getD_some]
  exact hp.rel_getElem_of_lt hi hj hij

private theorem xsds_shift_strict_tops {p : Proper} {layers : List (List Nat)}
    {top : List Int} {extra shifts : List Int} {top' : List Int}
    (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top.getD r' 0)
    (hextraLen : extra.length = top.length)
    (hpos : ∀ e ∈ extra, 0 ≤ e)
    (hshifts : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (htopLen : top.length = layers.length)
    (htop : ∀ (r : Nat), r < top.length → top'.getD r 0 = top.getD r 0 + shifts.getD r 0) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top'.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top'.getD r' 0 := by
  have hshiftsLen : shifts.length = top.length := by
    rw [hshifts, xsds_prefix_length]
    simp [hextraLen]
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hshifts]
    exact xsds_prefix_pairwise extra hpos 0 [] (by simp) (by simp)
  have hmono : ∀ i j, i < j → j < shifts.length →
      shifts.getD i 0 ≤ shifts.getD j 0 :=
    fun i j hij hj => xsds_pairwise_getD_le hpair hij hj
  intro r r' l l' hlt hly hly'
  have hrTop : r < top.length := by
    rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
  have hrTop' : r' < top.length := by
    rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly').1
  have hrShift' : r' < shifts.length := by rw [hshiftsLen]; exact hrTop'
  have e1 := htop r hrTop
  have e1' := htop r' hrTop'
  have hle := hmono r r' hlt hrShift'
  have hd := hdisj r r' l l' hlt hly hly'
  rw [e1, e1']
  omega

private theorem xsds_top_eq {inp : Input} {exactIds : List String}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {top_pre ys_pre : List Int}
    (hreserve : reserveExactRanks cg (exactDecls exactIds inp) labels run.coordinateProper
      run.layers ys_pre top_pre = .ok (run.ys, run.top)) :
    ∀ (r : Nat), r < top_pre.length → run.top.getD r 0 =
      top_pre.getD r 0 +
        ((cg.nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes cg.edges labels q.2 cg.slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 := by
  intro r hr
  have hrZ : r < (top_pre.zipIdx).length := by
    rw [List.length_zipIdx]
    exact hr
  have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
    have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
    simp [List.getElem?_zipIdx, h1]
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htopM, h1⟩ := bind_ok hreserve
  obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
  have hpair := Except.ok.inj h2
  have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
  rw [htopNew_eq] at htopM
  obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
  obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
  have hbeq : b = top_pre[r] +
      ((cg.nodes.zipIdx.foldl
        (fun (acc : List Int) (q : Node × Nat) =>
          if !(exactDecls exactIds inp).contains q.1.decl then acc
          else
            let sizes := loopSizes cg.edges labels q.2 cg.slot
            if sizes.isEmpty then acc
            else
              let rank := (run.coordinateProper.rank.getD q.2 0).toNat
              let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
              let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
              acc.set rank (max (acc.getD rank 0) needed))
        (List.replicate top_pre.length (0 : Int))).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 :=
    Measure.checkedI32_ok hb
  have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
  have e3 : top_pre.getD r 0 = top_pre[r] := by
    rw [List.getD_eq_getElem?_getD, h1]
    rfl
  have e4 : run.top.getD r 0 = b := by
    rw [List.getD_eq_getElem?_getD, hbr]
    rfl
  rw [e4, e3]
  exact hbeq

private theorem xsds_post_strict_gap {P : Params} {exactIds : List String} {inp : Input}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        run.top.getD r' 0 := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := xsds_run_pre hrun
  have hdisjPre : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      top_pre.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        top_pre.getD r' 0 :=
    fun r r' l l' hlt hly hly' => rankAxis_band_top_strict hry r r' l l' hlt hly hly'
  have hextra := xsds_extra_fold cg (exactDecls exactIds inp) labels run.coordinateProper
    ys_pre top_pre
    (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
  have hposM : ∀ e ∈ cg.nodes.zipIdx.foldl
      (fun (acc : List Int) (q : Node × Nat) =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes cg.edges labels q.2 cg.slot
          if sizes.isEmpty then acc
          else
            let rank := (run.coordinateProper.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
            let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
              (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed))
      (List.replicate top_pre.length (0 : Int)), 0 ≤ e := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    have h := hextra.2 i
    rw [List.getD_eq_getElem?_getD, hi] at h
    simp at h
    exact h
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  exact xsds_shift_strict_tops hdisjPre hextra.1 hposM rfl htopLen
    (xsds_top_eq hreserve)

private theorem xsds_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases xsds_coord_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp2 : labeled.nodes[q.2]? with
      | none => simp [hp2] at hk
      | some mp =>
        simp only [hp2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp2 with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

private theorem xsds_rect_mem_frame_hull {cg : Graph} {run : Run} {gpos v : Nat}
    {pn : ProperNode}
    (hv : run.proper.nodes[v]? = some pn)
    (hpath : (cg.nodes.getD gpos default).decl ∈ pn.node.clusterPath) :
    Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD gpos default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  have hmem : (pn, v) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hv
  have hcond : (pn, v).fst.node.clusterPath.contains
      (cg.nodes.getD gpos default).decl = true :=
    List.contains_iff_mem.mpr hpath
  apply List.mem_filterMap.mpr
  refine ⟨(pn, v), hmem, ?_⟩
  rw [hcond]
  simp

private theorem xsds_marker_rect_mem_borders {cg : Graph} {run : Run} {gpos m : Nat}
    {n : ProperNode} {gn : Node}
    (_hg : cg.nodes[gpos]? = some gn)
    (hmem : (n, m) ∈ run.proper.nodes.zipIdx)
    (hb : n.node.border = -1 ∨ n.node.border = 1)
    (hlast : n.node.clusterPath.getLast? = some gn.decl) :
    Labels.rectAt run.proper run.xs run.ys m ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  apply List.mem_filterMap.mpr
  refine ⟨(n, m), hmem, ?_⟩
  have hcond : (((n, m).fst.node.border == -1 || (n, m).fst.node.border == 1) &&
      (n, m).fst.node.clusterPath.getLast? == some gn.decl) = true := by
    rcases hb with hb | hb <;> simp [hb, hlast]
  rw [hcond]
  simp

private theorem xsds_frameRect_horizontal_edges {P : Params} {cg : Graph} {run : Run}
    {gpos : Nat} {gn : Node}
    (hg : cg.nodes[gpos]? = some gn) (hgroup : gn.border = -2) :
    (frameRect P cg run gpos).x =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minX ∧
    (frameRect P cg run gpos).x + (frameRect P cg run gpos).w =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).right := by
  have hget : cg.nodes.getD gpos default = gn := by
    rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  constructor
  · simp only [frameRect, hget, hgroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  · simp only [frameRect, hget, hgroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega

private theorem xsds_topY_strict {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) labels
      orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hlt : rk run.coordinateProper.rank gpos < rk run.coordinateProper.rank d)
    (hgap : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        run.top.getD r' 0) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run gpos).y < (Labels.rectAt run.proper run.xs run.ys d).y := by
  have hindexLt : gpos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  have hdLen : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnd).1
  obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hrouteOk := (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hrouteOk).2.2.2.1
  have hgLen : gpos < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun gpos hindexLt
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
    rw [hnodes]; exact (proxyWidths_rel hprox).2.2.1
  have hCgpos : gpos < run.coordinateProper.nodes.length := by omega
  have hCd : d < run.coordinateProper.nodes.length := by omega
  obtain ⟨tcoord, htcoord, htb, _, htpath, htcoordH⟩ :=
    xsds_top_coord execution.graph0_eq execution.graph_eq hcomp hrun hg hgroup
  obtain ⟨tprop, htprop, htpropP⟩ :=
    xsds_top_proper hrun htcoord htb
  have hdeclT : gn.clusterPath.contains gn.decl = true := by
    obtain ⟨_, _, hpathG⟩ :=
      X_cg_group_box execution.graph0_eq execution.graph_eq hg hgroup
    rw [hpathG]; simp
  have htcontains : tprop.node.clusterPath.contains gn.decl = true := by
    rw [htpropP, htpath]; exact hdeclT
  have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD gpos default =
      gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD
      gpos default).border = -2 := by
    rw [hgroupGet]; exact hgroup
  have htqmem : (tprop, gpos) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htprop
  have htcontains' : (tprop, gpos).1.node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD gpos default).decl =
      true := by
    rw [hgroupGet]; exact htcontains
  have htopLe : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run gpos).y ≤
      (Labels.rectAt run.proper run.xs run.ys gpos).y :=
    (frameRect_member_vertical (P := execution.params)
      (cg := componentCandidate execution.graph comp candidate) (run := run)
      (i := gpos) (q := (tprop, gpos)) hframeGroup htqmem htcontains').1
  obtain ⟨ltT, hlyT, hmemT, hnnT⟩ := hcov gpos hgLen
  obtain ⟨ltD, hlyD, hmemD, hnnD⟩ := hcov d hdLen
  have hrankT : rk run.proper.rank gpos = rk run.coordinateProper.rank gpos :=
    X_proper_rank_eq_local hrun gpos
  have hrankD : rk run.proper.rank d = rk run.coordinateProper.rank d :=
    X_proper_rank_eq_local hrun d
  rw [hrankT] at hlyT hnnT
  rw [hrankD] at hlyD hnnD
  have hTopY : (Labels.rectAt run.proper run.xs run.ys gpos).y = run.ys.getD gpos 0 := rfl
  have hMemY : (Labels.rectAt run.proper run.xs run.ys d).y = run.ys.getD d 0 := rfl
  obtain ⟨hinBand, _⟩ := X_ReserveBands_holds exactIds hrun
  have hrkT : rk run.coordinateProper.rank gpos =
      ((rk run.coordinateProper.rank gpos).toNat : Int) := by omega
  have hrkD : rk run.coordinateProper.rank d =
      ((rk run.coordinateProper.rank d).toNat : Int) := by omega
  have hbandT := (hinBand _ _ _ hlyT hmemT hCgpos hrkT).2
  have hbandDlo := (hinBand _ _ _ hlyD hmemD hCd hrkD).1
  have hnodeHT : CoordsImpl.nodeH run.coordinateProper gpos = 0 := by
    simp only [CoordsImpl.nodeH, htcoord]
    exact htcoordH
  rw [hnodeHT] at hbandT
  have hltTD : (rk run.coordinateProper.rank gpos).toNat <
      (rk run.coordinateProper.rank d).toNat := by omega
  have hgapTD := hgap _ _ _ _ hltTD hlyT hlyD
  omega

private theorem xsds_bottom_marker {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {t : Nat} {ndT : Node}
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordT : ndT.border = -2) :
    ∃ (v : Nat) (ndV : Node),
      (componentCandidate graph comp candidate).nodes[v]? = some ndV ∧
      ndV.border = 2 ∧ ndV.decl = ndT.decl := by
  obtain ⟨_, labeledB, bottom, _, _, hkB, _, hrecordsB, _, _, hfindB⟩ :=
    X_group_bottom_source h0 h hcomp hrun htGet hbordT
  obtain ⟨ndV, hvGet, hbordV, hpathV, _, _⟩ :=
    X_bottom_constraint_source h0 h hkB hrecordsB htGet hbordT hfindB
  obtain ⟨boxT, _, hpathT⟩ := X_cg_group_box h0 h htGet hbordT
  obtain ⟨boxV, _, hpathVbox⟩ := X_cg_bottom_box h0 h hvGet hbordV
  have hdecl : ndV.decl = ndT.decl := by
    have heq : Compound.path inp.boxes boxV ++ [ndV.decl] =
        Compound.path inp.boxes boxT ++ [ndT.decl] := by
      rw [← hpathVbox, hpathV, hpathT]
    have hlast := congrArg List.getLast? heq
    simp at hlast
    exact hlast
  exact ⟨_, _, hvGet, hbordV, hdecl⟩

private theorem xsds_bottom_frame_eq {P : Params} {cg : Graph} {run : Run}
    {gpos : Nat} {gn : Node}
    (hg : cg.nodes[gpos]? = some gn) (hgroup : gn.border = -2) :
    (frameRect P cg run gpos).y + (frameRect P cg run gpos).h =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom := by
  have hgroupGet : cg.nodes.getD gpos default = gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  simp only [frameRect, hgroupGet, hgroup,
    show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  change (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
    if q.1.node.clusterPath.contains gn.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none) []).minY +
    ((boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains gn.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none) []).bottom - (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains gn.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none) []).minY) = _
  omega

private theorem xsds_bottom_hull_mem {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate graph comp candidate).nodes[gpos]? = some gn)
    (_hgroup : gn.border = -2)
    {v : Nat} {ndV : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (hbordV : ndV.border = 2) (hdecl : ndV.decl = gn.decl) :
    Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  obtain ⟨bcoord, hbcoord, hbb, _, hpathB, hcoordH⟩ :=
    xsds_bottom_coord h0 h hcomp hrun hvGet hbordV
  obtain ⟨bprop, hbprop, hpathProp, _⟩ :=
    xsds_bottom_proper hrun hbcoord hbb hcoordH
  obtain ⟨_, _, hpathVbox⟩ := X_cg_bottom_box h0 h hvGet hbordV
  have hbcontains : bprop.node.clusterPath.contains gn.decl = true := by
    rw [hpathProp, hpathB, hpathVbox, hdecl]; simp
  have hgroupGet : (componentCandidate graph comp candidate).nodes.getD gpos default =
      gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  have hpath' : ((componentCandidate graph comp candidate).nodes.getD gpos default).decl ∈
      bprop.node.clusterPath := by
    rw [hgroupGet]; exact List.contains_iff_mem.mp hbcontains
  rw [← hgroupGet]
  exact xsds_rect_mem_frame_hull hbprop hpath'

private theorem xsds_bottomY_strict {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) labels
      orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hdum : nd.dummy = true) (_hpath : gn.decl ∈ nd.node.clusterPath)
    {v : Nat} {ndV : Node}
    (hvGet : (componentCandidate execution.graph comp candidate).nodes[v]? = some ndV)
    (hbordV : ndV.border = 2) (hdecl : ndV.decl = gn.decl)
    (hlt : rk run.coordinateProper.rank d < rk run.coordinateProper.rank v)
    (hgap : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        run.top.getD r' 0) :
    (Labels.rectAt run.proper run.xs run.ys d).y +
      (Labels.rectAt run.proper run.xs run.ys d).h <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run gpos).y +
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run gpos).h := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hrouteOk := (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hrouteOk).2.2.2.1
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
    rw [hnodes]; exact (proxyWidths_rel hprox).2.2.1
  have hdLen : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnd).1
  have hvLen : v < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun v
      (List.getElem?_eq_some_iff.mp hvGet).1
  obtain ⟨ltD, hlyD, hmemD, hnnD⟩ :=
    hcov d ((List.getElem?_eq_some_iff.mp hnd).1)
  obtain ⟨ltB, hlyB, hmemB, hnnB⟩ :=
    hcov v (componentRunX_original_nodes_covered hrun v
      (List.getElem?_eq_some_iff.mp hvGet).1)
  have hrankD : rk run.proper.rank d = rk run.coordinateProper.rank d :=
    X_proper_rank_eq_local hrun d
  have hrankB : rk run.proper.rank v = rk run.coordinateProper.rank v :=
    X_proper_rank_eq_local hrun v
  rw [hrankD] at hlyD hnnD
  rw [hrankB] at hlyB hnnB
  have hrkD : rk run.coordinateProper.rank d =
      ((rk run.coordinateProper.rank d).toNat : Int) := by omega
  have hrkB : rk run.coordinateProper.rank v =
      ((rk run.coordinateProper.rank v).toNat : Int) := by omega
  obtain ⟨hinBand, _⟩ := X_ReserveBands_holds exactIds hrun
  have hMemBandHi := (hinBand _ _ _ hlyD hmemD (by omega) hrkD).2
  have hbandBlo := (hinBand _ _ _ hlyB hmemB (by omega) hrkB).1
  have hBWF := xsds_coord_BWF execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨cn, hcn, _, _, _, hcnH⟩ := xsds_coord_dummy hrun hBWF hnd hdum
  have hnodeHcoord : CoordsImpl.nodeH run.coordinateProper d =
      RouteImpl.nodeH run.proper d := by
    simp only [CoordsImpl.nodeH, RouteImpl.nodeH, hcn, hnd]
    exact hcnH
  rw [hnodeHcoord] at hMemBandHi
  have hltMB : (rk run.coordinateProper.rank d).toNat <
      (rk run.coordinateProper.rank v).toNat := by omega
  have hgapMB := hgap _ _ _ _ hltMB hlyD hlyB
  obtain ⟨bcoord, hbcoord, hbb, _, _, hcoordH⟩ :=
    xsds_bottom_coord execution.graph0_eq execution.graph_eq hcomp hrun hvGet hbordV
  obtain ⟨_, _, _, hnodeH0⟩ :=
    xsds_bottom_proper hrun hbcoord hbb hcoordH
  have hBotYH : (Labels.rectAt run.proper run.xs run.ys v).y +
      (Labels.rectAt run.proper run.xs run.ys v).h = run.ys.getD v 0 := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
    simp [hnodeH0]
  have hbmem' := xsds_bottom_hull_mem execution.graph0_eq execution.graph_eq hcomp
    hrun hg hgroup hvGet hbordV hdecl
  have hle := rect_bottom_le_boundsOf_bottom _ [] _ hbmem'
  have hframeBot := xsds_bottom_frame_eq (P := execution.params) (run := run) hg hgroup
  have hMemBH : (Labels.rectAt run.proper run.xs run.ys d).y +
      (Labels.rectAt run.proper run.xs run.ys d).h =
      run.ys.getD d 0 + RouteImpl.nodeH run.proper d := rfl
  omega

private theorem xsds_leftX_strict {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) labels
      orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hdum : nd.dummy = true) (hpath : gn.decl ∈ nd.node.clusterPath)
    (hbracket : DummyMarkerBracket (componentCandidate execution.graph comp candidate) run) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run
      gpos).x < (Labels.rectAt run.proper run.xs run.ys d).x := by
  obtain ⟨mL, mR, nL, nR, layer, hlayer, hcoordML, hcoordMR, hbL, hbR,
      hlastL, hlastR, hwidthL, hwidthR, hrankL, hrankR, li, mi, ri, hli, hmi, hri,
      hlt, hgt⟩ :=
    hbracket gpos gn hg hgroup d nd hnd hdum hpath
  obtain ⟨hproperML, hxML⟩ := xsds_border_record hrun hcoordML (Or.inl hbL)
  have hBWF := xsds_coord_BWF execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨cn, hcn, hcnDum, _, _, _⟩ := xsds_coord_dummy hrun hBWF hnd hdum
  have hcnB0 : cn.node.border = 0 := hBWF.2.2 d cn hcn hcnDum
  obtain ⟨hproperD, hxD⟩ := xsds_nonproxy hrun hcn (by rw [hcnB0]; decide)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨_, _, _, hc, hkeys, _, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hshapeC := componentCandidate_shape (components_nodup _ _ hcomp)
    (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq)
    candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact xsds_pc_title_unique hkeys hshapeC (by rw [hc]; exact ha)
      (by rw [hc]; exact hb) hba hbb hp
  have hsepL := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi mL d _ _ hlt hli hmi hcoordML hcn
    (by rw [hbL]; decide) (by rw [hbL]; decide)
    (by rw [hcnB0]; decide) (by rw [hcnB0]; decide)
  have hmemML : (nL, mL) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproperML
  have hmemL : Labels.rectAt run.proper run.xs run.ys mL ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) :=
    xsds_marker_rect_mem_borders hg hmemML (Or.inl hbL) hlastL
  have hframeX := (xsds_frameRect_horizontal_edges (P := execution.params) (run := run)
    hg hgroup).1
  have hlo := boundsOf_minX_le_rect_x _ [] _ hmemL
  have hmStrict : (Labels.rectAt run.proper run.xs run.ys mL).x <
      (Labels.rectAt run.proper run.xs run.ys d).x := by
    have hmlW' : (0 : Int) ≤ nL.node.w :=
      (sizesNonneg_lookup hsizes mL nL hcoordML).1
    have hdW' : (0 : Int) ≤ cn.node.w :=
      (sizesNonneg_lookup hsizes d cn hcn).1
    have hloop1 : (0 : Int) ≤ (nL.node.loopExtent : Int) := Int.natCast_nonneg _
    have hloop2 : (0 : Int) ≤ (cn.node.loopExtent : Int) := Int.natCast_nonneg _
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordML, hcn] at hsepL
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproperML, hproperD, hxML, hxD] at hsepL ⊢
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsepL ⊢
    omega
  omega

private theorem xsds_rightX_strict {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) labels
      orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hdum : nd.dummy = true) (hpath : gn.decl ∈ nd.node.clusterPath)
    (hbracket : DummyMarkerBracket (componentCandidate execution.graph comp candidate) run) :
    (Labels.rectAt run.proper run.xs run.ys d).x +
      (Labels.rectAt run.proper run.xs run.ys d).w <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run gpos).x +
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run gpos).w := by
  obtain ⟨mL, mR, nL, nR, layer, hlayer, hcoordML, hcoordMR, hbL, hbR,
      hlastL, hlastR, hwidthL, hwidthR, hrankL, hrankR, li, mi, ri, hli, hmi, hri,
      hlt, hgt⟩ :=
    hbracket gpos gn hg hgroup d nd hnd hdum hpath
  obtain ⟨hproperMR, hxMR⟩ := xsds_border_record hrun hcoordMR (Or.inr hbR)
  have hBWF := xsds_coord_BWF execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨cn, hcn, hcnDum, _, _, _⟩ := xsds_coord_dummy hrun hBWF hnd hdum
  have hcnB0 : cn.node.border = 0 := hBWF.2.2 d cn hcn hcnDum
  obtain ⟨hproperD, hxD⟩ := xsds_nonproxy hrun hcn (by rw [hcnB0]; decide)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨_, _, _, hc, hkeys, _, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hshapeC := componentCandidate_shape (components_nodup _ _ hcomp)
    (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq)
    candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact xsds_pc_title_unique hkeys hshapeC (by rw [hc]; exact ha)
      (by rw [hc]; exact hb) hba hbb hp
  have hsepR := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri d mR _ _ hgt hmi hri hcn hcoordMR
    (by rw [hcnB0]; decide) (by rw [hcnB0]; decide)
    (by rw [hbR]; decide) (by rw [hbR]; decide)
  have hmemMR : (nR, mR) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproperMR
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) :=
    xsds_marker_rect_mem_borders hg hmemMR (Or.inr hbR) hlastR
  have hframeXW := (xsds_frameRect_horizontal_edges (P := execution.params) (run := run)
    hg hgroup).2
  have hloR := rect_right_le_boundsOf_right _ [] _ hmemR
  have hmStrictR : (Labels.rectAt run.proper run.xs run.ys d).x +
      (Labels.rectAt run.proper run.xs run.ys d).w <
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
    have hdW' : (0 : Int) ≤ cn.node.w :=
      (sizesNonneg_lookup hsizes d cn hcn).1
    have hnRW' : (0 : Int) ≤ nR.node.w :=
      (sizesNonneg_lookup hsizes mR nR hcoordMR).1
    have hloopD : (0 : Int) ≤ (cn.node.loopExtent : Int) := Int.natCast_nonneg _
    have hloopR : (0 : Int) ≤ (nR.node.loopExtent : Int) := Int.natCast_nonneg _
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcn, hcoordMR] at hsepR
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproperD, hproperMR, hxD, hxMR] at hsepR ⊢
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsepR ⊢
    omega
  omega

/-- Per-execution form of `XFD_StrictTopX`: the same strict-top statement with
two local admission premises after the execution binder. The plain def omits
them, but the exact rank straddle needs `WellFormed` / `framedParents`. -/
def XFD_StrictTopXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
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

/-- Per-execution form of `XFD_StrictBottomX`: the same strict-bottom statement
with two local admission premises after the execution binder. -/
def XFD_StrictBottomXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
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

/-- Per-execution form of `XFR_StrictDummyLinkedX`: the same linked strict-dummy
frame with two local admission premises after the execution binder. -/
def XFR_StrictDummyLinkedXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    StrictDummyFrameLinked execution.params
      (componentCandidate execution.graph comp candidate) run

theorem XFD_strictTopXW_holds (exactIds : List String) :
    XFD_StrictTopXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  have hlines : execution.lines.length = inp.boxes.length :=
    xsds_lines_len execution
  have hd : d < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnd).1
  have hgetD : run.proper.nodes.getD d default = nd := by
    simp [List.getD_eq_getElem?_getD, hnd]
  have hpathC : (run.proper.nodes.getD d default).node.clusterPath.contains
      gn.decl = true := by
    rw [hgetD]; exact List.contains_iff_mem.mpr hpath
  have hdumGet : (run.proper.nodes.getD d default).dummy = true := by
    rw [hgetD]; exact hdum
  have hvcg : gpos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  have hlt := xsds_topRank_strict execution.graph0_eq execution.graph_eq hlines
    hwf hfp hcomp hrun hg hgroup hvcg hd hpathC hdumGet
  have hgap := xsds_post_strict_gap hrun
  exact xsds_topY_strict execution hcomp hrun hg hgroup hnd hlt hgap

theorem XFD_strictBottomXW_holds (exactIds : List String) :
    XFD_StrictBottomXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  have hlines : execution.lines.length = inp.boxes.length :=
    xsds_lines_len execution
  obtain ⟨v, ndV, hvGet, hbordV, hdecl⟩ :=
    xsds_bottom_marker execution.graph0_eq execution.graph_eq hcomp hrun hg hgroup
  have hd : d < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnd).1
  have hgetD : run.proper.nodes.getD d default = nd := by
    simp [List.getD_eq_getElem?_getD, hnd]
  have hpathC : (run.proper.nodes.getD d default).node.clusterPath.contains
      gn.decl = true := by
    rw [hgetD]; exact List.contains_iff_mem.mpr hpath
  have hdumGet : (run.proper.nodes.getD d default).dummy = true := by
    rw [hgetD]; exact hdum
  have hlt := xsds_bottomRank_strict execution.graph0_eq execution.graph_eq hlines
    hwf hfp hcomp hrun hvGet hg hbordV hgroup hdecl hd hpathC hdumGet
  have hgap := xsds_post_strict_gap hrun
  exact xsds_bottomY_strict execution hcomp hrun hg hgroup hnd hdum hpath
    hvGet hbordV hdecl hlt hgap

theorem XFD_strictLeftX_holds (exactIds : List String)
    (hbracket : XFD_MarkerBracketX exactIds) : XFD_StrictLeftX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  exact xsds_leftX_strict execution hcomp hrun hg hgroup hnd hdum hpath
    (hbracket execution hcomp hrun)

theorem XFD_strictRightX_holds (exactIds : List String)
    (hbracket : XFD_MarkerBracketX exactIds) : XFD_StrictRightX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  exact xsds_rightX_strict execution hcomp hrun hg hgroup hnd hdum hpath
    (hbracket execution hcomp hrun)

theorem XFR_strictDummyLinkedX_closed (exactIds : List String)
    (hbracket : XFD_MarkerBracketX exactIds) :
    XFR_StrictDummyLinkedXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  have hL : XFD_StrictLeftX exactIds := XFD_strictLeftX_holds exactIds hbracket
  have hR : XFD_StrictRightX exactIds := XFD_strictRightX_holds exactIds hbracket
  have hT : XFD_StrictTopXW exactIds := XFD_strictTopXW_holds exactIds
  have hB : XFD_StrictBottomXW exactIds := XFD_strictBottomXW_holds exactIds
  exact ⟨hL execution hcomp hrun hg hgroup hnd hdum hpath,
    hR execution hcomp hrun hg hgroup hnd hdum hpath,
    hT execution hwf hfp hcomp hrun hg hgroup hnd hdum hpath,
    hB execution hwf hfp hcomp hrun hg hgroup hnd hdum hpath⟩
end PipelineImpl
end Layered
end Elegant
