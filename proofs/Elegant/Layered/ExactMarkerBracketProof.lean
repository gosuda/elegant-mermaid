import Elegant.Layered.ExactStrictDummySidesProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactLoopEnvelopeGroupProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC5Bottom
import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.Pipeline
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.Order
import Elegant.Layered.Coords
import Elegant.Layered.Route
import Elegant.Layered.Labels
import Elegant.Layered.SceneBounds
import Elegant.Layered.CgShape
import Elegant.Layered.Compound
import Elegant.Layered.Normalize
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.Loops
import Elegant.Layered.FlatC6Loops

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact marker bracket (`XFD_MarkerBracketX`) and group marker order
(`XLEG_GroupMarkerOrderX`).

Truth (probe `proofs/wip/Probe/ExactMarkerBracketTProbe.lean`, `#eval report`;
all counts over executed `componentRunX` runs, candidates × orders):
- bracket: 30 linked dummy pairs over flat / reversed-pair / wide / nested /
  zero-size inputs, `bracketBad = 0` (self-loop, empty-group, looping-group
  inputs are vacuously linked-free there).
- prefix residual: `prefixBad = 0` over the same 30 linked pairs.
- `XLEG` bottom: `true` on all 60 runs (11 inputs × runs × candidates).
- `XLEG` tops: 20 looping tops over sibling / empty-nest / long-label /
  two-loop inputs, `xlegTopBad = 0` (extent, layer membership, cross order,
  alignment, and separation all hold on the probes).

Proved in this file:
- `XFD_markerBracketX_of_residual`: the W-form marker bracket
  (`embMarkerBracketXW`, i.e. local `WellFormed` / `framedParents` as in
  `XCA_LinkLeftXW`) modulo the single narrower residual `embMarkerPrefixX`
  (group path prefixes the linked dummy's node path). Markers come from the
  proved `XN_bracketMarkersAtRank_holds`; widths, canon paths, order setup,
  and border-before positions are replayed over `componentRunX_spec`.
  The no-admission `XFD_MarkerBracketX` is *not* stated: its proof would need
  global admission, which the contract forbids.
- Residual `embLoopMarkerSpanX` (single public def over executed runs):
  same-side marker span alignment, right-edge nonnegativity, loop-extent
  lower bound, and later-layer separation for a looping group top with
  witness markers. A proper sub-case of the per-top block (four conjuncts);
  true on the probe.

Open (not attempted here for budget): the `XLEG_groupMarkerOrderX_holds`
assembly (bottom no-loop replay over the exact graph; marker existence via
`X_group_bottom_source` + `emb_rank_pair`; layer membership via `layer_mem`;
cross order via `XB_orderedIntervals_holds`; then `hspan` for the residual
conjuncts), the `emb_pathEq` main assembly plus scoped-prefix chain behind
the residual, and deletion of the now-unused pathEq bottom half
(`emb_matEndpoint`, `emb_preparedNondummy`, `emb_chain_edge`,
`emb_chain_nonself`), which is kept only as landed infrastructure.
-/

/-- W form of `XFD_MarkerBracketX`: the exact marker bracket with local
admission, mirroring `XCA_LinkLeftXW`. -/
def embMarkerBracketXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    DummyMarkerBracket (componentCandidate execution.graph comp candidate) run
/-- Scoped-prefix residual for the exact marker bracket: for a linked dummy of
a long edge crossing a group, the group path prefixes the dummy's node path.
Strictly narrower than `embMarkerBracketXW` (one order fact, no markers,
widths, ranks, or layer positions); a lemma on the way to the bracket (feeds
the border-before applications). True on the probe (`prefixBad = 0` over the
same 30 linked pairs). -/
def embMarkerPrefixX (exactIds : List String) : Prop :=
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
        gn.clusterPath <+: OrderImpl.nodePath run.coordinateProper d


/-- Single residual for `XLEG_GroupMarkerOrderX`: for a looping group top with
witness markers `mL`/`mR`, the same-side marker span alignment, the right
edge nonnegativity, the loop-extent lower bound, and the separation of the
right marker from later nonproxy boxes in shared layers. Sub-case of the
per-top block (four numeric/span conjuncts); true on the probe. -/
def embLoopMarkerSpanX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (cg : Graph),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run →
    ∀ {t : Nat} {nt : Node}, cg.nodes[t]? = some nt →
      (∃ e_ ∈ cg.edges, e_.tail = t ∧ e_.head = t) → nt.border = -2 →
      ∀ {mL mR : Nat} {nL nR : ProperNode},
        run.coordinateProper.nodes[mL]? = some nL →
        run.coordinateProper.nodes[mR]? = some nR →
        nL.node.border = -1 → nR.node.border = 1 →
        nL.node.clusterPath.getLast? = some nt.decl →
        nR.node.clusterPath.getLast? = some nt.decl →
        (∀ {q : Nat} {nd : ProperNode}, run.proper.nodes[q]? = some nd →
          nd.node.clusterPath.getLast? = some nt.decl →
          ((nd.node.border = -1 →
            RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mL ∧
            RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
              RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL) ∧
          (nd.node.border = 1 →
            RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mR ∧
            RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
              RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR))) ∧
        (nR.node.loopExtent : Int) ≥
          (if run.exact.contains t then Loops.exactExtent cg.slot (loopSizes cg.edges execution.measured t cg.slot)
           else Loops.extent cg.slot (loopSizes cg.edges execution.measured t cg.slot)) ∧
        0 ≤ RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ∧
        ∀ {b : Nat} {actualB : ProperNode}, run.coordinateProper.nodes[b]? = some actualB →
          ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) →
          ∀ {layer : List Nat}, layer ∈ run.layers →
          ∀ {j iv : Nat}, layer[j]? = some mR → layer[iv]? = some b → j < iv →
          Int.fdiv (nR.node.w + 2 * (nR.node.loopExtent : Int)) 2 +
            Int.fdiv (actualB.node.w + 2 * (actualB.node.loopExtent : Int)) 2 + 1 ≤
            run.coordinateXs.getD b 0 - run.coordinateXs.getD mR 0
/-- Title-reservation rank prefix for exact sizing. -/
private theorem emb_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

/-- Exact titled rank transport: titled ranks agree with ranking ranks below
the candidate length, and are nonnegative. -/
private theorem emb_titled_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact labeled)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  obtain ⟨_, heq⟩ := emb_titled_rank_prefix P exact labeled
  have htitledLookup : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? =
      some rr.ranks[index] := by
    rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlabLookup).1]
    exact hlabLookup
  have heq2 : rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq2, ?_⟩
  rw [heq2]
  exact rankWithBudget_rk_nonneg hrr index

/-- Exact prepared rank transport: coordinate ranks agree with ranking ranks
below the candidate length. -/
private theorem emb_prepared_rk {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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
  obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
  have hcoordLookup : run.coordinateProper.rank[index]? = some rr.ranks[index] := by
    rw [← hc, heq, List.getElem?_append_left hlabLen]
    exact hlabLookup
  simp only [rk, List.getD_eq_getElem?_getD, hcoordLookup, hrrLookup, Option.getD_some]

/-- Every exact proper rank is nonnegative (via layer coverage). -/
private theorem emb_proper_rk_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) (v : Nat)
    (hv : v < run.proper.nodes.length) : 0 ≤ rk run.proper.rank v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hok).2.2.2.1
  obtain ⟨_, _, _, hnn⟩ := hcov v hv
  exact hnn

/-- Exact proper ranks agree with coordinate ranks index-wise. -/
private theorem emb_proper_coord_rank_eq {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) (x : Nat) :
    rk run.proper.rank x = rk run.coordinateProper.rank x := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have h : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  rw [h]
/-- A candidate `-2` node ends its cluster path in its declaration. -/
private theorem emb_top_getLast {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hb : uNode.border = -2) :
    uNode.clusterPath.getLast? = some uNode.decl := by
  obtain ⟨_, _, hpath⟩ := X_cg_group_box h0 h hu hb
  rw [hpath, List.getLast?_append]
  simp

/-- A titled `-2` anchor with the same path-last as the candidate top is the
candidate top index. -/
private theorem emb_titledTopPin {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {labeled : Proper}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩)
    {u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hbU : uNode.border = -2)
    {top : ProperNode × Nat}
    (htopMem : top ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx)
    (hbTop : top.1.node.border = -2)
    (hlastTop : top.1.node.clusterPath.getLast? = some uNode.decl) :
    top.2 = u := by
  have htopLookup : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htopMem
  have hrequested : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[u]? =
      some (titleF ⟨uNode, false, none, false⟩) :=
    X_titled_marker_record (hrecords u uNode hu) (Or.inl hbU)
  have hrequestedBorder : (titleF ⟨uNode, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hbU
  have howner : top.1.node.clusterPath.getLast? =
      (titleF ⟨uNode, false, none, false⟩).node.clusterPath.getLast? := by
    have hpathTop : (titleF ⟨uNode, false, none, false⟩).node.clusterPath =
        uNode.clusterPath :=
      (titleF_keys _).2.2.1
    have hlastU : uNode.clusterPath.getLast? = some uNode.decl :=
      emb_top_getLast h0 h hu hbU
    rw [hpathTop, hlastU]
    exact hlastTop
  exact X_titled_group_owner_unique h0 h hcomp hkeys hrecords htopLookup hrequested
    hbTop hrequestedBorder howner
/-- Exact side record: a side marker of the exact bordered graph is already
a coordinate node. -/
private theorem emb_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with h | h <;> rw [h] <;> decide
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

/-- Exact rank pair: a bracketed rank carries the declaration's marker pair. -/
private theorem emb_rank_pair (P : Params) (exact : List Nat) (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
      rank)
    (hhi : rank ≤
      (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, emb_side_record hl rfl (Or.inl rfl),
    emb_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr
/-- Exact coordinate `BordersWellFormed` for one exact run. -/
private theorem emb_coord_BWF {P : Params} {inp : Input} {o : Options}
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
coordinate graph. -/
private theorem emb_coord_dummy {P : Params} {exact : List Nat} {cg : Graph}
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
/-- Materialization preserves the cluster path at a non-dummy index. -/
private theorem emb_matEndpoint {PREP : Proper} {e : Nat}
    {pm : ProperNode}
    (hprep : PREP.nodes[e]? = some pm) (hd : pm.dummy = false) :
    ((materializeDummyPaths PREP).nodes.getD e default).node.clusterPath =
      (PREP.nodes.getD e default).node.clusterPath := by
  have hmat : (materializeDummyPaths PREP).nodes[e]? = some pm := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
      hprep, Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]
  have h1 : (materializeDummyPaths PREP).nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hmat]
  have h2 : PREP.nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hprep]
  rw [h1, h2]

/-- A labeled non-dummy node has a non-dummy pre-materialization record. -/
private theorem emb_preparedNondummy {P : Params} {exact : List Nat}
    {labeled : Proper} {e : Nat} {ndL : ProperNode}
    (hlabeled : labeled.nodes[e]? = some ndL) (hdL : ndL.dummy = false) :
    ∃ pm : ProperNode,
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes[e]? = some pm ∧ pm.dummy = false := by
  have hsize : ∃ sized, (sizeProperPortsX P exact labeled).nodes[e]? = some sized ∧
      sized.dummy = false := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hlabeled,
      Option.map_some]
    split
    · exact ⟨_, rfl, hdL⟩
    · exact ⟨_, rfl, hdL⟩
  obtain ⟨sized, hsized, hdS⟩ := hsize
  have hlenS : e < (sizeProperPortsX P exact labeled).nodes.length :=
    (List.getElem?_eq_some_iff.mp hsized).1
  have htitle : (titleReservations (sizeProperPortsX P exact labeled)).nodes[e]? =
      some (titleF sized) := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hlenS)]
    simp [List.getElem?_map, hsized]
  have hdT : (titleF sized).dummy = false := by
    rw [(titleF_keys sized).1]; exact hdS
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hlenT : e < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map]
    omega
  have hborders : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[e]? = some (titleF sized) := by
    rw [hnodes, List.getElem?_append_left hlenT]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes[e]? = some (clearF (titleF sized)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders, Option.map_some]
  exact ⟨_, hclear, by rw [(clearF_keys _).1]; exact hdT⟩
/-- Chain identification for the path equation: a chain found in the
pre-materialization graph comes from a normalize chain over a ranked edge. -/
private theorem emb_chain_edge {P : Params} {exact : List Nat} {cg : Graph}
    {ranks : List Int} {normalized labeled : Proper} {v : Nat} {chain : List Nat}
    {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hfind : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW)).chains.find? (fun c => c.contains v) = some chain) :
    ∃ (_hmemC : v ∈ chain) (idx : Nat) (edge : Edge) (_hidxB : idx < cg.edges.length)
      (_hedge : cg.edges[idx]? = some edge),
      edge.tail < cg.nodes.length ∧ edge.head < cg.nodes.length ∧
      normalized.chains[idx]? = some chain := by
  have hmemC : v ∈ chain := by
    have hfv := List.find?_some hfind
    simpa only [List.contains_iff_mem] using hfv
  have hcmem : chain ∈ (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW)).chains := List.mem_of_find?_eq_some hfind
  have ePREP : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW)).chains = labeled.chains :=
    (OrderImpl.addClusterBorders_metadata _ _).2.1
  have hcNorm : chain ∈ normalized.chains := by
    have h1 := hcmem
    rw [ePREP, (Labels.addLabelNodes_metadata hlabels).2.2.1] at h1
    exact h1
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hcNorm
  have hidxB : idx < cg.edges.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hidx).1
    rwa [normalize_chains_length hnorm] at hlt
  obtain ⟨edge, hedge⟩ : ∃ e, cg.edges[idx]? = some e :=
    ⟨_, List.getElem?_eq_getElem hidxB⟩
  have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnorm).2
  have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
  have hbounds := RankImpl.wellformed_spec hwf edge hedgeMem
  obtain ⟨htailB, hheadB, _⟩ := hbounds
  exact ⟨hmemC, idx, edge, hidxB, hedge, htailB, hheadB, hidx⟩
/-- Non-self-loop chain case: chain ends are edge endpoints with stable paths. -/
private theorem emb_chain_nonself {P : Params} {exact : List Nat} {cg : Graph}
    {ranks : List Int} {normalized labeled : Proper} {v : Nat} {chain : List Nat}
    {idx : Nat} {edge : Edge} {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hidx : normalized.chains[idx]? = some chain)
    (htailB : edge.tail < cg.nodes.length)
    (hheadB : edge.head < cg.nodes.length)
    (hmemC : v ∈ chain)
    (chl : List Nat)
    (hch : normalized.chains[idx]? = some chl)
    (hhead : chl.head? = some edge.tail)
    (hlast : chl.getLast? = some edge.head) :
    ((materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).nodes.getD
      (chain.headD v) default).node.clusterPath =
      ((clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD (chain.headD v) default).node.clusterPath ∧
    ((materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).nodes.getD
      (chain.getLastD v) default).node.clusterPath =
      ((clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD (chain.getLastD v) default).node.clusterPath := by
  have hcc : chl = chain := Option.some.inj (hch.symm.trans hidx)
  have hhead' : chain.head? = some edge.tail := by
    rw [← hcc]; exact hhead
  have hlast' : chain.getLast? = some edge.head := by
    rw [← hcc]; exact hlast
  have ehead : chain.headD v = edge.tail := by
    cases hc : chain with
    | nil => simp [hc] at hmemC
    | cons h t =>
      have h2 := hhead'; rw [hc] at h2
      simp only [List.head?_cons, Option.some.injEq] at h2
      exact h2
  have elast : chain.getLastD v = edge.head := by
    rw [List.getLastD_eq_getLast?, hlast', Option.getD_some]
  have hnormT : normalized.nodes[edge.tail]? =
      some ⟨(cg.nodes[edge.tail]'htailB), false, none, false⟩ :=
    normalize_node_record hnorm (List.getElem?_eq_getElem htailB)
  have hlabT : labeled.nodes[edge.tail]? =
      some ⟨(cg.nodes[edge.tail]'htailB), false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels hnormT rfl
  obtain ⟨pmT, hprepT, hdT2⟩ := emb_preparedNondummy hlabT rfl
  have hnormH : normalized.nodes[edge.head]? =
      some ⟨(cg.nodes[edge.head]'hheadB), false, none, false⟩ :=
    normalize_node_record hnorm (List.getElem?_eq_getElem hheadB)
  have hlabH : labeled.nodes[edge.head]? =
      some ⟨(cg.nodes[edge.head]'hheadB), false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels hnormH rfl
  obtain ⟨pmH, hprepH, hdH2⟩ := emb_preparedNondummy hlabH rfl
  have hclH : ((materializeDummyPaths (clearProxyExtents
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW))).nodes.getD (chain.headD v) default).node.clusterPath =
      ((clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD (chain.headD v) default).node.clusterPath := by
    rw [ehead]
    exact emb_matEndpoint hprepT hdT2
  have hclL : ((materializeDummyPaths (clearProxyExtents
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW))).nodes.getD (chain.getLastD v) default).node.clusterPath =
      ((clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD (chain.getLastD v) default).node.clusterPath := by
    rw [elast]
    exact emb_matEndpoint hprepH hdH2
  exact ⟨hclH, hclL⟩
/-- Executed exact lines cover exactly the input boxes. -/
private theorem emb_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Folded border insertion preserves the side-marker width invariant. -/
private theorem emb_borderInner_fold (q : ProperNode × Nat) (width : Int) (lo : Nat)
    (l : List Nat) (st : Proper)
    (hst : ∀ n ∈ st.nodes, n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
    (n : ProperNode)
    (hn : n ∈ (List.foldl (OrderImpl.borderInner q width lo) st l).nodes)
    (hs : n.node.border = -1 ∨ n.node.border = 1) :
    n.node.w = width := by
  induction l generalizing st with
  | nil =>
    simp only [List.foldl_nil] at hn
    exact hst n hn hs
  | cons x xs ih =>
    rw [List.foldl_cons] at hn
    have hstep : ∀ n' ∈ (OrderImpl.borderInner q width lo st x).nodes,
        n'.node.border = -1 ∨ n'.node.border = 1 → n'.node.w = width := by
      intro n' hn' hs'
      have hn'' : n' ∈ st.nodes ++
          [OrderImpl.borderLeft q width, OrderImpl.borderRight q width] := hn'
      rcases List.mem_append.mp hn'' with hold | hnew
      · exact hst n' hold hs'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
        rcases hnew with rfl | rfl <;> rfl
    exact ih _ hstep hn

/-- Every side marker emitted by `addClusterBorders` carries the border width. -/
private theorem emb_side_width_copy (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper => ∀ n ∈ cur.nodes,
        n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
    · intro n hn hs
      rcases hs with hs | hs
      · exact ((hready.1 n hn).1 hs).elim
      · exact ((hready.1 n hn).2 hs).elim
    · intro state hstate entry hentry
      unfold OrderImpl.borderStep
      split
      · exact hstate
      · intro n hn hs
        exact emb_borderInner_fold _ _ _ _ _ hstate _ hn hs
  exact hP node (List.mem_of_getElem? hnode) hside

/-- Markers at the dummy's own rank, via the proved exact bracket. -/
private theorem emb_bracket_markers {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {gn : Node}
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hpath : gn.decl ∈ nd.node.clusterPath) :
    ∃ (mL mR : Nat) (nL nR : ProperNode),
      run.coordinateProper.nodes[mL]? = some nL ∧
      nL.node.border = -1 ∧
      nL.node.clusterPath.getLast? = some gn.decl ∧
      rk run.coordinateProper.rank mL = rk run.coordinateProper.rank d ∧
      run.coordinateProper.nodes[mR]? = some nR ∧
      nR.node.border = 1 ∧
      nR.node.clusterPath.getLast? = some gn.decl ∧
      rk run.coordinateProper.rank mR = rk run.coordinateProper.rank d := by
  have hlines : execution.lines.length = inp.boxes.length :=
    emb_lines_len execution
  have hcontain : nd.node.clusterPath.contains gn.decl = true :=
    List.contains_iff_mem.mpr hpath
  obtain ⟨mL, mR, nL, nR, hML, hbL, hlastL, hrankML, hMR, hbR, hlastR,
      hrankMR⟩ :=
    XN_bracketMarkersAtRank_holds exactIds execution.graph0_eq execution.graph_eq
      hlines hwf hfp hcomp hrun (rk run.proper.rank d).toNat hnd hcontain
      (Nat.le_refl _) hnd hcontain (Nat.le_refl _)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouteOk, _, _⟩ :=
    componentRunX_spec hrun
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteOk).1).2.2.2.1
  have hdLen : d < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnd).1
  obtain ⟨_, _, _, hnnD⟩ := hcov d hdLen
  have hnnC : 0 ≤ rk run.coordinateProper.rank d := by
    rw [← emb_proper_coord_rank_eq hrun d]; exact hnnD
  have hcast : ((rk run.coordinateProper.rank d).toNat : Int) =
      rk run.coordinateProper.rank d :=
    Int.toNat_of_nonneg hnnC
  have hrankL : rk run.coordinateProper.rank mL = rk run.coordinateProper.rank d := by
    have h1 := hrankML
    rw [emb_proper_coord_rank_eq hrun d] at h1
    exact h1.trans hcast
  have hrankR : rk run.coordinateProper.rank mR = rk run.coordinateProper.rank d := by
    have h1 := hrankMR
    rw [emb_proper_coord_rank_eq hrun d] at h1
    exact h1.trans hcast
  exact ⟨mL, mR, nL, nR, hML, hbL, hlastL, hrankL, hMR, hbR, hlastR, hrankR⟩
/-- Canonical cluster path of an executed exact side marker. -/
private theorem emb_sideCanon {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      inp.boxes[decl]? = some box ∧
      na.node.clusterPath = Compound.path inp.boxes box ++ [decl] := by
  obtain ⟨_, labeled, _, hc, hk, hready, _, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hcoordinate : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[a]? =
      some na := by
    rw [hc]; exact hna
  have horiginal := X_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal) hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases X_titled_node_origin hk hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hk top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨boxG, hboxG, hpathG⟩ := X_cg_group_box h0 h hbn hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      have hdeclEq : bn.decl = decl := Option.some.inj (hnaLast.symm.trans hlast)
      rw [hdeclEq] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hpathG, hdeclEq]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega

/-- Two exact side markers of one declaration share the anchor path. -/
private theorem emb_samePath {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {decl m m' : Nat} {marker marker' : ProperNode}
    (hmem : run.coordinateProper.nodes[m]? = some marker)
    (hborder : marker.node.border = -1 ∨ marker.node.border = 1)
    (hgetLast : marker.node.clusterPath.getLast? = some decl)
    (hmem' : run.coordinateProper.nodes[m']? = some marker')
    (hborder' : marker'.node.border = -1 ∨ marker'.node.border = 1)
    (hgetLast' : marker'.node.clusterPath.getLast? = some decl) :
    marker.node.clusterPath = marker'.node.clusterPath := by
  obtain ⟨boxL, hboxL, hpathL⟩ :=
    emb_sideCanon h0 h hcomp hrun hmem hborder hgetLast
  obtain ⟨boxR, hboxR, hpathR⟩ :=
    emb_sideCanon h0 h hcomp hrun hmem' hborder' hgetLast'
  have hbox : boxL = boxR := Option.some.inj (hboxL.symm.trans hboxR)
  rw [hpathL, hpathR, hbox]

/-- Exact border records transfer with cross centres. -/
private theorem emb_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Marker widths from the side-marker border width. -/
private theorem emb_marker_widths {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {mL mR : Nat} {nL nR : ProperNode}
    (hML : run.coordinateProper.nodes[mL]? = some nL)
    (hbL : nL.node.border = -1)
    (hMR : run.coordinateProper.nodes[mR]? = some nR)
    (hbR : nR.node.border = 1)
    {prof : Profile} {kd : String} (hchk : checkedParams prof kd = .ok P) :
    1 ≤ nL.node.w ∧ 1 ≤ nR.node.w := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hcoordML : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[mL]? =
      some nL := by
    rw [hc]; exact hML
  have hcoordMR : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[mR]? =
      some nR := by
    rw [hc]; exact hMR
  have horigL := X_side_original hready hcoordML (Or.inl hbL)
  have horigR := X_side_original hready hcoordMR (Or.inr hbR)
  have hwL : nL.node.w = P.clusterBorderW :=
    emb_side_width_copy _ _ hready horigL (Or.inl hbL)
  have hwR : nR.node.w = P.clusterBorderW :=
    emb_side_width_copy _ _ hready horigR (Or.inr hbR)
  have hge : 1 ≤ P.clusterBorderW := checkedParams_clusterBorderW_ge_one hchk
  exact ⟨by rw [hwL]; exact hge, by rw [hwR]; exact hge⟩

/-- Marker pair with records, lasts, ranks, widths, and paths bundled. -/
private theorem emb_marker_witness {P : Params} (exact : List Nat) (source : Proper)
    {decl : Nat} {rank : Nat}
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    (hlast : top.1.node.clusterPath.getLast? = some decl)
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
      rank)
    (hhi : rank ≤
      (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ mL mR : Nat, ∃ nL nR : ProperNode,
      (coordinateGraphX P exact source).nodes[mL]? = some nL ∧
      nL.node.border = -1 ∧ nL.node.clusterPath.getLast? = some decl ∧
      (coordinateGraphX P exact source).rank[mL]? = some (rank : Int) ∧
      nL.node.w = P.clusterBorderW ∧ nL.node.clusterPath = top.1.node.clusterPath ∧
      (coordinateGraphX P exact source).nodes[mR]? = some nR ∧
      nR.node.border = 1 ∧ nR.node.clusterPath.getLast? = some decl ∧
      (coordinateGraphX P exact source).rank[mR]? = some (rank : Int) ∧
      nR.node.w = P.clusterBorderW ∧
      nR.node.clusterPath = top.1.node.clusterPath ∧
      nR.node.loopExtent = top.1.node.loopExtent := by
  obtain ⟨mL, mR, hML, hMR, hleftRank, hrightRank⟩ :=
    emb_rank_pair P exact source haligned htop hborder hbottom hlo hhi
  exact ⟨mL, mR, _, _, hML, rfl, hlast, hleftRank, rfl, rfl, hMR, rfl, hlast,
    hrightRank, rfl, rfl, rfl⟩

/-- Marker paths equal the group path, via the shared fixedSizes box. -/
private theorem emb_marker_paths {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {mL mR : Nat} {nL nR : ProperNode}
    (hML : run.coordinateProper.nodes[mL]? = some nL)
    (hbL : nL.node.border = -1)
    (hlastL : nL.node.clusterPath.getLast? = some gn.decl)
    (hMR : run.coordinateProper.nodes[mR]? = some nR)
    (hbR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some gn.decl) :
    nL.node.clusterPath = gn.clusterPath ∧
      nR.node.clusterPath = gn.clusterPath := by
  obtain ⟨boxM, hboxM, hpathM⟩ :=
    emb_sideCanon h0 h hcomp hrun hML (Or.inl hbL) hlastL
  obtain ⟨boxR, hboxR, hpathR⟩ :=
    emb_sideCanon h0 h hcomp hrun hMR (Or.inr hbR) hlastR
  obtain ⟨boxG, hboxG, hpathG⟩ := X_cg_group_box h0 h hg hgroup
  have hboxM_eq : boxM = boxG := Option.some.inj (hboxM.symm.trans hboxG)
  have hboxR_eq : boxR = boxG := Option.some.inj (hboxR.symm.trans hboxG)
  have hmarkPath : nL.node.clusterPath = gn.clusterPath := by
    rw [hpathM, hboxM_eq, ← hpathG]
  have hmarkPathR : nR.node.clusterPath = gn.clusterPath := by
    rw [hpathR, hboxR_eq, ← hpathG]
  exact ⟨hmarkPath, hmarkPathR⟩

/-- Exact dummy marker bracket in W form, modulo the scoped-prefix residual:
markers from the proved exact bracket, widths from the border width, marker
paths from the shared fixedSizes box, and layer positions from the
border-before order with the residual prefix. -/
theorem XFD_markerBracketX_of_residual (exactIds : List String)
    (hpre : embMarkerPrefixX exactIds) : embMarkerBracketXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro gpos gn hg hgroup d nd hnd hdum hpath
  obtain ⟨mL, mR, nL, nR, hML, hbL, hlastL, hrankL, hMR, hbR, hlastR,
      hrankR⟩ :=
    emb_bracket_markers execution hwf hfp hcomp hrun hnd hpath
  obtain ⟨hgeL, hgeR⟩ :=
    emb_marker_widths execution.graph0_eq execution.graph_eq hcomp hrun
      hML hbL hMR hbR execution.checked
  obtain ⟨hmarkPath, hmarkPathR⟩ :=
    emb_marker_paths execution.graph0_eq execution.graph_eq hcomp hrun
      hg hgroup hML hbL hlastL hMR hbR hlastR
  have hsame : nL.node.clusterPath = nR.node.clusterPath :=
    hmarkPath.trans hmarkPathR.symm
  obtain ⟨_, _, _, _, _, _, _, hordEx, hcross, hproxy, hdrop, hroute, hrouting,
      hroutes⟩ :=
    componentRunX_spec hrun
  obtain ⟨ord, horder, hlayers⟩ := hordEx
  have hwfB := emb_coord_BWF execution.graph0_eq execution.graph_eq hcomp hrun
  have hbb : OrderImpl.LayersBB run.coordinateProper ord.layers := by
    unfold OrderImpl.orderWithBudget at horder
    split at horder
    · split at horder
      · simp only [Except.ok.injEq] at horder
        subst horder
        exact OrderImpl.runKey_bb hwfB orderOptions.key OrderImpl.sweepMax
          OrderImpl.sweepStall OrderImpl.sweepMax 0
          (OrderImpl.seedBest run.coordinateProper orderOptions.start)
          (OrderImpl.crossCount run.coordinateProper
            (OrderImpl.seedBest run.coordinateProper orderOptions.start)) 0
          (OrderImpl.seedBest_spec run.coordinateProper orderOptions.start).1
          (OrderImpl.seedBest_bb hwfB orderOptions.start)
      · simp at horder
    · simp at horder
  have hspec := (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord
    horder).1
  have hdmL : nL.dummy = false := by
    cases hd : nL.dummy with
    | false => rfl
    | true =>
      have h0 := hwfB.2.2 mL nL hML hd
      omega
  have hdmR : nR.dummy = false := by
    cases hd : nR.dummy with
    | false => rfl
    | true =>
      have h0 := hwfB.2.2 mR nR hMR hd
      omega
  have hnpL : OrderImpl.nodePath run.coordinateProper mL = nL.node.clusterPath :=
    OrderImpl.nodePath_of_nondummy hML hdmL
  have hnpR : OrderImpl.nodePath run.coordinateProper mR = nR.node.clusterPath :=
    OrderImpl.nodePath_of_nondummy hMR hdmR
  have hlayML : OrderImpl.lay run.coordinateProper mL =
      OrderImpl.lay run.coordinateProper d := by
    simp only [OrderImpl.lay, hrankL]
  have hlayMR : OrderImpl.lay run.coordinateProper mR =
      OrderImpl.lay run.coordinateProper d := by
    simp only [OrderImpl.lay, hrankR]
  rw [hlayers] at hbb
  obtain ⟨cn, hcn, hcnDum, _, _, _⟩ := emb_coord_dummy hrun hwfB hnd hdum
  have hcnB0 : cn.node.border = 0 := hwfB.2.2 d cn hcn hcnDum
  have hlenD : OrderImpl.lay run.coordinateProper d < run.layers.length := by
    rw [← hlayers]
    exact (ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord
      horder hcn).1
  let layer : List Nat := run.layers[OrderImpl.lay run.coordinateProper d]'hlenD
  have hlayerMem : layer ∈ run.layers := List.getElem_mem hlenD
  have hopt : run.layers[OrderImpl.lay run.coordinateProper d]? = some layer :=
    List.getElem?_eq_some_iff.mpr ⟨hlenD, rfl⟩
  obtain ⟨_, hmemD0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hcn
  obtain ⟨_, hmemL0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hML
  obtain ⟨_, hmemR0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hMR
  rw [hlayML] at hmemL0
  rw [hlayMR] at hmemR0
  have hmemD : d ∈ layer := by
    have h1 := hmemD0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hmemL : mL ∈ layer := by
    have h1 := hmemL0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hmemR : mR ∈ layer := by
    have h1 := hmemR0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  obtain ⟨li, hli⟩ := List.mem_iff_getElem?.mp hmemL
  obtain ⟨mi, hmi⟩ := List.mem_iff_getElem?.mp hmemD
  obtain ⟨ri, hri⟩ := List.mem_iff_getElem?.mp hmemR
  have hneML : mL ≠ d := by
    intro heq
    subst heq
    have hcnEq : nL = cn := Option.some.inj (hML.symm.trans hcn)
    rw [hcnEq, hcnB0] at hbL
    omega
  have hneMR : mR ≠ d := by
    intro heq
    subst heq
    have hcnEq : nR = cn := Option.some.inj (hMR.symm.trans hcn)
    rw [hcnEq, hcnB0] at hbR
    omega
  have hpreL : OrderImpl.nodePath run.coordinateProper mL <+:
      OrderImpl.nodePath run.coordinateProper d := by
    rw [hnpL, hmarkPath]
    exact hpre execution hwf hfp hcomp hrun hg hgroup hnd hdum hpath
  have hpreR : OrderImpl.nodePath run.coordinateProper mR <+:
      OrderImpl.nodePath run.coordinateProper d := by
    rw [hnpR, ← hsame, hmarkPath]
    exact hpre execution hwf hfp hcomp hrun hg hgroup hnd hdum hpath
  have hbdL : (run.coordinateProper.nodes.getD mL default).node.border = -1 := by
    rw [OrderImpl.getD_border hML]
    exact hbL
  have hbdR : (run.coordinateProper.nodes.getD mR default).node.border = 1 := by
    rw [OrderImpl.getD_border hMR]
    exact hbR
  have hbbLayer := hbb layer hlayerMem
  have hsubL : [mL, d].Sublist layer := (hbbLayer mL d hmemL hmemD hneML hpreL).1 hbdL
  have hsubR : [d, mR].Sublist layer := (hbbLayer mR d hmemR hmemD hneMR hpreR).2 hbdR
  have hnd : layer.Nodup :=
    OrderImpl.layering_mem_nodup hspec (by rw [hlayers]; exact hlayerMem)
  have hlt : li < mi :=
    OrderImpl.index_lt_of_pair_sublist hnd hsubL hneML hli hmi
  have hgt : mi < ri :=
    OrderImpl.index_lt_of_pair_sublist hnd hsubR hneMR.symm hmi hri
  exact ⟨mL, mR, nL, nR, layer, hlayerMem, hML, hMR, hbL, hbR, hlastL, hlastR,
    hgeL, hgeR, hrankL, hrankR, li, mi, ri, hli, hmi, hri, hlt, hgt⟩

/-- A candidate graph has exactly the component's nodes. -/
private theorem emb_cand_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- A candidate node record is the executed-graph record at the mapped index. -/
private theorem emb_cand_lookup {g : Graph} {comp : List Nat} {candidate v : Nat}
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

/-- The pre-prepare nodes of an executed measured graph cover exactly the
input boxes, and the graph is their `Compound.prepare` image. -/
private theorem emb_raw_graph {P : Params} {inp : Input} {o : Options}
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
record. -/
private theorem emb_border_of_lt_boxes {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)}
    {boxes' : List ModelBox} {pad : Int} {titles : List (Int × Int)} {raw : Graph}
    {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    (hraw : g = Compound.prepare boxes' pad titles raw)
    (hrawlen : raw.nodes.length = inp.boxes.length)
    (hlines : lines.length = inp.boxes.length)
    {m : Nat} (hmlt : m < inp.boxes.length)
    (hmap : boxes'[m]? = some (inp.boxes[m]'hmlt))
    {nodeV : Node} (hgetm : g.nodes.getD m default = nodeV) :
    nodeV.border = -2 ∨ nodeV.border = 0 := by
  have hbox : inp.boxes[m]? = some (inp.boxes[m]'hmlt) := List.getElem?_eq_getElem hmlt
  have hlen : m < g.nodes.length := by
    have hle : raw.nodes.length ≤ g.nodes.length := by
      rw [hraw]
      exact Compound.prepare_nodes_length_ge _ _ _ _
    omega
  have hsome : g.nodes[m]? = some (g.nodes[m]'hlen) :=
    List.getElem?_eq_getElem hlen
  have hgetm' : g.nodes.getD m default = g.nodes[m]'hlen := by
    simp only [List.getD_eq_getElem?_getD, hsome, Option.getD_some]
  have hnv : nodeV = g.nodes[m]'hlen := by rw [← hgetm, hgetm']
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
    have hmlines : m < lines.length := by rw [hlines]; exact hmlt
    have hnode : g.nodes[m]? = some nodeV := by rw [hnv]; exact hsome
    have hb0 := measuredGraph_ordinary_node_border_zero hg hmlines hbox hroleN hnode
    right
    exact hb0

/-- Raw-edge endpoint bound: graph edges reference input boxes. -/
private theorem emb_findIdx_lt_length {α : Type} {p : α → Bool} :
    ∀ (l : List α) (i : Nat), l.findIdx? p = some i → i < l.length := by
  intro l
  induction l with
  | nil =>
    intro i h
    rw [List.findIdx?_nil] at h
    simp at h
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

/-- Raw-edge endpoint bound. -/
private theorem emb_edgeOf_tail_head_lt {inp : Input} {r : ModelRoute} {i : Nat} {e : Edge}
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
      exact ⟨emb_findIdx_lt_length _ _ h1, emb_findIdx_lt_length _ _ h2⟩

/-- Raw graph edges reference input boxes. -/
private theorem emb_graphEdges_mem_bounds (inp : Input) :
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
    · exact emb_edgeOf_tail_head_lt hedge
    · exact ih (k + 1) edges hedges e he'

/-- Self-loop endpoint identity. -/
private theorem emb_compound_endpoint_self (boxes : List ModelBox) (source : Bool) (v : Nat) :
    Compound.endpoint boxes source v v = v := by
  cases hb : boxes[v]? <;> simp [Compound.endpoint, hb]

/-- Bottom-index strict monotonicity over group boxes. -/
private theorem emb_selfBottomIndex_lt {boxes : List ModelBox} {i j : Nat} (hij : i < j)
    (_hi : i < boxes.length) {bi : ModelBox} (hbi : boxes[i]? = some bi)
    (hg : bi.role == .group) : Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
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

/-- Bottom-alias impossibility: no aliased edge lands past the box count. -/
private theorem emb_selfBottom_ne {boxes : List ModelBox} {a b k : Nat}
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
      exact hk (by rw [← ea]; exact ha)
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
              · have hbound := emb_selfBottomIndex_lt hcmp ha hma hgrpA
                rw [ea, eb] at hbound
                exact absurd hbound (Nat.lt_irrefl k)
              · have hblt : b < a := by omega
                have hbound := emb_selfBottomIndex_lt hblt hb hmb hgrpB
                rw [eb, ea] at hbound
                exact absurd hbound (Nat.lt_irrefl k)