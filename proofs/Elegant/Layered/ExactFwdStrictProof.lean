import Elegant.Layered.ExactMarkerBracketProof
import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.StrictDummyFrameProof
import Elegant.Layered.SizingFacts

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact forward strict dummy frame, W form

Target leaf: `XFR_StrictDummyLinkedX`
(`ExactRouteForwardClearProof.lean:97`), consumed as the `fwdStrict` field of
`UsecaseValidExact.lean:280` and by the `glue_*` assemblers in
`ExactSeamClosureGlue.lean`. The leaf is the no-admission form; this module
proves its per-execution W form `XFR_StrictDummyLinkedXW`
(`ExactStrictDummySidesProof.lean:2072`) modulo the single order-stage
residual `embMarkerPrefixX` (`ExactMarkerBracketProof.lean:93`), which is
itself strictly narrower than the leaf (one prefix fact on executed runs,
no geometry).

Assembly, mirroring `XFR_strictDummyLinkedX_closed`
(`ExactStrictDummySidesProof.lean:2144`) but sourcing the horizontal halves
from the W-form marker bracket `embMarkerBracketXW` instead of the
no-admission `XFD_MarkerBracketX` (whose proof the contract forbids without
global admission):

* top and bottom: the closed `XFD_strictTopXW_holds` /
  `XFD_strictBottomXW_holds`;
* left and right: `xsds_leftX_strict` / `xsds_rightX_strict` replayed
  verbatim (they already take a `DummyMarkerBracket` instance as a
  hypothesis), fed by `XFD_markerBracketX_of_residual` applied to
  `embMarkerPrefixX`.

The `xsds_*` helpers below are verbatim copies of the private infrastructure
of `ExactStrictDummySidesProof.lean` (private there, so not importable);
every transitive dependency is public. Probe:
`proofs/wip/Probe/ExactFwdStrictProofProbe.lean` evaluates the prefix
residual and all four strict sides on executed `componentRunX` runs.
-/

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

/-- Exact strict-dummy left edge, W form: every linked dummy rect starts
strictly right of its group frame's left edge, with local admission premises
so the W-form marker bracket applies. The proof is `xsds_leftX_strict` fed by
`embMarkerBracketXW`; the admission premises are only used to obtain the
bracket instance. -/
theorem xfwd_strictLeftXW (exactIds : List String)
    (hbracket : embMarkerBracketXW exactIds) :
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
            (componentCandidate execution.graph comp candidate) run gpos).x <
            (Labels.rectAt run.proper run.xs run.ys d).x := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  exact xsds_leftX_strict execution hcomp hrun hg hgroup hnd hdum hpath
    (hbracket execution hwf hfp hcomp hrun)

/-- Exact strict-dummy right edge, W form: every linked dummy rect ends
strictly left of its group frame's right edge. Mirror of `xfwd_strictLeftXW`
through `xsds_rightX_strict`. -/
theorem xfwd_strictRightXW (exactIds : List String)
    (hbracket : embMarkerBracketXW exactIds) :
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
          (Labels.rectAt run.proper run.xs run.ys d).x +
            (Labels.rectAt run.proper run.xs run.ys d).w <
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run gpos).x +
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run gpos).w := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  exact xsds_rightX_strict execution hcomp hrun hg hgroup hnd hdum hpath
    (hbracket execution hwf hfp hcomp hrun)

/-- Exact strict linked dummy frame, W form, modulo `embMarkerPrefixX`: the
per-execution form of `XFR_StrictDummyLinkedX` with local `WellFormed` /
`framedParents` premises, proved from the prefix residual through the W-form
marker bracket (`XFD_markerBracketX_of_residual`) and the closed top/bottom
sides. This is the `original_of_residual` reduction for the `fwdStrict` leaf:
the residual `embMarkerPrefixX` is a single order fact (group path prefixes
the linked dummy's node path) on executed runs, strictly narrower than the
whole four-sided frame. -/
theorem xfwd_strictDummyLinkedXW_holds (exactIds : List String)
    (hpre : embMarkerPrefixX exactIds) : XFR_StrictDummyLinkedXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    gpos gn hg hgroup d nd hnd hdum hpath
  have hbracket : DummyMarkerBracket
      (componentCandidate execution.graph comp candidate) run :=
    XFD_markerBracketX_of_residual exactIds hpre execution hwf hfp hcomp hrun
  have hL := xsds_leftX_strict execution hcomp hrun hg hgroup hnd hdum hpath
    hbracket
  have hR := xsds_rightX_strict execution hcomp hrun hg hgroup hnd hdum hpath
    hbracket
  have hT := XFD_strictTopXW_holds exactIds execution hwf hfp hcomp hrun
    hg hgroup hnd hdum hpath
  have hB := XFD_strictBottomXW_holds exactIds execution hwf hfp hcomp hrun
    hg hgroup hnd hdum hpath
  exact ⟨hL, hR, hT, hB⟩

end PipelineImpl
end Layered
end Elegant
