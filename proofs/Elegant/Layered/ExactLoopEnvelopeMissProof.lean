import Elegant.Layered.ExactLoopEnvelopeLayerProof
import Elegant.Layered.ExactLoopEnvelopeRankProof
 import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.SizingFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.Route
import Elegant.Layered.Rank
import Elegant.Layered.Coords
import Elegant.Layered.LaneBands
import Elegant.Layered.Loops
import ElegantGeometry.Basic

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Skeleton: the extended loop-footprint miss over exact runs, split into an
other-rank direction (proved next), a same-rank direction (residual), and a
nonstandard-owner case (residual). This file states the three sub-lemmas and
proves the main dispatch modulo them. -/

/-- Exact-run membership bridge: an index recorded in `run.exact` (a filtered
`zipIdx`) is a valid graph node carrying an exact decl. -/
private theorem XLEM_exact_bound {cg : Graph} {exact : List Nat} {t : Nat}
    (h : (cg.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none).contains t = true) :
    t < cg.nodes.length ∧ exact.contains (cg.nodes.getD t default).decl = true := by
  have hm : t ∈ cg.nodes.zipIdx.filterMap fun q =>
      if exact.contains q.1.decl then some q.2 else none :=
    List.contains_iff_mem.mp h
  obtain ⟨q, hq, hfq⟩ := List.mem_filterMap.mp hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  rw [List.getElem?_zipIdx] at hi
  cases hni : cg.nodes[i]? with
  | none => simp [hni] at hi
  | some ni =>
    simp only [hni, Option.map_some, Nat.zero_add] at hi
    have hqq : (ni, i) = q := Option.some.inj hi
    rw [← hqq] at hfq
    dsimp only at hfq
    by_cases hc : exact.contains ni.decl = true
    · simp only [hc, ↓reduceIte] at hfq
      have hti : i = t := Option.some.inj hfq
      subst hti
      refine ⟨(List.getElem?_eq_some_iff.mp hni).1, ?_⟩
      rw [List.getD_eq_getElem?_getD, hni, Option.getD_some]
      exact hc
    · have hconj : exact.contains ni.decl = true ∧ i = t := by simpa using hfq
      exact absurd hconj.1 hc

/-- Exact proper nodes transfer unchanged for non-proxy borders (prefixed copy
of the `ExactFlatC2` fact). -/
private theorem XLEM_plain_node_dims {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

/-- Exact original plain nodes keep their measured record through the
coordinate phases (prefixed copy of the `ExactFlatC2` fact). -/
private theorem XLEM_original_plain_record {P : Params} {exact : List Nat}
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
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := XLEM_plain_node_dims h hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, _, _, _⟩ := componentRunX_spec h
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Other-rank direction: for an exact border-0 looping node, the extended
footprint misses every in-scope real box in a different rank. -/
def X_loopEnvOtherRank (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    run.exact.contains e.tail = true →
    (∀ nt, cg.nodes[e.tail]? = some nt → nt.border = 0) →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ∀ (rt rv : Nat) (lt lv : List Nat),
    run.layers[rt]? = some lt → e.tail ∈ lt →
    run.layers[rv]? = some lv → v ∈ lv → rt ≠ rv →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Same-rank direction (residual): for an exact border-0 looping node, the
extended footprint misses every other in-scope real box in its own rank.
Single horizontal-separation fact; true on every same-rank probe case. -/
def X_loopEnvSameRank (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    run.exact.contains e.tail = true →
    (∀ nt, cg.nodes[e.tail]? = some nt → nt.border = 0) →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ∀ (r : Nat) (l : List Nat),
    run.layers[r]? = some l → e.tail ∈ l → v ∈ l → v ≠ e.tail →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Nonstandard-owner case (residual): a looping node that is not exact or not
border-0 still misses every in-scope real box. No probe exercises such an
owner (all probe loops are exact border-0), so it holds vacuously there. -/
def X_loopEnvOtherOwner (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
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
    (run.exact.contains e.tail = false ∨
      ∃ nt, cg.nodes[e.tail]? = some nt ∧ nt.border ≠ 0) →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Dispatcher: the extended footprint miss follows from the two directions
plus the nonstandard-owner case; a box equal to the looping node is disjoint
by the footprint's left edge. -/
theorem X_loopEnvelopeMiss_holds (exactIds : List String)
    (hA : X_loopEnvOtherRank exactIds)
    (hB : X_loopEnvSameRank exactIds)
    (hC : X_loopEnvOtherOwner exactIds) :
    X_LoopEnvelopeMiss exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁
  have hrunGen := hrun
  rw [componentRunX_eq_gen] at hrunGen
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hroute, _, _, _, _, _, _, hexact⟩ :=
    componentRunGen_spec hrunGen
  obtain ⟨_, _, _, hcov4, _⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  by_cases hstd : run.exact.contains e.tail = true ∧
      (∀ ntx, cg.nodes[e.tail]? = some ntx → ntx.border = 0)
  · obtain ⟨hex, hbord⟩ := hstd
    have hexact' : (cg.nodes.zipIdx.filterMap fun q =>
        if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none).contains
          e.tail = true := by
      rw [← hexact]
      exact hex
    obtain ⟨hltCG, _hdecl⟩ := XLEM_exact_bound hexact'
    have hntEx : ∃ nt, cg.nodes[e.tail]? = some nt :=
      ⟨_, List.getElem?_eq_getElem hltCG⟩
    obtain ⟨nt, hnt⟩ := hntEx
    have hnb : nt.border = 0 := hbord nt hnt
    have htP : e.tail < run.proper.nodes.length :=
      componentRunX_original_nodes_covered hrun e.tail hltCG
    obtain ⟨lt, hly_t, htin_t, _⟩ := hcov4 (e.tail) htP
    obtain ⟨lv, hly_v, hvin_v, _⟩ := hcov4 v hv
    by_cases heq : (rk run.proper.rank e.tail).toNat = (rk run.proper.rank v).toNat
    · by_cases hvte : v = e.tail
      · subst hvte
        obtain ⟨actual, _, hpropT, _, _, _, _⟩ :=
          XLEM_original_plain_record hrun hnt hnb
        have hget : cg.nodes.getD e.tail default = nt := by
          rw [List.getD_eq_getElem?_getD, hnt]
          rfl
        have hne2 : (cg.nodes.getD e.tail default).border ≠ -2 := by
          rw [hget]
          omega
        have hFrBox : frameRect default cg run e.tail =
            RouteImpl.boxRect run.proper run.xs run.ys e.tail :=
          plain_frame_eq_boxRect default cg run e.tail htP hne2
        have hFP : loopFootprintExt cg run execution.measured e.tail =
            ⟨(RouteImpl.boxRect run.proper run.xs run.ys e.tail).x +
              (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w,
             (RouteImpl.boxRect run.proper run.xs run.ys e.tail).y,
             Loops.exactExtent cg.slot
               (loopSizes cg.edges execution.measured e.tail cg.slot),
             max (RouteImpl.boxRect run.proper run.xs run.ys e.tail).h
               (((loopSizes cg.edges execution.measured e.tail cg.slot).length : Int) *
                 Loops.band cg.slot
                   (loopSizes cg.edges execution.measured e.tail cg.slot))⟩ := by
          unfold loopFootprintExt
          simp only [hFrBox, hex, ↓reduceIte]
        have e1 : (loopFootprintExt cg run execution.measured e.tail).x =
            (RouteImpl.boxRect run.proper run.xs run.ys e.tail).x +
            (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w := by
          rw [hFP]
        have e3 : (loopFootprintExt cg run execution.measured e.tail).w =
            Loops.exactExtent cg.slot
              (loopSizes cg.edges execution.measured e.tail cg.slot) := by
          rw [hFP]
        have hBwEq : (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w =
            actual.node.w := by
          simp only [RouteImpl.boxRect, RouteImpl.nodeW, hpropT]
        have hdims := componentRunX_dims_nonneg hrun
        have hBW : (0 : Int) ≤
            (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w := by
          rw [hBwEq]
          exact (hdims e.tail actual hpropT).1
        have hslot : (0 : Int) ≤ cg.slot := componentRunX_slot_nonneg hrun
        have hmono : ∀ (acc : Int), 0 ≤ acc →
            ∀ (ss : List LoopLabel),
              0 ≤ ss.foldl (fun w l => max w l.width) acc := by
          intro acc ha ss
          induction ss generalizing acc with
          | nil => exact ha
          | cons s rest ih =>
            simp only [List.foldl]
            exact ih _ (Int.le_trans ha (Int.le_max_left _ _))
        have hwide : (0 : Int) ≤ (loopSizes cg.edges execution.measured e.tail cg.slot).foldl
            (fun w l => max w l.width) 0 :=
          hmono 0 (Int.le_refl _) _
        have hEW : (0 : Int) ≤ Loops.exactExtent cg.slot
            (loopSizes cg.edges execution.measured e.tail cg.slot) := by
          unfold Loops.exactExtent
          dsimp only
          split
          · exact hwide
          · have hnn : (0 : Int) ≤
                ((loopSizes cg.edges execution.measured e.tail cg.slot).length : Int) :=
              Int.natCast_nonneg _
            have h3 : (0 : Int) ≤ cg.slot *
                (2 * (((loopSizes cg.edges execution.measured e.tail cg.slot).length : Int)) + 1) :=
              Int.mul_nonneg hslot (by omega)
            omega
        intro hmeet
        obtain ⟨hx, _hy⟩ := hmeet
        rw [e1, e3] at hx
        exact absurd (Int.lt_of_le_of_lt (Int.le_max_left _ _)
          (Int.lt_of_lt_of_le hx (Int.min_le_right _ _))) (Int.lt_irrefl _)
      · have hly_v' : run.layers[(rk run.proper.rank e.tail).toNat]? = some lv := by
          rw [heq]
          exact hly_v
        have hlveq : lv = lt := Option.some.inj (hly_v'.symm.trans hly_t)
        rw [hlveq] at hvin_v
        exact hB inp o res execution hwf hfp comp candidate run orderOptions cg k e v
          hcomp hcg hrun hk hloop hex hbord hv hreal hscope₀ hscope₁
          _ _ hly_t htin_t hvin_v hvte
    · refine hA inp o res execution hwf hfp comp candidate run orderOptions cg k e v
        hcomp hcg hrun hk hloop hex hbord hv hreal hscope₀ hscope₁
        (rk run.proper.rank e.tail).toNat (rk run.proper.rank v).toNat lt lv
        hly_t htin_t hly_v hvin_v heq
  · have hdisj : run.exact.contains e.tail = false ∨
        ∃ ntx, cg.nodes[e.tail]? = some ntx ∧ ntx.border ≠ 0 := by
      by_cases hcT : run.exact.contains e.tail = true
      · right
        have hnb : ¬ (∀ ntx, cg.nodes[e.tail]? = some ntx → ntx.border = 0) := by
          intro hall
          exact hstd ⟨hcT, hall⟩
        exact Classical.byContradiction (fun hnone =>
          hnb (fun ntx hnt =>
            Classical.byContradiction (fun hne => hnone ⟨ntx, hnt, hne⟩)))
      · exact Or.inl (Bool.eq_false_of_ne_true hcT)
    exact hC inp o res execution hwf hfp comp candidate run orderOptions cg k e v
      hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hdisj

/-- Same-rank direction from the finished parts: layer membership gives the
layer and the positions inside it. -/
theorem X_loopEnvSameRank_of_parts (exactIds : List String)
    (hright : XLEM_PlainRightMiss exactIds)
    (hleft : XLEM_LeftMiss exactIds)
    (hgroup : XLEM_GroupOwnerMiss exactIds) :
    X_loopEnvSameRank exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hex hbord hv hreal hscope₀ hscope₁ r l hly htin hvin hvte
  have hmem : l ∈ run.layers := List.mem_of_getElem? hly
  obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp htin
  obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvin
  exact XLEM_sameRankMiss_holds exactIds hright hleft hgroup
    inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hmem hpu hpv

/-- Other-rank direction from the finished other-rank miss: layer indices give
proper ranks, and proper rank equals coordinate rank on exact runs. -/
theorem X_loopEnvOtherRank_of_otherRankMiss (exactIds : List String)
    (hother : XLEM_OtherRankMiss exactIds) :
    X_loopEnvOtherRank exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hex hbord hv hreal hscope₀ hscope₁ rt rv lt lv
    hly_t htin_t hly_v hvin_v hne
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hordEx, hxs, hproxy, hdrop,
      hroute, hrouting, hpts⟩ := componentRunX_spec hrun
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hproxy).2.1
  have hgeom := (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, _, hlay, _, _⟩ := RouteImpl.layersOk_spec hgeom
  have hrk_t : rk run.proper.rank e.tail = (rt : Int) :=
    (hlay rt lt hly_t e.tail htin_t).2
  have hrk_v : rk run.proper.rank v = (rv : Int) :=
    (hlay rv lv hly_v v hvin_v).2
  rw [hrankEq] at hrk_t hrk_v
  have e1 : (rk run.coordinateProper.rank e.tail).toNat = rt := by omega
  have e2 : (rk run.coordinateProper.rank v).toNat = rv := by omega
  have hne' : (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat := by omega
  exact hother inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope₀ hscope₁ hne'

/-- Closed loop-envelope miss: the seam-field type from the four named parts,
with the nonstandard-owner case as the remaining named premise. -/
theorem X_loopEnvelopeMiss_closed (exactIds : List String)
    (hother : XLEM_OtherRankMiss exactIds)
    (hright : XLEM_PlainRightMiss exactIds)
    (hleft : XLEM_LeftMiss exactIds)
    (hgroup : XLEM_GroupOwnerMiss exactIds)
    (howner : X_loopEnvOtherOwner exactIds) :
    X_LoopEnvelopeMiss exactIds :=
  X_loopEnvelopeMiss_holds exactIds
    (X_loopEnvOtherRank_of_otherRankMiss exactIds hother)
    (X_loopEnvSameRank_of_parts exactIds hright hleft hgroup)
    howner
end PipelineImpl
end Layered
end Elegant
