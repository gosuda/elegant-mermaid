import Elegant.Layered.LoopResNeighborDisjointProof
import Elegant.Layered.LoopResNeighborGapGroupTopWitnessProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.LoopFootprintResidualProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop-footprint neighbor gap, group-top and bottom-owner disjoint cases

Closes the two residuals of `LoopResNeighborDisjointProof.lean`:
`LoopResNeighborGapGroupTopDisj` and `LoopResNeighborGapBottomOwnerDisj`.

Truth-first probe evidence (`proofs/wip/Probe/LoopGapDisjResidualsTProbe.lean`,
`lake env lean` exit 0; every pair below is WellFormed and framedParents):
- `sharedRank` t=0 pos=2: fleft=true xgap=true y1=false y2=false shared=true.
- `tower3` t=0 pos=2: shared=true xgap=true; t=0 pos=4: shared=false xgap=true
  y1=true (unshared rank sets still satisfy the disjunction via the `y`-gap).
- `wideTower` t=0 pos=4: shared=false xgap=true y1=true.
- `zeroSize` (empty texts) t=0 pos=2: shared=true xgap=true.
- `nested` (loop on inner group top) t=1 pos=3: shared=true xgap=true.
- `emptyForeign`: no executed group-top pair (empty group sits in a separate
  component), so the universal claim is vacuous there.
- `dangling` (ill-formed): `measuredGraph` fails, so there is no executed run.
- `bottomLoopOwners = 0` on all seven inputs: no executed self-loop sits on a
  `border = 2` node, so the bottom-owner case below is vacuous (proved, via
  the public `LoopFootprintBottomEmpty_holds`).

Group-top proof by cases on the closed rank spans (`foreignClusterRankSpans'`):
disjoint spans give a `y`-gap through the rank-axis bands
(`fbs_member_hulls_y_separated`); overlapping spans give a shared marker rank,
hence the shared-rank witness (`loopResNeighborGapGroupTopWitnessShared_holds`)
and the `x`-gap (`loopResNeighborGapGroupTopShared_holds`).  The only named
seam premises are `ForeignBorderLayerOrder` and `ForeignBorderChainXAligned`;
the rank spans are a closed fact. -/

/-- Local copy of the private `lines_len`: executed lines cover every box. -/
private theorem lrngd_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Shared proper-rank pair from two coordinate markers at one rank: the
border records survive into `run.proper`, `getLast?` gives membership, and
the rank equality transports along `hrankEq`. -/
private theorem lrngd_shared_of_marks {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hrankEq : run.proper.rank = run.coordinateProper.rank)
    {mU mW : Nat} {nU nW : ProperNode} {du dw : Nat} {r : Int}
    (hU : run.coordinateProper.nodes[mU]? = some nU)
    (hbU : nU.node.border = -1 ∨ nU.node.border = 1)
    (hoU : nU.node.clusterPath.getLast? = some du)
    (hrU : rk run.coordinateProper.rank mU = r)
    (hW : run.coordinateProper.nodes[mW]? = some nW)
    (hbW : nW.node.border = -1 ∨ nW.node.border = 1)
    (hoW : nW.node.clusterPath.getLast? = some dw)
    (hrW : rk run.coordinateProper.rank mW = r) :
    ∃ (a b : Nat) (na nb : ProperNode), run.proper.nodes[a]? = some na ∧
      na.node.clusterPath.contains du = true ∧
      run.proper.nodes[b]? = some nb ∧
      nb.node.clusterPath.contains dw = true ∧
      rk run.proper.rank a = rk run.proper.rank b := by
  obtain ⟨hpU, -⟩ := componentRun_border_record hrun hU hbU
  obtain ⟨hpW, -⟩ := componentRun_border_record hrun hW hbW
  refine ⟨mU, mW, nU, nW, hpU, ?_, hpW, ?_, ?_⟩
  · exact List.contains_iff_mem.mpr (List.mem_of_getLast? hoU)
  · exact List.contains_iff_mem.mpr (List.mem_of_getLast? hoW)
  · rw [hrankEq, hrU, hrW]

/-- Overlapping rank spans give the `x`-gap: the overlap rank carries a
marker pair of each declaration, which is a shared proper rank, so the
shared-rank witness and the shared-rank gap apply. -/
private theorem lrngd_xgap_of_overlap {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) (horder : ForeignBorderLayerOrder)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl)
    (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x)
    {tU bU tW bW : Int}
    (hUle : tU ≤ bU) (hWle : tW ≤ bW)
    (hUmark : ∀ r : Int, tU ≤ r → r ≤ bU →
      ∃ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
          nL.node.clusterPath.getLast? = some nt.decl ∧
          rk run.coordinateProper.rank mL = r ∧
          run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
          nR.node.clusterPath.getLast? = some nt.decl ∧
          rk run.coordinateProper.rank mR = r)
    (hWmark : ∀ r : Int, tW ≤ r → r ≤ bW →
      ∃ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
          nL.node.clusterPath.getLast? = some np.decl ∧
          rk run.coordinateProper.rank mL = r ∧
          run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
          nR.node.clusterPath.getLast? = some np.decl ∧
          rk run.coordinateProper.rank mR = r)
    (hov1 : tW ≤ bU) (hov2 : tU ≤ bW) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hwit := loopResNeighborGapGroupTopWitnessShared_holds hwf hfp hx
    horder execution hcomp hrun
  by_cases hlt : tU ≤ tW
  · obtain ⟨mUL, _, _, _, hrecUL, hbUL, hoUL, hrkUL, _, _, _, _⟩ :=
      hUmark tW hlt hov1
    obtain ⟨mWL, _, _, _, hrecWL, hbWL, hoWL, hrkWL, _, _, _, _⟩ :=
      hWmark tW (Int.le_refl tW) hWle
    have hShared := lrngd_shared_of_marks hrun hrankEq hrecUL (Or.inl hbUL)
      hoUL hrkUL hrecWL (Or.inl hbWL) hoWL hrkWL
    exact loopResNeighborGapGroupTopShared_holds hwf hfp hx execution hcomp
      hrun hwit hnt htG het hnp hgrp hne hne2 hni1 hni2 hFL hShared
  · obtain ⟨mUL, _, _, _, hrecUL, hbUL, hoUL, hrkUL, _, _, _, _⟩ :=
      hUmark tU (Int.le_refl tU) hUle
    obtain ⟨mWL, _, _, _, hrecWL, hbWL, hoWL, hrkWL, _, _, _, _⟩ :=
      hWmark tU (by omega) hov2
    have hShared := lrngd_shared_of_marks hrun hrankEq hrecUL (Or.inl hbUL)
      hoUL hrkUL hrecWL (Or.inl hbWL) hoWL hrkWL
    exact loopResNeighborGapGroupTopShared_holds hwf hfp hx execution hcomp
      hrun hwit hnt htG het hnp hgrp hne hne2 hni1 hni2 hFL hShared

/-- `y`-gap when the owner span sits strictly above the foreign span: every
owner member ranks below every foreign member, so the band tops order the
member hulls and the footprint (same `y`/`h` as the owner frame) ends above
the foreign frame top. -/
private theorem lrngd_ygap_below {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    {tU bU tW bW : Int}
    (hUspan : ∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains nt.decl =
        true →
      tU ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bU)
    (hWspan : ∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains np.decl =
        true →
      tW ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bW)
    (hdisj : bU < tW) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, _, hmemT⟩ :=
    fbs_group_node_member execution.graph_eq hcomp hrun hnt htG
  obtain ⟨_, _, _, hmemP⟩ :=
    fbs_group_node_member execution.graph_eq hcomp hrun hnp hgrp
  have hneT : groupMemberRects
      (componentCandidate execution.graph comp candidate) run nt.decl ≠ [] :=
    List.ne_nil_of_mem hmemT
  have hneP : groupMemberRects
      (componentCandidate execution.graph comp candidate) run np.decl ≠ [] :=
    List.ne_nil_of_mem hmemP
  have hbelow : ∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains nt.decl =
        true →
      ∀ v', v' < run.proper.nodes.length →
        (run.proper.nodes.getD v' default).node.clusterPath.contains
          np.decl = true →
        rk run.proper.rank v < rk run.proper.rank v' := by
    intro v hv hcv v' hv' hcv'
    have hu1 := hUspan v hv hcv
    have hw1 := hWspan v' hv' hcv'
    omega
  have hsep := fbs_member_hulls_y_separated hrun hry hbelow hneT hneP
  have hfy : (loopFootprint (componentCandidate execution.graph comp candidate)
      run execution.measured t).y =
      (frameRect default
        (componentCandidate execution.graph comp candidate) run t).y := rfl
  have hfh : (loopFootprint (componentCandidate execution.graph comp candidate)
      run execution.measured t).h =
      (frameRect default
        (componentCandidate execution.graph comp candidate) run t).h := rfl
  have hTy : (frameRect default
      (componentCandidate execution.graph comp candidate) run t).y =
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        nt.decl) []).minY := by
    rw [frameRect_group_span hnt htG]
  have hTh : (frameRect default
      (componentCandidate execution.graph comp candidate) run t).h =
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        nt.decl) []).bottom -
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        nt.decl) []).minY := by
    rw [frameRect_group_span hnt htG]
  have hPy : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).y =
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        np.decl) []).minY := by
    rw [frameRect_group_span hnp hgrp]
  rw [hfy, hfh]
  omega

/-- `y`-gap when the foreign span sits strictly above the owner span: every
foreign member ranks below every owner member, so the foreign member hull
ends below the footprint top (same `y` as the owner frame). -/
private theorem lrngd_ygap_above {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    {tU bU tW bW : Int}
    (hWspan : ∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains np.decl =
        true →
      tW ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bW)
    (hUspan : ∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains nt.decl =
        true →
      tU ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bU)
    (hdisj : bW < tU) :
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, _, hmemT⟩ :=
    fbs_group_node_member execution.graph_eq hcomp hrun hnt htG
  obtain ⟨_, _, _, hmemP⟩ :=
    fbs_group_node_member execution.graph_eq hcomp hrun hnp hgrp
  have hneT : groupMemberRects
      (componentCandidate execution.graph comp candidate) run nt.decl ≠ [] :=
    List.ne_nil_of_mem hmemT
  have hneP : groupMemberRects
      (componentCandidate execution.graph comp candidate) run np.decl ≠ [] :=
    List.ne_nil_of_mem hmemP
  have habove : ∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains np.decl =
        true →
      ∀ v', v' < run.proper.nodes.length →
        (run.proper.nodes.getD v' default).node.clusterPath.contains
          nt.decl = true →
        rk run.proper.rank v < rk run.proper.rank v' := by
    intro v hv hcv v' hv' hcv'
    have hw1 := hWspan v hv hcv
    have hu1 := hUspan v' hv' hcv'
    omega
  have hsep := fbs_member_hulls_y_separated hrun hry habove hneP hneT
  have hQy : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).y =
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        np.decl) []).minY := by
    rw [frameRect_group_span hnp hgrp]
  have hQh : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).h =
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        np.decl) []).bottom -
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        np.decl) []).minY := by
    rw [frameRect_group_span hnp hgrp]
  have hFy : (loopFootprint
      (componentCandidate execution.graph comp candidate) run
      execution.measured t).y =
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run
        nt.decl) []).minY := by
    have hfy : (loopFootprint
        (componentCandidate execution.graph comp candidate) run
        execution.measured t).y =
        (frameRect default
          (componentCandidate execution.graph comp candidate) run t).y := rfl
    rw [hfy, frameRect_group_span hnt htG]
  rw [hQy, hQh, hFy]
  omega

/-- Group-top disjoint gap from the closed rank spans and the two order
seams: disjoint spans give a `y`-gap through the rank-axis bands, overlapping
spans give a shared marker rank and hence the `x`-gap. -/
theorem loopResNeighborGapGroupTopDisj_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) (horder : ForeignBorderLayerOrder)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResNeighborGapGroupTopDisj execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  intro t nt hnt htG het pos np hnp hgrp hne hne2 hni1 hni2 hFL
  have hlines : execution.lines.length = inp.boxes.length :=
    lrngd_lines_len execution
  obtain ⟨tU, bU, tW, bW, hUle, hWle, hUspan, hWspan, hUmark, hWmark⟩ :=
    foreignClusterRankSpans' execution.graph_eq hlines hwf hfp hcomp hrun
      hnt hnp htG hgrp hne2
  by_cases hdisj : bU < tW
  · exact Or.inr (Or.inl (lrngd_ygap_below execution hcomp hrun hnt htG hnp
      hgrp hUspan hWspan hdisj))
  · have hov1 : tW ≤ bU := by omega
    by_cases hdisj2 : bW < tU
    · exact Or.inr (Or.inr (lrngd_ygap_above execution hcomp hrun hnt htG hnp
        hgrp hWspan hUspan hdisj2))
    · have hov2 : tU ≤ bW := by omega
      exact Or.inl (lrngd_xgap_of_overlap hwf hfp hx horder execution hcomp
        hrun hnt htG het hnp hgrp hne hne2 hni1 hni2 hFL hUle hWle hUmark
        hWmark hov1 hov2)
/-- Bottom-owner disjoint gap, vacuous on executed runs: a `border = 2`
node owns no loop sizes (`LoopFootprintBottomEmpty_holds`, public), so the
self-loop witness is contradictory. Needs no seam premise. Probe:
`bottomLoopOwners = 0` on all seven
`LoopGapDisjResidualsTProbe.lean` inputs. -/
theorem loopResNeighborGapBottomOwnerDisj_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResNeighborGapBottomOwnerDisj execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  intro t nt hnt htB het pos np hnp _hgrpB _hne _hne2 _hni1 _hni2 _hFL
  have hvlen : t < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnt).1
  have hget : (componentCandidate execution.graph comp candidate).nodes.getD t
      default = nt := by
    simp only [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
  have hborder : ((componentCandidate execution.graph comp candidate).nodes.getD t
      default).border = 2 := by
    rw [hget, htB]
  have hempty := LoopFootprintBottomEmpty_holds execution comp candidate run
    orderOptions t hcomp hrun hvlen hborder
  obtain ⟨ed, hmem, htail, hhead⟩ := het
  have hmemF : ed ∈ loopEdges
      (componentCandidate execution.graph comp candidate).edges t := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    simp only [htail, hhead, beq_self_eq_true, Bool.and_self]
  have hne : loopEdges
      (componentCandidate execution.graph comp candidate).edges t ≠ [] :=
    List.ne_nil_of_mem hmemF
  have hneS : loopSizes (componentCandidate execution.graph comp candidate).edges
      execution.measured t
      (componentCandidate execution.graph comp candidate).slot ≠ [] := by
    intro hnil
    have hmap : (loopEdges
        (componentCandidate execution.graph comp candidate).edges t).map
        (fun e_ => stackSize
          (componentCandidate execution.graph comp candidate).slot
          (routeLabels execution.measured e_.decl)) = [] := hnil
    rw [List.map_eq_nil_iff] at hmap
    exact hne hmap
  exact False.elim (hneS hempty)


end PipelineImpl
end Layered
end Elegant
