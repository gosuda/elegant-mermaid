import Elegant.Layered.FamilyC5Measured
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BracketInsideRankFacts
import Elegant.Layered.FrameClearanceBottomFacts
import Elegant.Layered.BottomSeamsRank
import Elegant.Layered.Coords
import Elegant.Layered.CoordGraph
set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Bottom-proxy transport residual (coordinate/proper phase): for a measured
component run, the `border = 2` bottom marker keeps border `2` in the
coordinate graph with its declaration as path last, its proper node lies in the
title node's member set, its proper height is zero (`titleF` zeroes proxy
extents and neither `proxyWidths` nor `dropSynthetic` restores height), its
routed `ys` entry is nonnegative, and both indices are live in `run.proper`
(the coordinate index additionally in `run.coordinateProper`). Pinned to the
executed equations `measuredGraph ... = .ok graph` with `comp ∈ components
graph` and `componentRun ... = .ok run`. -/
def BottomProxyRunFacts (P : Params) (graph : Graph) : Prop :=
  ∀ {inp : Input} {o : Options} {lines : List (List Measure.Line)},
  measuredGraph P inp o lines = .ok graph →
  ∀ {comp : List Nat}, comp ∈ components graph →
  ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
  componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run →
  ∀ {v t : Nat},
  ((componentCandidate graph comp candidate).nodes.getD v default).border = 2 →
  ((componentCandidate graph comp candidate).nodes.getD t default).border = -2 →
  ((componentCandidate graph comp candidate).nodes.getD v default).decl =
    ((componentCandidate graph comp candidate).nodes.getD t default).decl →
  (run.coordinateProper.nodes.getD v default).node.border = 2 ∧
  (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
    some ((componentCandidate graph comp candidate).nodes.getD v default).decl ∧
  (run.proper.nodes.getD v default).node.clusterPath.contains
    ((componentCandidate graph comp candidate).nodes.getD t default).decl = true ∧
  RouteImpl.nodeH run.proper v = 0 ∧
  0 ≤ run.ys.getD v 0 ∧
  v < run.proper.nodes.length ∧ t < run.proper.nodes.length ∧
  v < run.coordinateProper.nodes.length
/-- A `border = 2` graph node index is in bounds and its `getD` lookup is a
real `getElem?` lookup; out-of-bounds reads hit the default node of border
`0`. Mirrors `group_top_index` (`GroupTopFacts.lean`). -/
private theorem bottom_marker_index {cg : Graph} {v : Nat}
    (hcb : (cg.nodes.getD v default).border = 2) :
    v < cg.nodes.length ∧ cg.nodes[v]? = some (cg.nodes.getD v default) := by
  by_cases hlt : v < cg.nodes.length
  · have hg : cg.nodes[v]? = some (cg.nodes.getD v default) := by
      rw [List.getD_eq_getElem?_getD]
      simp [List.getElem?_eq_getElem hlt]
    exact ⟨hlt, hg⟩
  · exfalso
    have hget : cg.nodes[v]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_none] at hcb
    have hz : (default : Node).border = 0 := rfl
    rw [hz] at hcb
    omega

/-- A `border = -2` graph node index is in bounds and its `getD` lookup is a
real `getElem?` lookup. Mirrors `group_top_index`. -/
private theorem top_marker_index {cg : Graph} {v : Nat}
    (hcb : (cg.nodes.getD v default).border = -2) :
    v < cg.nodes.length ∧ cg.nodes[v]? = some (cg.nodes.getD v default) := by
  by_cases hlt : v < cg.nodes.length
  · have hg : cg.nodes[v]? = some (cg.nodes.getD v default) := by
      rw [List.getD_eq_getElem?_getD]
      simp [List.getElem?_eq_getElem hlt]
    exact ⟨hlt, hg⟩
  · exfalso
    have hget : cg.nodes[v]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_none] at hcb
    have hz : (default : Node).border = 0 := rfl
    rw [hz] at hcb
    omega

/-- A candidate `border = 2` bottom marker carries its declaration as path last
and lies in its own member set. From `componentCandidate_nonplain_source` and
`measuredGraph_bottom_origin`. -/
private theorem bottom_marker_path {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = 2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨original, horiginal, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨box, hbox, hrole, hpath, hw, hh⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hborder
  exact ⟨by rw [hpath]; simp, by rw [hpath]; simp⟩

/-- The coordinate-graph record of a `border = 2` bottom marker: the titled,
cleared marker at the same index, of height zero. Mirrors
`group_top_coordinate_record`. -/
private theorem bottom_marker_coordinate_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, hnodeRec, _⟩ := componentRun_ranked_node_records hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hnodeRec v nd hnode
  have hmarker := coordinateGraph_marker_record (P := P) hrec (Or.inr hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))
/-- The executed record of the `border = 2` bottom proxy keeps the coordinate
record's cluster path, and its proper height is zero. Mirrors
`group_top_proper_clusterPath`. -/
private theorem bottom_marker_proper_node {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    componentRun_proxy_interval hrun hcoord (Or.inr hb)
  refine ⟨_, hproper, rfl, ?_⟩
  simp only [RouteImpl.nodeH, hproper]
  exact hcoordH

/-- The bottom-proxy transport facts, proved from the executed pipeline. -/
theorem bottomProxyRunFacts : ∀ (P : Params) (graph : Graph), BottomProxyRunFacts P graph := by
  intro P graph inp o lines hgraph comp hcomp candidate run labels orderOptions hrun v t hbordV hbordT hdecl
  obtain ⟨hvLt, hvGet⟩ := bottom_marker_index hbordV
  obtain ⟨htLt, htGet⟩ := top_marker_index hbordT
  obtain ⟨hpathLast, hcontainsSelf⟩ :=
    bottom_marker_path (graph := graph) hgraph hvGet hbordV
  obtain ⟨coord, hcoord, hcoordB, hcoordD, hcoordP, hcoordH⟩ :=
    bottom_marker_coordinate_record hrun hvGet hbordV
  obtain ⟨p, hproper, hproperP, hnodeH⟩ :=
    bottom_marker_proper_node hrun hcoord hcoordB hcoordH
  have hcoordD0 : run.coordinateProper.nodes.getD v default = coord := by
    rw [List.getD_eq_getElem?_getD, hcoord, Option.getD_some]
  subst hcoordD0
  have hvLen : v < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun v hvLt
  have htLen : t < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun t htLt
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvCoord : v < run.coordinateProper.nodes.length := by omega
  have hproperD : run.proper.nodes.getD v default = p := by
    rw [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
  have hcontains : (run.proper.nodes.getD v default).node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true := by
    rw [hproperD, hproperP, hcoordP, ← hdecl]
    exact hcontainsSelf
  have hband := (fbs_run_node_band hrun v hvLen).1
  have htopnn := fbs_run_top_nonneg hrun (rk run.proper.rank v).toNat
  have hysnn : 0 ≤ run.ys.getD v 0 := by omega
  exact ⟨hcoordB, by rw [hcoordP]; exact hpathLast, hcontains, hnodeH, hysnn,
    hvLen, htLen, hvCoord⟩
/-- Open seam (nesting-chain rank order): a bottom marker of a group nested
strictly inside the outer group (`decl` differs from the outer title's) ranks
at or below the outer bottom proxy. The discharge route is the upward chain:
pair the nested bottom with its group top, bound each ancestor bottom by its
parent bottom through `ranked_compound_child_interval`
(`componentRun_direct_group_rank_interval` supplies finds without line-count
premises), and close membership with `CandidateParentTopExists` (which needs
`WellFormed` and `framedParents`, to be added when this seam is discharged).
Pinned to the executed equations; strictly simpler than the geometric goal. -/
def BottomNestedBottomRankLe (P : Params) (graph : Graph) : Prop :=
  ∀ {inp : Input} {o : Options} {lines : List (List Measure.Line)},
  measuredGraph P inp o lines = .ok graph →
  ∀ {comp : List Nat}, comp ∈ components graph →
  ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
  componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run →
  ∀ {v t : Nat} {ndV ndT : Node},
  (componentCandidate graph comp candidate).nodes[v]? = some ndV →
  (componentCandidate graph comp candidate).nodes[t]? = some ndT →
  ndV.border = 2 → ndT.border = -2 → ndV.decl = ndT.decl →
  ∀ {j : Nat} {nb : Node},
  (componentCandidate graph comp candidate).nodes[j]? = some nb →
  nb.border = 2 → nb.decl ≠ ndT.decl →
  nb.clusterPath.contains ndT.decl = true →
  rk run.coordinateProper.rank j ≤ rk run.coordinateProper.rank v

/-- Open seam (construction-rank order): a synthetic member of the outer
group's frame (a label dummy, a side border, or a title copy) ranks at or
below the outer bottom proxy. Discharge routes: side markers through
`coordinateGraph_side_rank_bounds` against their own top and bottom (which
the original-rank induction below already bounds); title copies through the
title-rank source (`titleReservations` copies carry their anchor rank, the
anchor being an original top); dummies through
`componentRun_dummy_path_chain_source` (chain-rank contiguity puts a dummy
between its endpoint ranks, both endpoints being originals). Pinned to the
executed equations; strictly simpler than the geometric goal. -/
def BottomSyntheticRankLe (P : Params) (graph : Graph) : Prop :=
  ∀ {inp : Input} {o : Options} {lines : List (List Measure.Line)},
  measuredGraph P inp o lines = .ok graph →
  ∀ {comp : List Nat}, comp ∈ components graph →
  ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
  componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run →
  ∀ {v t : Nat} {ndV ndT : Node},
  (componentCandidate graph comp candidate).nodes[v]? = some ndV →
  (componentCandidate graph comp candidate).nodes[t]? = some ndT →
  ndV.border = 2 → ndT.border = -2 → ndV.decl = ndT.decl →
  ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
  q.1.node.clusterPath.contains
    ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
  (q.1.dummy = true ∨ q.1.node.border = -1 ∨ q.1.node.border = 1 ∨
    q.1.node.border = 3) →
  rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v

/-- Monotone `toNat` for nonnegative ranks. -/
private theorem rkToNat_le {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) :
    a.toNat ≤ b.toNat := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha h)
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by omega
  exact Int.ofNat_le.mp h3
private theorem le_foldr_max_mem {l : List Nat} {a : Nat} (h : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons head rest ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- A nonempty filter yields a member. -/
private theorem filter_ne_nil_of_not_empty {α : Type} {l : List α}
    (h : l.isEmpty = false) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

/-- Original member rank bound by fuel induction over cluster-path length,
mirroring `componentRun_group_top_lt_bottom`. Every candidate-graph original
node whose cluster path contains the outer title's declaration ranks at or
below the outer bottom proxy in the ranking: plain members by
`ranked_compound_member_interval` against the outer group; tops by their own
group's member/child/empty edges with the induction hypothesis on strictly
longer paths; the outer bottom itself by
`componentCandidate_bottom_find_eq`; nested bottoms defer to
`BottomNestedBottomRankLe`. No line-count premises are needed: every bottom
find comes from `componentRun_group_bottom_source` plus
`candidate_titled_bottom_constraint_source`. -/
theorem bottomOrigRankLe
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : ∀ P graph, BottomNestedBottomRankLe P graph) :
    ∀ {idx : Nat} {n : Node},
    (componentCandidate graph comp candidate).nodes[idx]? = some n →
    n.clusterPath.contains ndT.decl = true →
    rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, _, hranks, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  have hfindV : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndV.decl) = some (ndV, v) :=
    componentCandidate_bottom_find_eq hgraph hcomp hvGet hbordV
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
    rw [← hdecl]; exact hfindV
  have htopOuter : ((ndT, t) : Node × Nat) ∈
      (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htGet
  have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h2 := prepared_coordinate_original_rk (P := P) hrr hranks
      (List.getElem?_eq_some_iff.mp hvGet).1
    rw [hc] at h2
    exact h2
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
    exact le_foldr_max_mem hmap
  have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath ≠ [] := by
    intro index node hnode hgroup hnil
    exact (componentCandidate_marker_shape hgraph hnode).2 hgroup hnil
  have main : ∀ fuel idx n, cg.nodes[idx]? = some n →
      n.clusterPath.contains ndT.decl = true →
      maxLen - n.clusterPath.length = fuel → rk rr.ranks idx ≤ rk rr.ranks v := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro idx n hidx hcontains hfuel
      rcases (componentCandidate_marker_shape hgraph hidx).1 with hplain | hgroup | hbottom
      · -- plain member: outer interval directly
        have hinterval := ranked_compound_member_interval hrr htopOuter hbordT
          hbotFindOuter (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hplain hcontains
        have hle : rk rr.ranks idx + 1 ≤ rk rr.ranks v := hinterval.2
        omega
      · -- top marker: own-group edges
        obtain ⟨rrB, labeledB, bottomTB, hrrB, hcB, hkB, hreadyB, hrecordsB, hranksB,
            htitledB, hfindB⟩ :=
          componentRun_group_bottom_source hgraph hcomp hrun hidx hgroup
        obtain ⟨origB, horigB, hborderB, hpathB, hrecordB, hfindCB⟩ :=
          candidate_titled_bottom_constraint_source hgraph hkB hrecordsB hidx hgroup hfindB
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
          · have hne := hdeq
            have hleB : rk run.coordinateProper.rank bottomTB.2 ≤
                rk run.coordinateProper.rank v :=
              hnest P graph hgraph hcomp hrun hvGet htGet hbordV hbordT hdecl
                horigB hborderB hne hpathBmem
            have e1 : rk run.coordinateProper.rank bottomTB.2 =
                rk rr.ranks bottomTB.2 := by
              have h1 := prepared_coordinate_original_rk (P := P) hrr hranks
                (List.getElem?_eq_some_iff.mp horigB).1
              rw [hc] at h1
              exact h1
            omega
        cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
            entry.1.border == 0 && entry.1.clusterPath.contains n.decl).isEmpty with
        | false =>
          obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
            (filter_ne_nil_of_not_empty hmemCase)
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
              (filter_ne_nil_of_not_empty hchildCase)
            obtain ⟨hchildTop, hchildPath⟩ := List.mem_filter.mp hchildMem
            obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
            have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
            have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
            obtain ⟨rrC, labeledC, bottomTC, hrrC, hcC, hkC, hreadyC, hrecordsC, hranksC,
                htitledC, hfindC⟩ :=
              componentRun_group_bottom_source hgraph hcomp hrun hchildIndex hchildGroup'
            obtain ⟨origC, horigC, hborderC, hpathC, hrecordC, hfindCC⟩ :=
              candidate_titled_bottom_constraint_source hgraph hkC hrecordsC hchildIndex
                hchildGroup' hfindC
            have hpathEq : child.1.clusterPath.dropLast = n.clusterPath := by
              simpa using hchildPath
            have hdirect := ranked_compound_child_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
              hchildZip hchildGroup' hpathEq hfindCC
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
                rw [← hpathEq]; exact List.dropLast_prefix _
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
      · -- bottom marker: outer itself or nested residual
        by_cases hdeq : n.decl = ndT.decl
        · have hfindEq : (componentCandidate graph comp candidate).nodes.zipIdx.find?
              (fun entry => entry.1.border == 2 && entry.1.decl == n.decl) =
              some (n, idx) :=
            componentCandidate_bottom_find_eq hgraph hcomp hidx hbottom
          rw [hdeq] at hfindEq
          have heq : (n, idx) = (ndV, v) :=
            Option.some.inj (hfindEq.symm.trans hbotFindOuter)
          have hiv : idx = v := congrArg Prod.snd heq
          rw [hiv]
          exact Int.le_refl _
        · have hleB : rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v :=
            hnest P graph hgraph hcomp hrun hvGet htGet hbordV hbordT hdecl
              hidx hbottom hdeq hcontains
          have e1 : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
            have h1 := prepared_coordinate_original_rk (P := P) hrr hranks
              (List.getElem?_eq_some_iff.mp hidx).1
            rw [hc] at h1
            exact h1
          omega
  intro idx n hidx hcontains
  have hrr_le := main (maxLen - n.clusterPath.length) idx n hidx hcontains rfl
  have eI : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranks
      (List.getElem?_eq_some_iff.mp hidx).1
    rw [hc] at h1
    exact h1
  omega



/-- The bottom edge of a group frame equals `Y` when one member rectangle has
bottom `Y` and every member rectangle bottom is at most `Y`: the frame height
is `vertical.bottom - vertical.minY`, so the top cancels. Mirrors
`frameRect_top_eq_of_members`. -/
theorem frameRect_bottom_eq_of_members
    {P : Params} {cg : Graph} {run : Run} {t v : Nat} {Y : Int}
    (hf : (cg.nodes.getD t default).border = -2)
    (hmem : Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none))
    (hY : (Labels.rectAt run.proper run.xs run.ys v).y +
      (Labels.rectAt run.proper run.xs run.ys v).h = Y)
    (hzero : 0 ≤ Y)
    (hall : ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none), r.y + r.h ≤ Y) :
    (frameRect P cg run t).y + (frameRect P cg run t).h = Y := by
  have hle := boundsOf_bottom_le_of_all hzero hall
  have hmem' := rect_bottom_le_boundsOf_bottom _ [] _ hmem
  simp only [frameRect, hf, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  omega

/-- The horizontal span of a bottom proxy's box lies inside its group frame's
horizontal span. Mirrors `componentRun_group_frame_x_contains_port`: the proxy
span comes from rank-matched side borders, and every such border also belongs
to the frame's wider horizontal hull (via the declaration equation). -/
theorem componentRun_group_bottom_frame_x_contains_port
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v t : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hborder : (run.coordinateProper.nodes.getD v default).node.border = 2)
    (hcborderT : (cg.nodes.getD t default).border = -2)
    (hdecl : (cg.nodes.getD v default).decl = (cg.nodes.getD t default).decl)
    (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl)
    (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    (frameRect P cg run t).x ≤ px ∧
      px ≤ (frameRect P cg run t).x + (frameRect P cg run t).w := by
  obtain ⟨owner, span, ownerEq, hspan, _, _, hleft, hright⟩ :=
    componentRun_proxy_interval hrun hnode (Or.inr hborder)
  have hownerEq : owner = (cg.nodes.getD t default).decl := by
    have h := Option.some.inj (ownerEq.symm.trans howner)
    rw [hdecl] at h
    exact h
  obtain ⟨li, ri, left, right, hleftGet, hrightGet, hleftBorder, hrightBorder,
    hleftOwner, hrightOwner, _, _, hlo, hhi⟩ := proxySpan_endpoint_sources hspan
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with h | h <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with h | h <;> omega
  obtain ⟨hleftProper, hleftXs⟩ := componentRun_nonproxy_record hrun hleftGet hleftNotProxy
  obtain ⟨hrightProper, hrightXs⟩ := componentRun_nonproxy_record hrun hrightGet hrightNotProxy
  have hleftOwner' : left.node.clusterPath.getLast? =
      some (cg.nodes.getD t default).decl := by rw [hleftOwner, hownerEq]
  have hrightOwner' : right.node.clusterPath.getLast? =
      some (cg.nodes.getD t default).decl := by rw [hrightOwner, hownerEq]
  have hleftRect : Labels.rectAt run.proper run.xs run.ys li ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(left, li), List.mem_zipIdx_iff_getElem?.mpr hleftProper, ?_⟩
    rcases hleftBorder with h | h
    · simp [h, hleftOwner']
    · simp [h, hleftOwner']
  have hrightRect : Labels.rectAt run.proper run.xs run.ys ri ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(right, ri), List.mem_zipIdx_iff_getElem?.mpr hrightProper, ?_⟩
    rcases hrightBorder with h | h
    · simp [h, hrightOwner']
    · simp [h, hrightOwner']
  have hleftLo : (Labels.rectAt run.proper run.xs run.ys li).x = span.lo := by
    have hw : RouteImpl.nodeW run.proper li = left.node.w := by
      simp only [RouteImpl.nodeW, hleftProper]
    show run.xs.getD li 0 - Int.fdiv (RouteImpl.nodeW run.proper li) 2 = span.lo
    rw [hleftXs, hlo, hw]
  have hrightHi : (Labels.rectAt run.proper run.xs run.ys ri).x +
      (Labels.rectAt run.proper run.xs run.ys ri).w = span.hi := by
    have hw : RouteImpl.nodeW run.proper ri = right.node.w := by
      simp only [RouteImpl.nodeW, hrightProper]
    show run.xs.getD ri 0 - Int.fdiv (RouteImpl.nodeW run.proper ri) 2 +
      RouteImpl.nodeW run.proper ri = span.hi
    rw [hrightXs, hhi, hw]
  have hminX := boundsOf_minX_le_rect_x _ [] _ hleftRect
  have hrightBound := rect_right_le_boundsOf_right _ [] _ hrightRect
  have hboxX : (RouteImpl.boxRect run.proper run.xs run.ys v).x = span.lo := by
    show RouteImpl.leftOf run.proper run.xs v = span.lo
    exact hleft
  have hboxW : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w = span.hi := by
    show RouteImpl.leftOf run.proper run.xs v +
      RouteImpl.nodeW run.proper v = span.hi
    exact hright
  simp only [frameRect, hcborderT, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

/-- A bottom proxy's port point lies on its group frame boundary: its vertical
coordinate is the frame bottom and its horizontal coordinate stays inside the
frame's horizontal range. Mirrors `componentRun_group_frame_boundary`. -/
theorem componentRun_group_bottom_frame_boundary
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v t : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hborder : (run.coordinateProper.nodes.getD v default).node.border = 2)
    (hcborderT : (cg.nodes.getD t default).border = -2)
    (hdecl : (cg.nodes.getD v default).decl = (cg.nodes.getD t default).decl)
    (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl)
    (ht : t < run.proper.nodes.length)
    (hmem : Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none))
    (hYrect : (Labels.rectAt run.proper run.xs run.ys v).y +
      (Labels.rectAt run.proper run.xs run.ys v).h = run.ys.getD v 0)
    (hall : ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none), r.y + r.h ≤ run.ys.getD v 0)
    (hzero : 0 ≤ run.ys.getD v 0)
    (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run t) := by
  have hx := componentRun_group_bottom_frame_x_contains_port hrun hnode hborder
    hcborderT hdecl howner px hpx
  have hy := frameRect_bottom_eq_of_members (P := P) (t := t) (Y := run.ys.getD v 0)
    hcborderT hmem hYrect hzero hall
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hdims := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouting).1).2.1
  have hshape : ProperDimsNonneg run.proper := by
    intro i nd hget
    have hi : i < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hget).1
    have hw := hdims i hi
    have hnd : RouteImpl.nodeW run.proper i = nd.node.w ∧
        RouteImpl.nodeH run.proper i = nd.node.h := by
      simp only [RouteImpl.nodeW, RouteImpl.nodeH, hget]
      trivial
    omega
  have hdim := frameRect_dims_nonneg P cg run t hshape ht
  simp only [Validator.onBoundary]
  rw [hy]
  refine ⟨hx.1, hx.2, ?_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
  · omega
  · omega

/-- Member rank bound by classification: synthetic members (dummies, side
borders, title copies) defer to `BottomSyntheticRankLe`; non-synthetic members
transport through the coordinate record and `NodeKeys` to candidate-graph
originals, which `bottomOrigRankLe` bounds. -/
theorem bottomMemberRankLe
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hsynth : ∀ P graph, BottomSyntheticRankLe P graph)
    (hnest : ∀ P graph, BottomNestedBottomRankLe P graph) :
    ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
    q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  have hsynthAt := hsynth P graph hgraph hcomp hrun hvGet htGet hbordV hbordT hdecl
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  intro q hq hcontains
  have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, -⟩ := fbs_coordinate_record hrun hqget
  obtain ⟨rr, labeled, hrr, hc, hk, hranks, hrecords, hshape⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  have hncL : (coordinateGraph P labeled).nodes[q.2]? = some nvc := by
    rwa [← hc] at hnc
  rcases coordinateGraph_lookup P labeled hncL with
    ⟨m, hm, hmd, hb, hp, -⟩ | hside | ⟨_, _, _, _, _, hb3, _⟩
  · -- titled image of a labeled node
    by_cases hqd : q.1.dummy = true
    · exact hsynthAt q hq hcontains (Or.inl hqd)
    · have hqdF : q.1.dummy = false := by simpa using hqd
      by_cases hbS : nvc.node.border = -1 ∨ nvc.node.border = 1 ∨ nvc.node.border = 3
      · have hqbS : q.1.node.border = -1 ∨ q.1.node.border = 1 ∨
            q.1.node.border = 3 := by
          rcases hbS with h | h | h
          · exact Or.inl (by rw [← hborderEq]; exact h)
          · exact Or.inr (Or.inl (by rw [← hborderEq]; exact h))
          · exact Or.inr (Or.inr (by rw [← hborderEq]; exact h))
        exact hsynthAt q hq hcontains (Or.inr hqbS)
      · by_cases hbP : nvc.node.border = -2 ∨ nvc.node.border = 2
        · obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
            componentRun_proxy_interval hrun hnc hbP
          have hqq : q.1 =
              { nvc with node := { nvc.node with w := span.hi - span.lo } } :=
            Option.some.inj (hqget.symm.trans hproper)
          have hdu : nvc.dummy = q.1.dummy := by rw [hqq]
          have hmdF : m.dummy = false := by rw [← hmd, hdu]; exact hqdF
          have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
          rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
          · have hncN : n.clusterPath.contains ndT.decl = true := by
              rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
            exact bottomOrigRankLe hgraph hcomp hrun hvGet htGet hbordV hbordT hdecl
              hnest hn hncN
          · rw [hdT] at hmdF
            simp at hmdF
        · obtain ⟨hrecFull, -⟩ := componentRun_nonproxy_record hrun hnc hbP
          have hqq : q.1 = nvc := Option.some.inj (hqget.symm.trans hrecFull)
          have hmdF : m.dummy = false := by rw [← hmd, ← hqq]; exact hqdF
          have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
          rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
          · have hncN : n.clusterPath.contains ndT.decl = true := by
              rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
            exact bottomOrigRankLe hgraph hcomp hrun hvGet htGet hbordV hbordT hdecl
              hnest hn hncN
          · rw [hdT] at hmdF
            simp at hmdF
  · rcases hside.2 with h | h
    · exact hsynthAt q hq hcontains
        (Or.inr (Or.inl (by rw [← hborderEq]; exact h)))
    · exact hsynthAt q hq hcontains
        (Or.inr (Or.inr (Or.inl (by rw [← hborderEq]; exact h))))
  · exact hsynthAt q hq hcontains
      (Or.inr (Or.inr (Or.inr (by rw [← hborderEq]; exact hb3))))

/-- The band transfer: from a rank bound over all member rectangles, every
member bottom edge lies at or below the bottom proxy's routed `ys`. The proxy
itself attains the bound with equality (`proxyYs_getD` at `border = 2`,
zero height); lower bands transport through `rankAxis_bands_disjoint` and
equal bands are definitional. -/
theorem bottomMemberBottom_of_rank
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v t : Nat}
    (hvLen : v < run.proper.nodes.length)
    (hcoordV : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hbV : (run.coordinateProper.nodes.getD v default).node.border = 2)
    (hrank : ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains (cg.nodes.getD t default).decl = true →
      rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v) :
    ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none),
    r.y + r.h ≤ run.ys.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, hyseq, _⟩ :=
    componentRun_spec hrun
  have hrankEq : ∀ x, rk run.proper.rank x = rk run.coordinateProper.rank x := by
    intro x
    rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
    rw [hy]; simp
  have hvY : v < run.coordinateYs.length := by omega
  have hYsV : run.ys.getD v 0 = run.top.getD (rk run.coordinateProper.rank v).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
    have hpg := proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordV hvY
    have hbeqF : ((run.coordinateProper.nodes.getD v default).node.border == -2) =
        false := by rw [hbV]; simp
    have hbeqT : ((run.coordinateProper.nodes.getD v default).node.border == 2) =
        true := by rw [hbV]; simp
    simp only [hbeqF, ↓reduceIte, hbeqT, ↓reduceIte] at hpg
    rw [← hyseq]
    exact hpg
  intro r hr
  obtain ⟨q, hq, hqr⟩ := List.mem_filterMap.mp hr
  have hc : q.1.node.clusterPath.contains (cg.nodes.getD t default).decl = true := by
    by_cases h : q.1.node.clusterPath.contains (cg.nodes.getD t default).decl = true
    · exact h
    · have hf : q.1.node.clusterPath.contains (cg.nodes.getD t default).decl = false :=
        Bool.eq_false_iff.mpr h
      rw [hf] at hqr
      simp at hqr
  have hqr' : Labels.rectAt run.proper run.xs run.ys q.2 = r := by
    rw [hc] at hqr
    simpa using hqr
  have hlen : q.2 < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)).1
  have hband := (fbs_run_node_band hrun q.2 hlen).2
  rw [hrankEq q.2] at hband
  have hrk := hrank q hq hc
  have hqnn : 0 ≤ rk run.coordinateProper.rank q.2 := by
    obtain ⟨_, _, _, hnn⟩ := hcov q.2 hlen
    rw [hrankEq q.2] at hnn
    exact hnn
  have hqq := rkToNat_le hqnn hrk
  have hlayQ := hcov q.2 hlen
  rw [hrankEq q.2] at hlayQ
  obtain ⟨lq, hlyQ, -, -⟩ := hlayQ
  have hlayV := hcov v hvLen
  rw [hrankEq v] at hlayV
  obtain ⟨lv, hlyV, -, -⟩ := hlayV
  have hlyQD : run.layers.getD (rk run.coordinateProper.rank q.2).toNat [] = lq := by
    rw [List.getD_eq_getElem?_getD, hlyQ]
    rfl
  rw [hlyQD] at hband
  have hle : run.top.getD (rk run.coordinateProper.rank q.2).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper lq ≤ run.ys.getD v 0 := by
    by_cases heq : (rk run.coordinateProper.rank q.2).toNat =
        (rk run.coordinateProper.rank v).toNat
    · have htopEq : run.top.getD (rk run.coordinateProper.rank q.2).toNat 0 =
          run.top.getD (rk run.coordinateProper.rank v).toNat 0 := by rw [heq]
      have hlayerEq : CoordsImpl.layerHeight run.coordinateProper lq =
          CoordsImpl.layerHeight run.coordinateProper
            (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
        rw [← hlyQD, heq]
      rw [htopEq, hlayerEq, hYsV]
      exact Int.le_refl _
    · have hlt : (rk run.coordinateProper.rank q.2).toNat <
          (rk run.coordinateProper.rank v).toNat := by omega
      have hdisj := rankAxis_bands_disjoint hry _ _ lq lv hlt hlyQ hlyV
      have hnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lv :=
        RouteImpl.layerHeight_nonneg _ _
      have hlyVD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
        rw [List.getD_eq_getElem?_getD, hlyV]
        rfl
      rw [hYsV, hlyVD]
      omega
  rw [← hqr']
  show RouteImpl.yAt run.ys q.2 + RouteImpl.nodeH run.proper q.2 ≤ _
  exact Int.le_trans hband hle

/-- The group bottom boundary fact, from the two proved transports and the two
remaining one-phase seams. -/
theorem groupBottomBoundaryFacts_executed
    (hsynth : ∀ (P : Params) (graph : Graph), BottomSyntheticRankLe P graph)
    (hnest : ∀ (P : Params) (graph : Graph), BottomNestedBottomRankLe P graph) :
    GroupBottomBoundaryFacts := by
  intro P inp o lines graph hgraph _hlines _hwf _hframed comp hcomp candidate run
    labels orderOptions hrun v t px hbordV hbordT hdecl hpx
  obtain ⟨hvLt, hvGet⟩ := bottom_marker_index hbordV
  obtain ⟨htLt, htGet⟩ := top_marker_index hbordT
  have hR := bottomProxyRunFacts P graph hgraph hcomp hrun hbordV hbordT hdecl
  obtain ⟨hcoordB, howner, hcontains, hHzero, hYnonneg, hvLen, htLen, hvCoord⟩ := hR
  have hrank := bottomMemberRankLe hgraph hcomp hrun hvGet htGet hbordV hbordT hdecl
    hsynth hnest
  have hgetV : run.proper.nodes[v]? = some (run.proper.nodes.getD v default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvLen]
  have hnode : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes.getD v default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvCoord]
  have hAll := bottomMemberBottom_of_rank hrun hvLen hnode hcoordB hrank
  have hq0 : (run.proper.nodes.getD v default, v) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hgetV
  have hmem : Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains
            ((componentCandidate graph comp candidate).nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(run.proper.nodes.getD v default, v), hq0, ?_⟩
    rw [hcontains]
    simp
  have hYrect : (Labels.rectAt run.proper run.xs run.ys v).y +
      (Labels.rectAt run.proper run.xs run.ys v).h = run.ys.getD v 0 := by
    have heq := Elegant.Layered.rectAt_eq_box run.proper run.xs run.ys v
    rw [heq]
    show RouteImpl.yAt run.ys v + RouteImpl.nodeH run.proper v = run.ys.getD v 0
    rw [hHzero]
    show run.ys.getD v 0 + 0 = run.ys.getD v 0
    omega
  exact componentRun_group_bottom_frame_boundary hrun hnode hcoordB hbordT hdecl
    howner htLen hmem hYrect hAll hYnonneg px hpx

