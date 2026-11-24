import Elegant.Layered.LoopResNeighborGapOffRankProof
import Elegant.Layered.LoopResNeighborDisjointProof
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.Pipeline
import Elegant.Layered.CgShape
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds

set_option autoImplicit false
/-! Probes: wit3r top-level (path [], Fleft true, R3 false) shows ungrouped false;
grpOut/grpIn/wideSib grouped off-rank Fleft true CHAIN/R1/R3 true; nest2/zeroFix
spanning true vacuous; topLoop Fleft false vacuous; malformed parent vacuous.
Narrower: parent chain with parent foreign disjointness, parent member y-overlap,
foreign width pos. Consumer: offRank and groupedOffRank need only this; y-disjoint
uses YGap, widths/markers via bracket and spans for parent to discharge. -/

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- File-unique id uniqueness helper (copy of the private helper in
`ExclusiveKeyOutsideCgPathsProof`, which does not resolve outside its file). -/
private theorem lrpc_getElem_unique_id {α : Type} {f : α → String} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hid : f x = f y) :
    x = y := by
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy
  by_cases hij : i = j
  · subst hij
    exact hxi.symm.trans hyj
  · exfalso
    have hp := List.pairwise_iff_getElem.mp hnd
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have h := hp i j (by simpa using hi) (by simpa using hj) hlt
      exact h (by simp only [List.getElem_map, hxi, hyj, hid])
    · exact absurd heq hij
    · have h := hp j i (by simpa using hj) (by simpa using hi) hgt
      exact h (by simp only [List.getElem_map, hyj, hxi, hid])
/-- Every member of a `Compound.ancestors` walk is a group box (file-local
copy; the original is private to another module). -/
private theorem lrpc_path_member_group {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes)
    {i : Nat} (hin : i ∈ Compound.ancestors inp.boxes fuel c.parent) :
    ∃ b, inp.boxes[i]? = some b ∧ b.role = .group := by
  induction fuel generalizing c with
  | zero => simp [Compound.ancestors] at hin
  | succ fuel ih =>
    by_cases hcp : c.parent = ""
    · rw [hcp] at hin
      simp [Compound.ancestors] at hin
    · cases hf : inp.boxes.findIdx? (fun box => box.id == c.parent) with
      | none => simp [Compound.ancestors, hf] at hin
      | some k =>
        obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        cases hb : inp.boxes[k]? with
        | none => simp [Compound.ancestors, hf, hb] at hin
        | some b =>
          have hbElem : inp.boxes[k] = b :=
            Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hb)
          have he : b.id = c.parent := by
            have h := beq_iff_eq.mp hmatch
            rwa [hbElem] at h
          simp only [Compound.ancestors, hf, hb] at hin
          rcases List.mem_append.mp hin with hin | hin
          · exact ih b (List.mem_of_getElem? hb) hin
          · have hik : i = k := List.mem_singleton.mp hin
            subst hik
            have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
            have hall := List.all_eq_true.mp hframed c hc
            have hfalse : (c.parent == "") = false := by
              cases h2 : (c.parent == "") with
              | true => exact absurd (beq_iff_eq.mp h2) hcp
              | false => rfl
            rw [hfalse, Bool.false_or] at hall
            obtain ⟨pb, hpbmem, hpb⟩ := List.any_eq_true.mp hall
            obtain ⟨hpbIdRoleB, _hpbNotFixB⟩ := Bool.and_eq_true_iff.mp hpb
            obtain ⟨hpbIdB, hpbRoleB⟩ := Bool.and_eq_true_iff.mp hpbIdRoleB
            have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
            have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
            have heq : b = pb :=
              lrpc_getElem_unique_id hids (List.mem_of_getElem? hb) hpbmem
                (he.trans hpbId.symm)
            subst heq
            exact ⟨b, hb, hpbRole⟩
/-- Every ancestor is a non-fixed group box (file-local copy). -/
private theorem lrpc_path_member_group_nf {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes)
    {i : Nat} (hin : i ∈ Compound.ancestors inp.boxes fuel c.parent) :
    ∃ b, inp.boxes[i]? = some b ∧ b.role = .group ∧
      inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == b.id) = false := by
  induction fuel generalizing c with
  | zero => simp [Compound.ancestors] at hin
  | succ fuel ih =>
    by_cases hcp : c.parent = ""
    · rw [hcp] at hin
      simp [Compound.ancestors] at hin
    · cases hf : inp.boxes.findIdx? (fun box => box.id == c.parent) with
      | none => simp [Compound.ancestors, hf] at hin
      | some k =>
        obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        cases hb : inp.boxes[k]? with
        | none => simp [Compound.ancestors, hf, hb] at hin
        | some b =>
          have hbElem : inp.boxes[k] = b :=
            Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hb)
          have he : b.id = c.parent := by
            have h := beq_iff_eq.mp hmatch
            rwa [hbElem] at h
          simp only [Compound.ancestors, hf, hb] at hin
          rcases List.mem_append.mp hin with hin | hin
          · exact ih b (List.mem_of_getElem? hb) hin
          · have hik : i = k := List.mem_singleton.mp hin
            subst hik
            have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
            have hall := List.all_eq_true.mp hframed c hc
            have hfalse : (c.parent == "") = false := by
              cases h2 : (c.parent == "") with
              | true => exact absurd (beq_iff_eq.mp h2) hcp
              | false => rfl
            rw [hfalse, Bool.false_or] at hall
            obtain ⟨pb, hpbmem, hpb⟩ := List.any_eq_true.mp hall
            obtain ⟨hpbIdRoleB, hpbNf⟩ := Bool.and_eq_true_iff.mp hpb
            obtain ⟨hpbIdB, hpbRoleB⟩ := Bool.and_eq_true_iff.mp hpbIdRoleB
            have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
            have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
            have heq : b = pb :=
              lrpc_getElem_unique_id hids (List.mem_of_getElem? hb) hpbmem
                (he.trans hpbId.symm)
            subst heq
            have hnf : inp.fixedSizes.any
                (fun fixed : String × Size => fixed.1 == b.id) = false := by
              simpa using hpbNf
            exact ⟨b, hb, hpbRole, hnf⟩
/-- File-local `find?` witness helper (copy of the private helper in
`BottomClearanceExistence`). -/
private theorem lrpc_findSomeOfMember {l : List (Node × Nat)}
    {pred : Node × Nat → Bool} {entry : Node × Nat}
    (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b := by
  exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)
/-- Parent transfer: a graph top for the immediate parent decl appears in the
candidate with the required decl/path facts. Hard steps (top lookup, comp
membership) are hypotheses discharged by later lemmas. -/
private theorem lrpc_parent_transfer {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat}
    {nt : Node}
    {p : Nat} {top : Node}
    (hlast : nt.clusterPath.getLast? = some p)
    (hTopLookup : execution.graph.nodes[p]? = some top)
    (hTopBorder : top.border = -2) (hTopDecl : top.decl = p)
    (hParInComp : p ∈ comp) :
    ∃ (u : Nat) (nu : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some nu ∧
      nu.border = -2 ∧ nu.decl ∈ nt.clusterPath ∧
      nt.clusterPath.getLast? = some nu.decl := by
  obtain ⟨u, hu⟩ := List.mem_iff_getElem?.mp hParInComp
  have hcg : (componentCandidate execution.graph comp candidate).nodes[u]? =
      some top := by
    rw [componentCandidate_nodes]
    show ((componentGraph execution.graph comp).nodes[u]? = some top)
    simp only [componentGraph, List.getElem?_map, hu, Option.map_some]
    rw [List.getD_eq_getElem?_getD, hTopLookup, Option.getD_some]
  refine ⟨u, top, hcg, hTopBorder, ?_, ?_⟩
  · rw [hTopDecl]
    exact List.mem_of_getLast? hlast
  · rw [hTopDecl]; exact hlast
/-- Graph top for the immediate parent decl (from paired markers). -/
private theorem lrpc_top_lookup {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0) (hgrouped : nt.clusterPath ≠ [])
    {p : Nat} (hlast : nt.clusterPath.getLast? = some p) :
    ∃ top : Node, execution.graph.nodes[p]? = some top ∧ top.border = -2 ∧
      top.decl = p := by
  obtain ⟨orig, ho, hsource⟩ :=
    componentCandidate_nonempty_path_source hnt hgrouped
  obtain ⟨boxT, hboxT, hdeclT, hpathT⟩ :=
    execution.plain_node_path_source hsource htB
  have hmemT : p ∈ Compound.path inp.boxes boxT := by
    rw [← hpathT]; exact List.mem_of_getLast? hlast
  rw [Compound.path] at hmemT
  obtain ⟨boxP, hboxP, hroleP, hnfP⟩ :=
    lrpc_path_member_group_nf hwf hframed _ boxT (List.mem_of_getElem? hboxT) hmemT
  have hplt : p < execution.lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hboxP).1
    have hl : execution.lines.length = inp.boxes.length := by
      have h := execution.lines_eq
      unfold boxLines at h
      calc execution.lines.length = (inp.boxes.zipIdx).length :=
          (mapM_getElem? _ _ _ h).1
        _ = inp.boxes.length := List.length_zipIdx
    omega
  have heff : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[p]? = some boxP := by
    simp [List.getElem?_map, hboxP, hnfP]
  have hrole : boxP.role = .group := hroleP
  obtain ⟨top, _, htop, _, hbTop, _, hdecl, _, _, _, _, _⟩ :=
    measuredGraph_paired_markers execution.graph_eq hplt heff hrole
  exact ⟨top, htop, hbTop, hdecl⟩
/-- File-local demote-id (copy of private `demote_id`). -/
private theorem lrpc_demote_id (inp : Input) (b : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
      { b with role := .node } else b).id = b.id := by
  split <;> rfl
/-- File-local demote-parent (copy of private `demote_parent`). -/
private theorem lrpc_demote_parent (inp : Input) (b : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
      { b with role := .node } else b).parent = b.parent := by
  split <;> rfl

/-- Parent decl lies in the same component (via the member constraint edge). -/
private theorem lrpc_parent_in_comp {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0) (hgrouped : nt.clusterPath ≠ [])
    {p : Nat} (hlast : nt.clusterPath.getLast? = some p) : p ∈ comp := by
  obtain ⟨orig, ho, hsource⟩ :=
    componentCandidate_nonempty_path_source hnt hgrouped
  have hoIn : orig ∈ comp := List.mem_of_getElem? ho
  obtain ⟨top, htopLookup, hbTop, hdeclTop⟩ :=
    lrpc_top_lookup hwf hframed execution hnt htB hgrouped hlast
  have htopZip : (top, p) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopLookup
  have hmemZip : (nt, orig) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsource
  have hinside : nt.clusterPath.contains top.decl = true := by
    rw [hdeclTop]; exact List.contains_iff_mem.mpr (List.mem_of_getLast? hlast)
  obtain ⟨boxT, hboxT, _, hpathT⟩ :=
    execution.plain_node_path_source hsource htB
  have hmemT : p ∈ Compound.path inp.boxes boxT := by
    rw [← hpathT]; exact List.mem_of_getLast? hlast
  rw [Compound.path] at hmemT
  obtain ⟨boxP, hboxP, hroleP, hnfP⟩ :=
    lrpc_path_member_group_nf hwf hframed _ boxT (List.mem_of_getElem? hboxT) hmemT
  have hplt : p < execution.lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hboxP).1
    have hl : execution.lines.length = inp.boxes.length := by
      have h := execution.lines_eq
      unfold boxLines at h
      calc execution.lines.length = (inp.boxes.zipIdx).length :=
          (mapM_getElem? _ _ _ h).1
        _ = inp.boxes.length := List.length_zipIdx
    omega
  have heff : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[p]? = some boxP := by
    simp [List.getElem?_map, hboxP, hnfP]
  obtain ⟨_, bottom, _, hbmem, _, hbbord, _, hbdecl, _, _, _, _⟩ :=
    measuredGraph_paired_markers execution.graph_eq hplt heff hroleP
  obtain ⟨bidx, hbidx⟩ := List.mem_iff_getElem?.mp hbmem
  have hpred : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == top.decl)
      (bottom, bidx)) = true := by simp [hbbord, hbdecl, hdeclTop]
  obtain ⟨_, hfind⟩ := lrpc_findSomeOfMember (pred :=
      fun e : Node × Nat => e.1.border == 2 && e.1.decl == top.decl)
    (List.mem_zipIdx_iff_getElem?.mpr hbidx) hpred
  obtain ⟨he1, _⟩ := compound_member_constraint_edges htopZip hbTop hfind
    hmemZip htB hinside
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hbd : ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧
      e.head < execution.graph.nodes.length := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact measuredGraph_edges_bounded execution.graph_eq hlines e h
    · exact constraints_bounded execution.graph e h
  obtain ⟨c, hcMem, hcP, hcO⟩ :=
    components_edge_endpoints hbd (List.mem_append_right _ he1)
  have hcEq := components_shared_member_eq hcMem hcomp hcO hoIn
  rw [hcEq] at hcP
  exact hcP
/-- Narrow parent chain (probes and consumer in file header). -/
theorem loopResOffRankParentChain_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hstab : ForeignBorderDivergeStable)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0) (hgrouped : nt.clusterPath ≠ [])
    {p : Nat} (hlast : nt.clusterPath.getLast? = some p)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2) (hni1 : np.decl ∉ nt.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x)
    (hParDisj1 : p ∉ np.clusterPath)
    (hParDisj2 : ∀ (u : Nat) (nu : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some nu →
      nu.border = -2 → nu.decl ∈ nt.clusterPath →
      nt.clusterPath.getLast? = some nu.decl → np.decl ∉ nu.clusterPath)
    (hParOvl : ¬ ((boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run p) []).bottom ≤
        (boundsOf (groupMemberRects
          (componentCandidate execution.graph comp candidate) run np.decl) []).minY ∨
      (boundsOf (groupMemberRects
        (componentCandidate execution.graph comp candidate) run np.decl) []).bottom ≤
        (boundsOf (groupMemberRects
          (componentCandidate execution.graph comp candidate) run p) []).minY))
    (hFwPos : 0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).w) :
    ∃ (u : Nat) (nu : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some nu ∧
      nu.border = -2 ∧ nu.decl ∈ nt.clusterPath ∧
      nt.clusterPath.getLast? = some nu.decl ∧
      (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run u).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run u).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := by
  obtain ⟨top, htopLookup, hbTop, hdeclTop⟩ :=
    lrpc_top_lookup hwf hframed execution hnt htB hgrouped hlast
  have hParInComp : p ∈ comp :=
    lrpc_parent_in_comp hwf hframed execution hcomp hnt htB hgrouped hlast
  obtain ⟨u, nu, hu, hbU, hmemU, hlastU⟩ :=
    lrpc_parent_transfer execution hlast htopLookup hbTop hdeclTop hParInComp
  have hnuEq : nu.decl = p := Option.some.inj (hlastU.symm.trans hlast)
  have hmemP : p ∈ nt.clusterPath := List.mem_of_getLast? hlast
  have hnePF : nu.decl ≠ np.decl := by
    rw [hnuEq]
    intro heq
    subst heq
    exact hni1 hmemP
  have hcon1 : np.clusterPath.contains nu.decl = false := by
    rw [hnuEq, List.contains_eq_mem]
    exact decide_eq_false hParDisj1
  have hTopMem : np.decl ∉ nu.clusterPath :=
    hParDisj2 u nu hu hbU hmemU hlastU
  have hcon2 : nu.clusterPath.contains np.decl = false := by
    rw [List.contains_eq_mem]
    exact decide_eq_false hTopMem
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hgroups : ForeignBorderSpansSeparated :=
    foreignBorderSpansSeparated foreignClusterRankSpans'
      foreignBorderLayerOrder' (foreignBorderChainXAligned' hstab)
  have h4way := hgroups execution.graph_eq hlines hwf hframed hcomp hrun
    hu hnp hbU hgrpB hnePF hcon1 hcon2
  have hGp := frameRect_group_span (P := execution.params) (run := run) hu hbU
  have hGf := frameRect_group_span (P := execution.params) (run := run) hnp hgrpB
  have hinsideT : nt.clusterPath.contains p = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hmemP
  have hinsideU : nt.clusterPath.contains nu.decl = true := by
    rw [hnuEq]
    exact hinsideT
  have hCont := execution.component_member_contained hwf hcomp hrun
    hu hbU hnt htB hinsideU
  have hdim := componentRun_dims_nonneg hrun
  have htLen : t < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnt).1
  have hcov := componentRun_original_nodes_covered hrun t htLen
  have hDimsT := (frameRect_dims_nonneg execution.params
    (componentCandidate execution.graph comp candidate) run t hdim hcov).1
  have hFwNN : 0 ≤ (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).w :=
    Int.le_of_lt hFwPos
  refine ⟨u, nu, hu, hbU, hmemU, hlastU, ?_⟩
  rcases h4way with hDesB | hRevB | hY1 | hY2
  · rw [hGp, hGf]
    dsimp only
    omega
  · exfalso
    have hRevF : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x +
        (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).w ≤
        (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run u).x := by
      rw [hGp, hGf]
      dsimp only
      omega
    unfold Rect.Contained at hCont
    obtain ⟨hpx_le, _, _, _⟩ := hCont
    omega
  · exfalso
    rw [hnuEq] at hY1
    exact hParOvl (Or.inl hY1)
  · exfalso
    rw [hnuEq] at hY2
    exact hParOvl (Or.inr hY2)

/-- Grouped off-rank plain owners satisfy the disjoint gap with no chain premise.
This is `loopResNeighborGapDisj_groupedOffRank_holds` replayed through
`loopResNeighborGapDisj_offRankYGap_holds`, which needs no grouped premise and
no `LoopResOffRankParentChain`: under `¬ LoopResNeighborSpanning` every foreign
member lies strictly above or strictly below the owner rank, so the foreign hull
lies wholly above or below the footprint. The disjoint pipeline
(`plain` → `disj` → `loopHullRightNeighborCover_Disj_holds`) therefore closes
without the parent-chain residual; the cover's `y`-overlap premise selects the
`x`-gap disjunct. -/
theorem loopResNeighborGapDisj_groupedOffRank_closed {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (_hgrouped : nt.clusterPath ≠ [])
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl)
    (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath)
    (hoff : ¬ LoopResNeighborSpanning run t np.decl)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y :=
  loopResNeighborGapDisj_offRankYGap_holds execution hcomp hrun hnt htB het
    hnp hgrpB hne hne2 hni1 hni2 hoff hFL

end PipelineImpl
end Layered
end Elegant