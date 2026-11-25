import Elegant.Layered.RegionFallbackAncestorFrameSides
import Elegant.Layered.RegionFallbackAncestorGroupVertical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem activeTopCluster {P : Params} {s : RegionSpec} {inp : Input}
    {cand : Graph} {rm : ComponentRegions}
    (ha : newComponentRegions (some s) P inp cand = .ok (some rm))
    {v : Nat} {raw : Node} (hv : cand.nodes[v]? = some raw) (hb : raw.border = -2) :
    ∃ i c, clusterOfDecl rm raw.decl = some i ∧ rm.clusters[i]? = some c ∧ c.decl = raw.decl := by
  have hrows : rm.clusters = clusterRows inp s cand := by
    unfold newComponentRegions at ha
    dsimp only at ha
    split at ha
    · cases ha
    obtain ⟨_, _, he⟩ := bind_ok ha
    split at he
    · cases he
    exact (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj he))).symm
  have hex : ∃ c ∈ rm.clusters, c.decl = raw.decl := by
    rw [hrows]
    unfold clusterRows
    let isBottom := fun q : Node × Nat => q.1.border == 2 && q.1.decl == raw.decl
    let isDecl := fun q : Node × Nat => q.1.decl == raw.decl
    let c : RegionCluster :=
      { id := boxId inp raw.decl
        decl := raw.decl
        node := match cand.nodes.zipIdx.find? isDecl with | some q => q.2 | none => v
        top := v
        bottom := match cand.nodes.zipIdx.find? isBottom with | some q => q.2 | none => v
        titleW := raw.w
        titleH := (s.titles.getD raw.decl (0, 0)).2
        extent := raw.loopExtent }
    refine ⟨c, List.mem_filterMap.mpr
      ⟨(raw, v), List.mem_zipIdx_iff_getElem?.mpr hv, ?_⟩, rfl⟩
    simp [c, isDecl, isBottom, hb]
    exact ⟨rfl, rfl⟩
  obtain ⟨c, hc, hdecl⟩ := hex
  cases hi : clusterOfDecl rm raw.decl with
  | none =>
    have hno := List.findIdx?_eq_none_iff.mp hi c hc
    simp [hdecl] at hno
  | some i =>
    obtain ⟨hiLen, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    exact ⟨i, rm.clusters[i], rfl, List.getElem?_eq_getElem hiLen, beq_iff_eq.mp hmatch⟩

private theorem rootedLastChild {pl : RegionPlacement} {resolve : Nat → Nat}
    {root parent child : Nat} (ancestors : List Nat)
    (h : GroupPlainRootedPath pl resolve root (ancestors ++ [parent, child])) :
    resolve child ∈ pl.children.getD (resolve parent) [] := by
  induction ancestors generalizing root with
  | nil =>
    change resolve parent ∈ pl.children.getD root [] ∧
      resolve child ∈ pl.children.getD (resolve parent) [] ∧ True at h
    exact h.2.1
  | cons d rest ih =>
    change resolve d ∈ pl.children.getD root [] ∧
      GroupPlainRootedPath pl resolve (resolve d) (rest ++ [parent, child]) at h
    exact ih (root := resolve d) h.2

private theorem widthSumNonnegative (width : Nat → Int) (h : ∀ v, 0 ≤ width v)
    (kids : List Nat) : 0 ≤ (kids.map width).sum := by
  induction kids with
  | nil => simp
  | cons k ks ih => simpa only [List.map_cons, List.sum_cons] using Int.add_nonneg (h k) ih

/-- Every non-demoted child group in an active component is strictly inside
its actual group parent. The proof uses the selected allocation and every
contributor to the emitted vertical hull. No fixed-size fit is assumed. -/
theorem regionActiveDirectGroupFrame_strict
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp index) e.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp index) = .ok (some rm))
    {u v : Nat} {parent child : Node} {ps cs : ModelBox}
    (hu : cg.nodes[u]? = some parent) (hp : parent.border = -2)
    (hv : cg.nodes[v]? = some child) (hc : child.border = -2)
    (hps : inp.boxes[parent.decl]? = some ps) (hcs : inp.boxes[child.decl]? = some cs)
    (href : cs.parent = ps.id) (hnonroot : cs.parent ≠ "") :
    (frameRect e.params cg run u).StrictInside (frameRect e.params cg run v) := by
  let cand := componentCandidateR (some s) e.graph comp index
  obtain ⟨_, _, _, _, _, _, _, _, hrank, hnorm, hlabels, hcoord, hmin, _, ⟨st⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = cand.nodes := rankEquivalentR_nodes_eq hrank
  have hnodeP : cand.nodes[u]? = some parent := by rwa [← hnodes]
  have hnodeC : cand.nodes[v]? = some child := by rwa [← hnodes]
  have keys {j : Nat} {n : Node} {source : ModelBox}
      (hj : cand.nodes[j]? = some n) (hborder : n.border = -2)
      (hsource : inp.boxes[n.decl]? = some source) :
      n.clusterPath = Compound.path inp.boxes source ++ [n.decl] := by
    have hx : (componentCandidate e.graph comp index).nodes[j]? = some n := by
      rw [componentCandidate_nodes]
      exact hj
    obtain ⟨b, hb, hpath⟩ := X_cg_group_box e.graph0_eq e.graph_eq hx hborder
    have hbox : b = source := Option.some.inj (hb.symm.trans hsource)
    simpa only [hbox] using hpath
  have hParent := keys hnodeP hp hps
  have hChild := keys hnodeC hc hcs
  have hstep : Compound.path inp.boxes cs = Compound.path inp.boxes ps ++ [parent.decl] :=
    Compound.path_of_parent (inputModel inp o) hwf hps hcs href hnonroot
  have hChildPath : child.clusterPath = Compound.path inp.boxes ps ++ [parent.decl, child.decl] := by
    rw [hChild, hstep, List.append_assoc]
    rfl
  have hDirect : child.clusterPath.dropLast = parent.clusterPath := by
    rw [hChild, List.dropLast_append_of_ne_nil (by simp : [child.decl] ≠ []), hstep, hParent,
      List.dropLast_singleton, List.append_nil]
  have hY := regionActiveChildGroup_strictVertical e hwf hfp hcomp hrun hactive hu hp hv hc hDirect
    (by rw [hParent]; simp) (by rw [hChild]; simp)
  obtain ⟨i, pCluster, hpi, hpCluster, hdP⟩ := activeTopCluster hactive hnodeP hp
  obtain ⟨j, cCluster, hcj, hcCluster, hdC⟩ := activeTopCluster hactive hnodeC hc
  have hrooted := r8b_executed_endpoint_rooted e hwf hfp hcomp hactive st hmin hnodeC
    (owner := j) (by simp [hChild, List.getLast?_append, hcj])
  rw [hChildPath] at hrooted
  have hKids : j ∈ st.placement.children.getD i [] := by
    simpa only [hpi, hcj, Option.getD_some] using
      rootedLastChild (Compound.path inp.boxes ps) hrooted
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hKids
  have hi := (List.getElem?_eq_some_iff.mp hpCluster).1
  have hL := st.childBudget_left_from_allocation hactive hmin (Nat.le_of_lt hi) hk
  rw [ite_eq_right (Nat.ne_of_lt hi)] at hL
  have hslot0 : 0 ≤ e.params.slot := by have := componentRunR_slot_pos hrun; omega
  have hR := st.childBudget_precedes_laneBand (o := o) hactive e.checked hslot0 hmin hi hk
  have houter := st.activeGroup_frame_covers_reservation e.graph0_eq e.graph_eq hcomp hrun
    hactive hrank hnorm hlabels hcoord e.checked hpCluster hu hp hdP.symm
  have hinner := st.activeChild_frame_within_reservation e.graph0_eq e.graph_eq hcomp hrun
    hactive hrank hnorm hlabels hcoord e.checked hmin hcCluster hv hc hdC.symm
  have hBW := checkedParams_clusterBorderW_ge_one e.checked
  have hPad := checkedParams_clusterPad_nonneg e.checked
  have hInset : 0 < regionInsetOf e.params := by unfold regionInsetOf; omega
  obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun st
  have hw := reserveWidths_nonnegative (pl := st.placement) (P := e.params)
    (Int.le_of_lt hInset) hown hlane hloop
  have hPrefix := widthSumNonnegative (fun c => (reserveWidths st.placement e.params).getD c 0)
    hw ((st.placement.children.getD i []).take k)
  have hOwn := hown i
  have hLane := hlane i
  dsimp only at hR houter
  obtain ⟨hOuterLeft, hOuterRight⟩ := houter
  obtain ⟨hInnerLeft, hInnerRight⟩ := hinner
  exact ⟨by omega, by omega, hY.1, hY.2⟩

end Elegant.Layered.PipelineImpl

