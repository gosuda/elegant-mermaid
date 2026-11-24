import Elegant.Layered.RegionFlatC8a
import Elegant.Layered.RegionSharedAllocation
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.RegionParentInComponent
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.RegionReservedChildMarkerHull

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem gp_bind_ok {α β : Type} {a : Except LayoutError α}
    {step : α → Except LayoutError β} {out : β} (h : a.bind step = .ok out) :
    ∃ value, a = .ok value ∧ step value = .ok out := by
  cases a with
  | error e => cases h
  | ok value => exact ⟨value, rfl, h⟩


private theorem gp_set_length {α : Type} (xs : List α) (i : Nat) (value : α) :
    (setAt xs i value).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem gp_set_getD {α : Type} (xs : List α) (i j : Nat) (value fallback : α) :
    (setAt xs i value).getD j fallback =
      if j = i ∧ i < xs.length then value else xs.getD j fallback := by
  induction xs generalizing i j with
  | nil => simp [setAt]
  | cons x xs ih =>
    cases i with
    | zero => cases j <;> simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j


private theorem gp_path_fork (a b : List Nat) (h : ¬ a <+: b) :
    ∃ common group rest, a = common ++ group :: rest ∧
      (b = common ∨ ∃ other tail, b = common ++ other :: tail ∧ group ≠ other) := by
  induction a generalizing b with
  | nil => exact (h ⟨b, rfl⟩).elim
  | cons group rest ih =>
    cases b with
    | nil => exact ⟨[], group, rest, rfl, Or.inl rfl⟩
    | cons other tail =>
      by_cases hs : group = other
      · subst other
        have ht : ¬ rest <+: tail := by
          rintro ⟨suffix, htail⟩
          exact h ⟨suffix, congrArg (List.cons group) htail⟩
        obtain ⟨common, g, gs, hg, hp⟩ := ih tail ht
        refine ⟨group :: common, g, gs, congrArg (List.cons group) hg, ?_⟩
        rcases hp with he | ⟨p, ps, he, hne⟩
        · exact Or.inl (congrArg (List.cons group) he)
        · exact Or.inr ⟨p, ps, congrArg (List.cons group) he, hne⟩
      · exact ⟨[], group, rest, rfl, Or.inr ⟨other, tail, rfl, hs⟩⟩

theorem groupPlain_foreign_owner_fork {boxes : List ModelBox} {group plain : ModelBox}
    {g : Nat} {gn pn : Node}
    (hg : gn.clusterPath = Compound.path boxes group ++ [g])
    (hp : pn.clusterPath = Compound.path boxes plain)
    (hforeign : pn.clusterPath.contains g = false) :
    ∃ common child rest, gn.clusterPath = common ++ child :: rest ∧
      (pn.clusterPath = common ∨
        ∃ other tail, pn.clusterPath = common ++ other :: tail ∧ child ≠ other) := by
  rw [hp] at hforeign ⊢
  apply gp_path_fork
  rintro ⟨suffix, hs⟩
  have hmem : g ∈ Compound.path boxes plain := by
    rw [← hs, hg]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (by simp))))
  have htrue : (Compound.path boxes plain).contains g = true := List.contains_iff_mem.mpr hmem
  rw [hforeign] at htrue
  cases htrue

theorem groupPlain_gap_comm {a b : Rect} (h : R8a_OverlapRowsXGap a b) :
    R8a_OverlapRowsXGap b a := by
  intro hy hb ha
  have hy' : max a.y b.y < min (a.y + a.h) (b.y + b.h) := by omega
  exact (h hy' ha hb).symm

theorem groupPlain_gap_of_interval_bounds {P : Params} {cg : Graph} {run : Run}
    {u w : Nat} {gn : Node} (hg : cg.nodes[u]? = some gn) (hgroup : gn.border = -2)
    {groupLo groupHi plainLo plainHi : Int}
    (hzero : 0 ≤ groupHi)
    (hmarkers : ∀ r ∈ groupBorderRects cg run gn.decl, groupLo ≤ r.x ∧ r.x + r.w ≤ groupHi)
    (hplain : plainLo ≤ (frameRect P cg run w).x ∧
      (frameRect P cg run w).x + (frameRect P cg run w).w ≤ plainHi)
    (hslots : groupHi ≤ plainLo ∨ plainHi ≤ groupLo) :
    R8a_OverlapRowsXGap (frameRect P cg run u) (frameRect P cg run w) := by
  rw [frameRect_group_span hg hgroup]
  intro _ hw _
  have hnonempty : groupBorderRects cg run gn.decl ≠ [] := by
    intro hn
    simp [hn, boundsOf] at hw
  have hmin := boundsOf_minX_ge_of_all hnonempty (fun r hr => (hmarkers r hr).1)
  have hright := boundsOf_right_le_of_all hzero (fun r hr => (hmarkers r hr).2)
  dsimp only
  rcases hplain with ⟨hpl, hpr⟩
  rcases hslots with h | h
  · left
    omega
  · right
    omega

def GroupPlainOwnerFork (group plain : List Nat) : Prop :=
  ∃ common child rest, group = common ++ child :: rest ∧
    (plain = common ∨ ∃ other tail, plain = common ++ other :: tail ∧ child ≠ other)

private theorem gp_selected_source_path {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {node : Node} {source : ModelBox} (hnode : execution.graph.nodes[node.decl]? = some node)
    (hsource : inp.boxes[node.decl]? = some source) :
    (node.border = -2 → node.clusterPath = Compound.path inp.boxes source ++ [node.decl]) ∧
    (node.border = 0 → node.clusterPath = Compound.path inp.boxes source) := by
  have hbound := (List.getElem?_eq_some_iff.mp hnode).1
  rw [exactGraph_length execution.graph_eq] at hbound
  obtain ⟨old, h0⟩ : ∃ old, execution.graph0.nodes[node.decl]? = some old :=
    ⟨_, List.getElem?_eq_getElem hbound⟩
  obtain ⟨node', hnode', hb, hp, _⟩ := exactGraph_node_key execution.graph_eq h0
  have he := Option.some.inj (hnode'.symm.trans hnode)
  subst node'
  obtain ⟨_, hmap, hpath⟩ := fixedSizes_path_index inp hsource
  constructor
  · intro hgroup
    obtain ⟨hdecl, effective, heffective, _, hraw⟩ :=
      measuredGraph_group_origin execution.graph0_eq h0 (hb.symm.trans hgroup)
    rw [hdecl] at heffective
    have hbox := Option.some.inj (hmap.symm.trans heffective)
    rw [← hbox, hpath, hdecl] at hraw
    exact hp.trans hraw
  · intro hplain
    obtain ⟨_, _, _, hprepared, _, hmetadata⟩ :=
      measuredGraph_prepared_source execution.graph0_eq
    rw [hprepared] at h0
    obtain ⟨_, hraw⟩ := prepare_plain_path_origin _ _ _ _ hmetadata h0 (hb.symm.trans hplain) hmap
    exact hp.trans (hraw.trans hpath)

theorem groupPlain_selected_owner_fork {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (pair : R8a_SelectedPair execution g b)
    (hb : (pair.uNode.border = -2 ∧ pair.wNode.border = 0) ∨
      (pair.uNode.border = 0 ∧ pair.wNode.border = -2)) :
    (pair.uNode.border = -2 ∧ pair.wNode.border = 0 ∧
      GroupPlainOwnerFork pair.uNode.clusterPath pair.wNode.clusterPath) ∨
    (pair.wNode.border = -2 ∧ pair.uNode.border = 0 ∧
      GroupPlainOwnerFork pair.wNode.clusterPath pair.uNode.clusterPath) := by
  have hpart := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hparts := (actual_components_parts_geometryR (by rfl) execution.components_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hpart
  have hnodes : pair.selected.cg.nodes =
      (componentCandidateR pair.selected.spec execution.graph pair.part.1
        pair.selected.candidate).nodes := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ :=
      componentRunR_stages pair.selected.run_eq
    rcases stages.hRank with ⟨_, _, _, _, heq, _⟩ | ⟨_, _, hrank⟩
    · rw [heq]
    · exact rankEquivalentR_nodes_eq hrank
  have source {i : Nat} {node : Node} (hpos : pair.part.1[i]? = some node.decl)
      (hnode : pair.selected.cg.nodes[i]? = some node) :
      execution.graph.nodes[node.decl]? = some node := by
    have hm := List.mem_of_getElem? hpos
    obtain ⟨root, hroot⟩ := mem_components_eq hcomp
    rw [hroot] at hm
    have hin := ((mem_componentOf (g := execution.graph) (r := root)).mp hm).1
    obtain ⟨_, hlookup⟩ : ∃ n, execution.graph.nodes[node.decl]? = some n :=
      ⟨_, List.getElem?_eq_getElem hin⟩
    have hprojected := component_node_lookupR (spec := pair.selected.spec)
      (cand := pair.selected.candidate) hpos hlookup
    rw [hnodes] at hnode
    exact hlookup.trans (congrArg some (Option.some.inj (hprojected.symm.trans hnode)))
  have hpG := gp_selected_source_path execution (source pair.group_pos pair.group_node)
    pair.group_source
  have hpB := gp_selected_source_path execution (source pair.peer_pos pair.peer_node)
    pair.peer_source
  rcases hb with ⟨hgroup, hplain⟩ | ⟨hplain, hgroup⟩
  · exact Or.inl ⟨hgroup, hplain,
      groupPlain_foreign_owner_fork (hpG.1 hgroup) (hpB.2 hplain) pair.group_not_in_path⟩
  · exact Or.inr ⟨hgroup, hplain,
      groupPlain_foreign_owner_fork (hpB.1 hgroup) (hpG.2 hplain) pair.peer_not_in_path⟩

theorem groupPlain_selected_allocation {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (pair : R8a_SelectedPair execution g b) :
    ∃ (rm : ComponentRegions) (p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)),
      newComponentRegions (some pair.spec) execution.params inp
        (componentCandidateR (some pair.spec) execution.graph pair.part.1
          pair.selected.candidate) = .ok (some rm) ∧
      constrainR rm execution.params p = .ok minimum ∧
      Nonempty (RegionCrossAllocationStages execution.params rm pair.selected.cg
        execution.measured p minimum ord.layers pair.selected.run.layers
        pair.selected.run.coordinateXs reserved pair.selected.run.coordinateProper) := by
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  have hregions : newComponentRegions pair.selected.spec execution.params inp
      (componentCandidateR pair.selected.spec execution.graph pair.part.1
        pair.selected.candidate) = .ok pair.selected.regions := by
    rw [pair.selected.effective_eq]
    exact componentTrialR_selected_regions _ pair.selected.regions_eq
  rw [pair.active] at hregions
  have hsome : ∃ rm, pair.selected.regions = some rm := by
    cases hr : pair.selected.regions with
    | none =>
      have heff := pair.selected.effective_eq
      rw [pair.active, hr] at heff
      simp at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hregions
  obtain ⟨_, _, _, p, minimum, ord, reserved, _, _, _, _, _, hminimum, _, hstages⟩ :=
    componentRunR_active_allocation_stages hrun hregions
  exact ⟨rm, p, minimum, ord, reserved, hregions, hminimum, hstages⟩

theorem groupPlain_frame_eq_nodeRect {P : Params} {cg : Graph} {run : Run} {node : Node}
    {i : Nat} (hi : cg.nodes[i]? = some node) (hplain : node.border = 0) :
    frameRect P cg run i = nodeRect cg run i := by
  simp [frameRect, List.getD_eq_getElem?_getD, hi, hplain]

private theorem gp_sum_nonneg (width : Nat → Int) (hw : ∀ i, 0 ≤ width i) :
    ∀ row : List Nat, 0 ≤ (row.map width).sum := by
  intro row
  induction row with
  | nil => simp
  | cons i row ih =>
    simpa only [List.map_cons, List.sum_cons] using Int.add_nonneg (hw i) ih

private theorem gp_index_width (width : Nat → Int) (hw : ∀ i, 0 ≤ width i)
    {row : List Nat} {i child : Nat} (hi : row[i]? = some child) :
    ((row.take i).map width).sum + width child ≤ (row.map width).sum := by
  induction row generalizing i with
  | nil => simp at hi
  | cons head row ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst head
      have htail := gp_sum_nonneg width hw row
      simp only [List.take_zero, List.map_nil, List.sum_nil, Int.zero_add,
        List.map_cons, List.sum_cons]
      omega
    | succ i =>
      have ht := ih (by simpa only [List.getElem?_cons_succ] using hi)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

private theorem gp_two_index_widths (width : Nat → Int) (hw : ∀ i, 0 ≤ width i)
    {row : List Nat} {i j first second : Nat}
    (hi : row[i]? = some first) (hj : row[j]? = some second) (hij : i < j) :
    ((row.take i).map width).sum + width first ≤ ((row.take j).map width).sum := by
  induction row generalizing i j with
  | nil => simp at hi
  | cons head row ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst head
        have htail := gp_sum_nonneg width hw (row.take j)
        simp only [List.take_zero, List.map_nil, List.sum_nil, Int.zero_add,
          List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
      | succ i =>
        have ht := ih (i := i) (j := j)
          (by simpa only [List.getElem?_cons_succ] using hi)
          (by simpa only [List.getElem?_cons_succ] using hj) (by omega)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega

def groupPlain_allocLeft (alloc : RegionAllocation) (g : Nat) : Int :=
  alloc.lefts.getD g 0

def groupPlain_allocRight (alloc : RegionAllocation) (g : Nat) : Int :=
  groupPlain_allocLeft alloc g + alloc.widths.getD g 0

def groupPlain_bucketLeft (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (g : Nat) : Int :=
  groupPlain_allocLeft alloc g + (if g = pl.rm.clusters.length then 0 else regionInsetOf P)

def groupPlain_bucketRight (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (g : Nat) : Int :=
  groupPlain_bucketLeft pl P alloc g + pl.buckets.widths.getD g 0

theorem groupPlain_allocation_width_eq {pl : RegionPlacement} {P : Params}
    {before after : List Int} {alloc : RegionAllocation}
    (h : allocatePl pl P before = .ok (alloc, after)) : alloc.widths = reserveWidths pl P := by
  unfold allocatePl at h
  obtain ⟨_, _, h⟩ := gp_bind_ok h
  exact (congrArg (fun q : RegionAllocation × List Int => q.1.widths) (Except.ok.inj h)).symm

theorem groupPlain_child_slot_bounds {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {g i child : Nat}
    (hi : (pl.children.getD g [])[i]? = some child)
    (hinset : 0 ≤ regionInsetOf P)
    (hown : 0 ≤ pl.buckets.widths.getD g 0)
    (hw : ∀ c, 0 ≤ alloc.widths.getD c 0)
    (hleft : groupPlain_allocLeft alloc child =
      groupPlain_bucketRight pl P alloc g +
        (((pl.children.getD g []).take i).map fun c => alloc.widths.getD c 0).sum)
    (hroom : (if g = pl.rm.clusters.length then 0 else regionInsetOf P) + pl.buckets.widths.getD g 0 +
      ((pl.children.getD g []).map fun c => alloc.widths.getD c 0).sum ≤ alloc.widths.getD g 0) :
    groupPlain_allocLeft alloc g ≤ groupPlain_allocLeft alloc child ∧
      groupPlain_allocRight alloc child ≤ groupPlain_allocRight alloc g := by
  have hprefix := gp_sum_nonneg (fun c => alloc.widths.getD c 0) hw
    ((pl.children.getD g []).take i)
  have hsum := gp_index_width (fun c => alloc.widths.getD c 0) hw hi
  unfold groupPlain_allocRight
  unfold groupPlain_bucketRight groupPlain_bucketLeft at hleft
  split at hleft
  · rename_i hroot
    rw [ite_eq_left hroot] at hroom
    omega
  · rename_i hroot
    rw [ite_eq_right hroot] at hroom
    omega

theorem groupPlain_sibling_slot_gap {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {g i j a b : Nat}
    (ha : (pl.children.getD g [])[i]? = some a)
    (hb : (pl.children.getD g [])[j]? = some b)
    (hab : a ≠ b)
    (hw : ∀ c, 0 ≤ alloc.widths.getD c 0)
    (hla : groupPlain_allocLeft alloc a =
      groupPlain_bucketRight pl P alloc g +
        (((pl.children.getD g []).take i).map fun c => alloc.widths.getD c 0).sum)
    (hlb : groupPlain_allocLeft alloc b =
      groupPlain_bucketRight pl P alloc g +
        (((pl.children.getD g []).take j).map fun c => alloc.widths.getD c 0).sum) :
    groupPlain_allocRight alloc a ≤ groupPlain_allocLeft alloc b ∨
      groupPlain_allocRight alloc b ≤ groupPlain_allocLeft alloc a := by
  unfold groupPlain_allocRight
  rcases Nat.lt_trichotomy i j with hij | hsame | hji
  · have hsum := gp_two_index_widths (fun c => alloc.widths.getD c 0) hw ha hb hij
    left
    omega
  · subst j
    exact (hab (Option.some.inj (ha.symm.trans hb))).elim
  · have hsum := gp_two_index_widths (fun c => alloc.widths.getD c 0) hw hb ha hji
    right
    omega

theorem groupPlain_bucket_before_child {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {g i child : Nat}
    (hw : ∀ c, 0 ≤ alloc.widths.getD c 0)
    (hleft : groupPlain_allocLeft alloc child =
      groupPlain_bucketRight pl P alloc g +
        (((pl.children.getD g []).take i).map fun c => alloc.widths.getD c 0).sum) :
    groupPlain_bucketRight pl P alloc g ≤ groupPlain_allocLeft alloc child := by
  have hprefix := gp_sum_nonneg (fun c => alloc.widths.getD c 0) hw
    ((pl.children.getD g []).take i)
  omega

theorem groupPlain_marker_arithmetic {left right width : Int} (hw : 0 ≤ width)
    (hroom : left + width ≤ right) :
    (left + Int.tdiv width 2 - Int.fdiv width 2 = left ∧
      left + Int.tdiv width 2 - Int.fdiv width 2 + width ≤ right) ∧
    (left ≤ right - width + Int.tdiv width 2 - Int.fdiv width 2 ∧
      right - width + Int.tdiv width 2 - Int.fdiv width 2 + width = right) := by
  rw [Int.tdiv_eq_ediv_of_nonneg hw, Int.fdiv_eq_ediv_of_nonneg width (by decide)]
  omega

private def gp_frame_step (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (xs : List Int) (q : RegionCluster × Nat) : List Int :=
  let c := q.1
  let left := alloc.lefts.getD q.2 0
  let right := left + alloc.widths.getD q.2 0 - pl.buckets.loopWidth.getD q.2 0
  let center := left + Int.tdiv (right - left) 2
  let xs := pl.p.nodes.zipIdx.foldl (fun xs n =>
    if n.1.node.clusterPath.getLast? != some c.decl then xs
    else
      match n.1.node.border with
      | -1 => setAt xs n.2 (left + Int.tdiv P.clusterBorderW 2)
      | 1 => setAt xs n.2 (right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
      | 3 => setAt xs n.2 center
      | _ => xs) xs
  setAt (setAt xs c.top center) c.bottom center

private theorem gp_frame_step_length (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (xs : List Int) (q : RegionCluster × Nat) :
    (gp_frame_step pl P alloc xs q).length = xs.length := by
  unfold gp_frame_step
  simp only [gp_set_length]
  apply OrderImpl.foldl_inv (fun ys : List Int => ys.length = xs.length) _ _ _
  · rfl
  · intro ys hy n _
    split
    · exact hy
    · split <;> first | exact (gp_set_length _ _ _).trans hy | exact hy

private theorem gp_frame_step_marker {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {xs : List Int} {v : Nat} {marker : ProperNode}
    {q : RegionCluster × Nat}
    (hv : pl.p.nodes[v]? = some marker) (hside : marker.node.border = -1 ∨ marker.node.border = 1)
    (hbound : v < xs.length) (htop : q.1.top ≠ v) (hbottom : q.1.bottom ≠ v) :
    (gp_frame_step pl P alloc xs q).getD v 0 =
      if marker.node.clusterPath.getLast? = some q.1.decl then
        if marker.node.border = -1 then
          alloc.lefts.getD q.2 0 + Int.tdiv P.clusterBorderW 2
        else
          alloc.lefts.getD q.2 0 + alloc.widths.getD q.2 0 - pl.buckets.loopWidth.getD q.2 0 -
            P.clusterBorderW + Int.tdiv P.clusterBorderW 2
      else xs.getD v 0 := by
  unfold gp_frame_step
  dsimp only
  rw [gp_set_getD, ite_eq_right (fun he => hbottom he.1.symm),
    gp_set_getD, ite_eq_right (fun he => htop he.1.symm)]
  let left := alloc.lefts.getD q.2 0
  let right := left + alloc.widths.getD q.2 0 - pl.buckets.loopWidth.getD q.2 0
  let center := left + Int.tdiv (right - left) 2
  let step (ys : List Int) (n : ProperNode × Nat) :=
    if n.1.node.clusterPath.getLast? != some q.1.decl then ys
    else
      match n.1.node.border with
      | -1 => setAt ys n.2 (left + Int.tdiv P.clusterBorderW 2)
      | 1 => setAt ys n.2 (right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
      | 3 => setAt ys n.2 center
      | _ => ys
  let target := if marker.node.border = -1 then left + Int.tdiv P.clusterBorderW 2
    else right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2
  change (pl.p.nodes.zipIdx.foldl step xs).getD v 0 =
    if marker.node.clusterPath.getLast? = some q.1.decl then target else xs.getD v 0
  have fold (ns : List (ProperNode × Nat)) (ys : List Int)
      (hys : v < ys.length) (hrecords : ∀ n ∈ ns, pl.p.nodes[n.2]? = some n.1) :
      (ns.foldl step ys).getD v 0 =
        if marker.node.clusterPath.getLast? = some q.1.decl ∧ v ∈ ns.map Prod.snd
        then target else ys.getD v 0 := by
    induction ns generalizing ys with
    | nil => simp
    | cons n ns ih =>
      have hlen : (step ys n).length = ys.length := by
        unfold step
        split
        · rfl
        · split <;> first | rfl | apply gp_set_length
      rw [List.foldl_cons, ih _ (by rwa [hlen]) (fun k hk => hrecords k (List.Mem.tail n hk))]
      by_cases hi : n.2 = v
      · have hrecord := hrecords n (List.Mem.head ns)
        rw [hi, hv] at hrecord
        have hn : n.1 = marker := (Option.some.inj hrecord).symm
        have hstep : (step ys n).getD v 0 =
            if marker.node.clusterPath.getLast? = some q.1.decl then target else ys.getD v 0 := by
          unfold step target
          by_cases hp : marker.node.clusterPath.getLast? = some q.1.decl
          · rcases hside with hside | hside <;>
              simp [hn, hp, hside, hi] <;>
              exact (gp_set_getD ys v v _ 0).trans (ite_eq_left ⟨rfl, hys⟩)
          · simp [hn, hp]
        rw [hstep]
        simp only [List.map_cons, List.mem_cons, hi, eq_self, true_or, and_true]
        split <;> simp_all
      · have hstep : (step ys n).getD v 0 = ys.getD v 0 := by
          unfold step
          split
          · rfl
          · split <;> first | rfl | rw [gp_set_getD, ite_eq_right (fun he => hi he.1.symm)]
        rw [hstep]
        simp only [List.map_cons, List.mem_cons, Ne.symm hi, false_or]
  have hmem : v ∈ pl.p.nodes.zipIdx.map Prod.snd :=
    List.mem_map.mpr ⟨(marker, v), List.mem_zipIdx_iff_getElem?.mpr hv, rfl⟩
  simpa only [hmem, and_true] using fold pl.p.nodes.zipIdx xs hbound
    (fun n hn => List.mem_zipIdx_iff_getElem?.mp hn)

theorem groupPlain_regionFrames_marker {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {xs : List Int} {v g : Nat} {marker : ProperNode}
    {cluster : RegionCluster} (hv : pl.p.nodes[v]? = some marker)
    (hside : marker.node.border = -1 ∨ marker.node.border = 1)
    (hbound : v < xs.length) (hc : pl.rm.clusters[g]? = some cluster)
    (hpath : marker.node.clusterPath.getLast? = some cluster.decl)
    (hunique : ∀ q ∈ pl.rm.clusters.zipIdx,
      marker.node.clusterPath.getLast? = some q.1.decl → q = (cluster, g))
    (haway : ∀ c ∈ pl.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v) :
    (regionFrames pl P alloc xs).getD v 0 =
      if marker.node.border = -1 then alloc.lefts.getD g 0 + Int.tdiv P.clusterBorderW 2
      else alloc.lefts.getD g 0 + alloc.widths.getD g 0 - pl.buckets.loopWidth.getD g 0 -
        P.clusterBorderW + Int.tdiv P.clusterBorderW 2 := by
  have hmem : (cluster, g) ∈ pl.rm.clusters.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hc
  obtain ⟨pre, post, hentries⟩ := List.mem_iff_append.mp hmem
  have hnodup : (pl.rm.clusters.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hnot : (cluster, g) ∉ post := by
    rw [hentries, List.map_append, List.map_cons] at hnodup
    have hnot := (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
    intro h
    exact hnot (List.mem_map.mpr ⟨(cluster, g), h, rfl⟩)
  let before := pre.foldl (gp_frame_step pl P alloc) xs
  have hbefore : before.length = xs.length := by
    exact OrderImpl.foldl_inv (fun ys : List Int => ys.length = xs.length) _ _ _ rfl
      (fun ys hys q _ => (gp_frame_step_length _ _ _ _ _).trans hys)
  let written := gp_frame_step pl P alloc before (cluster, g)
  have hwritten : written.length = xs.length := (gp_frame_step_length _ _ _ _ _).trans hbefore
  have hs := haway cluster (List.mem_of_getElem? hc)
  have hmiddle := gp_frame_step_marker (P := P) (alloc := alloc) (q := (cluster, g))
    hv hside (show v < before.length by rwa [hbefore]) hs.1 hs.2
  change written.getD v 0 = _ at hmiddle
  rw [ite_eq_left hpath] at hmiddle
  have htail : (post.foldl (gp_frame_step pl P alloc) written).getD v 0 = written.getD v 0 := by
    refine (OrderImpl.foldl_inv (fun ys : List Int =>
      ys.length = xs.length ∧ ys.getD v 0 = written.getD v 0)
      _ _ _ ⟨hwritten, rfl⟩ ?_).2
    intro ys hy q hq
    have hqmem : q ∈ pl.rm.clusters.zipIdx := by
      rw [hentries]
      exact List.mem_append_right _ (List.Mem.tail _ hq)
    have ha := haway q.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hqmem))
    have hne : marker.node.clusterPath.getLast? ≠ some q.1.decl :=
      fun he => hnot ((hunique q hqmem he) ▸ hq)
    refine ⟨(gp_frame_step_length _ _ _ _ _).trans hy.1, ?_⟩
    rw [gp_frame_step_marker hv hside (show v < ys.length by rwa [hy.1]) ha.1 ha.2,
      ite_eq_right hne]
    exact hy.2
  change (pl.rm.clusters.zipIdx.foldl (gp_frame_step pl P alloc) xs).getD v 0 = _
  rw [hentries, List.foldl_append, List.foldl_cons]
  exact htail.trans hmiddle

private theorem gp_fold_ok {α β : Type} {step : α → β → Except LayoutError α}
    {inv : α → Prop} {entries : List β} {initial final : α}
    (hinit : inv initial)
    (hstep : ∀ a b out, inv a → b ∈ entries → step a b = .ok out → inv out)
    (h : entries.foldlM step initial = .ok final) : inv final := by
  induction entries generalizing initial with
  | nil =>
    change Except.ok initial = Except.ok final at h
    exact (Except.ok.inj h) ▸ hinit
  | cons head tail ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, htail⟩ := gp_bind_ok h
    exact ih (hstep initial head mid hinit (List.Mem.head _) hmid)
      (fun a b out ha hb ho => hstep a b out ha (List.Mem.tail _ hb) ho) htail

private def AllLeftsNonnegative (xs : List Int) : Prop :=
  ∀ g, 0 ≤ xs.getD g 0

private theorem gp_allocateGroup_lefts_nonneg {pl : RegionPlacement} {P : Params}
    {widths : List Int} {g : Nat} {initial final : List Int × List Int × List (Option Int)}
    (h : allocateGroup pl P widths g initial = .ok final)
    (hinit : AllLeftsNonnegative initial.2.1)
    (horigin : 0 ≤ pl.minimum.origins.getD g 0)
    (hown : 0 ≤ pl.buckets.widths.getD g 0) (hw : ∀ c, 0 ≤ widths.getD c 0) :
    AllLeftsNonnegative final.2.1 := by
  rcases initial with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, hplaced, h⟩ := gp_bind_ok h
  obtain ⟨_, _, h⟩ := gp_bind_ok h
  have hlefts : final.2.1 = placed.2 :=
    (congrArg (fun out : List Int × List Int × List (Option Int) => out.2.1)
      (Except.ok.inj h)).symm
  have hstart : 0 ≤ lefts.getD g 0 +
      (if g != pl.rm.clusters.length then pl.minimum.origins.getD g 0 else 0) +
      pl.buckets.widths.getD g 0 := by
    have hleft : 0 ≤ lefts.getD g 0 := hinit g
    refine Int.add_nonneg (Int.add_nonneg hleft ?_) hown
    split
    · exact horigin
    · exact Int.le_refl 0
  have hf := gp_fold_ok (inv := fun a : Int × List Int => 0 ≤ a.1 ∧ AllLeftsNonnegative a.2)
    ⟨hstart, hinit⟩ (by
      intro a c out ha _ hnext
      change Except.ok (a.1 + widths.getD c 0, setAt a.2 c a.1) = .ok out at hnext
      rw [← Except.ok.inj hnext]
      refine ⟨Int.add_nonneg ha.1 (hw c), ?_⟩
      intro i
      change 0 ≤ (setAt a.2 c a.1).getD i 0
      rw [gp_set_getD]
      split
      · exact ha.1
      · exact ha.2 i) hplaced
  rw [hlefts]
  exact hf.2

theorem groupPlain_allocation_lefts_nonneg {pl : RegionPlacement} {P : Params}
    {xs shifted : List Int} {alloc : RegionAllocation}
    (h : allocatePl pl P xs = .ok (alloc, shifted))
    (horigin : ∀ g, 0 ≤ pl.minimum.origins.getD g 0)
    (hown : ∀ g, 0 ≤ pl.buckets.widths.getD g 0)
    (hw : ∀ c, 0 ≤ (reserveWidths pl P).getD c 0) :
    ∀ g, 0 ≤ alloc.lefts.getD g 0 := by
  unfold allocatePl at h
  obtain ⟨final, hfold, h⟩ := gp_bind_ok h
  have heil : final.2.1 = alloc.lefts :=
    congrArg (fun q : RegionAllocation × List Int => q.1.lefts) (Except.ok.inj h)
  have hinit : AllLeftsNonnegative (List.replicate (pl.rm.clusters.length + 1) 0) := by
    intro g
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> decide
  rw [← heil]
  exact gp_fold_ok (inv := fun a : List Int × List Int × List (Option Int) =>
    AllLeftsNonnegative a.2.1) hinit
    (fun _ g _ hi _ h => gp_allocateGroup_lefts_nonneg h hi (horigin g) (hown g) hw) hfold

theorem groupPlain_selected_nonnegative_slots {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (pair : R8a_SelectedPair execution g b) :
    ∃ (rm : ComponentRegions) (p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages execution.params rm pair.selected.cg
        execution.measured p minimum ord.layers pair.selected.run.layers
        pair.selected.run.coordinateXs reserved pair.selected.run.coordinateProper,
      (∀ child, 0 ≤ stages.allocation.lefts.getD child 0) ∧
      (∀ child, 0 ≤ stages.allocation.widths.getD child 0) ∧
      (∀ owner < rm.clusters.length,
        2 * regionInsetOf execution.params + stages.placement.buckets.widths.getD owner 0 +
          ((stages.placement.children.getD owner []).map fun c =>
            stages.allocation.widths.getD c 0).sum ≤
          stages.allocation.widths.getD owner 0 - stages.placement.buckets.loopWidth.getD owner 0) ∧
      ∀ {owner child k}, owner < rm.clusters.length →
        (stages.placement.children.getD owner [])[k]? = some child →
        groupPlain_allocLeft stages.allocation child =
          groupPlain_bucketRight stages.placement execution.params stages.allocation owner +
            (((stages.placement.children.getD owner []).take k).map fun c =>
              stages.allocation.widths.getD c 0).sum := by
  obtain ⟨rm, p, minimum, ord, reserved, hactive, hmin, ⟨stages⟩⟩ :=
    groupPlain_selected_allocation pair
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  have hp := (checkedParams_sizing_nonneg execution.checked).2.1
  have hb := checkedParams_clusterBorderW_ge_one execution.checked
  have hinset : 0 ≤ regionInsetOf execution.params := by
    unfold regionInsetOf
    omega
  obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun stages
  have hw := reserveWidths_nonnegative hinset hown hlane hloop
  have hwidth := groupPlain_allocation_width_eq stages.hAllocation
  have horigin (child : Nat) : 0 ≤ stages.placement.minimum.origins.getD child 0 := by
    rw [stages.hPlacement, constrainR_origins hmin, List.getD_eq_getElem?_getD,
      List.getElem?_replicate]
    split
    · exact hinset
    · exact Int.le_refl 0
  refine ⟨rm, p, minimum, ord, reserved, stages,
    groupPlain_allocation_lefts_nonneg stages.hAllocation horigin hown hw, ?_, ?_, ?_⟩
  · rw [hwidth]
    exact hw
  · intro owner howner
    have hparents := activeRegion_parent_count hactive
    obtain ⟨pre, post, hsplit, hlast, hchild⟩ :=
      (stages.reservation_order hparents hmin).2 owner (Nat.le_of_lt howner)
    have hownerPl : owner < stages.placement.rm.clusters.length := by
      simpa only [stages.hPlacement] using howner
    rw [hwidth]
    exact Int.le_trans (Int.le_add_of_nonneg_right (hlane owner))
      (reserveWidths_room_from_last_writes (pl := stages.placement) (P := execution.params)
        hsplit hownerPl hlast hchild)
  · intro owner child k howner hchild
    have hone : owner ≠ stages.placement.rm.clusters.length := by
      rw [stages.hPlacement]
      exact Nat.ne_of_lt howner
    unfold groupPlain_bucketRight groupPlain_bucketLeft groupPlain_allocLeft
    rw [ite_eq_right hone, hwidth]
    simpa only [ite_eq_right (Nat.ne_of_lt howner)] using
      stages.childBudget_left_from_allocation hactive hmin (Nat.le_of_lt howner) hchild

theorem groupPlain_plainRect_of_bucket_shift {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {run : Run} {v owner : Nat} {original : Node} {proper : ProperNode}
    (hplain : original.border = 0) (hv : cg.nodes[v]? = some original)
    (hnode : stages.placement.p.nodes[v]? = some proper)
    (hfinal : run.proper.nodes[v]? = some proper)
    (hmem : v ∈ stages.placement.buckets.members.getD owner [])
    (hmove : run.xs.getD v 0 = stages.before.getD v 0 +
      groupPlain_bucketLeft stages.placement P stages.allocation owner -
        stages.placement.buckets.low.getD owner 0) :
    groupPlain_bucketLeft stages.placement P stages.allocation owner ≤ (frameRect P cg run v).x ∧
      (frameRect P cg run v).x + (frameRect P cg run v).w ≤
        groupPlain_bucketRight stages.placement P stages.allocation owner := by
  have h := stages.bucket_width_and_hull.2 owner v hmem
  have hw0 : 0 ≤ CoordsImpl.nodeW stages.placement.p v := by
    have hsizes := (CoordsImpl.crossCoordsClusterWith_spec stages.hCross).2.2.2.1
    have hEq : stages.placement.p = p := by rw [stages.hPlacement]
    rw [hEq]
    exact CoordsImpl.nodeW_nonneg hsizes _
  have hext : 0 ≤ (proper.node.loopExtent : Int) := Int.natCast_nonneg _
  have hnn : 0 ≤ proper.node.w + 2 * (proper.node.loopExtent : Int) := by
    simpa only [CoordsImpl.nodeW, hnode] using hw0
  have hfhalf := Int.fdiv_eq_ediv_of_nonneg proper.node.w (b := 2) (by decide)
  have hthalf : Int.tdiv (proper.node.w + 2 * (proper.node.loopExtent : Int)) 2 =
      (proper.node.w + 2 * (proper.node.loopExtent : Int)) / 2 := Int.tdiv_eq_ediv_of_nonneg hnn
  have hhalf := Int.add_mul_ediv_left proper.node.w (proper.node.loopExtent : Int)
    (by decide : (2 : Int) ≠ 0)
  have hproper : run.proper.nodes.getD v default = proper := by
    simp only [List.getD_eq_getElem?_getD, hfinal, Option.getD_some]
  rw [groupPlain_frame_eq_nodeRect hv hplain]
  simp only [nodeRect, hproper, hfhalf]
  unfold groupPlain_bucketRight
  dsimp only at h
  simp only [CoordsImpl.nodeW, hnode, hthalf, hhalf] at h
  omega

theorem groupPlain_overlap_gap_of_common_owner_slots {P : Params} {cg : Graph}
    {run : Run} {pl : RegionPlacement} {alloc : RegionAllocation}
    {u w owner groupBranch plainOwner : Nat} {gn : Node}
    (hg : cg.nodes[u]? = some gn) (hgroup : gn.border = -2)
    (hlefts : ∀ x, 0 ≤ groupPlain_allocLeft alloc x)
    (hwidths : ∀ x, 0 ≤ alloc.widths.getD x 0)
    (hmarkers : ∀ r ∈ groupBorderRects cg run gn.decl,
      groupPlain_allocLeft alloc groupBranch ≤ r.x ∧
        r.x + r.w ≤ groupPlain_allocRight alloc groupBranch)
    (hplain : groupPlain_bucketLeft pl P alloc plainOwner ≤ (frameRect P cg run w).x ∧
      (frameRect P cg run w).x + (frameRect P cg run w).w ≤
        groupPlain_bucketRight pl P alloc plainOwner)
    (hfork :
      (plainOwner = owner ∧ groupPlain_bucketRight pl P alloc owner ≤
        groupPlain_allocLeft alloc groupBranch) ∨
      ∃ branch, groupPlain_allocLeft alloc branch ≤ groupPlain_bucketLeft pl P alloc plainOwner ∧
        groupPlain_bucketRight pl P alloc plainOwner ≤ groupPlain_allocRight alloc branch ∧
        (groupPlain_allocRight alloc groupBranch ≤ groupPlain_allocLeft alloc branch ∨
          groupPlain_allocRight alloc branch ≤ groupPlain_allocLeft alloc groupBranch)) :
    R8a_OverlapRowsXGap (frameRect P cg run u) (frameRect P cg run w) := by
  have hzero : 0 ≤ groupPlain_allocRight alloc groupBranch :=
    Int.add_nonneg (hlefts groupBranch) (hwidths groupBranch)
  refine groupPlain_gap_of_interval_bounds hg hgroup hzero hmarkers hplain ?_
  rcases hfork with ⟨rfl, hbefore⟩ | ⟨branch, hlo, hhi, hgap⟩
  · exact Or.inr hbefore
  · exact hgap.elim (fun h => Or.inl (Int.le_trans h hlo))
      (fun h => Or.inr (Int.le_trans hhi h))

inductive GroupPlainAllocatedTrail (pl : RegionPlacement) : Nat → Nat → Prop
  | here (g : Nat) : GroupPlainAllocatedTrail pl g g
  | down {g child target : Nat} (hchild : child ∈ pl.children.getD g [])
      (htail : GroupPlainAllocatedTrail pl child target) : GroupPlainAllocatedTrail pl g target

def GroupPlainRootedPath (pl : RegionPlacement) (resolve : Nat → Nat) :
    Nat → List Nat → Prop
  | _, [] => True
  | owner, decl :: rest =>
    resolve decl ∈ pl.children.getD owner [] ∧ GroupPlainRootedPath pl resolve (resolve decl) rest

private theorem gp_rooted_suffix {pl : RegionPlacement} {resolve : Nat → Nat} {owner : Nat}
    (common tail : List Nat)
    (h : GroupPlainRootedPath pl resolve owner (common ++ tail)) :
    GroupPlainRootedPath pl resolve ((common.map resolve).getLast?.getD owner) tail := by
  induction common generalizing owner with
  | nil => exact h
  | cons decl common ih =>
    change resolve decl ∈ pl.children.getD owner [] ∧
      GroupPlainRootedPath pl resolve (resolve decl) (common ++ tail) at h
    rw [List.map_cons, List.getLast?_cons, Option.getD_some]
    exact ih (owner := resolve decl) h.2

private theorem gp_rooted_trail {pl : RegionPlacement} {resolve : Nat → Nat}
    {owner : Nat} (path : List Nat) (h : GroupPlainRootedPath pl resolve owner path) :
    GroupPlainAllocatedTrail pl owner ((path.map resolve).getLast?.getD owner) := by
  induction path generalizing owner with
  | nil => exact .here _
  | cons decl tail ih =>
    change resolve decl ∈ pl.children.getD owner [] ∧
      GroupPlainRootedPath pl resolve (resolve decl) tail at h
    rw [List.map_cons, List.getLast?_cons, Option.getD_some]
    exact .down h.1 (ih (owner := resolve decl) h.2)

theorem groupPlain_common_path_branches {pl : RegionPlacement} {resolve : Nat → Nat}
    {group plain : List Nat} (hfork : GroupPlainOwnerFork group plain)
    (hg : GroupPlainRootedPath pl resolve pl.rm.clusters.length group)
    (hp : GroupPlainRootedPath pl resolve pl.rm.clusters.length plain)
    (hinj : ∀ a ∈ group, ∀ b ∈ plain, resolve a = resolve b → a = b) :
    ∃ owner groupBranch,
      groupBranch ∈ pl.children.getD owner [] ∧
      GroupPlainAllocatedTrail pl groupBranch
        ((group.map resolve).getLast?.getD pl.rm.clusters.length) ∧
      (((plain.map resolve).getLast?.getD pl.rm.clusters.length) = owner ∨
        ∃ branch, branch ∈ pl.children.getD owner [] ∧ groupBranch ≠ branch ∧
          GroupPlainAllocatedTrail pl branch
            ((plain.map resolve).getLast?.getD pl.rm.clusters.length)) := by
  obtain ⟨common, child, rest, hgroup, hplain⟩ := hfork
  let owner := (common.map resolve).getLast?.getD pl.rm.clusters.length
  rw [hgroup] at hg
  have hgt := gp_rooted_suffix common (child :: rest) hg
  change resolve child ∈ pl.children.getD owner [] ∧
    GroupPlainRootedPath pl resolve (resolve child) rest at hgt
  have hlast (item : Nat) (tail : List Nat) :
      (((common ++ item :: tail).map resolve).getLast?.getD pl.rm.clusters.length) =
        ((tail.map resolve).getLast?.getD (resolve item)) := by
    simp [List.map_append, List.getLast?_append, List.getLast?_cons]
  refine ⟨owner, resolve child, hgt.1, ?_, ?_⟩
  · rw [hgroup, hlast]
    exact gp_rooted_trail rest hgt.2
  · rcases hplain with rfl | ⟨other, tail, hplain, hne⟩
    · exact Or.inl rfl
    · rw [hplain] at hp
      have hpt := gp_rooted_suffix common (other :: tail) hp
      change resolve other ∈ pl.children.getD owner [] ∧
        GroupPlainRootedPath pl resolve (resolve other) tail at hpt
      have hsep : resolve child ≠ resolve other := by
        intro he
        apply hne
        apply hinj child (by rw [hgroup]; simp) other (by rw [hplain]; simp) he
      rw [hplain, hlast]
      exact Or.inr ⟨resolve other, hpt.1, hsep, gp_rooted_trail tail hpt.2⟩

theorem groupPlain_nested_slot_bounds {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {base target : Nat}
    (htrail : GroupPlainAllocatedTrail pl base target)
    (hinset : 0 ≤ regionInsetOf P)
    (hown : ∀ g, 0 ≤ pl.buckets.widths.getD g 0)
    (hwidths : ∀ c, 0 ≤ alloc.widths.getD c 0)
    (hleft : ∀ {g i child}, (pl.children.getD g [])[i]? = some child →
      groupPlain_allocLeft alloc child =
        groupPlain_bucketRight pl P alloc g +
          (((pl.children.getD g []).take i).map fun c => alloc.widths.getD c 0).sum)
    (hroom : ∀ g, (if g = pl.rm.clusters.length then 0 else regionInsetOf P) + pl.buckets.widths.getD g 0 +
      ((pl.children.getD g []).map fun c => alloc.widths.getD c 0).sum ≤ alloc.widths.getD g 0) :
    groupPlain_allocLeft alloc base ≤ groupPlain_allocLeft alloc target ∧
      groupPlain_allocRight alloc target ≤ groupPlain_allocRight alloc base := by
  induction htrail with
  | here g => exact ⟨Int.le_refl _, Int.le_refl _⟩
  | @down g child target hchild _ ih =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hchild
    obtain ⟨hlo, hhi⟩ := groupPlain_child_slot_bounds hi hinset (hown g) hwidths (hleft hi) (hroom g)
    exact ⟨Int.le_trans hlo ih.1, Int.le_trans ih.2 hhi⟩

theorem groupPlain_group_slot_of_markers {P : Params} {cg : Graph} {run : Run}
    {pl : RegionPlacement} {alloc : RegionAllocation} {decl owner : Nat}
    (hb : 0 ≤ P.clusterBorderW)
    (hloop : 0 ≤ pl.buckets.loopWidth.getD owner 0)
    (hroom : P.clusterBorderW ≤ alloc.widths.getD owner 0 - pl.buckets.loopWidth.getD owner 0)
    (hmarkers : ∀ r ∈ groupBorderRects cg run decl,
      r.w = P.clusterBorderW ∧
        (r.x =
          groupPlain_allocLeft alloc owner + Int.tdiv P.clusterBorderW 2 -
            Int.fdiv P.clusterBorderW 2 ∨
          r.x =
            groupPlain_allocRight alloc owner - pl.buckets.loopWidth.getD owner 0 -
              P.clusterBorderW + Int.tdiv P.clusterBorderW 2 - Int.fdiv P.clusterBorderW 2)) :
    ∀ r ∈ groupBorderRects cg run decl,
      groupPlain_allocLeft alloc owner ≤ r.x ∧
        r.x + r.w ≤ groupPlain_allocRight alloc owner := by
  intro r hr
  obtain ⟨hw, hx⟩ := hmarkers r hr
  have hends := groupPlain_marker_arithmetic
    (left := groupPlain_allocLeft alloc owner)
    (right := groupPlain_allocRight alloc owner - pl.buckets.loopWidth.getD owner 0)
    hb (by unfold groupPlain_allocRight; omega)
  rcases hx with he | he
  · rw [hw, he]
    obtain ⟨hl, hr⟩ := hends.1
    constructor <;> omega
  · rw [hw, he]
    obtain ⟨hl, hr⟩ := hends.2
    constructor <;> omega

theorem groupPlain_bucket_in_owner {pl : RegionPlacement} {P : Params} {alloc : RegionAllocation}
    {owner : Nat} (hinset : 0 ≤ regionInsetOf P)
    (hroom : regionInsetOf P + pl.buckets.widths.getD owner 0 ≤ alloc.widths.getD owner 0) :
    groupPlain_allocLeft alloc owner ≤ groupPlain_bucketLeft pl P alloc owner ∧
      groupPlain_bucketRight pl P alloc owner ≤ groupPlain_allocRight alloc owner := by
  unfold groupPlain_bucketRight groupPlain_bucketLeft groupPlain_allocRight
  split <;> omega

theorem groupPlain_gap_from_chosen_branches {P : Params} {cg : Graph} {run : Run}
    {pl : RegionPlacement} {alloc : RegionAllocation}
    {u w owner groupBranch groupOwner plainOwner : Nat} {gn : Node}
    (hg : cg.nodes[u]? = some gn) (hgroup : gn.border = -2)
    (hinset : 0 ≤ regionInsetOf P)
    (hlefts : ∀ x, 0 ≤ groupPlain_allocLeft alloc x)
    (hwidths : ∀ x, 0 ≤ alloc.widths.getD x 0)
    (hleft : ∀ {g i child}, (pl.children.getD g [])[i]? = some child →
      groupPlain_allocLeft alloc child =
        groupPlain_bucketRight pl P alloc g +
          (((pl.children.getD g []).take i).map fun c => alloc.widths.getD c 0).sum)
    (hroom : ∀ g, g ≠ pl.rm.clusters.length →
      regionInsetOf P + pl.buckets.widths.getD g 0 +
        ((pl.children.getD g []).map fun c => alloc.widths.getD c 0).sum ≤ alloc.widths.getD g 0)
    (htrailBounds : ∀ {base target}, GroupPlainAllocatedTrail pl base target →
      groupPlain_allocLeft alloc base ≤ groupPlain_allocLeft alloc target ∧
        groupPlain_allocRight alloc target ≤ groupPlain_allocRight alloc base)
    (hmarkers : ∀ r ∈ groupBorderRects cg run gn.decl,
      groupPlain_allocLeft alloc groupOwner ≤ r.x ∧
        r.x + r.w ≤ groupPlain_allocRight alloc groupOwner)
    (hplain : groupPlain_bucketLeft pl P alloc plainOwner ≤ (frameRect P cg run w).x ∧
      (frameRect P cg run w).x + (frameRect P cg run w).w ≤
        groupPlain_bucketRight pl P alloc plainOwner)
    (hgtrail : GroupPlainAllocatedTrail pl groupBranch groupOwner)
    (hgroupChild : groupBranch ∈ pl.children.getD owner [])
    (hfork : plainOwner = owner ∨ ∃ branch,
      branch ∈ pl.children.getD owner [] ∧ groupBranch ≠ branch ∧
        GroupPlainAllocatedTrail pl branch plainOwner ∧ plainOwner ≠ pl.rm.clusters.length) :
    R8a_OverlapRowsXGap (frameRect P cg run u) (frameRect P cg run w) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hgroupChild
  obtain ⟨hglo, hghi⟩ := htrailBounds hgtrail
  refine groupPlain_overlap_gap_of_common_owner_slots (owner := owner) hg hgroup hlefts hwidths
    (fun r hr => ⟨Int.le_trans hglo (hmarkers r hr).1, Int.le_trans (hmarkers r hr).2 hghi⟩)
    hplain ?_
  rcases hfork with he | ⟨branch, hbranch, hne, htrail, hplainNotRoot⟩
  · exact Or.inl ⟨he, groupPlain_bucket_before_child hwidths (hleft hi)⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbranch
    have hsum := gp_sum_nonneg (fun c => alloc.widths.getD c 0) hwidths
      (pl.children.getD plainOwner [])
    have hroom' := hroom plainOwner hplainNotRoot
    obtain ⟨hlo, hhi⟩ :=
      groupPlain_bucket_in_owner (pl := pl) (alloc := alloc) (owner := plainOwner) hinset
        (by omega)
    obtain ⟨hbranchlo, hbranchhi⟩ := htrailBounds htrail
    exact Or.inr ⟨branch, Int.le_trans hbranchlo hlo, Int.le_trans hhi hbranchhi,
      groupPlain_sibling_slot_gap hi hj hne hwidths (hleft hi) (hleft hj)⟩

private theorem gp_active_original_keys (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {n : ProperNode}
    (hn : labeled.nodes[v]? = some n) (hreal : n.dummy = false) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[v]? = some m ∧
      m.node.border = n.node.border ∧ m.node.clusterPath = n.node.clusterPath := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hk := sizeProperPortsX_key P exact labeled v
  change (sized.nodes[v]?).map _ = _ at hk
  cases hs : sized.nodes[v]? with
  | none => simp [hs, hn] at hk
  | some sz =>
    simp only [hs, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    have ht : titled.nodes[v]? = some (titleF sz) := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some] <;> rfl
    obtain ⟨_, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hc : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
        some (clearF (titleF sz)) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, hbordered,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht] <;> rfl
    obtain ⟨m, hm, _⟩ := materialize_exists _ hc
    obtain ⟨orig, ho, _, _, _, hunchanged⟩ := materialize_lookup _ hm
    have he : orig = clearF (titleF sz) := Option.some.inj (ho.symm.trans hc)
    subst orig
    have hm' : m = clearF (titleF sz) := hunchanged (by
      rw [(clearF_keys _).1, (titleF_keys _).1, hk.1, hreal])
    refine ⟨m, hm, ?_, ?_⟩
    · rw [hm', (clearF_keys _).2.1, (titleF_keys _).2.1, hk.2.1]
    · rw [hm', (clearF_keys _).2.2.1, (titleF_keys _).2.2.1, hk.2.2]

private theorem gp_regionFrames_plain {pl : RegionPlacement} {P : Params}
    {allocation : RegionAllocation} {xs : List Int} {v : Nat} {n : ProperNode}
    (hn : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (haway : ∀ c ∈ pl.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v) :
    (regionFrames pl P allocation xs).getD v 0 = xs.getD v 0 := by
  change (pl.rm.clusters.zipIdx.foldl (gp_frame_step pl P allocation) xs).getD v 0 = _
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ rfl
  intro ys hy q hq
  obtain ⟨ht, hb⟩ := haway q.1
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq))
  unfold gp_frame_step
  dsimp only
  rw [gp_set_getD, ite_eq_right (fun he => hb he.1.symm),
    gp_set_getD, ite_eq_right (fun he => ht he.1.symm)]
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ hy
  intro x hx job hj
  by_cases he : job.2 = v
  · have hlook := List.mem_zipIdx_iff_getElem?.mp hj
    rw [he, hn] at hlook
    have hzero : job.1.node.border = 0 := by rw [← Option.some.inj hlook, hplain]
    simp only [hzero]
    split <;> exact hx
  · have hwrite (x' : Int) : (setAt x job.2 x').getD v 0 = xs.getD v 0 := by
      rw [gp_set_getD, ite_eq_right (fun hf => he hf.1.symm)]
      exact hx
    split
    · exact hx
    · split <;> first | exact hwrite _ | exact hx

private theorem gp_port_x_other {pl : RegionPlacement} {g k v : Nat} {xs ys : List Int}
    (h : clusterPortR pl g k xs = .ok ys) (hk : k ≠ v) :
    ys.getD v 0 = xs.getD v 0 := by
  unfold clusterPortR at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · rw [← Except.ok.inj h, gp_set_getD, ite_eq_right (fun he => hk he.1.symm)]
  · cases h

private def gp_port_step (pl : RegionPlacement) (cg : Graph) (labels : List MeasuredLabel)
    (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
    Except LayoutError (List Int × Array ProperNode) := do
  let c := q.1
  let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
  if c.titleW < 0 ∨ footprint < 0 then throw .domain
  else
    let x ← clusterPortR pl q.2 c.top acc.1
    let x ← clusterPortR pl q.2 c.bottom x
    let top := acc.2.getD c.top default
    pure (x, acc.2.set! c.top { top with node := { top.node with
      h := max (RouteImpl.nodeH pl.p c.top) footprint } })

theorem groupPlain_reservedPorts_record {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper}
    (h : reservedPortsR pl cg labels xs = .ok (ys, placed)) :
    placed.nodes.length = pl.p.nodes.length ∧
    ∀ {v : Nat} {n : ProperNode}, pl.p.nodes[v]? = some n →
      ∃ m, placed.nodes[v]? = some m ∧ m.node.border = n.node.border ∧
        ((∀ c ∈ pl.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v) →
          m = n ∧ ys.getD v 0 = xs.getD v 0) := by
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM (gp_port_step pl cg labels)
    (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hfold, hresult⟩ := gp_bind_ok h
  have hp : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hresult)).symm
  have hy : ys = out.1 := (congrArg Prod.fst (Except.ok.inj hresult)).symm
  rw [hp, hy]
  refine ⟨?_, ?_⟩
  · rw [Array.length_toList, ← List.size_toArray]
    refine gp_fold_ok (inv := fun acc => acc.2.size = pl.p.nodes.toArray.size) rfl ?_ hfold
    intro a q b ha _ hab
    dsimp only [gp_port_step] at hab
    split at hab
    · cases hab
    · obtain ⟨_, _, hab⟩ := gp_bind_ok hab
      obtain ⟨_, _, hab⟩ := gp_bind_ok hab
      rw [← Except.ok.inj hab]
      simpa only [size_set!_eq] using ha
  · intro v n hn
    have keep (jobs : List (RegionCluster × Nat)) (start finish : List Int × Array ProperNode)
        (src : ProperNode) (hsrc : start.2[v]? = some src)
        (hj : jobs.foldlM (gp_port_step pl cg labels) start = .ok finish) :
        ∃ dst, finish.2[v]? = some dst ∧ dst.node.border = src.node.border ∧
          ((∀ q ∈ jobs, q.1.top ≠ v ∧ q.1.bottom ≠ v) →
            dst = src ∧ finish.1.getD v 0 = start.1.getD v 0) := by
      induction jobs generalizing start src with
      | nil =>
        rw [← Except.ok.inj hj]
        exact ⟨src, hsrc, rfl, fun _ => ⟨rfl, rfl⟩⟩
      | cons q qs ih =>
        rw [List.foldlM_cons] at hj
        obtain ⟨mid, hm, ht⟩ := gp_bind_ok hj
        dsimp only [gp_port_step] at hm
        split at hm
        · cases hm
        · obtain ⟨x, hx, hm⟩ := gp_bind_ok hm
          obtain ⟨y, hy', hm⟩ := gp_bind_ok hm
          have hrec : ∃ m, mid.2[v]? = some m ∧ m.node.border = src.node.border := by
            rw [← Except.ok.inj hm]
            dsimp only
            rw [Array.set!_eq_setIfInBounds]
            by_cases htop : q.1.top = v
            · have hi := (Array.getElem?_eq_some_iff.mp hsrc).1
              have hget : start.2.getD v default = src := by
                simp only [Array.getD_eq_getD_getElem?, hsrc, Option.getD_some]
              rw [htop, Array.getElem?_setIfInBounds_self_of_lt hi, hget]
              exact ⟨_, rfl, rfl⟩
            · rw [Array.getElem?_setIfInBounds_ne htop]
              exact ⟨src, hsrc, rfl⟩
          obtain ⟨m, hmid, hb⟩ := hrec
          obtain ⟨dst, hd, hborder, hkeep⟩ := ih mid m hmid ht
          refine ⟨dst, hd, hborder.trans hb, ?_⟩
          intro ha
          obtain ⟨hTop, hBottom⟩ := ha q List.mem_cons_self
          obtain ⟨he, hxs⟩ := hkeep (fun r hr => ha r (List.mem_cons_of_mem _ hr))
          have hcurrent : mid.2[v]? = some src := by
            rw [← Except.ok.inj hm]
            dsimp only
            rwa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hTop]
          have hmidX : mid.1 = y := (congrArg Prod.fst (Except.ok.inj hm)).symm
          rw [hmidX] at hxs
          exact ⟨he.trans (Option.some.inj (hmid.symm.trans hcurrent)),
            hxs.trans ((gp_port_x_other hy' hBottom).trans (gp_port_x_other hx hTop))⟩
    obtain ⟨m, hm, hb, hs⟩ := keep _ _ _ n (by rwa [List.getElem?_toArray]) hfold
    exact ⟨m, by simpa only [Array.getElem?_toList] using hm, hb,
      fun ha => hs (fun q hq => ha q.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)))⟩

private def gp_node_owner (rm : ComponentRegions) (q : ProperNode × Nat) :
    Except LayoutError Nat :=
  match q.1.node.clusterPath.getLast? with
  | none => .ok rm.clusters.length
  | some decl =>
    match clusterOfDecl rm decl with
    | some owner => .ok owner
    | none => .error .domain

theorem groupPlain_nodeGroups_lookup {rm : ComponentRegions} {p : Proper} {groups : List Nat}
    (hgroups : nodeGroupsOf rm p = .ok groups) {v : Nat} {n : ProperNode}
    (hn : p.nodes[v]? = some n) :
    ∃ owner, groups[v]? = some owner ∧ owner ≤ rm.clusters.length ∧
      match n.node.clusterPath.getLast? with
      | none => owner = rm.clusters.length
      | some decl => clusterOfDecl rm decl = some owner := by
  have hmap : p.nodes.zipIdx.mapM (gp_node_owner rm) = .ok groups := hgroups
  have hz : p.nodes.zipIdx[v]? = some (n, v) := by
    simp only [List.getElem?_zipIdx, hn, Option.map_some, Nat.zero_add]
  obtain ⟨owner, hcall, hlook⟩ := (mapM_getElem? (gp_node_owner rm) _ _ hmap).2 v (n, v) hz
  refine ⟨owner, hlook, ?_⟩
  cases hp : n.node.clusterPath.getLast? with
  | none =>
    have he : (Except.ok rm.clusters.length : Except LayoutError Nat) = .ok owner := by
      simpa only [gp_node_owner, hp] using hcall
    exact ⟨Nat.le_of_eq (Except.ok.inj he).symm, (Except.ok.inj he).symm⟩
  | some d =>
    cases hd : clusterOfDecl rm d with
    | none =>
      have he : (Except.error .domain : Except LayoutError Nat) = .ok owner := by
        simpa only [gp_node_owner, hp, hd] using hcall
      cases he
    | some k =>
      have he : (Except.ok k : Except LayoutError Nat) = .ok owner := by
        simpa only [gp_node_owner, hp, hd] using hcall
      obtain ⟨hk, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hd
      have heq := Except.ok.inj he
      subst owner
      refine ⟨Nat.le_of_lt hk, ?_⟩
      change clusterOfDecl rm d = some k
      exact hd

private def gp_parent_index (inp : Input) (rows : List RegionCluster) (c : RegionCluster) : Int :=
  match boxParent inp c.decl with
  | "" => -1
  | pid =>
    match rows.findIdx? (fun a => a.id == pid) with
    | some k => (k : Int)
    | none => -1

private theorem gp_resolved_tables {P : Params} {s : RegionSpec} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    rm.clusters = clusterRows inp s cg ∧
      rm.parents = rm.clusters.map (gp_parent_index inp rm.clusters) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := gp_bind_ok h
    split at h
    · cases h
    · rw [← Option.some.inj (Except.ok.inj h)]
      refine ⟨rfl, ?_⟩
      apply List.map_congr_left
      intro c _
      unfold gp_parent_index
      first | rfl | split <;> rfl

private def gp_cluster_row (inp : Input) (s : RegionSpec) (cg : Graph)
    (q : Node × Nat) : Option RegionCluster :=
  if q.1.border != -2 then none
  else
    let bottom := match cg.nodes.zipIdx.find? (fun b =>
        b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2
    let node := match cg.nodes.zipIdx.find? (fun b => b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2
    let titles := s.titles.getD q.1.decl (0, 0)
    some ({ id := boxId inp q.1.decl, decl := q.1.decl, node := node, top := q.2,
            bottom := bottom, titleW := q.1.w, titleH := titles.2,
            extent := q.1.loopExtent } : RegionCluster)

private theorem gp_cluster_entry {inp : Input} {s : RegionSpec} {cg : Graph}
    {q : Node × Nat} {c : RegionCluster}
    (hq : cg.nodes[q.2]? = some q.1) (hc : gp_cluster_row inp s cg q = some c) :
    c.decl = q.1.decl ∧ c.id = boxId inp c.decl ∧ c.top = q.2 ∧ q.1.border = -2 ∧
      ∃ bottom : Node, cg.nodes[c.bottom]? = some bottom ∧
        (bottom.border = -2 ∨ bottom.border = 2) := by
  unfold gp_cluster_row at hc
  split at hc
  · cases hc
  · rename_i htest
    have htop : q.1.border = -2 := by simpa using htest
    rw [← Option.some.inj hc]
    refine ⟨rfl, rfl, rfl, htop, ?_⟩
    change ∃ bottom : Node, cg.nodes[(match cg.nodes.zipIdx.find? (fun b =>
      b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2)]? = some bottom ∧ (bottom.border = -2 ∨ bottom.border = 2)
    split
    · rename_i bottom hbottom
      have hbottomTest : (bottom.1.border == 2 && bottom.1.decl == q.1.decl) = true :=
        List.find?_some (p := fun b : Node × Nat =>
          b.1.border == 2 && b.1.decl == q.1.decl) hbottom
      exact ⟨bottom.1, List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hbottom),
        Or.inr (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hbottomTest).1)⟩
    · exact ⟨q.1, hq, Or.inl htop⟩

private theorem gp_cluster_anchors {inp : Input} {s : RegionSpec} {cg : Graph}
    {rm : ComponentRegions} (hrows : rm.clusters = clusterRows inp s cg)
    {c : RegionCluster} (hc : c ∈ rm.clusters) :
    ∃ top bottom : Node, cg.nodes[c.top]? = some top ∧ top.border = -2 ∧
      top.decl = c.decl ∧ c.id = boxId inp c.decl ∧ cg.nodes[c.bottom]? = some bottom ∧
      (bottom.border = -2 ∨ bottom.border = 2) := by
  rw [hrows] at hc
  change c ∈ cg.nodes.zipIdx.filterMap (gp_cluster_row inp s cg) at hc
  obtain ⟨q, hq, hsys⟩ := List.mem_filterMap.mp hc
  have hget := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨hd, hid, ht, hb, b, hbget, hbkind⟩ := gp_cluster_entry hget hsys
  exact ⟨q.1, b, ht.symm ▸ hget, hb, hd.symm, hid, hbget, hbkind⟩

private theorem gp_cluster_of_top {inp : Input} {s : RegionSpec} {cg : Graph}
    {rm : ComponentRegions} (hrows : rm.clusters = clusterRows inp s cg)
    {v : Nat} {n : Node} (hn : cg.nodes[v]? = some n) (hb : n.border = -2) :
    ∃ c ∈ rm.clusters, c.decl = n.decl ∧ c.titleW = n.w := by
  have hn' : (n, v) ∈ cg.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hn
  obtain ⟨c, hc⟩ : ∃ c, gp_cluster_row inp s cg (n, v) = some c := by
    have htop : ¬ ((n, v).1.border != (-2 : Int)) := fun h => (bne_iff_ne.mp h) hb
    unfold gp_cluster_row
    rw [ite_eq_right htop]
    exact ⟨_, rfl⟩
  refine ⟨c, ?_, (gp_cluster_entry hn hc).1, ?_⟩
  · rw [hrows]
    change c ∈ cg.nodes.zipIdx.filterMap (gp_cluster_row inp s cg)
    exact List.mem_filterMap.mpr ⟨(n, v), hn', hc⟩
  · unfold gp_cluster_row at hc
    split at hc
    · cases hc
    · rw [← Option.some.inj hc]

private theorem gp_cluster_decls_unique {inp : Input} {s : RegionSpec} {cg : Graph}
    {rm : ComponentRegions} (hrows : rm.clusters = clusterRows inp s cg)
    (hkeys : ∀ {i j : Nat} {a b : Node}, cg.nodes[i]? = some a →
      cg.nodes[j]? = some b → a.border = -2 → b.border = -2 → a.decl = b.decl → i = j) :
    (rm.clusters.map (·.decl)).Nodup := by
  rw [hrows]
  change ((cg.nodes.zipIdx.filterMap (gp_cluster_row inp s cg)).map
    (·.decl)).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  have hp : cg.nodes.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := by
    rw [← List.pairwise_map (f := Prod.snd), List.zipIdx_map_snd]
    exact List.nodup_range'
  let agrees (q q' : Node × Nat) : Prop :=
    q.2 ≠ q'.2 ∧ q ∈ cg.nodes.zipIdx ∧ q' ∈ cg.nodes.zipIdx
  have hs : cg.nodes.zipIdx.Pairwise agrees :=
    List.Pairwise.imp_of_mem (fun hq hq' hn => ⟨hn, hq, hq'⟩) hp
  refine List.Pairwise.filterMap (gp_cluster_row inp s cg) ?_ hs
  intro q q' ⟨hne, hq, hq'⟩ a ha b hb he
  have hqget := List.mem_zipIdx_iff_getElem?.mp hq
  have hq'get := List.mem_zipIdx_iff_getElem?.mp hq'
  have ha' := gp_cluster_entry hqget ha
  have hb' := gp_cluster_entry hq'get hb
  exact hne (hkeys hqget hq'get ha'.2.2.2.1 hb'.2.2.2.1
    (ha'.1.symm.trans (he.trans hb'.1)))

private theorem gp_component_member_node {graph : Graph} {comp : List Nat} {s : RegionSpec}
    {k i : Nat} {node : Node} (hcomp : comp ∈ components graph)
    (hnode : (componentCandidateR (some s) graph comp k).nodes[i]? = some node) :
    ∃ key, comp[i]? = some key ∧ graph.nodes[key]? = some node := by
  change (comp.map fun v => graph.nodes.getD v default)[i]? = some node at hnode
  rw [List.getElem?_map] at hnode
  cases hp : comp[i]? with
  | none => simp [hp] at hnode
  | some key =>
    obtain ⟨root, he⟩ := mem_components_eq hcomp
    have hm := List.mem_of_getElem? hp
    rw [he] at hm
    have hlt := ((mem_componentOf (g := graph)).mp hm).1
    simp only [hp, Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some, Option.some.injEq] at hnode
    exact ⟨key, rfl, hnode ▸ List.getElem?_eq_getElem hlt⟩

private theorem gp_measured_node_key {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {v : Nat} {n : Node}
    (h : e.graph.nodes[v]? = some n) :
    ∃ src, e.graph0.nodes[v]? = some src ∧ src.border = n.border ∧ src.decl = n.decl := by
  have hv := (List.getElem?_eq_some_iff.mp h).1
  rw [exactGraph_length e.graph_eq] at hv
  obtain ⟨x, hx, hb, _, hd⟩ := exactGraph_node_key e.graph_eq (List.getElem?_eq_getElem hv)
  rw [h] at hx
  cases hx
  exact ⟨_, List.getElem?_eq_getElem hv, hb.symm, hd.symm⟩

theorem active_candidate_top_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k i : Nat} {n : Node}
    (hn : (componentCandidateR (some s) e.graph comp k).nodes[i]? = some n)
    (hb : n.border = -2) :
    comp[i]? = some n.decl ∧ e.graph.nodes[n.decl]? = some n ∧
      ∃ source, inp.boxes[n.decl]? = some source := by
  obtain ⟨key, hkey, hnode⟩ := gp_component_member_node hcomp hn
  obtain ⟨raw, hraw, hk, hd⟩ := gp_measured_node_key e hnode
  obtain ⟨hi, _, hsrc, _, _⟩ := measuredGraph_group_origin e.graph0_eq hraw (hk.trans hb)
  have he : key = n.decl := hi.symm.trans hd
  rw [he] at hkey hnode
  rw [hd, List.getElem?_map] at hsrc
  obtain ⟨source, hsource, _⟩ := Option.map_eq_some_iff.mp hsrc
  exact ⟨hkey, hnode, source, hsource⟩

theorem active_candidate_plain_decl {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k i key : Nat}
    {n : Node} {source : ModelBox}
    (hn : (componentCandidateR (some s) e.graph comp k).nodes[i]? = some n)
    (hb : n.border = 0) (hkey : comp[i]? = some key) (hsrc : inp.boxes[key]? = some source) :
    n.decl = key := by
  obtain ⟨atKey, hAt, hnode⟩ := gp_component_member_node hcomp hn
  have he := Option.some.inj (hAt.symm.trans hkey)
  subst atKey
  obtain ⟨raw, hraw, hk, hd⟩ := gp_measured_node_key e hnode
  obtain ⟨_, _, _, hprepared, _, hmetadata⟩ :=
    measuredGraph_prepared_source e.graph0_eq
  obtain ⟨_, hchanged, _⟩ := fixedSizes_path_index inp hsrc
  rw [hprepared] at hraw
  exact hd.symm.trans (prepare_plain_path_origin _ _ _ _ hmetadata hraw (hk.trans hb) hchanged).1

private theorem gp_candidate_cluster_sources {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k : Nat} {rm : ComponentRegions}
    (hrows : rm.clusters = clusterRows inp s (componentCandidateR (some s) e.graph comp k)) :
    (rm.clusters.map (·.decl)).Nodup ∧
    ∀ c ∈ rm.clusters, ∃ source top, inp.boxes[c.decl]? = some source ∧ c.id = source.id ∧
      c.decl ∈ comp ∧ e.graph.nodes[c.decl]? = some top := by
  refine ⟨gp_cluster_decls_unique hrows ?_, ?_⟩
  · intro i j a b ha hb hba hbb he
    have hi := (active_candidate_top_source e hcomp ha hba).1
    have hj := (active_candidate_top_source e hcomp hb hbb).1
    have hnd := components_nodup e.graph comp hcomp
    exact hnd.eq_of_getElem_eq (List.getElem?_eq_some_iff.mp hi).1
      (List.getElem?_eq_some_iff.mp hj).1
      ((List.getElem?_eq_some_iff.mp hi).2.trans
        (he.trans (List.getElem?_eq_some_iff.mp hj).2.symm))
  · intro c hc
    obtain ⟨top, _, ht, hb, hd, hid, _, _⟩ := gp_cluster_anchors hrows hc
    obtain ⟨hi, htop, source, hsource⟩ := active_candidate_top_source e hcomp ht hb
    rw [hd] at hi htop hsource
    exact ⟨source, top, hsource, by simp [hid, boxId, hsource], List.mem_of_getElem? hi, htop⟩

private theorem gp_findIdx_unique {α β : Type} [BEq β] [LawfulBEq β]
    {rows : List α} (key : α → β) {i : Nat} {row : α}
    (hrow : rows[i]? = some row)
    (hunique : ∀ {j : Nat} {r : α}, rows[j]? = some r → key r = key row → j = i) :
    rows.findIdx? (fun r => key r == key row) = some i := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hrow
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨hi, by rw [he]; exact beq_self_eq_true _, ?_⟩
  intro j hj hjKey
  have heq := hunique (List.getElem?_eq_getElem (Nat.lt_trans hj hi)) (beq_iff_eq.mp hjKey)
  omega

private theorem gp_decl_index {rm : ComponentRegions}
    (hnd : (rm.clusters.map (·.decl)).Nodup)
    {i : Nat} {c : RegionCluster} (hc : rm.clusters[i]? = some c) :
    clusterOfDecl rm c.decl = some i := by
  unfold clusterOfDecl
  apply gp_findIdx_unique RegionCluster.decl hc
  intro j d hd hkey
  have hj : j < (rm.clusters.map (·.decl)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hd).1
  apply (hnd.getElem?_inj hj).mp
  simp only [List.getElem?_map, hd, hc, Option.map_some, hkey]

private theorem gp_parent_top {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {i : Nat} {source : ModelBox} (hi : inp.boxes[i]? = some source)
    (hg : source.role = .group)
    (hf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    ∃ top, e.graph.nodes[i]? = some top ∧ top.border = -2 ∧ top.decl = i := by
  obtain ⟨_, hbox, _⟩ := fixedSizes_path_index inp hi
  have hl := e.lines_eq
  unfold boxLines at hl
  have hlen : e.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hl).1
  have hbound : i < e.lines.length := by
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hi).1
  dsimp only at hbox
  simp only [hf, Bool.false_eq_true, ↓reduceIte] at hbox
  obtain ⟨raw, _, hraw, _, hborder, _, hdecl, _, _, _, _, _⟩ :=
    measuredGraph_paired_markers e.graph0_eq hbound hbox hg
  obtain ⟨top, htop, hb, _, hd⟩ := exactGraph_node_key e.graph_eq hraw
  exact ⟨top, htop, hb.trans hborder, hd.trans hdecl⟩

private theorem gp_parentGroup_table {inp : Input} {rm : ComponentRegions}
    (hparents : rm.parents = rm.clusters.map (gp_parent_index inp rm.clusters))
    {i : Nat} {c : RegionCluster} {source : ModelBox}
    (hc : rm.clusters[i]? = some c) (hsource : inp.boxes[c.decl]? = some source) :
    parentGroup rm i = if source.parent = "" then rm.clusters.length
      else (rm.clusters.findIdx? fun row => row.id == source.parent).getD rm.clusters.length := by
  unfold parentGroup
  rw [hparents, List.getD_eq_getElem?_getD, List.getElem?_map, hc, Option.map_some,
    Option.getD_some]
  unfold gp_parent_index boxParent
  simp only [hsource, Option.map_some, Option.getD_some]
  by_cases hroot : source.parent = ""
  · simp [hroot]
  · have hmatch : (match source.parent with
      | "" => (-1 : Int)
      | pid => match rm.clusters.findIdx? (fun row => row.id == pid) with
        | some k => (k : Int)
        | none => -1) =
      (match rm.clusters.findIdx? (fun row => row.id == source.parent) with
       | some k => (k : Int)
       | none => -1) := by
      split
      · rename_i he
        exact (hroot he).elim
      · rfl
    rw [hmatch, ite_eq_right hroot]
    cases rm.clusters.findIdx? (fun row => row.id == source.parent) <;> simp

private theorem gp_actual_root_parent {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k : Nat}
    {rm : ComponentRegions}
    (hrows : rm.clusters = clusterRows inp s (componentCandidateR (some s) e.graph comp k))
    (hparents : rm.parents = rm.clusters.map (gp_parent_index inp rm.clusters))
    {i : Nat} {c : RegionCluster} {source : ModelBox} {top : Node}
    (hc : rm.clusters[i]? = some c) (hsource : inp.boxes[c.decl]? = some source)
    (hmem : c.decl ∈ comp) (htop : e.graph.nodes[c.decl]? = some top)
    (hroot : parentGroup rm i = rm.clusters.length) :
    source.parent = "" := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨parent, hp, hid, hg, hf⟩ := framedParents_parent hframed
    (List.mem_of_getElem? hsource) hn
  obtain ⟨pid, hpid⟩ := List.mem_iff_getElem?.mp hp
  have hmember := R_parentInComponentR_holds e hwf hframed comp hcomp c.decl pid
    (List.getElem?_eq_some_iff.mp hsource).1 hmem top htop source hsource parent hpid hid.symm hn
  obtain ⟨pos, hpos⟩ := List.mem_iff_getElem?.mp hmember
  obtain ⟨pTop, hpTop, hpBorder, hpDecl⟩ := gp_parent_top e hpid hg hf
  obtain ⟨row, hrow, hdecl, _⟩ := gp_cluster_of_top hrows
    (component_node_lookupR (spec := some s) (cand := k) hpos hpTop) hpBorder
  have hrowId : row.id = source.parent := by
    obtain ⟨_, _, _, _, _, hname, _, _⟩ := gp_cluster_anchors hrows hrow
    rw [hname, hdecl, hpDecl]
    simp [boxId, hpid, hid]
  have hw : ∃ i, rm.clusters.findIdx? (fun row => row.id == source.parent) = some i := by
    cases he : rm.clusters.findIdx? (fun row => row.id == source.parent) with
    | none =>
      have hf := List.findIdx?_eq_none_iff.mp he row hrow
      simp [hrowId] at hf
    | some i => exact ⟨i, rfl⟩
  obtain ⟨idx, hidx⟩ := hw
  have hlt := (List.findIdx?_eq_some_iff_getElem.mp hidx).1
  rw [gp_parentGroup_table hparents hc hsource, ite_eq_right hn, hidx, Option.getD_some] at hroot
  omega

private theorem gp_actual_parent_ref {inp : Input} {rm : ComponentRegions}
    (hparents : rm.parents = rm.clusters.map (gp_parent_index inp rm.clusters))
    {a i : Nat} {p c : RegionCluster} {parent source : ModelBox}
    (ha : rm.clusters[a]? = some p) (hc : rm.clusters[i]? = some c)
    (hid : p.id = parent.id) (hsource : inp.boxes[c.decl]? = some source)
    (hparent : parentGroup rm i = a) :
    source.parent = parent.id ∧ source.parent ≠ "" := by
  have haBound := (List.getElem?_eq_some_iff.mp ha).1
  rw [gp_parentGroup_table hparents hc hsource] at hparent
  split at hparent
  · omega
  · rename_i hne
    cases hf : rm.clusters.findIdx? (fun row => row.id == source.parent) with
    | none => rw [hf, Option.getD_none] at hparent; omega
    | some k =>
      rw [hf, Option.getD_some] at hparent
      subst k
      have hh := (List.findIdx?_eq_some_iff_getElem.mp hf).2.1
      rw [(List.getElem?_eq_some_iff.mp ha).2, hid] at hh
      exact ⟨(beq_iff_eq.mp hh).symm, hne⟩

private def gp_resolve (rm : ComponentRegions) (decl : Nat) : Nat :=
  (clusterOfDecl rm decl).getD rm.clusters.length

private theorem gp_rooted_append {pl : RegionPlacement} {resolve : Nat → Nat} {owner : Nat}
    (start tail : List Nat) (hstart : GroupPlainRootedPath pl resolve owner start)
    (htail : GroupPlainRootedPath pl resolve ((start.map resolve).getLast?.getD owner) tail) :
    GroupPlainRootedPath pl resolve owner (start ++ tail) := by
  induction start generalizing owner with
  | nil => exact htail
  | cons first rest ih =>
    rw [List.map_cons, List.getLast?_cons, Option.getD_some] at htail
    change resolve first ∈ pl.children.getD owner [] ∧
      GroupPlainRootedPath pl resolve (resolve first) rest at hstart
    exact ⟨hstart.1, ih hstart.2 htail⟩

private theorem gp_cluster_rooted {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k : Nat}
    {rm : ComponentRegions} {pl : RegionPlacement}
    (hrows : rm.clusters = clusterRows inp s (componentCandidateR (some s) e.graph comp k))
    (hparents : rm.parents = rm.clusters.map (gp_parent_index inp rm.clusters))
    (hnd : (rm.clusters.map (·.decl)).Nodup)
    (hsource : ∀ c ∈ rm.clusters, ∃ source top, inp.boxes[c.decl]? = some source ∧
      c.id = source.id ∧ c.decl ∈ comp ∧ e.graph.nodes[c.decl]? = some top)
    (hchildren : ∀ a b, b ∈ pl.children.getD a [] →
      b < rm.clusters.length ∧ parentGroup rm b = a)
    {owner : Nat} (htrail : RegionGroupBranch pl.children rm.clusters.length owner)
    {c : RegionCluster} {source : ModelBox} (hc : rm.clusters[owner]? = some c)
    (hsrc : inp.boxes[c.decl]? = some source) :
    GroupPlainRootedPath pl (gp_resolve rm) rm.clusters.length
      (Compound.path inp.boxes source ++ [c.decl]) := by
  let root := rm.clusters.length
  let resolve := gp_resolve rm
  let known (g : Nat) : Prop := g = root ∨
    ∃ (c : RegionCluster) (src : ModelBox), rm.clusters[g]? = some c ∧
      inp.boxes[c.decl]? = some src ∧
      GroupPlainRootedPath pl resolve root (Compound.path inp.boxes src ++ [c.decl])
  have hres {g : Nat} {d : RegionCluster} (hd : rm.clusters[g]? = some d) :
      resolve d.decl = g := by
    simp only [resolve, gp_resolve, gp_decl_index hnd hd, Option.getD_some]
  have advance {a b : Nat} (ha : known a) (hb : b ∈ pl.children.getD a []) : known b := by
    obtain ⟨hbound, hp⟩ := hchildren a b hb
    let d := rm.clusters[b]
    have hd : rm.clusters[b]? = some d := List.getElem?_eq_getElem hbound
    obtain ⟨src, top, hsrc', _, hmem, htop⟩ := hsource d (List.mem_of_getElem? hd)
    refine Or.inr ⟨d, src, hd, hsrc', ?_⟩
    have hedge : resolve d.decl ∈ pl.children.getD a [] := by rwa [hres hd]
    rcases ha with hroot | ⟨pa, ps, hpa, hps, hprev⟩
    · rw [hroot] at hedge hp
      have he := gp_actual_root_parent e hwf hframed hcomp hrows hparents hd hsrc' hmem htop hp
      have hnil : Compound.path inp.boxes src = [] := by
        unfold Compound.path
        rw [he]
        cases inp.boxes.length <;> rfl
      rw [hnil]
      exact ⟨hedge, trivial⟩
    · obtain ⟨srcP, _, hsrcP, hid, _, _⟩ := hsource pa (List.mem_of_getElem? hpa)
      have he : srcP = ps := Option.some.inj (hsrcP.symm.trans hps)
      subst srcP
      obtain ⟨hpRef, hpNe⟩ := gp_actual_parent_ref hparents hpa hd hid hsrc' hp
      have hpPath := Compound.path_of_parent (inputModel inp o) hwf hps hsrc' hpRef hpNe
      change Compound.path inp.boxes src = Compound.path inp.boxes ps ++ [pa.decl] at hpPath
      rw [hpPath]
      refine gp_rooted_append (Compound.path inp.boxes ps ++ [pa.decl]) [d.decl] hprev ?_
      rw [List.map_append, List.getLast?_append]
      simp only [List.map_singleton, List.getLast?_singleton, Option.some_or,
        Option.getD_some, hres hpa]
      exact ⟨hedge, trivial⟩
  have transport {a b : Nat} (hs : RegionGroupBranch pl.children a b) : known a → known b := by
    induction hs with
    | here => exact id
    | down he _ ih => exact fun h => ih (advance h he)
  rcases transport htrail (Or.inl rfl) with hr | ⟨d, src, hd, hlookup, hpath⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hc).1
    change owner = rm.clusters.length at hr
    omega
  · have he : d = c := Option.some.inj (hd.symm.trans hc)
    subst d
    have he : src = source := Option.some.inj (hlookup.symm.trans hsrc)
    subst src
    exact hpath

private abbrev GpAllocationState := List Int × List Int × List (Option Int)

private theorem gp_allocation_left_stays {pl : RegionPlacement} {P : Params}
    {widths : List Int} {jobs : List Nat} {before after : GpAllocationState} {owner : Nat}
    (havoid : ∀ g ∈ jobs, owner ∉ pl.children.getD g [])
    (h : jobs.foldlM (fun a g => allocateGroup pl P widths g a) before = .ok after) :
    after.2.1.getD owner 0 = before.2.1.getD owner 0 := by
  refine gp_fold_ok (inv := fun a : GpAllocationState =>
    a.2.1.getD owner 0 = before.2.1.getD owner 0) rfl ?_ h
  intro a g b ha hg hstep
  rcases a with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at hstep
  dsimp only at hstep
  obtain ⟨placed, hplaced, hstep⟩ := gp_bind_ok hstep
  obtain ⟨_, _, hstep⟩ := gp_bind_ok hstep
  rw [← Except.ok.inj hstep]
  change placed.2.getD owner 0 = before.2.1.getD owner 0
  refine gp_fold_ok (inv := fun a : Int × List Int =>
    a.2.getD owner 0 = before.2.1.getD owner 0) ha ?_ hplaced
  intro st c out hs hc hnext
  change Except.ok (st.1 + widths.getD c 0, setAt st.2 c st.1) = .ok out at hnext
  rw [← Except.ok.inj hnext]
  change (setAt st.2 c st.1).getD owner 0 = _
  have hne : ¬ (owner = c ∧ c < st.2.length) := fun he => havoid g hg (he.1.symm ▸ hc)
  rw [gp_set_getD, ite_eq_right hne]
  exact hs

private def gp_bucket_member (groups : List Nat) (g : Nat) (q : ProperNode × Nat) : Bool :=
  q.1.node.border == 0 && groups.getD q.2 0 == g

private theorem gp_bucket_member_iff {groups : List Nat} {g : Nat} {q : ProperNode × Nat} :
    gp_bucket_member groups g q ↔ q.1.node.border = 0 ∧ groups.getD q.2 0 = g := by
  simp only [gp_bucket_member, Bool.and_eq_true_iff, beq_iff_eq]

private def gp_gather_members (groups : List Nat) (rows : List (List Nat))
    (q : ProperNode × Nat) : List (List Nat) :=
  if q.1.node.border != 0 then rows else
    let owner := groups.getD q.2 0
    setAt rows owner (rows.getD owner [] ++ [q.2])

private theorem gp_gather_members_length (groups : List Nat) (rows : List (List Nat))
    (q : ProperNode × Nat) : (gp_gather_members groups rows q).length = rows.length := by
  unfold gp_gather_members
  split <;> first | rfl | exact gp_set_length _ _ _

private theorem gp_gather_members_lookup (groups : List Nat) (jobs : List (ProperNode × Nat))
    (rows : List (List Nat)) (g : Nat) :
    (jobs.foldl (gp_gather_members groups) rows).getD g [] = rows.getD g [] ++
      (if g < rows.length then (jobs.filter (gp_bucket_member groups g)).map Prod.snd else []) := by
  induction jobs generalizing rows with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih, gp_gather_members_length]
    by_cases hp : q.1.node.border = 0
    · have hs : gp_gather_members groups rows q =
          setAt rows (groups.getD q.2 0) (rows.getD (groups.getD q.2 0) [] ++ [q.2]) := by
        simp [gp_gather_members, hp]
      rw [hs, gp_set_getD]
      by_cases he : groups.getD q.2 0 = g
      · by_cases hb : g < rows.length
        · have hm : gp_bucket_member groups g q := gp_bucket_member_iff.mpr ⟨hp, he⟩
          rw [he, ite_eq_left ⟨rfl, hb⟩, List.filter_cons_of_pos hm]
          simp only [ite_eq_left hb, List.map_cons, List.append_assoc, List.singleton_append]
        · have hn : ¬ (g = g ∧ g < rows.length) := fun h => hb h.2
          rw [he, ite_eq_right hn]
          simp only [ite_eq_right hb]
      · have hm : ¬ gp_bucket_member groups g q := fun h => he (gp_bucket_member_iff.mp h).2
        have hn : ¬ (g = groups.getD q.2 0 ∧ groups.getD q.2 0 < rows.length) :=
          fun h => he h.1.symm
        rw [ite_eq_right hn, List.filter_cons_of_neg hm]
    · have hm : ¬ gp_bucket_member groups g q := fun h => hp (gp_bucket_member_iff.mp h).1
      have hstep : gp_gather_members groups rows q = rows :=
        ite_eq_left (bne_iff_ne.mpr hp)
      rw [hstep, List.filter_cons_of_neg hm]

private theorem gp_bucket_members (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (groups : List Nat) (labelWidths x : List Int) (g : Nat) :
    (newRegionBuckets rm cg p groups labelWidths x).members.getD g [] =
      if g < rm.clusters.length + 1 then
        (p.nodes.zipIdx.filter (gp_bucket_member groups g)).map Prod.snd else [] := by
  let empty : RegionBuckets :=
    ⟨List.replicate (rm.clusters.length + 1) [], List.replicate (rm.clusters.length + 1) 0,
      List.replicate (rm.clusters.length + 1) 2147483647,
      List.replicate (rm.clusters.length + 1) (-2147483648),
      List.replicate (rm.clusters.length + 1) [], List.replicate (rm.clusters.length + 1) 0,
      List.replicate (rm.clusters.length + 1) 0⟩
  let gather (acc : RegionBuckets) (q : ProperNode × Nat) : RegionBuckets :=
    if q.1.node.border != 0 then acc else
      let owner := groups.getD q.2 0
      let width := q.1.node.w + 2 * (q.1.node.loopExtent : Int)
      let left := RouteImpl.xAt x q.2 - Int.tdiv width 2
      let right := left + width
      { acc with
        low := setAt acc.low owner (min (acc.low.getD owner 2147483647) left)
        high := setAt acc.high owner (max (acc.high.getD owner (-2147483648)) right)
        members := setAt acc.members owner (acc.members.getD owner [] ++ [q.2]) }
  let addLane (acc : RegionBuckets) (q : Edge × Nat) : RegionBuckets :=
    if !q.1.reversed || q.1.tail == q.1.head then acc else
      let root := rm.clusters.length
      let owner := edgeOwnerOf rm groups root q.1.tail q.1.head
      if owner == root then acc else
        { acc with
          lanes := setAt acc.lanes owner (acc.lanes.getD owner [] ++ [q.2])
          laneWidth := setAt acc.laneWidth owner
            (max (acc.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }
  change ((cg.edges.zipIdx.foldl addLane (p.nodes.zipIdx.foldl gather empty)).members).getD g [] = _
  have laneMembers (jobs : List (Edge × Nat)) (acc : RegionBuckets) :
      (jobs.foldl addLane acc).members = acc.members := by
    induction jobs generalizing acc with
    | nil => rfl
    | cons q qs ih =>
      rw [List.foldl_cons, ih]
      dsimp only [addLane]
      split
      · rfl
      · split <;> rfl
  have gatheredMembers (jobs : List (ProperNode × Nat)) (acc : RegionBuckets) :
      (jobs.foldl gather acc).members = jobs.foldl (gp_gather_members groups) acc.members := by
    induction jobs generalizing acc with
    | nil => rfl
    | cons q qs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      have heq : (gather acc q).members = gp_gather_members groups acc.members q := by
        dsimp only [gather, gp_gather_members]
        split <;> rfl
      rw [heq]
  rw [laneMembers, gatheredMembers, gp_gather_members_lookup]
  have hn : (List.replicate (rm.clusters.length + 1) ([] : List Nat)).getD g [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  simp only [empty, hn, List.length_replicate, List.nil_append]

private theorem gp_bucket_count (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (groups : List Nat) (labelWidths x : List Int) (g v owner : Nat) (hb : owner ≤ rm.clusters.length)
    {n : ProperNode} (hv : p.nodes[v]? = some n) (hp : n.node.border = 0)
    (howner : groups[v]? = some owner) :
    ((newRegionBuckets rm cg p groups labelWidths x).members.getD g []).count v =
      if g = owner then 1 else 0 := by
  rw [gp_bucket_members]
  by_cases hg : g < rm.clusters.length + 1
  · rw [ite_eq_left hg]
    have hmem : v ∈ (p.nodes.zipIdx.filter (gp_bucket_member groups g)).map Prod.snd ↔
        g = owner := by
      constructor
      · intro h
        obtain ⟨⟨m, k⟩, hq, hk⟩ := List.mem_map.mp h
        change k = v at hk
        subst k
        have htest : (m.node.border == 0 && groups.getD v 0 == g) = true :=
          (List.mem_filter.mp hq).2
        have heq := beq_iff_eq.mp (Bool.and_eq_true_iff.mp htest).2
        simpa only [List.getD_eq_getElem?_getD, howner, Option.getD_some] using heq.symm
      · intro h
        subst g
        exact List.mem_map.mpr ⟨(n, v), List.mem_filter.mpr
          ⟨List.mem_zipIdx_iff_getElem?.mpr hv, by
            simp [gp_bucket_member, hp, List.getD_eq_getElem?_getD, howner]⟩, rfl⟩
    by_cases he : g = owner
    · rw [ite_eq_left he]
      have hnd : (p.nodes.zipIdx.map Prod.snd).Nodup := by
        rw [List.zipIdx_map_snd]
        exact List.nodup_range'
      have hsub := (List.filter_sublist (p := gp_bucket_member groups g)
        (l := p.nodes.zipIdx)).map Prod.snd
      exact (hsub.nodup hnd).count_of_mem (hmem.mpr he)
    · rw [ite_eq_right he]
      exact List.count_eq_zero_of_not_mem (fun h => he (hmem.mp h))
  · have hne : g ≠ owner := by omega
    simp [hg, hne]

private theorem gp_sum_other_visits (jobs : List (Nat × Int)) (owner : Nat)
    (h : owner ∉ jobs.map Prod.fst) :
    (jobs.map (fun q => if q.1 = owner then q.2 else 0)).sum = 0 := by
  induction jobs with
  | nil => rfl
  | cons q qs ih =>
    have hne : q.1 ≠ owner := fun he => h (he ▸ List.mem_cons_self)
    have ht : owner ∉ qs.map Prod.fst := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, List.sum_cons, ite_eq_right hne, ih ht, Int.zero_add]

theorem groupPlain_shifted_center {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum)
    {v owner : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n) (hp : n.node.border = 0)
    (howner : stages.groups[v]? = some owner) (hb : owner ≤ rm.clusters.length) :
    v ∈ stages.placement.buckets.members.getD owner [] ∧
    stages.shifted.getD v 0 = stages.before.getD v 0 +
      groupPlain_bucketLeft stages.placement P stages.allocation owner -
        stages.placement.buckets.low.getD owner 0 := by
  let pl := stages.placement
  have hcount (g : Nat) : (pl.buckets.members.getD g []).count v = if g = owner then 1 else 0 := by
    change (stages.placement.buckets.members.getD g []).count v = _
    rw [stages.hPlacement]
    exact gp_bucket_count rm cg p stages.groups _ stages.before g v owner hb hn hp howner
  have hm : v ∈ pl.buckets.members.getD owner [] := by
    apply List.count_pos_iff.mp
    rw [hcount, ite_eq_left rfl]
    exact Nat.zero_lt_succ 0
  obtain ⟨hnd, hordered, hnoself, hmembers⟩ := stages.allocation_topology hparents hmin
  obtain ⟨visits, horder, hvisit, _, htrace⟩ := allocatePl_translation_trace stages.hAllocation
  have hmem : owner ∈ visits.map Prod.fst := horder.symm ▸ hmembers owner hb
  obtain ⟨⟨g, dx⟩, hq, he⟩ := List.mem_map.mp hmem
  change g = owner at he
  subst g
  obtain ⟨pre, post, hviews⟩ := List.mem_iff_append.mp hq
  have ho : pl.order = pre.map Prod.fst ++ owner :: post.map Prod.fst := by
    rw [← horder, hviews, List.map_append, List.map_cons]
  have hidx : visits[pre.length]? = some (owner, dx) := by
    rw [hviews, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨before, hbefore, hshift⟩ := hvisit pre.length owner dx hidx
  have htake : pl.order.take pre.length = pre.map Prod.fst := by
    rw [ho]
    exact List.take_left' (List.length_map Prod.fst)
  rw [htake] at hbefore
  have hav : ∀ g ∈ owner :: post.map Prod.fst, owner ∉ pl.children.getD g [] := by
    rw [ho] at hordered
    have htail := (List.pairwise_cons.mp (List.pairwise_append.mp hordered).2.1).1
    intro g hg
    rcases List.mem_cons.mp hg with hself | hpost
    · rw [hself]
      exact hnoself owner
    · exact htail g hpost
  have halloc := stages.hAllocation
  unfold allocatePl at halloc
  obtain ⟨final, hfold, hfinal⟩ := gp_bind_ok halloc
  have hleft : final.2.1 = stages.allocation.lefts :=
    congrArg (fun q : RegionAllocation × List Int => q.1.lefts) (Except.ok.inj hfinal)
  change pl.order.foldlM (fun acc g => allocateGroup pl P (reserveWidths pl P) g acc)
    (stages.before, List.replicate (pl.rm.clusters.length + 1) 0,
      List.replicate pl.p.chains.length none) = Except.ok final at hfold
  rw [ho, List.foldlM_append] at hfold
  obtain ⟨prefixState, hprefix, hsuffix⟩ := gp_bind_ok hfold
  have hsame : prefixState = before := Except.ok.inj (hprefix.symm.trans hbefore)
  rw [hsame] at hsuffix
  have hread := gp_allocation_left_stays hav hsuffix
  rw [hleft] at hread
  have hbound : v < stages.before.length := by
    rw [CoordsImpl.crossCoordsClusterWith_length stages.hCross]
    exact (List.getElem?_eq_some_iff.mp hn).1
  have hf : stages.shifted.getD v 0 = stages.before.getD v 0 +
      (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2).sum :=
    htrace v hbound
  have hs : (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2).sum = dx := by
    have heq : (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2) =
        visits.map (fun q => if q.1 = owner then q.2 else 0) := by
      apply List.map_congr_left
      intro q _
      rw [hcount]
      by_cases hqOwner : q.1 = owner <;> simp [hqOwner]
    rw [heq, hviews, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [ho] at hnd
    obtain ⟨_, hpost, hcross⟩ := List.nodup_append.mp hnd
    have hp' : owner ∉ pre.map Prod.fst := fun hx => hcross owner hx owner List.mem_cons_self rfl
    have ht' := (List.nodup_cons.mp hpost).1
    simp only [gp_sum_other_visits pre owner hp', gp_sum_other_visits post owner ht',
      ite_true, Int.add_zero, Int.zero_add]
  have hinset : (if owner != pl.rm.clusters.length then pl.minimum.origins.getD owner 0 else 0) =
      (if owner = pl.rm.clusters.length then 0 else regionInsetOf P) := by
    rw [show pl = stages.placement from rfl, stages.hPlacement]
    change (if owner != rm.clusters.length then minimum.origins.getD owner 0 else 0) = _
    by_cases he : owner = rm.clusters.length
    · simp [he]
    · have hlt := Nat.lt_of_le_of_ne hb he
      rw [ite_eq_left (bne_iff_ne.mpr he), ite_eq_right he, constrainR_origins hmin, hparents,
        List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hlt, Option.getD_some]
  have hdx : dx = groupPlain_bucketLeft pl P stages.allocation owner -
      pl.buckets.low.getD owner 0 := by
    change dx = regionBucketShift pl before.2.1 owner at hshift
    rw [regionBucketShift, ← hread, hinset] at hshift
    exact hshift
  refine ⟨hm, ?_⟩
  rw [hs, hdx] at hf
  exact hf.trans (Int.add_sub_assoc _ _ _).symm

private theorem gp_plain_run_record {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {ranks : List Int} {budget : Bool}
    {normalized labeled p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp candidate labels orderOptions = .ok (cg, run))
    (hrank : rankEquivalentR rm candidate = .ok (ranks, cg, budget))
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hrows : rm.clusters = clusterRows inp s candidate)
    {v : Nat} {original : Node} (hv : cg.nodes[v]? = some original)
    (hplain : original.border = 0) :
    ∃ n : ProperNode, p.nodes[v]? = some n ∧ n.node.border = 0 ∧
      n.node.clusterPath = original.clusterPath ∧ run.proper.nodes[v]? = some n ∧
      run.xs.getD v 0 = stages.shifted.getD v 0 := by
  have sourceRecord {k : Nat} {raw : Node} (hk : cg.nodes[k]? = some raw) :
      ∃ n : ProperNode, p.nodes[k]? = some n ∧ n.node.border = raw.border ∧
        n.node.clusterPath = raw.clusterPath := by
    have hl := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hk) rfl
    obtain ⟨n, hn, hb, hp⟩ := gp_active_original_keys P exact s hl rfl
    rw [hcoord] at hn
    exact ⟨n, hn, hb, hp⟩
  obtain ⟨n, hn, hb, hp⟩ := sourceRecord hv
  have hpn := hb.trans hplain
  have hpp : stages.placement.p = p := by rw [stages.hPlacement]
  have hrm : stages.placement.rm = rm := by rw [stages.hPlacement]
  have hn' : stages.placement.p.nodes[v]? = some n := by rwa [hpp]
  have haway : ∀ c ∈ stages.placement.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v := by
    intro c hc
    rw [hrm] at hc
    obtain ⟨top, bottom, ht, htop, _, _, hbot, hbottom⟩ := gp_cluster_anchors hrows hc
    have avoid {k : Nat} {raw : Node} (hk : candidate.nodes[k]? = some raw)
        (hborder : raw.border ≠ 0) : k ≠ v := by
      rw [← rankEquivalentR_nodes_eq hrank] at hk
      intro he
      rw [he, hv] at hk
      have heq := Option.some.inj hk
      exact hborder (heq ▸ hplain)
    exact ⟨avoid ht (by rw [htop]; decide),
      avoid hbot (by rcases hbottom with h | h <;> rw [h] <;> decide)⟩
  obtain ⟨post, hpost, _, hstay⟩ := (groupPlain_reservedPorts_record stages.hFramesAndPorts).2 hn'
  obtain ⟨he, hxPorts⟩ := hstay haway
  subst post
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, actual⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [actual.hCoordProper]
    exact actual.hProxy
  have hnp : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by simp [hpn]
  obtain ⟨hout, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v n hpost hnp
  have hfinal : run.proper.nodes[v]? = some n := by
    rwa [← actual.hDrop, OrderImpl.dropSynthetic_nodes]
  have hframe := gp_regionFrames_plain hn' hpn haway
    (P := P) (allocation := stages.allocation) (xs := stages.shifted)
  refine ⟨n, hn, hpn, hp, hfinal, ?_⟩
  rw [List.getD_eq_getElem?_getD, hx, Option.getD_some, hxPorts]
  exact hframe

private theorem gp_rooted_resolve_bound {pl : RegionPlacement} {rm : ComponentRegions}
    (hchildren : ∀ a b, b ∈ pl.children.getD a [] → b < rm.clusters.length)
    {path : List Nat} {owner d : Nat}
    (hp : GroupPlainRootedPath pl (gp_resolve rm) owner path) (hd : d ∈ path) :
    gp_resolve rm d < rm.clusters.length := by
  induction path generalizing owner with
  | nil => cases hd
  | cons c cs ih =>
    change gp_resolve rm c ∈ pl.children.getD owner [] ∧
      GroupPlainRootedPath pl (gp_resolve rm) (gp_resolve rm c) cs at hp
    rcases List.mem_cons.mp hd with he | ht
    · rw [he]
      exact hchildren owner _ hp.1
    · exact ih hp.2 ht

private theorem gp_resolve_injective {rm : ComponentRegions} {a b : Nat}
    (ha : gp_resolve rm a < rm.clusters.length)
    (he : gp_resolve rm a = gp_resolve rm b) : a = b := by
  unfold gp_resolve at ha he
  cases hA : clusterOfDecl rm a with
  | none => simp [hA] at ha
  | some i =>
    cases hB : clusterOfDecl rm b with
    | none => simp [hA, hB] at ha he; omega
    | some j =>
      simp only [hA, hB, Option.getD_some] at he
      subst j
      have htestA := (List.findIdx?_eq_some_iff_getElem.mp hA).2.1
      have htestB := (List.findIdx?_eq_some_iff_getElem.mp hB).2.1
      exact (beq_iff_eq.mp htestA).symm.trans (beq_iff_eq.mp htestB)

private theorem gp_plain_rooted {inp : Input} {o : Options} {rm : ComponentRegions}
    {pl : RegionPlacement}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hrooted : ∀ {i : Nat} {c : RegionCluster} {src : ModelBox},
      rm.clusters[i]? = some c → inp.boxes[c.decl]? = some src →
      GroupPlainRootedPath pl (gp_resolve rm) rm.clusters.length
        (Compound.path inp.boxes src ++ [c.decl]))
    {k owner : Nat} {source : ModelBox} (hsrc : inp.boxes[k]? = some source)
    (howner : match (Compound.path inp.boxes source).getLast? with
      | none => owner = rm.clusters.length
      | some d => clusterOfDecl rm d = some owner) :
    GroupPlainRootedPath pl (gp_resolve rm) rm.clusters.length (Compound.path inp.boxes source) ∧
      ((Compound.path inp.boxes source).map (gp_resolve rm)).getLast?.getD rm.clusters.length =
        owner ∧
      ((Compound.path inp.boxes source) = [] ∨ owner < rm.clusters.length) := by
  by_cases hroot : source.parent = ""
  · have hnil : Compound.path inp.boxes source = [] := by
      unfold Compound.path
      rw [hroot]
      cases inp.boxes.length <;> rfl
    rw [hnil] at howner ⊢
    exact ⟨trivial, howner.symm, Or.inl rfl⟩
  · obtain ⟨parent, hm, hid, _, _⟩ :=
      framedParents_parent hframed (List.mem_of_getElem? hsrc) hroot
    obtain ⟨pid, hpid⟩ := List.mem_iff_getElem?.mp hm
    have hp := Compound.path_of_parent (inputModel inp o) hwf hpid hsrc hid.symm hroot
    change Compound.path inp.boxes source = Compound.path inp.boxes parent ++ [pid] at hp
    have hlast : (Compound.path inp.boxes source).getLast? = some pid := by
      rw [hp, List.getLast?_append]
      simp
    rw [hlast] at howner
    change clusterOfDecl rm pid = some owner at howner
    obtain ⟨hlt, hkey, _⟩ := List.findIdx?_eq_some_iff_getElem.mp howner
    let c := rm.clusters[owner]
    have hc : rm.clusters[owner]? = some c := List.getElem?_eq_getElem hlt
    have hdecl : c.decl = pid := beq_iff_eq.mp hkey
    have hparentLookup : inp.boxes[c.decl]? = some parent := by rwa [hdecl]
    have hr := hrooted hc hparentLookup
    rw [hdecl, ← hp] at hr
    exact ⟨hr, by simp only [List.getLast?_map, hlast, Option.map_some, Option.getD_some,
      gp_resolve, howner], Or.inr hlt⟩

private theorem gp_real_trail_bounds {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {base target : Nat}
    (htrail : GroupPlainAllocatedTrail pl base target) (hbase : base < pl.rm.clusters.length)
    (hinset : 0 ≤ regionInsetOf P) (hown : ∀ g, 0 ≤ pl.buckets.widths.getD g 0)
    (hwidths : ∀ c, 0 ≤ alloc.widths.getD c 0)
    (hchildren : ∀ a b, b ∈ pl.children.getD a [] → b < pl.rm.clusters.length)
    (hleft : ∀ {g i child}, g ≤ pl.rm.clusters.length → (pl.children.getD g [])[i]? = some child →
      groupPlain_allocLeft alloc child =
        groupPlain_bucketRight pl P alloc g +
          (((pl.children.getD g []).take i).map fun c => alloc.widths.getD c 0).sum)
    (hroom : ∀ g < pl.rm.clusters.length, regionInsetOf P + pl.buckets.widths.getD g 0 +
      ((pl.children.getD g []).map fun c => alloc.widths.getD c 0).sum ≤ alloc.widths.getD g 0) :
    groupPlain_allocLeft alloc base ≤ groupPlain_allocLeft alloc target ∧
      groupPlain_allocRight alloc target ≤ groupPlain_allocRight alloc base := by
  induction htrail with
  | here g => exact ⟨Int.le_refl _, Int.le_refl _⟩
  | @down parent child target hedge _ ih =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hedge
    obtain ⟨hlo, hhi⟩ := groupPlain_child_slot_bounds hi hinset (hown parent) hwidths
      (hleft (Nat.le_of_lt hbase) hi)
      (by rw [ite_eq_right (Nat.ne_of_lt hbase)]; exact hroom parent hbase)
    obtain ⟨htlo, hthi⟩ := ih (hchildren parent child hedge)
    exact ⟨Int.le_trans hlo htlo, Int.le_trans hthi hhi⟩

private theorem gp_path_last_not_root {pl : RegionPlacement}
    (hchildren : ∀ a b, b ∈ pl.children.getD a [] → b < pl.rm.clusters.length)
    {branch target : Nat} (hb : branch < pl.rm.clusters.length)
    (ht : GroupPlainAllocatedTrail pl branch target) : target < pl.rm.clusters.length := by
  induction ht with
  | here => exact hb
  | @down g child target hedge _ ih => exact ih (hchildren g child hedge)

theorem RegionCrossAllocationStages.active_title_interval
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {spec : RegionSpec} {candidate : Nat} {cg : Graph} {run : Run}
    {rm : ComponentRegions} {ranks : List Int} {budget : Bool}
    {normalized labeled p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages e.params rm cg e.measured p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some spec) inp
      (componentCandidateR (some spec) e.graph comp candidate) e.measured
      (candidateOrder candidate) = .ok (cg, run))
    (hregions : newComponentRegions (some spec) e.params inp
      (componentCandidateR (some spec) e.graph comp candidate) = .ok (some rm))
    (hrank : rankEquivalentR rm (componentCandidateR (some spec) e.graph comp candidate) =
      .ok (ranks, cg, budget))
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg e.measured) = .ok labeled)
    (hcoord : coordinateGraphR e.params (exactDecls exactIds inp) (some spec) labeled = p)
    (hmin : constrainR rm e.params p = .ok minimum)
    {owner u : Nat} {cluster : RegionCluster} {gn : Node} {r : Rect}
    (howner : rm.clusters[owner]? = some cluster)
    (hg : cg.nodes[u]? = some gn) (hpath : gn.clusterPath.getLast? = some cluster.decl)
    (hwidth : cluster.titleW = gn.w)
    (hspan : 0 ≤ stages.allocation.widths.getD owner 0 -
      stages.placement.buckets.loopWidth.getD owner 0)
    (hr : (u, r) ∈ componentTitles e.params cg run) :
    stages.allocation.lefts.getD owner 0 ≤ r.x ∧
      r.x + r.w ≤ stages.allocation.lefts.getD owner 0 +
        stages.allocation.widths.getD owner 0 - stages.placement.buckets.loopWidth.getD owner 0 := by
  unfold componentTitles at hr
  obtain ⟨top, ht, hemit⟩ := List.mem_filterMap.mp hr
  dsimp only at hemit
  split at hemit
  · cases hemit
  cases hfind : run.proper.nodes.zipIdx.find?
      (fun q => q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
  | none => simp [hfind] at hemit
  | some title =>
    simp [hfind] at hemit
    obtain ⟨hpos, hrect⟩ := hemit
    have htLookup := List.mem_zipIdx_iff_getElem?.mp ht
    rw [hpos, hg] at htLookup
    have htNode := (Option.some.inj htLookup).symm
    have htest : (title.1.node.border == 3 &&
        title.1.node.clusterPath == top.1.clusterPath) = true :=
      List.find?_some
        (p := fun q : ProperNode × Nat =>
          q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
        (l := run.proper.nodes.zipIdx) (a := title) hfind
    have htests : title.1.node.border = 3 ∧ title.1.node.clusterPath = gn.clusterPath := by
      rw [htNode] at htest
      simpa only [Bool.and_eq_true, beq_iff_eq] using htest
    have hlast : title.1.node.clusterPath.getLast? = some cluster.decl := by
      rwa [htests.2]
    have htitle := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
    obtain ⟨hW, hX⟩ := stages.activeChild_title_center e.graph0_eq e.graph_eq hcomp
      hrun hregions hrank hnorm hlabels hcoord howner htitle htests.1 hlast
    obtain ⟨_, _, ho, hf, _⟩ := (stages.reservation_order
      (activeRegion_parent_count hregions) hmin).2 owner
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp howner).1)
    have hc : stages.placement.rm.clusters[owner]? = some cluster := by
      rwa [stages.hPlacement]
    have hfoot := reserveWidths_title_from_last_write (P := e.params) hc ho hf
    rw [← groupPlain_allocation_width_eq stages.hAllocation, hwidth] at hfoot
    have hpad := (checkedParams_sizing_nonneg e.checked).2.1
    have hborder := checkedParams_clusterBorderW_ge_one e.checked
    have hinset : 0 ≤ regionInsetOf e.params := by unfold regionInsetOf; omega
    rw [← hrect]
    change _ ≤ run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2 ∧
      run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2 + top.1.w ≤ _
    rw [hX, hW, hwidth, htNode, Int.tdiv_eq_ediv_of_nonneg hspan,
      Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega

theorem active_group_plain_slot_geometry
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} {spec : RegionSpec} {candidate : Nat}
    {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some spec) inp
      (componentCandidateR (some spec) e.graph comp candidate)
      e.measured (candidateOrder candidate) = .ok (cg, run))
    (hregions : newComponentRegions (some spec) e.params inp
      (componentCandidateR (some spec) e.graph comp candidate) = .ok (some rm))
    {u w : Nat} {gn pn : Node} {groupSource plainSource : ModelBox}
    (hg : cg.nodes[u]? = some gn) (hp : cg.nodes[w]? = some pn)
    (hgroup : gn.border = -2) (hplain : pn.border = 0)
    (hgPos : comp[u]? = some gn.decl) (hpPos : comp[w]? = some pn.decl)
    (hgSrc : inp.boxes[gn.decl]? = some groupSource)
    (hpSrc : inp.boxes[pn.decl]? = some plainSource)
    (hforeign : pn.clusterPath.contains gn.decl = false) :
    ∃ lo hi : Int, 0 ≤ hi ∧
      (∀ r ∈ groupBorderRects cg run gn.decl, lo ≤ r.x ∧ r.x + r.w ≤ hi) ∧
      (∀ r : Rect, (u, r) ∈ componentTitles e.params cg run →
        lo ≤ r.x ∧ r.x + r.w ≤ hi) ∧
      (hi ≤ (frameRect e.params cg run w).x ∨
        (frameRect e.params cg run w).x + (frameRect e.params cg run w).w ≤ lo) := by
  obtain ⟨_, _, _, p, minimum, _, _, _, hrank, hnorm, hlabels, hCoord, hmin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hregions
  obtain ⟨hrows, hparentsTable⟩ := gp_resolved_tables hregions
  obtain ⟨hnd, hsources⟩ := gp_candidate_cluster_sources e hcomp hrows
  have hparents := activeRegion_parent_count hregions
  have hnodes := rankEquivalentR_nodes_eq hrank
  have hgCand := hg
  have hpCand := hp
  rw [hnodes] at hgCand hpCand
  have global {pos : Nat} {node : Node}
      (hnode : (componentCandidateR (some spec) e.graph comp candidate).nodes[pos]? = some node)
      (hpos : comp[pos]? = some node.decl) :
      e.graph.nodes[node.decl]? = some node := by
    obtain ⟨key, hkey, hsource⟩ := gp_component_member_node hcomp hnode
    rw [hpos] at hkey
    have he : node.decl = key := Option.some.inj hkey
    rw [he]
    exact hsource
  have hgPath := (gp_selected_source_path e (global hgCand hgPos) hgSrc).1 hgroup
  have hpPath := (gp_selected_source_path e (global hpCand hpPos) hpSrc).2 hplain
  have hfork := groupPlain_foreign_owner_fork hgPath hpPath hforeign
  let pl := stages.placement
  let a := stages.allocation
  have hplRm : pl.rm = rm := by rw [show pl = stages.placement from rfl, stages.hPlacement]
  have hplP : pl.p = p := by rw [show pl = stages.placement from rfl, stages.hPlacement]
  have hcounts := stages.group_paths hparents hmin
  have hrooted {i : Nat} {c : RegionCluster} {src : ModelBox}
      (hc : rm.clusters[i]? = some c) (hs : inp.boxes[c.decl]? = some src) :
      GroupPlainRootedPath pl (gp_resolve rm) rm.clusters.length
        (Compound.path inp.boxes src ++ [c.decl]) :=
    gp_cluster_rooted e hwf hframed hcomp hrows hparentsTable hnd hsources hcounts.1
      (hcounts.2 i (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hc).1)) hc hs
  obtain ⟨cluster, hcluster, hgDecl, hgWidth⟩ := gp_cluster_of_top hrows hgCand hgroup
  obtain ⟨groupOwner, hgroupOwner⟩ := List.mem_iff_getElem?.mp hcluster
  have hgRooted : GroupPlainRootedPath pl (gp_resolve rm) pl.rm.clusters.length gn.clusterPath := by
    rw [hplRm, hgPath, ← hgDecl]
    exact hrooted hgroupOwner (by rwa [hgDecl])
  have hgOwnerEnd : ((gn.clusterPath.map (gp_resolve rm)).getLast?).getD pl.rm.clusters.length =
      groupOwner := by
    rw [hgPath, ← hgDecl, List.getLast?_map, List.getLast?_append]
    simp only [List.getLast?_singleton, Option.some_or, Option.map_some, Option.getD_some,
      gp_resolve, gp_decl_index hnd hgroupOwner]
  obtain ⟨plain, hplainCoord, hplainKind, hplainPath, hplainFinal, hplainX⟩ :=
    gp_plain_run_record hrun hrank hnorm hlabels hCoord stages hrows hp hplain
  obtain ⟨plainOwner, hplainOwner, hplainBound, hplainRule⟩ :=
    groupPlain_nodeGroups_lookup stages.hGroups hplainCoord
  rw [hplainPath, hpPath] at hplainRule
  obtain ⟨hPlainRoot, hPlainLast, _⟩ := gp_plain_rooted hwf hframed hrooted hpSrc hplainRule
  have hpRooted : GroupPlainRootedPath pl (gp_resolve rm) pl.rm.clusters.length pn.clusterPath :=
    by rw [hplRm, hpPath]; exact hPlainRoot
  have hpOwnerEnd : ((pn.clusterPath.map (gp_resolve rm)).getLast?).getD pl.rm.clusters.length =
      plainOwner := by rwa [hplRm, hpPath]
  have hinjective : ∀ d ∈ gn.clusterPath, ∀ q ∈ pn.clusterPath,
      gp_resolve rm d = gp_resolve rm q → d = q := by
    intro d hd q _ he
    exact gp_resolve_injective (gp_rooted_resolve_bound
      (fun a b hb => (hcounts.1 a b hb).1) hgRooted hd) he
  obtain ⟨owner, groupBranch, hgroupChild, hgroupTrail, hbranches⟩ :=
    groupPlain_common_path_branches hfork hgRooted hpRooted hinjective
  rw [hgOwnerEnd] at hgroupTrail
  rw [hpOwnerEnd] at hbranches
  have hchildren : ∀ u v, v ∈ pl.children.getD u [] → v < pl.rm.clusters.length := by
    intro u v hv
    rw [hplRm]
    exact (hcounts.1 u v hv).1
  have hownerBound : owner ≤ pl.rm.clusters.length := by
    obtain ⟨hcBound, hparent⟩ := hcounts.1 owner groupBranch hgroupChild
    let c := rm.clusters[groupBranch]
    have hc : rm.clusters[groupBranch]? = some c := List.getElem?_eq_getElem hcBound
    obtain ⟨src, _, hsrc, _, _, _⟩ := hsources c (List.mem_of_getElem? hc)
    rw [← hparent, hplRm, gp_parentGroup_table hparentsTable hc hsrc]
    split
    · exact Nat.le_refl _
    · cases hh : rm.clusters.findIdx? (fun row => row.id == src.parent) with
      | none => exact Nat.le_refl _
      | some index => exact Nat.le_of_lt (List.findIdx?_eq_some_iff_getElem.mp hh).1
  have hpad := (checkedParams_sizing_nonneg e.checked).2.1
  have hBW := checkedParams_clusterBorderW_ge_one e.checked
  have hb0 : 0 ≤ e.params.clusterBorderW := by omega
  have hinset : 0 ≤ regionInsetOf e.params := by unfold regionInsetOf; omega
  obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun stages
  have hrawWidths := reserveWidths_nonnegative hinset hown hlane hloop
  have heWidths := groupPlain_allocation_width_eq stages.hAllocation
  have hwidths : ∀ i, 0 ≤ a.widths.getD i 0 := by
    intro i
    change 0 ≤ stages.allocation.widths.getD i 0
    rw [heWidths]
    exact hrawWidths i
  have horigin (i : Nat) : 0 ≤ pl.minimum.origins.getD i 0 := by
    rw [show pl = stages.placement from rfl, stages.hPlacement]
    change 0 ≤ minimum.origins.getD i 0
    rw [constrainR_origins hmin, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split
    · exact hinset
    · exact Int.le_refl _
  have hlefts : ∀ i, 0 ≤ groupPlain_allocLeft a i :=
    groupPlain_allocation_lefts_nonneg stages.hAllocation horigin hown hrawWidths
  have hleft {i j child : Nat} (hi : i ≤ pl.rm.clusters.length)
      (hc : (pl.children.getD i [])[j]? = some child) :
      groupPlain_allocLeft a child = groupPlain_bucketRight pl e.params a i +
        (((pl.children.getD i []).take j).map fun k => a.widths.getD k 0).sum := by
    have hi' : i ≤ rm.clusters.length := by simpa only [hplRm] using hi
    have h := stages.childBudget_left_from_allocation hregions hmin hi' hc
    simpa only [groupPlain_allocLeft, groupPlain_bucketRight, groupPlain_bucketLeft,
      a, heWidths, hplRm] using h
  have hroom (i : Nat) (hi : i < pl.rm.clusters.length) :
      2 * regionInsetOf e.params + pl.buckets.widths.getD i 0 +
        ((pl.children.getD i []).map fun j => a.widths.getD j 0).sum ≤
        a.widths.getD i 0 - pl.buckets.loopWidth.getD i 0 := by
    have hi' : i ≤ rm.clusters.length := Nat.le_of_lt (by simpa only [hplRm] using hi)
    obtain ⟨_, _, horder, hfinal, hstable⟩ := (stages.reservation_order hparents hmin).2 i hi'
    change 2 * regionInsetOf e.params + stages.placement.buckets.widths.getD i 0 +
      ((stages.placement.children.getD i []).map fun j => stages.allocation.widths.getD j 0).sum ≤
      stages.allocation.widths.getD i 0 - stages.placement.buckets.loopWidth.getD i 0
    rw [heWidths]
    exact Int.le_trans (Int.le_add_of_nonneg_right (hlane i))
      (reserveWidths_room_from_last_writes (pl := stages.placement) (P := e.params)
        horder hi hfinal hstable)
  have hslot (i : Nat) (hi : i < pl.rm.clusters.length) :
      regionInsetOf e.params + pl.buckets.widths.getD i 0 +
        ((pl.children.getD i []).map fun j => a.widths.getD j 0).sum ≤ a.widths.getD i 0 := by
    have hr := hroom i hi
    have hl : 0 ≤ pl.buckets.loopWidth.getD i 0 := hloop i
    omega
  have hgroupBound : groupOwner < pl.rm.clusters.length := by
    rw [hplRm]
    exact (List.getElem?_eq_some_iff.mp hgroupOwner).1
  have hgroupRoom : e.params.clusterBorderW ≤
      a.widths.getD groupOwner 0 - pl.buckets.loopWidth.getD groupOwner 0 := by
    have hr := hroom groupOwner hgroupBound
    have ho : 0 ≤ pl.buckets.widths.getD groupOwner 0 := hown groupOwner
    have hs := gp_sum_nonneg (fun j => a.widths.getD j 0) hwidths
      (pl.children.getD groupOwner [])
    unfold regionInsetOf at hr
    omega
  have hmarkerBounds := groupPlain_group_slot_of_markers (cg := cg)
    (run := run) (decl := gn.decl) (pl := pl) (alloc := a) (owner := groupOwner)
    hb0 (hloop groupOwner) hgroupRoom (by
      intro rect hm
      obtain ⟨i, side, hi, hb, hlast, rfl⟩ := groupBorderRects_inv hm
      have hlast' := hlast.trans (congrArg some hgDecl.symm)
      obtain ⟨hwidth, hx⟩ := stages.activeChild_side_centers e.graph0_eq e.graph_eq hcomp
        hrun hregions hrank hnorm hlabels hCoord hgroupOwner hi hb hlast'
      rw [← heWidths] at hx
      change RouteImpl.nodeW run.proper i = e.params.clusterBorderW ∧ _
      have hW : RouteImpl.nodeW run.proper i = e.params.clusterBorderW := by
        rw [RouteImpl.nodeW, hi]
        exact hwidth
      refine ⟨hW, ?_⟩
      change run.xs.getD i 0 - Int.fdiv (RouteImpl.nodeW run.proper i) 2 = _ ∨
        run.xs.getD i 0 - Int.fdiv (RouteImpl.nodeW run.proper i) 2 = _
      rw [hW, hx]
      unfold groupPlain_allocLeft groupPlain_allocRight
      rcases hb with h | h
      · exact Or.inl (by rw [h, ite_eq_left (Eq.refl (-1 : Int))])
      · exact Or.inr (by rw [h, ite_eq_right (by decide : (1 : Int) ≠ -1), groupPlain_allocLeft])
    )
  have htitleBounds (r : Rect) (hr : (u, r) ∈ componentTitles e.params cg run) :
      groupPlain_allocLeft a groupOwner ≤ r.x ∧
        r.x + r.w ≤ groupPlain_allocRight a groupOwner := by
    have hlast : gn.clusterPath.getLast? = some cluster.decl := by simp [hgPath, hgDecl]
    have hspan : 0 ≤ a.widths.getD groupOwner 0 - pl.buckets.loopWidth.getD groupOwner 0 :=
      Int.le_trans hb0 hgroupRoom
    obtain ⟨hlo, hhi⟩ := stages.active_title_interval e hcomp hrun hregions hrank hnorm hlabels
      hCoord hmin hgroupOwner hg hlast hgWidth hspan hr
    refine ⟨hlo, ?_⟩
    have hLoop : 0 ≤ pl.buckets.loopWidth.getD groupOwner 0 := hloop groupOwner
    change r.x + r.w ≤ a.lefts.getD groupOwner 0 + a.widths.getD groupOwner 0
    change r.x + r.w ≤ a.lefts.getD groupOwner 0 + a.widths.getD groupOwner 0 -
      pl.buckets.loopWidth.getD groupOwner 0 at hhi
    omega
  obtain ⟨hpMem, hpShift⟩ := groupPlain_shifted_center stages hparents hmin hplainCoord
    hplainKind hplainOwner hplainBound
  have hplainBounds := groupPlain_plainRect_of_bucket_shift stages hplain hp
    (show pl.p.nodes[w]? = some plain by rwa [hplP]) hplainFinal hpMem
    (hplainX.trans hpShift)
  obtain ⟨glo, ghi⟩ := gp_real_trail_bounds hgroupTrail (hchildren owner groupBranch hgroupChild)
    hinset hown hwidths hchildren (fun hi hj => hleft hi hj) hslot
  refine ⟨groupPlain_allocLeft a groupOwner, groupPlain_allocRight a groupOwner,
    Int.add_nonneg (hlefts groupOwner) (hwidths groupOwner), hmarkerBounds, htitleBounds, ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hgroupChild
  rcases hbranches with he | ⟨branch, hbranch, hne, htrail⟩
  · have hbefore := groupPlain_bucket_before_child hwidths (hleft hownerBound hi)
    rw [he] at hplainBounds
    exact Or.inr (Int.le_trans hplainBounds.2 (Int.le_trans hbefore glo))
  · have hb := hchildren owner branch hbranch
    have hPlainBound := gp_path_last_not_root hchildren hb htrail
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbranch
    obtain ⟨plo, phi⟩ := gp_real_trail_bounds htrail hb hinset hown hwidths hchildren
      (fun hi hj => hleft hi hj) hslot
    have hn := gp_sum_nonneg (fun j => a.widths.getD j 0) hwidths (pl.children.getD plainOwner [])
    have hmax := hslot plainOwner hPlainBound
    obtain ⟨blo, bhi⟩ :=
      groupPlain_bucket_in_owner (pl := pl) (alloc := a) (owner := plainOwner) hinset (by omega)
    rcases groupPlain_sibling_slot_gap hi hj hne hwidths (hleft hownerBound hi)
        (hleft hownerBound hj) with h | h
    · exact Or.inl (Int.le_trans ghi (Int.le_trans h (Int.le_trans plo
        (Int.le_trans blo hplainBounds.1))))
    · exact Or.inr (Int.le_trans hplainBounds.2 (Int.le_trans bhi
        (Int.le_trans phi (Int.le_trans h glo))))

private theorem gp_selected_group_plain_ordered
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (pair : R8a_SelectedPair e g b)
    {u w : Nat} {gn pn : Node} {groupSource plainSource : ModelBox}
    (hg : pair.selected.cg.nodes[u]? = some gn) (hp : pair.selected.cg.nodes[w]? = some pn)
    (hgroup : gn.border = -2) (hplain : pn.border = 0)
    (hgPos : pair.part.1[u]? = some gn.decl) (hpPos : pair.part.1[w]? = some pn.decl)
    (hgSrc : inp.boxes[gn.decl]? = some groupSource) (hpSrc : inp.boxes[pn.decl]? = some plainSource)
    (hforeign : pn.clusterPath.contains gn.decl = false) :
    R8a_OverlapRowsXGap (frameRect e.params pair.selected.cg pair.selected.run u)
      (frameRect e.params pair.selected.cg pair.selected.run w) := by
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  have hregions : newComponentRegions pair.selected.spec e.params inp
      (componentCandidateR pair.selected.spec e.graph pair.part.1 pair.selected.candidate) =
        .ok pair.selected.regions := by
    rw [pair.selected.effective_eq]
    exact componentTrialR_selected_regions _ pair.selected.regions_eq
  rw [pair.active] at hregions
  obtain ⟨rm, hrm⟩ : ∃ rm, pair.selected.regions = some rm := by
    cases he : pair.selected.regions with
    | none =>
      have heff := pair.selected.effective_eq
      rw [pair.active, he] at heff
      simp at heff
    | some rm => exact ⟨rm, rfl⟩
  rw [hrm] at hregions
  have hpart := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components e.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) e.components_eq).1]
    exact List.mem_map_of_mem hpart
  obtain ⟨_, _, hn, hm, _, hs⟩ := active_group_plain_slot_geometry e hwf hframed hcomp hrun
    hregions hg hp hgroup hplain hgPos hpPos hgSrc hpSrc hforeign
  exact groupPlain_gap_of_interval_bounds hg hgroup hn hm ⟨Int.le_refl _, Int.le_refl _⟩ hs

theorem r8a_selected_group_plain_xgap {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (pair : R8a_SelectedPair execution g b)
    (hb : (pair.uNode.border = -2 ∧ pair.wNode.border = 0) ∨
      (pair.uNode.border = 0 ∧ pair.wNode.border = -2)) :
    R8a_OverlapRowsXGap (frameRect execution.params pair.selected.cg pair.selected.run pair.u)
      (frameRect execution.params pair.selected.cg pair.selected.run pair.w) := by
  rcases hb with ⟨hg, hp⟩ | ⟨hp, hg⟩
  · exact gp_selected_group_plain_ordered hwf hframed pair pair.group_node pair.peer_node hg hp
      pair.group_pos pair.peer_pos pair.group_source pair.peer_source pair.group_not_in_path
  · exact groupPlain_gap_comm
      (gp_selected_group_plain_ordered hwf hframed pair pair.peer_node pair.group_node hg hp
        pair.peer_pos pair.group_pos pair.peer_source pair.group_source pair.peer_not_in_path)

theorem groupPlain_root_bucket_left {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    groupPlain_bucketLeft stages.placement P stages.allocation rm.clusters.length = 0 := by
  have hroot : stages.placement.rm.clusters.length = rm.clusters.length := by rw [stages.hPlacement]
  unfold groupPlain_bucketLeft groupPlain_allocLeft
  rw [hroot, ite_eq_left (Eq.refl rm.clusters.length), stages.root_left hparents hmin, Int.add_zero]

private theorem r8b_endpoint_decl_path {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (ex : SceneExecutionR exactIds idSets inp o res) {comp : List Nat} {s : RegionSpec}
    {k v : Nat} {raw : Node} (hcomp : comp ∈ components ex.graph)
    (hraw : (componentCandidateR (some s) ex.graph comp k).nodes[v]? = some raw) :
    ∃ box, inp.boxes[raw.decl]? = some box ∧
      (raw.clusterPath = Compound.path inp.boxes box ∨
        raw.clusterPath = Compound.path inp.boxes box ++ [raw.decl]) := by
  obtain ⟨index, _, hg⟩ := gp_component_member_node hcomp hraw
  have hi := (List.getElem?_eq_some_iff.mp hg).1
  rw [exactGraph_length ex.graph_eq] at hi
  obtain ⟨old, h0⟩ : ∃ old, ex.graph0.nodes[index]? = some old :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨now, hnow, _, hp, hd⟩ := exactGraph_node_key ex.graph_eq h0
  have he : now = raw := Option.some.inj (hnow.symm.trans hg)
  subst now
  rcases (measuredGraph_marker_shape ex.graph0_eq h0).1 with hplain | htop | hbottom
  · have hlines := ex.lines_eq
    unfold boxLines at hlines
    have hlength : ex.lines.length = inp.boxes.length := by
      simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
    obtain ⟨nodes, _, _, hprepared, hnlen, hmetadata⟩ :=
      measuredGraph_prepared_source ex.graph0_eq
    rw [hprepared] at h0
    have hbefore : index < nodes.length := by
      by_cases h : index < nodes.length
      · exact h
      · have hmarker := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega) h0
        omega
    have hboxBound : index < inp.boxes.length := by omega
    let box := inp.boxes[index]'hboxBound
    have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hboxBound
    obtain ⟨_, hchanged, hmapPath⟩ := fixedSizes_path_index inp hbox
    obtain ⟨hkey, hpath⟩ :=
      prepare_plain_path_origin _ _ _ _ hmetadata h0 hplain hchanged
    exact ⟨box, by rwa [hd, hkey], Or.inl (hp.trans (hpath.trans hmapPath))⟩
  · obtain ⟨_, box, hbox, _, hpath⟩ := measuredGraph_group_origin ex.graph0_eq h0 htop
    rw [List.getElem?_map] at hbox
    obtain ⟨source, hsource, hmatch⟩ := Option.map_eq_some_iff.mp hbox
    obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hsource
    rw [← hmatch, hpathMap] at hpath
    exact ⟨source, by rwa [hd], Or.inr (by rw [hd]; exact hp.trans hpath)⟩
  · obtain ⟨box, hbox, _, hpath, _, _⟩ :=
      measuredGraph_bottom_origin ex.graph0_eq (List.mem_of_getElem? h0) hbottom
    rw [List.getElem?_map] at hbox
    obtain ⟨source, hsource, hmatch⟩ := Option.map_eq_some_iff.mp hbox
    obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hsource
    rw [← hmatch, hpathMap] at hpath
    exact ⟨source, by rwa [hd], Or.inr (by rw [hd]; exact hp.trans hpath)⟩

theorem r8b_executed_endpoint_rooted {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (ex : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components ex.graph)
    {s : RegionSpec} {k : Nat} {rm : ComponentRegions}
    (hactive : newComponentRegions (some s) ex.params inp
      (componentCandidateR (some s) ex.graph comp k) = .ok (some rm))
    {cg : Graph} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages ex.params rm cg ex.measured p minimum
      layers pinned xs reserved placed)
    (hmin : constrainR rm ex.params p = .ok minimum)
    {v owner : Nat} {raw : Node}
    (hraw : (componentCandidateR (some s) ex.graph comp k).nodes[v]? = some raw)
    (howner : match raw.clusterPath.getLast? with
      | none => owner = rm.clusters.length
      | some d => clusterOfDecl rm d = some owner) :
    GroupPlainRootedPath stages.placement
      (fun d => (clusterOfDecl rm d).getD rm.clusters.length) rm.clusters.length raw.clusterPath := by
  obtain ⟨hrows, hparentsTable⟩ := gp_resolved_tables hactive
  obtain ⟨hnd, hsources⟩ := gp_candidate_cluster_sources ex hcomp hrows
  have hparents := activeRegion_parent_count hactive
  have hcounts := stages.group_paths hparents hmin
  have hrooted {i : Nat} {c : RegionCluster} {src : ModelBox}
      (hc : rm.clusters[i]? = some c) (hs : inp.boxes[c.decl]? = some src) :
      GroupPlainRootedPath stages.placement (gp_resolve rm) rm.clusters.length
        (Compound.path inp.boxes src ++ [c.decl]) :=
    gp_cluster_rooted ex hwf hframed hcomp hrows hparentsTable hnd hsources hcounts.1
      (hcounts.2 i (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hc).1)) hc hs
  obtain ⟨src, hsrc, hp | hp⟩ := r8b_endpoint_decl_path ex hcomp hraw
  · rw [hp] at howner ⊢
    exact (gp_plain_rooted hwf hframed hrooted hsrc howner).1
  · have hl : raw.clusterPath.getLast? = some raw.decl := by
      rw [hp, List.getLast?_append]
      simp
    rw [hl] at howner
    change clusterOfDecl rm raw.decl = some owner at howner
    obtain ⟨hlt, hkey, _⟩ := List.findIdx?_eq_some_iff_getElem.mp howner
    let c := rm.clusters[owner]
    have hc : rm.clusters[owner]? = some c := List.getElem?_eq_getElem hlt
    have hdecl : c.decl = raw.decl := beq_iff_eq.mp hkey
    rw [hp, ← hdecl]
    exact hrooted hc (by rwa [hdecl])

theorem r8b_executed_rooted_path_bounds {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length) (hmin : constrainR rm P p = .ok minimum)
    {path : List Nat}
    (hrooted : GroupPlainRootedPath stages.placement
      (fun d => (clusterOfDecl rm d).getD rm.clusters.length) rm.clusters.length path) :
    path.length ≤ rm.clusters.length ∧
      ∀ d ∈ path, (clusterOfDecl rm d).getD rm.clusters.length < rm.clusters.length := by
  let resolve := gp_resolve rm
  let order := stages.placement.order
  let pos := fun g => order.idxOf g
  obtain ⟨_, horder, hnoself, hmem⟩ := stages.allocation_topology hparents hmin
  have hchildren := (stages.group_paths hparents hmin).1
  have hstep {a b : Nat} (ha : a ≤ rm.clusters.length)
      (hb : b ∈ stages.placement.children.getD a []) : pos a < pos b := by
    have ha' : pos a < order.length := List.idxOf_lt_length_of_mem (hmem a ha)
    have hb' : pos b < order.length := List.idxOf_lt_length_of_mem
      (hmem b (Nat.le_of_lt (hchildren a b hb).1))
    have haRead : order[pos a] = a := List.getElem_idxOf ha'
    have hbRead : order[pos b] = b := List.getElem_idxOf hb'
    rcases Nat.lt_trichotomy (pos a) (pos b) with h | h | h
    · exact h
    · have hsame : a = b := by
        have hQa : order[pos a]? = some a :=
          (List.getElem?_eq_getElem ha').trans (congrArg some haRead)
        have hQb : order[pos b]? = some b :=
          (List.getElem?_eq_getElem hb').trans (congrArg some hbRead)
        rw [h] at hQa
        exact Option.some.inj (hQa.symm.trans hQb)
      exact (hnoself a (hsame.symm ▸ hb)).elim
    · have hbad := List.pairwise_iff_getElem.mp horder (pos b) (pos a) hb' ha' h
      rw [hbRead, haRead] at hbad
      exact (hbad hb).elim
  have walk (ds : List Nat) {g : Nat} (hg : g ≤ rm.clusters.length)
      (h : GroupPlainRootedPath stages.placement resolve g ds) :
      (∀ d ∈ ds, resolve d < rm.clusters.length ∧ pos g < pos (resolve d)) ∧
        (ds.map resolve).Nodup := by
    induction ds generalizing g with
    | nil => simp
    | cons d ds ih =>
      change resolve d ∈ stages.placement.children.getD g [] ∧
        GroupPlainRootedPath stages.placement resolve (resolve d) ds at h
      have hD := (hchildren _ _ h.1).1
      have hpos := hstep hg h.1
      obtain ⟨hh, hn⟩ := ih (Nat.le_of_lt hD) h.2
      constructor
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨hD, hpos⟩
        · exact ⟨(hh v hv).1, Nat.lt_trans hpos (hh v hv).2⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, hn⟩
        intro hv
        obtain ⟨v, hv, he⟩ := List.mem_map.mp hv
        have hlt := (hh v hv).2
        rw [he] at hlt
        omega
  obtain ⟨hb, hn⟩ := walk path (Nat.le_refl _) hrooted
  have hsub : path.map resolve ⊆ List.range rm.clusters.length := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    exact List.mem_range.mpr (hb d hd).1
  exact ⟨by simpa only [List.length_map, List.length_range] using hn.length_le_of_subset hsub,
    fun d hd => (hb d hd).1⟩

theorem r8b_executed_resolver_injective {rm : ComponentRegions} {d e : Nat}
    (hd : (clusterOfDecl rm d).getD rm.clusters.length < rm.clusters.length)
    (he : (clusterOfDecl rm d).getD rm.clusters.length =
      (clusterOfDecl rm e).getD rm.clusters.length) : d = e :=
  gp_resolve_injective hd he

theorem active_candidate_plain_source_path {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k i key : Nat}
    {n : Node} {source : ModelBox}
    (hn : (componentCandidateR (some s) e.graph comp k).nodes[i]? = some n)
    (hb : n.border = 0) (hkey : comp[i]? = some key) (hsrc : inp.boxes[key]? = some source) :
    n.clusterPath = Compound.path inp.boxes source := by
  have hd := active_candidate_plain_decl e hcomp hn hb hkey hsrc
  obtain ⟨actual, ha, hglobal⟩ := gp_component_member_node hcomp hn
  have he : actual = key := Option.some.inj (ha.symm.trans hkey)
  rw [he, ← hd] at hglobal
  exact (gp_selected_source_path e hglobal (source := source) (by rwa [hd])).2 hb

theorem active_candidate_source_border {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k i key : Nat}
    {n : Node} (hn : (componentCandidateR (some s) e.graph comp k).nodes[i]? = some n)
    (hkey : comp[i]? = some key) (hbound : key < inp.boxes.length) :
    n.border = -2 ∨ n.border = 0 := by
  obtain ⟨actual, ha, hglobal⟩ := gp_component_member_node hcomp hn
  have he : actual = key := Option.some.inj (ha.symm.trans hkey)
  rw [he] at hglobal
  obtain ⟨raw, hraw, hkind, _⟩ := gp_measured_node_key e hglobal
  obtain ⟨nodes, _, _, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source e.graph0_eq
  have hk : key < nodes.length := by rwa [hlength, boxLines_length e.lines_eq]
  rw [hprepared] at hraw
  change (Compound.markNodes _ _ _ nodes)[key]? = some raw at hraw
  have hm := Compound.markNodes_getElem?_prefix_border _ _ _ nodes hk hraw
  have hz := (hmetadata key nodes[key] (List.getElem?_eq_getElem hk)).2
  rw [← hkind]
  simpa only [hz] using hm

theorem active_candidate_top_cluster {P : Params} {s : RegionSpec} {inp : Input}
    {cand : Graph} {rm : ComponentRegions}
    (hactive : newComponentRegions (some s) P inp cand = .ok (some rm))
    {v : Nat} {top : Node} (ht : cand.nodes[v]? = some top) (hb : top.border = -2) :
    ∃ owner c, clusterOfDecl rm top.decl = some owner ∧
      rm.clusters[owner]? = some c ∧ c.decl = top.decl := by
  obtain ⟨c, hc, hd, _⟩ := gp_cluster_of_top (gp_resolved_tables hactive).1 ht hb
  cases hf : clusterOfDecl rm top.decl with
  | none =>
    have hn := List.findIdx?_eq_none_iff.mp hf c hc
    simp [hd] at hn
  | some owner =>
    obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    exact ⟨owner, rm.clusters[owner], rfl,
      List.getElem?_eq_getElem hi, beq_iff_eq.mp hmatch⟩

theorem RegionCrossAllocationStages.activePlain_frame_in_ownerBucket {P : Params}
    {exact : List Nat} {s : RegionSpec} {inp : Input} {cand cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    {ranks : List Int} {budget : Bool} {normalized labeled p : Proper}
    {minimum : RegionConstraints} {layers : List (List Nat)} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hrun : componentRunR P exact (some s) inp cand labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp cand = .ok (some rm))
    (hrank : rankEquivalentR rm cand = .ok (ranks, cg, budget))
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (hmin : constrainR rm P p = .ok minimum)
    {v : Nat} {original : Node} (hv : cg.nodes[v]? = some original) (hplain : original.border = 0) :
    ∃ owner, stages.groups[v]? = some owner ∧
      (match original.clusterPath.getLast? with
        | none => owner = rm.clusters.length
        | some decl => clusterOfDecl rm decl = some owner) ∧
      v ∈ stages.placement.buckets.members.getD owner [] ∧
      groupPlain_bucketLeft stages.placement P stages.allocation owner ≤
        (frameRect P cg run v).x ∧
      (frameRect P cg run v).x + (frameRect P cg run v).w ≤
        groupPlain_bucketRight stages.placement P stages.allocation owner := by
  obtain ⟨n, hn, hb, hpath, hfinal, hx⟩ :=
    gp_plain_run_record hrun hrank hnorm hlabels hcoord stages (gp_resolved_tables hactive).1
      hv hplain
  obtain ⟨owner, hlookup, hbound, howner⟩ := groupPlain_nodeGroups_lookup stages.hGroups hn
  obtain ⟨hmem, hshift⟩ :=
    groupPlain_shifted_center stages (activeRegion_parent_count hactive) hmin hn hb hlookup hbound
  have hplaced : stages.placement.p.nodes[v]? = some n := by rwa [stages.hPlacement]
  have hrect := groupPlain_plainRect_of_bucket_shift stages hplain hv hplaced hfinal hmem
    (hx.trans hshift)
  exact ⟨owner, hlookup, by simpa only [hpath] using howner, hmem, hrect⟩

#print axioms active_candidate_plain_source_path
#print axioms active_candidate_source_border
#print axioms active_candidate_top_cluster
#print axioms RegionCrossAllocationStages.activePlain_frame_in_ownerBucket

#print axioms r8b_executed_endpoint_rooted
#print axioms r8b_executed_rooted_path_bounds
#print axioms r8b_executed_resolver_injective

end Elegant.Layered.PipelineImpl

#print axioms Elegant.Layered.PipelineImpl.groupPlain_foreign_owner_fork
#print axioms Elegant.Layered.PipelineImpl.groupPlain_gap_of_interval_bounds
#print axioms Elegant.Layered.PipelineImpl.groupPlain_selected_owner_fork
#print axioms Elegant.Layered.PipelineImpl.groupPlain_selected_allocation
#print axioms Elegant.Layered.PipelineImpl.groupPlain_frame_eq_nodeRect
#print axioms Elegant.Layered.PipelineImpl.groupPlain_gap_comm
#print axioms Elegant.Layered.PipelineImpl.groupPlain_allocation_width_eq
#print axioms Elegant.Layered.PipelineImpl.groupPlain_child_slot_bounds
#print axioms Elegant.Layered.PipelineImpl.groupPlain_sibling_slot_gap
#print axioms Elegant.Layered.PipelineImpl.groupPlain_bucket_before_child
#print axioms Elegant.Layered.PipelineImpl.groupPlain_marker_arithmetic
#print axioms Elegant.Layered.PipelineImpl.groupPlain_regionFrames_marker
#print axioms Elegant.Layered.PipelineImpl.groupPlain_allocation_lefts_nonneg
#print axioms Elegant.Layered.PipelineImpl.groupPlain_selected_nonnegative_slots
#print axioms Elegant.Layered.PipelineImpl.groupPlain_plainRect_of_bucket_shift
#print axioms Elegant.Layered.PipelineImpl.groupPlain_overlap_gap_of_common_owner_slots
#print axioms Elegant.Layered.PipelineImpl.groupPlain_nested_slot_bounds
#print axioms Elegant.Layered.PipelineImpl.groupPlain_group_slot_of_markers
#print axioms Elegant.Layered.PipelineImpl.groupPlain_bucket_in_owner
#print axioms Elegant.Layered.PipelineImpl.groupPlain_gap_from_chosen_branches
#print axioms Elegant.Layered.PipelineImpl.groupPlain_common_path_branches
#print axioms Elegant.Layered.PipelineImpl.groupPlain_reservedPorts_record
#print axioms Elegant.Layered.PipelineImpl.groupPlain_nodeGroups_lookup
#print axioms Elegant.Layered.PipelineImpl.groupPlain_shifted_center
#print axioms Elegant.Layered.PipelineImpl.r8a_selected_group_plain_xgap
#print axioms Elegant.Layered.PipelineImpl.groupPlain_root_bucket_left
