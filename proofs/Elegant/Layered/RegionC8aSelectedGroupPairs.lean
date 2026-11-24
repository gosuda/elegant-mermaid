import Elegant.Layered.RegionSharedAllocation
import Elegant.Layered.RegionFlatC8a
import Elegant.Layered.RegionBucketBounds
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.RegionC8aGroupPlain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem r8ag_bind {α β : Type} {input : Except LayoutError α}
    {next : α → Except LayoutError β} {out : β} (h : input.bind next = .ok out) :
    ∃ a, input = .ok a ∧ next a = .ok out := by
  cases input with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem r8ag_foldM {α β : Type} (good : α → Prop)
    (f : α → β → Except LayoutError α) (l : List β) (a z : α) (ha : good a)
    (hs : ∀ x ∈ l, ∀ {u v}, good u → f u x = .ok v → good v)
    (hf : l.foldlM f a = .ok z) : good z := by
  induction l generalizing a with
  | nil =>
    change Except.ok a = Except.ok z at hf
    cases hf
    exact ha
  | cons x xs ih =>
    rw [List.foldlM_cons] at hf
    obtain ⟨mid, hmid, htail⟩ := r8ag_bind hf
    exact ih mid (hs x List.mem_cons_self ha hmid)
      (fun y hy => hs y (List.mem_cons_of_mem _ hy)) htail

private theorem r8ag_setAt_length {α : Type} (l : List α) (i : Nat) (x : α) :
    (setAt l i x).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih => cases i <;> simp [setAt, ih]

private theorem r8ag_setAt_getD {α : Type} (l : List α) (i j : Nat) (x d : α) :
    (setAt l i x).getD j d = if j = i ∧ i < l.length then x else l.getD j d := by
  induction l generalizing i j with
  | nil => simp [setAt]
  | cons a l ih =>
    cases i with
    | zero => cases j <;> simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j


theorem r8ag_selected_region {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (pair : R8a_SelectedPair e g b) :
    ∃ (labeled p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)) (rm : ComponentRegions),
      newComponentRegions (some pair.spec) e.params inp
        (componentCandidateR (some pair.spec) e.graph pair.part.1 pair.selected.candidate) =
        .ok (some rm) ∧
      constrainR rm e.params p = .ok minimum ∧
      coordinateGraphR e.params (exactDecls exactIds inp) (some pair.spec) labeled = p ∧
      NodeKeys pair.selected.cg labeled ∧
      (∀ {j : Nat} {original : Node}, pair.selected.cg.nodes[j]? = some original →
        labeled.nodes[j]? = some ⟨original, false, none, false⟩) ∧
      pair.selected.cg.nodes =
        (componentCandidateR (some pair.spec) e.graph pair.part.1 pair.selected.candidate).nodes ∧
      Nonempty (RegionCrossAllocationStages e.params rm pair.selected.cg e.measured p minimum
        ord.layers pair.selected.run.layers pair.selected.run.coordinateXs reserved
        pair.selected.run.coordinateProper) := by
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  have hregions : newComponentRegions pair.selected.spec e.params inp
      (componentCandidateR pair.selected.spec e.graph pair.part.1 pair.selected.candidate) =
      .ok pair.selected.regions := by
    rw [pair.selected.effective_eq]
    exact componentTrialR_selected_regions _ pair.selected.regions_eq
  rw [pair.active] at hregions
  have hsome : ∃ rm, pair.selected.regions = some rm := by
    cases he : pair.selected.regions with
    | none =>
      have heff := pair.selected.effective_eq
      rw [pair.active, he] at heff
      simp at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hregions
  obtain ⟨_, _, labeled, p, minimum, ord, reserved, _, hrank, hnorm, hlabel, hcoord, hmin,
    _, hstages⟩ :=
    componentRunR_active_allocation_stages hrun hregions
  exact ⟨labeled, p, minimum, ord, reserved, rm, hregions, hmin, hcoord,
    addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabel,
    fun hk => addLabelNodes_untouched_node hlabel (normalize_node_record hnorm hk) rfl,
    rankEquivalentR_nodes_eq hrank, hstages⟩

private theorem r8ag_selected_group_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (pair : R8a_SelectedPair e g b) {i : Nat} {n : Node} {source : ModelBox}
    (hpart : pair.part.1[i]? = some n.decl) (hnode : pair.selected.cg.nodes[i]? = some n)
    (hsource : inp.boxes[n.decl]? = some source) (hgroup : n.border = -2) :
    n.clusterPath = Compound.path inp.boxes source ++ [n.decl] := by
  have hb := sceneExecutionR_graph_lenR e (List.getElem?_eq_some_iff.mp hsource).1
  have hb0 : n.decl < e.graph0.nodes.length := by
    rw [← exactGraph_length e.graph_eq]
    exact hb
  obtain ⟨n1, hn1, hborder, hpath, _⟩ := exactGraph_node_key e.graph_eq
    (List.getElem?_eq_getElem hb0)
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hnodes : pair.selected.cg.nodes =
      (componentCandidateR (some pair.spec) e.graph pair.part.1 pair.selected.candidate).nodes := by
    rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hrank⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq hrank
  have hn1' := component_node_lookupR (spec := some pair.spec) (cand := pair.selected.candidate)
    hpart hn1
  rw [← hnodes, hnode] at hn1'
  have h1 : n1 = n := (Option.some.inj hn1').symm
  subst n1
  have h0 : e.graph0.nodes[n.decl].border = -2 := hborder.symm.trans hgroup
  obtain ⟨hdecl, effective, heffective, _, horigin⟩ :=
    measuredGraph_group_origin e.graph0_eq (List.getElem?_eq_getElem hb0) h0
  rw [hdecl, List.getElem?_map, hsource, Option.map_some] at heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hsource
  rw [← Option.some.inj heffective, hpathMap, hdecl] at horigin
  exact hpath.trans horigin

inductive R8agSourceAncestor (inp : Input) : Nat → Nat → Prop
  | parent {i j : Nat} {a b : ModelBox} (ha : inp.boxes[i]? = some a)
      (hb : inp.boxes[j]? = some b) (hparent : b.parent = a.id) (hne : b.parent ≠ "") :
      R8agSourceAncestor inp i j
  | down {i j k : Nat} {a b : ModelBox} (above : R8agSourceAncestor inp i j)
      (ha : inp.boxes[j]? = some a) (hb : inp.boxes[k]? = some b)
      (hparent : b.parent = a.id) (hne : b.parent ≠ "") : R8agSourceAncestor inp i k

private theorem r8ag_ancestor_in_path {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) {i j : Nat}
    (h : R8agSourceAncestor inp i j) {b : ModelBox} (hb : inp.boxes[j]? = some b) :
    i ∈ Compound.path inp.boxes b := by
  induction h generalizing b with
  | parent ha hb' hp hn =>
    replace hb' := Option.some.inj (hb'.symm.trans hb)
    cases hb'
    change i ∈ Compound.path (inputModel inp o).boxes _
    rw [Compound.path_of_parent (inputModel inp o) hwf ha hb hp hn]
    exact List.mem_append.mpr (Or.inr (by simp))
  | down _ ha hb' hp hn ih =>
    replace hb' := Option.some.inj (hb'.symm.trans hb)
    cases hb'
    change i ∈ Compound.path (inputModel inp o).boxes _
    rw [Compound.path_of_parent (inputModel inp o) hwf ha hb hp hn]
    exact List.mem_append.mpr (Or.inl (ih ha))

theorem r8ag_selected_not_nested {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (hwf : WellFormed (inputModel inp o)) (pair : R8a_SelectedPair e g b)
    (hg : pair.uNode.border = -2) (hb : pair.wNode.border = -2) :
    ¬ R8agSourceAncestor inp pair.uNode.decl pair.wNode.decl ∧
      ¬ R8agSourceAncestor inp pair.wNode.decl pair.uNode.decl := by
  have hp := r8ag_selected_group_source pair pair.group_pos pair.group_node pair.group_source hg
  have hq := r8ag_selected_group_source pair pair.peer_pos pair.peer_node pair.peer_source hb
  constructor
  · intro hn
    have hm := r8ag_ancestor_in_path hwf hn pair.peer_source
    have ht : pair.wNode.clusterPath.contains pair.uNode.decl = true := by
      rw [hq, List.contains_iff_mem]
      exact List.mem_append.mpr (Or.inl hm)
    rw [pair.group_not_in_path] at ht
    cases ht
  · intro hn
    have hm := r8ag_ancestor_in_path hwf hn pair.group_source
    have ht : pair.uNode.clusterPath.contains pair.wNode.decl = true := by
      rw [hp, List.contains_iff_mem]
      exact List.mem_append.mpr (Or.inl hm)
    rw [pair.peer_not_in_path] at ht
    cases ht

private theorem r8ag_hull_gap {P : Params} {cg : Graph} {run : Run}
    {u w : Nat} {uNode wNode : Node} {aLo aHi bLo bHi : Int}
    (hu : cg.nodes[u]? = some uNode) (hw : cg.nodes[w]? = some wNode)
    (hgu : uNode.border = -2) (hgw : wNode.border = -2)
    (ha0 : 0 ≤ aHi) (hb0 : 0 ≤ bHi)
    (ha : ∀ r ∈ groupBorderRects cg run uNode.decl, aLo ≤ r.x ∧ r.x + r.w ≤ aHi)
    (hb : ∀ r ∈ groupBorderRects cg run wNode.decl, bLo ≤ r.x ∧ r.x + r.w ≤ bHi)
    (hgap : aHi ≤ bLo ∨ bHi ≤ aLo) :
    R8a_OverlapRowsXGap (frameRect P cg run u) (frameRect P cg run w) := by
  rw [frameRect_group_span hu hgu, frameRect_group_span hw hgw]
  intro _ hwu hww
  have hneU : groupBorderRects cg run uNode.decl ≠ [] := by
    intro he
    simp [he, boundsOf] at hwu
  have hneW : groupBorderRects cg run wNode.decl ≠ [] := by
    intro he
    simp [he, boundsOf] at hww
  have hulo := boundsOf_minX_ge_of_all hneU (fun r hr => (ha r hr).1)
  have hwlo := boundsOf_minX_ge_of_all hneW (fun r hr => (hb r hr).1)
  have huhi := boundsOf_right_le_of_all ha0 (fun r hr => (ha r hr).2)
  have hwhi := boundsOf_right_le_of_all hb0 (fun r hr => (hb r hr).2)
  dsimp only
  rcases hgap with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem r8ag_prefix_room
    (width : Nat → Int) (hn : ∀ a, 0 ≤ width a)
    {l : List Nat} {i a : Nat} (ha : l[i]? = some a) :
    ((l.take i).map width).sum + width a ≤ (l.map width).sum := by
  have hsum : ∀ l : List Nat, 0 ≤ (l.map width).sum := by
    intro l
    induction l with
    | nil => exact Int.le_refl _
    | cons x xs ih => exact Int.add_nonneg (hn x) ih
  induction l generalizing i with
  | nil => simp at ha
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst x
      simp only [List.take_zero, List.map_nil, List.sum_nil, Int.zero_add, List.map_cons,
        List.sum_cons]
      exact Int.le_add_of_nonneg_right (hsum xs)
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      have hh := ih ha
      omega

private theorem r8ag_prefix_order
    (width : Nat → Int) (hn : ∀ a, 0 ≤ width a)
    {l : List Nat} {i j a : Nat} (ha : l[i]? = some a) (hij : i < j) :
    ((l.take i).map width).sum + width a ≤ ((l.take j).map width).sum := by
  have hb : (l.take j)[i]? = some a :=
    (List.getElem?_take_of_lt hij).trans ha
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)] using
    r8ag_prefix_room width hn hb

private theorem r8ag_branch_mono {rows : List (List Nat)} {n : Nat} {left right : Nat → Int}
    (hrange : ∀ a b, b ∈ rows.getD a [] → b < n)
    (hchild : ∀ a b, a ≤ n → b ∈ rows.getD a [] → left a ≤ left b)
    (hroom : ∀ a b, a < n → b ∈ rows.getD a [] → right b ≤ right a)
    {a b : Nat} (ha : a ≤ n) (h : RegionGroupBranch rows a b) :
    left a ≤ left b ∧ (a < n → right b ≤ right a) := by
  induction h with
  | here => exact ⟨Int.le_refl _, fun _ => Int.le_refl _⟩
  | @down p q z hedge _ ih =>
    have hq := hrange p q hedge
    obtain ⟨hlo, hhi⟩ := ih (Nat.le_of_lt hq)
    exact ⟨Int.le_trans (hchild p q ha hedge) hlo,
      fun hp => Int.le_trans (hhi hq) (hroom p q hp hedge)⟩

private theorem r8ag_branch_gap {rows : List (List Nat)} {n : Nat} {left right : Nat → Int}
    (hrange : ∀ a b, b ∈ rows.getD a [] → b < n)
    (hchild : ∀ a b, a ≤ n → b ∈ rows.getD a [] → left a ≤ left b)
    (hroom : ∀ a b, a < n → b ∈ rows.getD a [] → right b ≤ right a)
    (hsiblings : ∀ a b c, a ≤ n → b ∈ rows.getD a [] → c ∈ rows.getD a [] →
      b ≠ c → right b ≤ left c ∨ right c ≤ left b)
    {root a b : Nat} (hroot : root ≤ n) (ha : RegionGroupBranch rows root a)
    (hb : RegionGroupBranch rows root b) (hab : ¬ RegionGroupBranch rows a b)
    (hba : ¬ RegionGroupBranch rows b a) :
    right a ≤ left b ∨ right b ≤ left a := by
  induction ha generalizing b with
  | here => exact (hab hb).elim
  | @down root firstA a heA tailA ih =>
    cases hb with
    | here => exact (hba (.down heA tailA)).elim
    | @down _ firstB _ heB tailB =>
      by_cases he : firstA = firstB
      · subst firstB
        exact ih (Nat.le_of_lt (hrange _ _ heA)) tailB hab hba
      · obtain ⟨hloA, hhiA⟩ := r8ag_branch_mono hrange hchild hroom
          (Nat.le_of_lt (hrange _ _ heA)) tailA
        obtain ⟨hloB, hhiB⟩ := r8ag_branch_mono hrange hchild hroom
          (Nat.le_of_lt (hrange _ _ heB)) tailB
        rcases hsiblings root firstA firstB hroot heA heB he with h | h
        · exact Or.inl (Int.le_trans (Int.le_trans (hhiA (hrange _ _ heA)) h) hloB)
        · exact Or.inr (Int.le_trans (Int.le_trans (hhiB (hrange _ _ heB)) h) hloA)

private theorem r8ag_alloc_widths {pl : RegionPlacement} {P : Params} {xs moved : List Int}
    {alloc : RegionAllocation} (h : allocatePl pl P xs = .ok (alloc, moved)) :
    alloc.widths = reserveWidths pl P := by
  unfold allocatePl at h
  obtain ⟨_, _, h⟩ := r8ag_bind h
  exact (congrArg (fun q : RegionAllocation × List Int => q.1.widths) (Except.ok.inj h)).symm

private theorem r8ag_distinct_band {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {s : RegionSpec} {inp : Input} {candidate : Graph}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hmin : constrainR rm P p = .ok minimum)
    (hslot : 0 ≤ P.slot) (hinset : 0 ≤ regionInsetOf P)
    {a b : Nat} (ha : a < rm.clusters.length) (hb : b < rm.clusters.length)
    (hab : ¬ RegionGroupBranch stages.placement.children a b)
    (hba : ¬ RegionGroupBranch stages.placement.children b a) :
    let left (c : Nat) := stages.allocation.lefts.getD c 0
    let right (c : Nat) := left c + stages.allocation.widths.getD c 0 -
      stages.placement.buckets.loopWidth.getD c 0
    0 ≤ left a ∧ 0 ≤ left b ∧
      P.clusterBorderW ≤ right a - left a ∧ P.clusterBorderW ≤ right b - left b ∧
      (right a ≤ left b ∨ right b ≤ left a) := by
  let n := rm.clusters.length
  let pl := stages.placement
  let rows := pl.children
  let L (c : Nat) := stages.allocation.lefts.getD c 0
  let W (c : Nat) := (reserveWidths pl P).getD c 0
  let R (c : Nat) := L c + W c - pl.buckets.loopWidth.getD c 0
  have hparents := activeRegion_parent_count hactive
  obtain ⟨hrows, hpath⟩ := stages.group_paths hparents hmin
  obtain ⟨hown, hlane, hloop⟩ := stages.bucket_signs hslot
  have hw := reserveWidths_nonnegative (pl := pl) hinset hown hlane hloop
  obtain ⟨_, horder⟩ := stages.reservation_order hparents hmin
  have hminWidth (a : Nat) (ha : a < n) :
      2 * regionInsetOf P + pl.buckets.widths.getD a 0 +
        ((rows.getD a []).map W).sum ≤ W a - pl.buckets.loopWidth.getD a 0 := by
    obtain ⟨_, _, hsplit, htail, hchildren⟩ := horder a (Nat.le_of_lt ha)
    have hpa : a < pl.rm.clusters.length := by simpa only [pl, stages.hPlacement] using ha
    have hroom : 2 * regionInsetOf P + pl.buckets.widths.getD a 0 +
        ((rows.getD a []).map W).sum + laneExtentOf pl.buckets P.slot a ≤
        W a - pl.buckets.loopWidth.getD a 0 :=
      reserveWidths_room_from_last_writes (P := P) hsplit hpa htail hchildren
    have hl : 0 ≤ laneExtentOf pl.buckets P.slot a := hlane a
    omega
  have hprefixNonneg (entries : List Nat) : 0 ≤ (entries.map W).sum := by
    induction entries with
    | nil => exact Int.le_refl _
    | cons x xs ih => exact Int.add_nonneg (hw x) ih
  have hleftEq (a b i : Nat) (ha : a ≤ n) (h : (rows.getD a [])[i]? = some b) :
      L b = L a + (if a = n then 0 else regionInsetOf P) + pl.buckets.widths.getD a 0 +
        (((rows.getD a []).take i).map W).sum :=
    stages.childBudget_left_from_allocation hactive hmin ha h
  have hleft (a b : Nat) (ha : a ≤ n) (h : b ∈ rows.getD a []) : L a ≤ L b := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    rw [hleftEq a b i ha hi]
    have hb : 0 ≤ pl.buckets.widths.getD a 0 := hown a
    have hpre := hprefixNonneg ((rows.getD a []).take i)
    split <;> omega
  have hright (a b : Nat) (ha : a < n) (h : b ∈ rows.getD a []) : R b ≤ R a := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    have hh := r8ag_prefix_room W hw hi
    have hr := hminWidth a ha
    have hl : 0 ≤ pl.buckets.loopWidth.getD b 0 := hloop b
    unfold R
    rw [hleftEq a b i (Nat.le_of_lt ha) hi, ite_eq_right (Nat.ne_of_lt ha)]
    omega
  have hsibling (a b c : Nat) (ha : a ≤ n) (hb : b ∈ rows.getD a [])
      (hc : c ∈ rows.getD a []) (hne : b ≠ c) : R b ≤ L c ∨ R c ≤ L b := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    have hne' : i ≠ j := by
      intro he
      rw [he] at hi
      exact hne (Option.some.inj (hi.symm.trans hj))
    unfold R
    rw [hleftEq a b i ha hi, hleftEq a c j ha hj]
    have hlb : 0 ≤ pl.buckets.loopWidth.getD b 0 := hloop b
    have hlc : 0 ≤ pl.buckets.loopWidth.getD c 0 := hloop c
    by_cases hi' : i < j
    · have hp := r8ag_prefix_order W hw hi hi'
      exact Or.inl (by omega)
    · have hp := r8ag_prefix_order W hw hj (show j < i by omega)
      exact Or.inr (by omega)
  have hrange (a b : Nat) (h : b ∈ rows.getD a []) : b < n := (hrows a b h).1
  have hpathA := hpath a (Nat.le_of_lt ha)
  have hpathB := hpath b (Nat.le_of_lt hb)
  have hroot : L n = 0 := stages.root_left hparents hmin
  have hnonneg (a : Nat) (ha : RegionGroupBranch rows n a) : 0 ≤ L a := by
    rw [← hroot]
    exact (r8ag_branch_mono hrange hleft hright (Nat.le_refl n) ha).1
  have hp (a : Nat) (ha : a < n) : P.clusterBorderW ≤ R a - L a := by
    have hminA := hminWidth a ha
    have hone : 0 ≤ pl.buckets.widths.getD a 0 := hown a
    have hsum := hprefixNonneg (rows.getD a [])
    have hpad := (CoordsImpl.crossCoordsClusterWith_spec stages.hCross).2.1
    have hinset' : 0 ≤ P.clusterPad + P.clusterBorderW := hinset
    unfold R
    unfold regionInsetOf at hminA
    omega
  change 0 ≤ L a ∧ 0 ≤ L b ∧
    P.clusterBorderW ≤ L a + stages.allocation.widths.getD a 0 -
      pl.buckets.loopWidth.getD a 0 - L a ∧
    P.clusterBorderW ≤ L b + stages.allocation.widths.getD b 0 -
      pl.buckets.loopWidth.getD b 0 - L b ∧
    (L a + stages.allocation.widths.getD a 0 - pl.buckets.loopWidth.getD a 0 ≤ L b ∨
      L b + stages.allocation.widths.getD b 0 - pl.buckets.loopWidth.getD b 0 ≤ L a)
  rw [r8ag_alloc_widths stages.hAllocation]
  exact ⟨hnonneg a hpathA, hnonneg b hpathB, hp a ha, hp b hb,
    r8ag_branch_gap hrange hleft hright hsibling (Nat.le_refl n) hpathA hpathB hab hba⟩

private def r8ag_parent_index (inp : Input) (rows : List RegionCluster)
    (c : RegionCluster) : Int :=
  match boxParent inp c.decl with
  | "" => -1
  | pid =>
    match rows.findIdx? (fun a => a.id == pid) with
    | some k => (k : Int)
    | none => -1

private theorem r8ag_resolved_tables {P : Params} {s : RegionSpec} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    rm.clusters = clusterRows inp s cg ∧
      rm.parents = rm.clusters.map (r8ag_parent_index inp rm.clusters) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := r8ag_bind h
    split at h
    · cases h
    · rw [← Option.some.inj (Except.ok.inj h)]
      exact ⟨rfl, rfl⟩

private def r8ag_emit_cluster (inp : Input) (s : RegionSpec) (cg : Graph)
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
    some ({ id := boxId inp q.1.decl, decl := q.1.decl,
            node := node, top := q.2, bottom := bottom,
            titleW := q.1.w, titleH := titles.2, extent := q.1.loopExtent } : RegionCluster)

private theorem r8ag_top_only {inp : Input} {s : RegionSpec} {cg : Graph}
    {q : Node × Nat} {c : RegionCluster}
    (hq : cg.nodes[q.2]? = some q.1) (h : r8ag_emit_cluster inp s cg q = some c) :
    c.decl = q.1.decl ∧ c.id = boxId inp q.1.decl ∧ c.top = q.2 ∧ q.1.border = -2 ∧
      ∃ bot : Node, cg.nodes[c.bottom]? = some bot ∧ (bot.border = -2 ∨ bot.border = 2) := by
  unfold r8ag_emit_cluster at h
  split at h
  · cases h
  · rename_i ht
    have htop : q.1.border = -2 := by simpa using ht
    rw [← Option.some.inj h]
    refine ⟨rfl, rfl, rfl, htop, ?_⟩
    change ∃ bot : Node, cg.nodes[(match cg.nodes.zipIdx.find? (fun b =>
      b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2)]? = some bot ∧ (bot.border = -2 ∨ bot.border = 2)
    split
    · rename_i bot hbot
      refine ⟨bot.1, List.mem_zipIdx_iff_getElem?.mp
        (List.mem_of_find?_eq_some hbot), Or.inr ?_⟩
      have hmatch : (bot.1.border == 2 && bot.1.decl == q.1.decl) = true :=
        List.find?_some (p := fun b : Node × Nat =>
          b.1.border == 2 && b.1.decl == q.1.decl) hbot
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hmatch).1
    · exact ⟨q.1, hq, Or.inl htop⟩

private theorem r8ag_table_entry {inp : Input} {s : RegionSpec} {cg : Graph}
    {rows : List RegionCluster} (hrows : rows = clusterRows inp s cg)
    {c : RegionCluster} (hc : c ∈ rows) :
    ∃ top bottom : Node, cg.nodes[c.top]? = some top ∧ top.border = -2 ∧
      top.decl = c.decl ∧ c.id = boxId inp c.decl ∧
      cg.nodes[c.bottom]? = some bottom ∧ (bottom.border = -2 ∨ bottom.border = 2) := by
  rw [hrows] at hc
  change c ∈ cg.nodes.zipIdx.filterMap (r8ag_emit_cluster inp s cg) at hc
  obtain ⟨q, hq, hqemit⟩ := List.mem_filterMap.mp hc
  have hlookup := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨hd, hid, ht, hb, bottom, hblookup, hbside⟩ := r8ag_top_only hlookup hqemit
  exact ⟨q.1, bottom, ht.symm ▸ hlookup, hb, hd.symm, hid.trans (congrArg (boxId inp) hd.symm),
    hblookup, hbside⟩

private theorem r8ag_table_find_top {inp : Input} {s : RegionSpec} {cg : Graph}
    {rm : ComponentRegions} (hrows : rm.clusters = clusterRows inp s cg)
    {a : Nat} {n : Node} (ha : cg.nodes[a]? = some n) (hb : n.border = -2) :
    ∃ (i : Nat) (c : RegionCluster), rm.clusters[i]? = some c ∧
      c.decl = n.decl ∧ c.titleW = n.w := by
  have hm : (n, a) ∈ cg.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr ha
  have hs : ∃ c, r8ag_emit_cluster inp s cg (n, a) = some c := by
    let bottom := match cg.nodes.zipIdx.find? (fun q =>
        q.1.border == 2 && q.1.decl == n.decl) with
      | some q => q.2
      | none => a
    let node := match cg.nodes.zipIdx.find? (fun q => q.1.decl == n.decl) with
      | some q => q.2
      | none => a
    let c : RegionCluster :=
      { id := boxId inp n.decl, decl := n.decl, node := node, top := a, bottom := bottom,
        titleW := n.w, titleH := (s.titles.getD n.decl (0, 0)).2, extent := n.loopExtent }
    refine ⟨c, ?_⟩
    have htop : ¬ (n.border != -2) := by simp [hb]
    rw [r8ag_emit_cluster, ite_eq_right htop] <;> rfl
  obtain ⟨c, hc⟩ := hs
  have hm' : c ∈ rm.clusters := by
    rw [hrows]
    change c ∈ cg.nodes.zipIdx.filterMap (r8ag_emit_cluster inp s cg)
    exact List.mem_filterMap.mpr ⟨(n, a), hm, hc⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm'
  refine ⟨i, c, hi, (r8ag_top_only (q := (n, a)) ha hc).1, ?_⟩
  unfold r8ag_emit_cluster at hc
  split at hc
  · cases hc
  · rw [← Option.some.inj hc]

private theorem r8ag_table_unique {inp : Input} {s : RegionSpec} {cg : Graph}
    {rm : ComponentRegions} (hrows : rm.clusters = clusterRows inp s cg)
    (hkeys : ∀ {i j : Nat} {a b : Node}, cg.nodes[i]? = some a →
      cg.nodes[j]? = some b → a.border = -2 → b.border = -2 → a.decl = b.decl → i = j) :
    (rm.clusters.map (·.decl)).Nodup := by
  rw [hrows]
  change ((cg.nodes.zipIdx.filterMap (r8ag_emit_cluster inp s cg)).map
    (·.decl)).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  have hp : cg.nodes.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := by
    rw [← List.pairwise_map (f := Prod.snd), List.zipIdx_map_snd]
    exact List.nodup_range' 1
  let agrees (q q' : Node × Nat) : Prop :=
    q.2 ≠ q'.2 ∧ q ∈ cg.nodes.zipIdx ∧ q' ∈ cg.nodes.zipIdx
  have hp' : cg.nodes.zipIdx.Pairwise agrees :=
    List.Pairwise.imp_of_mem (fun hq hq' hn => ⟨hn, hq, hq'⟩) hp
  refine List.Pairwise.filterMap (r8ag_emit_cluster inp s cg) ?_ hp'
  intro q q' ⟨hne, hq, hq'⟩ a ha b hb he
  have hget : cg.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hget' : cg.nodes[q'.2]? = some q'.1 := List.mem_zipIdx_iff_getElem?.mp hq'
  obtain ⟨hd, _, _, ht, _⟩ := r8ag_top_only hget ha
  obtain ⟨hd', _, _, ht', _⟩ := r8ag_top_only hget' hb
  exact hne (hkeys hget hget' ht ht' (hd.symm.trans (he.trans hd')))

private theorem r8ag_component_global {graph : Graph} {comp : List Nat} {s : RegionSpec}
    {k i : Nat} {node : Node} (hcomp : comp ∈ components graph)
    (hnode : (componentCandidateR (some s) graph comp k).nodes[i]? = some node) :
    ∃ global, comp[i]? = some global ∧ graph.nodes[global]? = some node := by
  change (comp.map fun v => graph.nodes.getD v default)[i]? = some node at hnode
  rw [List.getElem?_map] at hnode
  cases hp : comp[i]? with
  | none => simp [hp] at hnode
  | some global =>
    obtain ⟨root, he⟩ := mem_components_eq hcomp
    have hg := List.mem_of_getElem? hp
    rw [he] at hg
    have hbound := ((mem_componentOf (g := graph)).mp hg).1
    simp only [hp, Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hbound, Option.getD_some, Option.some.injEq] at hnode
    exact ⟨global, rfl, hnode ▸ List.getElem?_eq_getElem hbound⟩

private theorem r8ag_measured_keys {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {v : Nat} {n : Node}
    (h : e.graph.nodes[v]? = some n) :
    ∃ source, e.graph0.nodes[v]? = some source ∧ source.border = n.border ∧
      source.clusterPath = n.clusterPath ∧ source.decl = n.decl := by
  have hb := (List.getElem?_eq_some_iff.mp h).1
  rw [exactGraph_length e.graph_eq] at hb
  obtain ⟨x, hx, hborder, hpath, hdecl⟩ :=
    exactGraph_node_key e.graph_eq (List.getElem?_eq_getElem hb)
  rw [h] at hx
  cases hx
  exact ⟨_, List.getElem?_eq_getElem hb, hborder.symm, hpath.symm, hdecl.symm⟩

private theorem r8ag_rows_sources {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {k : Nat}
    {rm : ComponentRegions}
    (hrows : rm.clusters = clusterRows inp s (componentCandidateR (some s) e.graph comp k)) :
    (rm.clusters.map (·.decl)).Nodup ∧
    (∀ c ∈ rm.clusters, ∃ source, inp.boxes[c.decl]? = some source ∧ c.id = source.id) ∧
    ∀ {i : Nat} {node : Node},
      (componentCandidateR (some s) e.graph comp k).nodes[i]? = some node →
      node.border = 0 ∨ node.border = -2 ∨ node.border = 2 := by
  let candidate := componentCandidateR (some s) e.graph comp k
  have htop {v : Nat} {n : Node} (hn : candidate.nodes[v]? = some n) (hb : n.border = -2) :
      comp[v]? = some n.decl ∧ ∃ source, inp.boxes[n.decl]? = some source := by
    obtain ⟨j, hj, hjnode⟩ := r8ag_component_global hcomp hn
    obtain ⟨original, ho, hb', _, hd⟩ := r8ag_measured_keys e hjnode
    obtain ⟨hj', source, hsrc, _, _⟩ :=
      measuredGraph_group_origin e.graph0_eq ho (hb'.trans hb)
    rw [hd, List.getElem?_map] at hsrc
    obtain ⟨source, hsource, _⟩ := Option.map_eq_some_iff.mp hsrc
    exact ⟨(hd.symm.trans hj').symm ▸ hj, source, hsource⟩
  refine ⟨r8ag_table_unique hrows ?_, ?_, ?_⟩
  · intro i j a b ha hb hba hbb he
    have hi := (htop ha hba).1
    have hj := (htop hb hbb).1
    have hnd : comp.Nodup := by
      obtain ⟨_, h⟩ := mem_components_eq hcomp
      rw [h]
      exact List.Pairwise.filter _ List.nodup_range
    have hi' := (List.getElem?_eq_some_iff.mp hi).1
    have hj' := (List.getElem?_eq_some_iff.mp hj).1
    exact hnd.eq_of_getElem_eq hi' hj'
      ((List.getElem?_eq_some_iff.mp hi).2.trans
        (he.trans (List.getElem?_eq_some_iff.mp hj).2.symm))
  · intro c hc
    obtain ⟨top, _, ht, hb, hd, hid, _, _⟩ := r8ag_table_entry hrows hc
    obtain ⟨_, source, hsource⟩ := htop ht hb
    rw [hd] at hsource
    exact ⟨source, hsource, by simp [hid, boxId, hsource]⟩
  · intro v node hnode
    obtain ⟨_, _, hglobal⟩ := r8ag_component_global hcomp hnode
    obtain ⟨src, hsrc, hb, _, _⟩ := r8ag_measured_keys e hglobal
    rw [← hb]
    exact (measuredGraph_marker_shape e.graph0_eq hsrc).1

private theorem r8ag_parent_edge {inp : Input} {rm : ComponentRegions}
    (hparents : rm.parents = rm.clusters.map (r8ag_parent_index inp rm.clusters))
    (hsource : ∀ c ∈ rm.clusters, ∃ source, inp.boxes[c.decl]? = some source ∧ c.id = source.id)
    {a b : Nat} {ca cb : RegionCluster} (ha : rm.clusters[a]? = some ca)
    (hb : rm.clusters[b]? = some cb) (h : parentGroup rm b = a) :
    R8agSourceAncestor inp ca.decl cb.decl := by
  obtain ⟨sourceB, hsourceB, _⟩ := hsource cb (List.mem_of_getElem? hb)
  obtain ⟨sourceA, hsourceA, hAID⟩ := hsource ca (List.mem_of_getElem? ha)
  have hbound := (List.getElem?_eq_some_iff.mp ha).1
  have hnotRoot : rm.clusters.length ≠ a := (Nat.ne_of_lt hbound).symm
  unfold parentGroup at h
  rw [hparents, List.getD_eq_getElem?_getD, List.getElem?_map, hb,
    Option.map_some, Option.getD_some] at h
  have hp : boxParent inp cb.decl = sourceB.parent := by simp [boxParent, hsourceB]
  by_cases hzero : sourceB.parent = ""
  · have hroot : r8ag_parent_index inp rm.clusters cb = -1 := by
      simp [r8ag_parent_index, hp, hzero]
    rw [hroot] at h
    simp at h
    exact (hnotRoot h).elim
  · have hindex : r8ag_parent_index inp rm.clusters cb =
      (match rm.clusters.findIdx? (fun c => c.id == sourceB.parent) with
        | some k => (k : Int)
        | none => -1) := by
      unfold r8ag_parent_index
      rw [hp]
      split
      · rename_i he
        exact (hzero he).elim
      · rfl
    rw [hindex] at h
    cases hf : rm.clusters.findIdx? (fun c => c.id == sourceB.parent) with
    | none =>
      simp [hf] at h
      exact (hnotRoot h).elim
    | some k =>
      simp only [hf] at h
      have hk : k = a := by
        change (if 0 ≤ (k : Int) then (k : Int).toNat else rm.clusters.length) = a at h
        rw [ite_eq_left (Int.natCast_nonneg k), Int.toNat_natCast] at h
        exact h
      subst k
      obtain ⟨_, hid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      rw [(List.getElem?_eq_some_iff.mp ha).2, hAID] at hid
      exact .parent hsourceA hsourceB (beq_iff_eq.mp hid).symm hzero

private theorem r8ag_branch_ancestor {inp : Input} {rm : ComponentRegions}
    {rows : List (List Nat)}
    (hchildren : ∀ a b, b ∈ rows.getD a [] →
      b < rm.clusters.length ∧ parentGroup rm b = a)
    (hparents : rm.parents = rm.clusters.map (r8ag_parent_index inp rm.clusters))
    (hsource : ∀ c ∈ rm.clusters, ∃ source, inp.boxes[c.decl]? = some source ∧ c.id = source.id)
    {a b : Nat} (h : RegionGroupBranch rows a b) {ca cb : RegionCluster}
    (ha : rm.clusters[a]? = some ca) (hb : rm.clusters[b]? = some cb) :
    ca.decl = cb.decl ∨ R8agSourceAncestor inp ca.decl cb.decl := by
  have append {i j k : Nat} (hij : R8agSourceAncestor inp i j)
      (hjk : R8agSourceAncestor inp j k) : R8agSourceAncestor inp i k := by
    induction hjk with
    | parent ha hb hp hn => exact .down hij ha hb hp hn
    | down _ ha hb hp hn ih => exact .down ih ha hb hp hn
  induction h generalizing ca with
  | here => exact Or.inl (congrArg RegionCluster.decl (Option.some.inj (ha.symm.trans hb)))
  | @down a m b edge _ ih =>
    obtain ⟨hm, hp⟩ := hchildren a m edge
    have hm' := List.getElem?_eq_getElem (l := rm.clusters) hm
    have hhead := r8ag_parent_edge hparents hsource ha hm' hp
    rcases ih hm' hb with he | htail
    · exact Or.inr (he ▸ hhead)
    · exact Or.inr (append hhead htail)

private theorem r8ag_clusterPort_other {pl : RegionPlacement} {g k v : Nat} {xs ys : List Int}
    (h : clusterPortR pl g k xs = .ok ys) (hk : k ≠ v) :
    ys.getD v 0 = xs.getD v 0 := by
  unfold clusterPortR at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · rw [← Except.ok.inj h, r8ag_setAt_getD, ite_eq_right (fun he => hk he.1.symm)]
  · cases h

private theorem r8ag_ports_at {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper} {v : Nat}
    (h : reservedPortsR pl cg labels xs = .ok (ys, placed))
    (haway : ∀ c ∈ pl.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v) :
    placed.nodes[v]? = pl.p.nodes[v]? ∧ ys.getD v 0 = xs.getD v 0 := by
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hf, hout⟩ := r8ag_bind h
  have hnodes : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hout)).symm
  have hx : ys = out.1 := (congrArg Prod.fst (Except.ok.inj hout)).symm
  rw [hnodes, Array.getElem?_toList, hx, ← List.getElem?_toArray]
  refine r8ag_foldM (fun st : List Int × Array ProperNode =>
     st.2[v]? = pl.p.nodes.toArray[v]? ∧ st.1.getD v 0 = xs.getD v 0) _ _ _ _
    ⟨rfl, rfl⟩ ?_ hf
  intro q hq st st' hs hstep
  obtain ⟨ht, hb⟩ := haway q.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq))
  dsimp only [step] at hstep
  split at hstep
  · cases hstep
  · obtain ⟨x1, hx1, hstep⟩ := r8ag_bind hstep
    obtain ⟨x2, hx2, hstep⟩ := r8ag_bind hstep
    rw [← Except.ok.inj hstep]
    exact ⟨by simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne ht]
      using hs.1, (r8ag_clusterPort_other hx2 hb).trans ((r8ag_clusterPort_other hx1 ht).trans hs.2)⟩

private theorem r8ag_ports_anchor_record {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper} {v : Nat}
    {n : ProperNode} (h : reservedPortsR pl cg labels xs = .ok (ys, placed))
    (hn : pl.p.nodes[v]? = some n) : ∃ out, placed.nodes[v]? = some out ∧
      out.node.border = n.node.border := by
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hf, hout⟩ := r8ag_bind h
  have hnodes : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hout)).symm
  rw [hnodes, Array.getElem?_toList]
  refine r8ag_foldM (fun st : List Int × Array ProperNode =>
      ∃ m, st.2[v]? = some m ∧ m.node.border = n.node.border) _ _ _ _
    ⟨n, by rwa [List.getElem?_toArray], rfl⟩ ?_ hf
  intro q _ st st' hs hstep
  obtain ⟨m, hm, hmb⟩ := hs
  dsimp only [step] at hstep
  split at hstep
  · cases hstep
  · obtain ⟨_, _, hm1⟩ := r8ag_bind hstep
    obtain ⟨_, _, hm2⟩ := r8ag_bind hm1
    rw [← Except.ok.inj hm2]
    change ∃ m', (st.2.set! q.1.top _)[v]? = some m' ∧ m'.node.border = n.node.border
    rw [Array.set!_eq_setIfInBounds]
    by_cases he : q.1.top = v
    · have hv := (Array.getElem?_eq_some_iff.mp hm).1
      rw [he, Array.getElem?_setIfInBounds_self_of_lt hv]
      have ht : st.2.getD v default = m := by
        simp only [Array.getD_eq_getD_getElem?, hm, Option.getD_some]
      rw [ht]
      exact ⟨_, rfl, hmb⟩
    · rw [Array.getElem?_setIfInBounds_ne he]
      exact ⟨m, hm, hmb⟩

private theorem r8ag_fold_pick {α β : Type} (valid : α → Prop) (read : α → Int)
    (f : α → β → α) (chosen : β → Bool) (pick : Int)
    (l : List β) (start : α) (hstart : valid start)
    (hstep : ∀ q ∈ l, ∀ st, valid st → valid (f st q) ∧
      read (f st q) = if chosen q then pick else read st) :
    valid (l.foldl f start) ∧
      read (l.foldl f start) = if l.any chosen then pick else read start := by
  induction l generalizing start with
  | nil => exact ⟨hstart, rfl⟩
  | cons q qs ih =>
    obtain ⟨hgood, hread⟩ := hstep q List.mem_cons_self start hstart
    have ht := ih (f start q) hgood (fun r hr => hstep r (List.mem_cons_of_mem _ hr))
    refine ⟨ht.1, ?_⟩
    rw [List.foldl_cons, ht.2, hread, List.any_cons]
    cases chosen q <;> cases qs.any chosen <;> rfl

private def r8ag_right (pl : RegionPlacement) (alloc : RegionAllocation) (i : Nat) : Int :=
  alloc.lefts.getD i 0 + alloc.widths.getD i 0 - pl.buckets.loopWidth.getD i 0

private def r8ag_marker_step (P : Params) (c : RegionCluster) (left right center : Int)
    (xs : List Int) (q : ProperNode × Nat) : List Int :=
  if q.1.node.clusterPath.getLast? != some c.decl then xs
  else
    match q.1.node.border with
    | -1 => setAt xs q.2 (left + Int.tdiv P.clusterBorderW 2)
    | 1 => setAt xs q.2 (right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
    | 3 => setAt xs q.2 center
    | _ => xs

private def r8ag_frame_step (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (xs : List Int) (q : RegionCluster × Nat) : List Int :=
  let left := alloc.lefts.getD q.2 0
  let right := r8ag_right pl alloc q.2
  let center := left + Int.tdiv (right - left) 2
  let xs := pl.p.nodes.zipIdx.foldl (r8ag_marker_step P q.1 left right center) xs
  setAt (setAt xs q.1.top center) q.1.bottom center

private theorem r8ag_regionFrames_side {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {xs : List Int} {v i : Nat} {n : ProperNode}
    {c : RegionCluster} (hc : pl.rm.clusters[i]? = some c)
    (hunique : (pl.rm.clusters.map (·.decl)).Nodup)
    (hn : pl.p.nodes[v]? = some n) (hv : v < xs.length)
    (hpath : n.node.clusterPath.getLast? = some c.decl)
    (hside : n.node.border = -1 ∨ n.node.border = 1)
    (haway : ∀ c ∈ pl.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v) :
    (regionFrames pl P alloc xs).getD v 0 =
      if n.node.border = -1 then alloc.lefts.getD i 0 + Int.tdiv P.clusterBorderW 2
      else r8ag_right pl alloc i - P.clusterBorderW + Int.tdiv P.clusterBorderW 2 := by
  let pick := if n.node.border = -1 then alloc.lefts.getD i 0 + Int.tdiv P.clusterBorderW 2
    else r8ag_right pl alloc i - P.clusterBorderW + Int.tdiv P.clusterBorderW 2
  let chosen (q : RegionCluster × Nat) : Bool := q.1.decl == c.decl
  have hhit : pl.rm.clusters.zipIdx.any chosen = true :=
    List.any_eq_true.mpr ⟨(c, i), List.mem_zipIdx_iff_getElem?.mpr hc, beq_self_eq_true _⟩
  have h (q : RegionCluster × Nat) (hq : q ∈ pl.rm.clusters.zipIdx)
      (st : List Int) (hst : st.length = xs.length) :
      (r8ag_frame_step pl P alloc st q).length = xs.length ∧
      (r8ag_frame_step pl P alloc st q).getD v 0 =
        if chosen q then pick else st.getD v 0 := by
    let left := alloc.lefts.getD q.2 0
    let right := r8ag_right pl alloc q.2
    let center := left + Int.tdiv (right - left) 2
    let chooseNode (nq : ProperNode × Nat) : Bool := nq.2 == v && chosen q
    have hrecord := List.mem_zipIdx_iff_getElem?.mp hq
    obtain ⟨htop, hbot⟩ := haway q.1 (List.mem_of_getElem? hrecord)
    have hchoose : pl.p.nodes.zipIdx.any chooseNode = chosen q := by
      cases hh : chosen q with
      | false => simp [chooseNode, hh]
      | true =>
        apply List.any_eq_true.mpr
        exact ⟨(n, v), List.mem_zipIdx_iff_getElem?.mpr hn, by simp [chooseNode, hh]⟩
    have hstep (nq : ProperNode × Nat) (hnq : nq ∈ pl.p.nodes.zipIdx)
        (state : List Int) (hstate : state.length = xs.length) :
        (r8ag_marker_step P q.1 left right center state nq).length = xs.length ∧
          (r8ag_marker_step P q.1 left right center state nq).getD v 0 =
            if chooseNode nq then pick else state.getD v 0 := by
      by_cases he : nq.2 = v
      · have hget := List.mem_zipIdx_iff_getElem?.mp hnq
        rw [he, hn] at hget
        have hnode : nq.1 = n := (Option.some.inj hget).symm
        have hb : v < state.length := hstate.symm ▸ hv
        by_cases hd : q.1.decl = c.decl
        · have hi := nodup_map_inj (·.decl) hunique hrecord hc hd
          have hq' : q.1 = c := by
            rw [hi, hc] at hrecord
            exact (Option.some.inj hrecord).symm
          have he' : q = (c, i) := Prod.ext hq' hi
          have hwrite (x : Int) : (setAt state v x)[v]?.getD 0 = x := by
            change (setAt state v x).getD v 0 = x
            rw [r8ag_setAt_getD, ite_eq_left ⟨rfl, hb⟩]
          rcases hside with hs | hs <;>
            simp [r8ag_marker_step, chooseNode, chosen, he, hnode, hpath, hs, he',
              r8ag_setAt_length, hstate, pick, left, right] <;>
            exact hwrite _
        · simp [r8ag_marker_step, chooseNode, chosen, he, hnode, hpath, Ne.symm hd, hd, hstate]
      · have hwrite (x : Int) : (setAt state nq.2 x).length = xs.length ∧
            (setAt state nq.2 x).getD v 0 = state.getD v 0 := by
          rw [r8ag_setAt_length, r8ag_setAt_getD, ite_eq_right (fun hf => he hf.1.symm)]
          exact ⟨hstate, rfl⟩
        simp only [chooseNode, beq_false_of_ne he, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        unfold r8ag_marker_step
        split
        · exact ⟨hstate, rfl⟩
        · split
          · exact hwrite _
          · exact hwrite _
          · exact hwrite _
          · exact ⟨hstate, rfl⟩
    obtain ⟨hlen, hlookup⟩ := r8ag_fold_pick (fun l : List Int => l.length = xs.length)
      (fun l => l.getD v 0) (r8ag_marker_step P q.1 left right center) chooseNode pick
      pl.p.nodes.zipIdx st hst hstep
    unfold r8ag_frame_step
    dsimp only
    simp only [r8ag_setAt_length]
    rw [r8ag_setAt_getD, ite_eq_right (fun hx => hbot hx.1.symm),
      r8ag_setAt_getD, ite_eq_right (fun hx => htop hx.1.symm)]
    rw [hchoose] at hlookup
    exact ⟨hlen, hlookup⟩
  have hout := r8ag_fold_pick (fun l : List Int => l.length = xs.length)
    (fun l => l.getD v 0) (r8ag_frame_step pl P alloc) chosen pick
    pl.rm.clusters.zipIdx xs rfl h
  change (pl.rm.clusters.zipIdx.foldl (r8ag_frame_step pl P alloc) xs).getD v 0 = pick
  exact hout.2.trans (ite_eq_left hhit)

private theorem r8ag_coord_original (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {n : ProperNode} (hn : labeled.nodes[v]? = some n) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[v]? = some m ∧
      m.node.border = n.node.border := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact labeled v
  change (sized.nodes[v]?).map _ = _ at hkeys
  cases hs : sized.nodes[v]? with
  | none => simp [hs, hn] at hkeys
  | some sz =>
    simp only [hs, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkeys
    let t : ProperNode := if sz.node.border == -2 || sz.node.border == 2 then
      { sz with node := { sz.node with w := 0, h := 0 } } else sz
    have ht : titled.nodes[v]? = some t := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some] <;> rfl
    have htitle : t.node.border = sz.node.border := by
      dsimp only [t]
      split <;> rfl
    obtain ⟨_, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hc : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
        some (clearF t) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, hbordered,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht] <;> rfl
    obtain ⟨m, hm, _⟩ := materialize_exists _ hc
    obtain ⟨old, hold, _, hborder, _, _⟩ := materialize_lookup _ hm
    have heq : old = clearF t := Option.some.inj (hold.symm.trans hc)
    subst old
    exact ⟨m, hm, hborder.trans ((clearF_keys t).2.1.trans (htitle.trans hkeys.2.1))⟩

private theorem r8ag_new_side_width (p : Proper) (width : Int)
    (hsrc : ∀ n ∈ p.nodes, ¬ (n.node.border = -1 ∨ n.node.border = 1))
    {n : ProperNode} (hn : n ∈ (OrderImpl.addClusterBorders p width).nodes)
    (hside : n.node.border = -1 ∨ n.node.border = 1) :
    n.node.w = width ∧ n.dummy = false := by
  have hAll : ∀ n ∈ (OrderImpl.addClusterBorders p width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width ∧ n.dummy = false := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv (fun cur : Proper => ∀ n ∈ cur.nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width ∧ n.dummy = false)
    · intro n hm hs
      exact (hsrc n hm hs).elim
    · intro state hstate entry _
      unfold OrderImpl.borderStep
      split
      · exact hstate
      · apply OrderImpl.foldl_inv (fun cur : Proper => ∀ n ∈ cur.nodes,
          n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width ∧ n.dummy = false)
        · exact hstate
        · intro st hst _ _
          intro n hn hs
          have hn' : n ∈ st.nodes ++ [OrderImpl.borderLeft entry width,
              OrderImpl.borderRight entry width] := hn
          rcases List.mem_append.mp hn' with hold | hnew
          · exact hst n hold hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
            rcases hnew with rfl | rfl <;> exact ⟨rfl, rfl⟩
  exact hAll n hn hside

private theorem r8ag_coord_side_width {P : Params} {exact : List Nat} {s : RegionSpec}
    {cg : Graph} {labeled : Proper} (hkeys : NodeKeys cg labeled)
    (hgraph : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n →
      n.border = 0 ∨ n.border = -2 ∨ n.border = 2)
    {v : Nat} {n : ProperNode}
    (hv : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n)
    (hside : n.node.border = -1 ∨ n.node.border = 1) : n.node.w = P.clusterBorderW := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  have hnoSized (a : ProperNode) (ha : a ∈ sized.nodes) :
      a.node.border = 0 ∨ a.node.border = -2 ∨ a.node.border = 2 := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hk := sizeProperPortsX_key P exact labeled i
    change (sized.nodes[i]?).map _ = _ at hk
    cases hj : labeled.nodes[i]? with
    | none => simp [hi, hj] at hk
    | some src =>
      simp only [hi, hj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      rw [hk.2.1]
      rcases hkeys i src hj with ⟨orig, horig, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · rw [hborder]
        exact hgraph horig
      · exact Or.inl hborder
  have hnoTitled (a : ProperNode) (ha : a ∈ titled.nodes) :
      ¬ (a.node.border = -1 ∨ a.node.border = 1) := by
    unfold titled titleReservationsR at ha
    rcases List.mem_append.mp ha with hm | hm
    · obtain ⟨orig, ho, he⟩ := List.mem_map.mp hm
      have hbo := hnoSized orig ho
      have hb : a.node.border = orig.node.border := by
        rw [← he]
        split <;> rfl
      omega
    · obtain ⟨orig, _, he⟩ := List.mem_map.mp hm
      have hb : a.node.border = 3 := by rw [← he]
      omega
  change (materializeDummyPaths (clearProxyExtents bordered)).nodes[v]? = some n at hv
  obtain ⟨nd, hnd, _, hb, _, hun⟩ := materialize_lookup _ hv
  rw [clearProxyExtents_nodes, List.getElem?_map] at hnd
  obtain ⟨b, hbget, hclear⟩ := Option.map_eq_some_iff.mp hnd
  have hbs : b.node.border = -1 ∨ b.node.border = 1 := by
    rw [← hclear] at hb
    rw [hb, (clearF_keys b).2.1] at hside
    exact hside
  obtain ⟨hw, hd⟩ := r8ag_new_side_width titled P.clusterBorderW hnoTitled
    (List.mem_of_getElem? hbget) hbs
  have hcl : clearF b = b := by
    rcases hbs with he | he <;> simp [clearF, he]
  rw [hcl] at hclear
  rw [hun (hclear ▸ hd), ← hclear, hw]

private theorem r8ag_marker_covered {P : Params} {exact : List Nat} {s : RegionSpec}
    {cg candidate : Graph} {labels : List MeasuredLabel} {p labeled : Proper}
    {rm : ComponentRegions} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)} {run : Run}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    {inp : Input} (hrows : rm.clusters = clusterRows inp s candidate)
    (hnd : (rm.clusters.map (·.decl)).Nodup)
    (hnodes : cg.nodes = candidate.nodes)
    (hkeys : NodeKeys cg labeled)
    (horig : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n →
      labeled.nodes[i]? = some ⟨n, false, none, false⟩)
    (hgraph : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n →
      n.border = 0 ∨ n.border = -2 ∨ n.border = 2)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    {q0 : Proper} (hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (q0, run.xs))
    (hdrop : OrderImpl.dropSynthetic q0 = run.proper)
    (hbw : 0 ≤ P.clusterBorderW) {i : Nat} {c : RegionCluster} (hc : rm.clusters[i]? = some c)
    (hwidth : P.clusterBorderW ≤ r8ag_right stages.placement stages.allocation i -
      stages.allocation.lefts.getD i 0) :
    ∀ r ∈ groupBorderRects cg run c.decl,
      stages.allocation.lefts.getD i 0 ≤ r.x ∧
        r.x + r.w ≤ r8ag_right stages.placement stages.allocation i := by
  intro r hr
  unfold groupBorderRects at hr
  obtain ⟨item, hitem, hrect⟩ := List.mem_filterMap.mp hr
  split at hrect
  · rename_i htest
    have hside : item.1.node.border = -1 ∨ item.1.node.border = 1 := by
      simpa using (Bool.and_eq_true_iff.mp htest).1
    have hpath : item.1.node.clusterPath.getLast? = some c.decl :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp htest).2
    let v := item.2
    have hfinal : run.proper.nodes[v]? = some item.1 := List.mem_zipIdx_iff_getElem?.mp hitem
    rw [← hdrop, OrderImpl.dropSynthetic_nodes] at hfinal
    have hpc := proxyWidths_rel hproxy
    have hv : v < run.coordinateProper.nodes.length := by
      rw [← hpc.2.2.1]
      exact (List.getElem?_eq_some_iff.mp hfinal).1
    let n := run.coordinateProper.nodes[v]
    have hn : run.coordinateProper.nodes[v]? = some n := List.getElem?_eq_getElem hv
    obtain ⟨nOut, hnOut, _, hborder, _⟩ := hpc.2.2.2.2.1 v n hn
    have hneq : nOut = item.1 := Option.some.inj (hnOut.symm.trans hfinal)
    have hnotproxy : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by
      rw [hneq] at hborder
      omega
    obtain ⟨hnFinal, hxFinal⟩ := hpc.2.2.2.2.2 v n hn hnotproxy
    have heq : n = item.1 := Option.some.inj (hnFinal.symm.trans hfinal)
    have hsideN : n.node.border = -1 ∨ n.node.border = 1 := by simpa only [heq] using hside
    have hpl : stages.placement.p = p := by rw [stages.hPlacement]
    have hrm : stages.placement.rm = rm := by rw [stages.hPlacement]
    have haway : ∀ cluster ∈ stages.placement.rm.clusters, cluster.top ≠ v ∧ cluster.bottom ≠ v := by
      intro cluster hm
      rw [hrm] at hm
      obtain ⟨_, _, ht, hbt, _, _, hb, hbb⟩ := r8ag_table_entry hrows hm
      have away {k : Nat} {raw : Node} (hk : candidate.nodes[k]? = some raw)
          (hs : raw.border = -2 ∨ raw.border = 2) : k ≠ v := by
        rw [← hnodes] at hk
        obtain ⟨mark, hmark, hmarkB⟩ := r8ag_coord_original P exact s
          (horig hk)
        rw [hcoord, ← hpl] at hmark
        obtain ⟨out, hout, hborder⟩ := r8ag_ports_anchor_record stages.hFramesAndPorts hmark
        intro hkv
        rw [hkv, hn] at hout
        have he := Option.some.inj hout
        have hborderEq : n.node.border = raw.border :=
          (congrArg (fun q : ProperNode => q.node.border) he).trans
            (hborder.trans hmarkB)
        rw [hborderEq] at hsideN
        omega
      exact ⟨away ht (Or.inl hbt), away hb hbb⟩
    obtain ⟨hproper, hportX⟩ := r8ag_ports_at stages.hFramesAndPorts haway
    have hn0 : stages.placement.p.nodes[v]? = some n := hproper.symm.trans hn
    have hn' : p.nodes[v]? = some n := by rwa [hpl] at hn0
    have hnCoord : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n := by
      rw [hcoord]
      exact hn'
    have hmarkerW := r8ag_coord_side_width hkeys hgraph hnCoord hsideN
    have hmarkPath : n.node.clusterPath.getLast? = some c.decl := by
      simpa only [heq] using hpath
    have hshifted : v < stages.shifted.length := by
      obtain ⟨_, _, _, hlen, _⟩ := allocatePl_translation_trace stages.hAllocation
      rw [hlen, CoordsImpl.crossCoordsClusterWith_length stages.hCross]
      exact (List.getElem?_eq_some_iff.mp hn').1
    have hcl : stages.placement.rm.clusters[i]? = some c := by rwa [hrm]
    have hnd' : (stages.placement.rm.clusters.map (·.decl)).Nodup := by rwa [hrm]
    have hframeX := r8ag_regionFrames_side (P := P) (alloc := stages.allocation)
      hcl hnd' hn0 hshifted hmarkPath hsideN haway
    have hX : run.xs.getD v 0 =
        if n.node.border = -1 then stages.allocation.lefts.getD i 0 +
          Int.tdiv P.clusterBorderW 2
        else r8ag_right stages.placement stages.allocation i - P.clusterBorderW +
          Int.tdiv P.clusterBorderW 2 := by
      rw [List.getD_eq_getElem?_getD, hxFinal, Option.getD_some, hportX]
      exact hframeX
    have hfinal' : run.proper.nodes[v]? = some n := by
      rw [heq]
      exact List.mem_zipIdx_iff_getElem?.mp hitem
    rw [← Option.some.inj hrect]
    have hnodeW : RouteImpl.nodeW run.proper v = P.clusterBorderW := by
      unfold RouteImpl.nodeW
      rw [hfinal']
      exact hmarkerW
    have hdiv : Int.fdiv P.clusterBorderW 2 = Int.tdiv P.clusterBorderW 2 :=
      Int.fdiv_eq_tdiv_of_nonneg hbw (by decide)
    change _ ≤ run.xs.getD v 0 - Int.fdiv (RouteImpl.nodeW run.proper v) 2 ∧
      run.xs.getD v 0 - Int.fdiv (RouteImpl.nodeW run.proper v) 2 +
        RouteImpl.nodeW run.proper v ≤ _
    rw [hnodeW, hdiv, hX]
    rcases hsideN with hs | hs
    · rw [ite_eq_left hs]
      omega
    · rw [ite_eq_right (by omega : n.node.border ≠ -1)]
      omega
  · cases hrect

private theorem active_foreign_group_bands {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run}
    {rm : ComponentRegions}
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp index) e.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp index) = .ok (some rm))
    {u v : Nat} {gn fn : Node}
    (hg : cg.nodes[u]? = some gn) (hf : cg.nodes[v]? = some fn)
    (hgtop : gn.border = -2) (hftop : fn.border = -2)
    (hne : gn.decl ≠ fn.decl)
    (hNA : ¬ R8agSourceAncestor inp gn.decl fn.decl)
    (hNB : ¬ R8agSourceAncestor inp fn.decl gn.decl) :
    ∃ alo ahi blo bhi : Int, 0 ≤ ahi ∧ 0 ≤ bhi ∧
      (∀ r ∈ groupBorderRects cg run gn.decl, alo ≤ r.x ∧ r.x + r.w ≤ ahi) ∧
      (∀ r ∈ groupBorderRects cg run fn.decl, blo ≤ r.x ∧ r.x + r.w ≤ bhi) ∧
      (∀ r : Rect, (u, r) ∈ componentTitles e.params cg run → alo ≤ r.x ∧ r.x + r.w ≤ ahi) ∧
      (ahi ≤ blo ∨ bhi ≤ alo) := by
  obtain ⟨_, _, labeled, _, _, _, _, _, hrank, hnorm, hlabels, hcoord, hmin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes := rankEquivalentR_nodes_eq hrank
  obtain ⟨hrows, hparents⟩ := r8ag_resolved_tables hactive
  obtain ⟨hnd, hsrc, hshape⟩ := r8ag_rows_sources e hcomp hrows
  have hu := hg
  have hw := hf
  rw [hnodes] at hu hw
  obtain ⟨a, cA, ha, hda, hwa⟩ := r8ag_table_find_top hrows hu hgtop
  obtain ⟨b, cB, hb, hdb, _⟩ := r8ag_table_find_top hrows hw hftop
  have hchildren := (stages.group_paths (activeRegion_parent_count hactive) hmin).1
  have hab : ¬ RegionGroupBranch stages.placement.children a b := by
    intro h
    have hSource := r8ag_branch_ancestor hchildren hparents hsrc h ha hb
    rw [hda, hdb] at hSource
    exact hSource.elim hne hNA
  have hba : ¬ RegionGroupBranch stages.placement.children b a := by
    intro h
    have hSource := r8ag_branch_ancestor hchildren hparents hsrc h hb ha
    rw [hda, hdb] at hSource
    exact hSource.elim (Ne.symm hne) hNB
  have hBW := checkedParams_clusterBorderW_ge_one e.checked
  have hBW0 : 0 ≤ e.params.clusterBorderW := by omega
  have hpad := (CoordsImpl.crossCoordsClusterWith_spec stages.hCross).2.1
  have hI : 0 ≤ regionInsetOf e.params := by unfold regionInsetOf; omega
  have hslot := componentRunR_slot_pos hrun
  let left (i : Nat) : Int := stages.allocation.lefts.getD i 0
  let right (i : Nat) : Int := r8ag_right stages.placement stages.allocation i
  have hband :
      0 ≤ left a ∧ 0 ≤ left b ∧
      e.params.clusterBorderW ≤ right a - left a ∧
      e.params.clusterBorderW ≤ right b - left b ∧
      (right a ≤ left b ∨ right b ≤ left a) :=
    r8ag_distinct_band stages hactive hmin (Int.le_trans (by decide : (0 : Int) ≤ 1) hslot) hI
      (List.getElem?_eq_some_iff.mp ha).1 (List.getElem?_eq_some_iff.mp hb).1 hab hba
  obtain ⟨hleftA, hleftB, hwidthA, hwidthB, hgap⟩ := hband
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := componentRunR_stages hrun
  have hproxy := hs.hProxy
  rw [← hs.hCoordProper] at hproxy
  have hkeys := addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabels
  have horig {i : Nat} {n : Node} (hn : cg.nodes[i]? = some n) :
      labeled.nodes[i]? = some ⟨n, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hn) rfl
  have hshape' {i : Nat} {n : Node} (hn : cg.nodes[i]? = some n) :
      n.border = 0 ∨ n.border = -2 ∨ n.border = 2 := by
    rw [hnodes] at hn
    exact hshape hn
  have hma := r8ag_marker_covered stages hrows hnd hnodes hkeys horig hshape' hcoord
    hproxy hs.hDrop hBW0 ha hwidthA
  have hmb := r8ag_marker_covered stages hrows hnd hnodes hkeys horig hshape' hcoord
    hproxy hs.hDrop hBW0 hb hwidthB
  rw [hda] at hma
  rw [hdb] at hmb
  have rightNonneg {i : Nat} (hleft : 0 ≤ left i)
      (hwidth : e.params.clusterBorderW ≤ right i - left i) : 0 ≤ right i :=
    Int.le_trans hleft (Int.sub_nonneg.mp (Int.le_trans hBW0 hwidth))
  refine ⟨left a, right a, left b, right b, rightNonneg hleftA hwidthA,
    rightNonneg hleftB hwidthB, hma, hmb, ?_, hgap⟩
  intro r hr
  have hcg : (componentCandidate e.graph comp index).nodes[u]? = some gn := by
    rw [componentCandidate_nodes]
    exact hu
  obtain ⟨_, _, hp⟩ := X_cg_group_box e.graph0_eq e.graph_eq hcg hgtop
  have hlast : gn.clusterPath.getLast? = some cA.decl := by simp [hp, hda]
  have hspan : 0 ≤ stages.allocation.widths.getD a 0 -
      stages.placement.buckets.loopWidth.getD a 0 := by
    dsimp [right, left, r8ag_right] at hwidthA
    omega
  exact stages.active_title_interval e hcomp hrun hactive hrank hnorm hlabels hcoord hmin
    ha hg hlast hwa hspan hr

theorem active_foreign_group_title_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run}
    {rm : ComponentRegions}
    (hcomp : comp ∈ components e.graph)
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp index) e.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp index) = .ok (some rm))
    {u v : Nat} {gn fn : Node}
    (hg : cg.nodes[u]? = some gn) (hf : cg.nodes[v]? = some fn)
    (hgtop : gn.border = -2) (hftop : fn.border = -2)
    (hne : gn.decl ≠ fn.decl)
    (hG : fn.clusterPath.contains gn.decl = false)
    (hF : gn.clusterPath.contains fn.decl = false)
    {raw : Rect} (ht : (u, raw) ∈ componentTitles e.params cg run)
    (width height : Int) (hwidth : width ≤ raw.w) :
    Disjoint (frameRect e.params cg run v) { raw with w := width, h := height } := by
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have heq := rankEquivalentR_nodes_eq hrank
  have global {k : Nat} {n : Node} (hn : cg.nodes[k]? = some n) :
      (componentCandidate e.graph comp index).nodes[k]? = some n := by
    rw [componentCandidate_nodes]
    rwa [heq] at hn
  obtain ⟨_, hgSource, hgPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq (global hg) hgtop
  obtain ⟨_, hfSource, hfPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq (global hf) hftop
  have notAncestor {a b : Nat} {src : ModelBox} {n : Node}
      (hsrc : inp.boxes[b]? = some src)
      (hp : n.clusterPath = Compound.path inp.boxes src ++ [b])
      (hf : n.clusterPath.contains a = false) : ¬ R8agSourceAncestor inp a b := by
    intro h
    have hm := r8ag_ancestor_in_path hwf h hsrc
    have hcontains : n.clusterPath.contains a = true := by
      rw [hp, List.contains_iff_mem]
      exact List.mem_append.mpr (Or.inl hm)
    rw [hf] at hcontains
    cases hcontains
  obtain ⟨_, _, _, _, _, hright, _, hmarkers, htitle, hgap⟩ :=
    active_foreign_group_bands e hcomp hrun hactive hg hf hgtop hftop hne
      (notAncestor hfSource hfPath hG) (notAncestor hgSource hgPath hF)
  obtain ⟨hl, hr⟩ := htitle raw ht
  rw [frameRect_group_span hf hftop]
  by_cases hempty : groupBorderRects cg run fn.decl = []
  · rw [hempty]
    unfold Disjoint Rect.meetsInterior
    simp only [boundsOf, List.foldl_nil]
    omega
  have hmin := boundsOf_minX_ge_of_all hempty (fun r hm => (hmarkers r hm).1)
  have hmax := boundsOf_right_le_of_all hright (fun r hm => (hmarkers r hm).2)
  apply rect_disjoint_of_x
  dsimp only
  rcases hgap with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem r8a_selected_groups_xgap {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {g b : Box}
    (hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (pair : R8a_SelectedPair execution g b)
    (hg : pair.uNode.border = -2) (hb : pair.wNode.border = -2) :
    R8a_OverlapRowsXGap (frameRect execution.params pair.selected.cg pair.selected.run pair.u)
      (frameRect execution.params pair.selected.cg pair.selected.run pair.w) := by
  obtain ⟨_, _, _, _, _, rm, hactive, _, _, _, _, _, _⟩ := r8ag_selected_region pair
  have hpart := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem hpart
  obtain ⟨hNA, hNB⟩ := r8ag_selected_not_nested hwf pair hg hb
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  obtain ⟨_, _, _, _, ha, hb', hma, hmb, _, hgap⟩ :=
    active_foreign_group_bands execution hcomp hrun hactive pair.group_node pair.peer_node
      hg hb pair.decl_ne hNA hNB
  exact r8ag_hull_gap pair.group_node pair.peer_node hg hb ha hb' hma hmb hgap

end Elegant.Layered.PipelineImpl