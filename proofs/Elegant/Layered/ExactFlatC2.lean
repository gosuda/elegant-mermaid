import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.RecursiveBLiftsA
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- `mapM` preserves length on success (copy of the flat helper, which is private). -/
private theorem X_mapM_ok_len {err α β : Type} (f : α → Except err β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

/-- Packed shelf boxes keep the declaring part dims (copy of the flat helper). -/
private theorem X_pack_box_dims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {k : Nat} (hk : k < out.boxes.length) (hik : k < items.length) :
    out.boxes[k].w = items[k].width ∧ out.boxes[k].h = items[k].height := by
  have hd := Pack.pack_dimensions h
  unfold Pack.dimensions at hd
  have h1 := congrArg (fun l => l[k]?) hd
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hik] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact h1

/-- An exclusive source box of a successful exact execution is a border-0 node. -/
private theorem X_exclusive_source_border_zero {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hlinesLen : execution.lines.length = inp.boxes.length)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hex : source.exclusive = true) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hrole : source.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hex
  have hkeyLen : key < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hkeyLen, rfl⟩
  obtain ⟨node0, hnode0, hborder0⟩ :=
    measuredGraph_exclusive_node_border_zero execution.checked
      execution.graph0_eq hline hsource hrole
  obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode0
  exact ⟨node, hnode, hborder.trans hborder0⟩

/-- Exact proper nodes transfer unchanged for non-proxy borders. -/
private theorem X_plain_node_dims {P : Params} {exact : List Nat}
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

/-- Non-proxy exact coordinate nodes transfer to the proper run unchanged. -/
private theorem X_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Exact original plain nodes keep their measured widths as lower bounds. -/
private theorem X_original_plain_record {P : Params} {exact : List Nat}
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
  have hproper := X_plain_node_dims h hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
 private def X_proj (n : Node) : Nat × Int × List Nat := (n.decl, n.border, n.clusterPath)
 
 private theorem X_projMap {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
     List.map X_proj execution.graph.nodes =
       List.map X_proj execution.graph0.nodes := by
   have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
     exactGraph_length execution.graph_eq
   apply List.ext_getElem?
   intro v
   rw [List.getElem?_map, List.getElem?_map]
   cases h0 : execution.graph0.nodes[v]? with
   | none =>
     have hnone : execution.graph.nodes[v]? = none := by
       rw [List.getElem?_eq_none_iff] at h0 ⊢
       omega
     rw [hnone]
   | some nd0 =>
     obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq h0
     rw [hnd']
     simp only [Option.map_some, X_proj, hnb, hnap, hnd]
 
 private theorem X_revKey {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
     {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
     ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
       nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
   have hmap := X_projMap execution
   have h1 : (List.map X_proj execution.graph.nodes)[v]? = some (X_proj nd) := by
     simp only [List.getElem?_map, h, Option.map_some]
   rw [hmap] at h1
   rw [List.getElem?_map] at h1
   obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
   simp only [X_proj, Prod.mk.injEq] at hproj
   exact ⟨nd0, hnd0, hproj.1, hproj.2.1, hproj.2.2⟩
 
 
 private theorem X_ranked_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run) :
     ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
       rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
       normalize cg rr.ranks = .ok normalized ∧
       Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
       coordinateGraphX P exact labeled = run.coordinateProper ∧
       ∀ edge ∈ (Compound.rankingGraph cg).edges,
         edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
   unfold componentRunX at h
   obtain ⟨rr, hrr, h⟩ := bind_ok h
   obtain ⟨normalized, hn, h⟩ := bind_ok h
   obtain ⟨labeled, hl, h⟩ := bind_ok h
   obtain ⟨ord, _, h⟩ := bind_ok h
   obtain ⟨xs, _, h⟩ := bind_ok h
   obtain ⟨routed, _, h⟩ := bind_ok h
   obtain ⟨lanes, _, h⟩ := bind_ok h
   obtain ⟨yt, _, h⟩ := bind_ok h
   obtain ⟨shifted, _, h⟩ := bind_ok h
   obtain ⟨routes, _, h⟩ := bind_ok h
   have heq := Except.ok.inj h
   subst run
   refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
   apply rank_feasible (Compound.rankingGraph cg) rr.ranks
   simp only [RankImpl.rank, hrr]
 
 private theorem X_cgShape {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
     CgShape execution.graph := by
   have hshape := measuredGraph_shape execution.graph0_eq
   refine ⟨?_, ?_⟩
   · intro a b na nb ha hb h1 h2 hp
     obtain ⟨na0, ha0, _, hb1, hp1⟩ := X_revKey execution ha
     obtain ⟨nb0, hb0, _, hb2, hp2⟩ := X_revKey execution hb
     exact hshape.1 a b na0 nb0 ha0 hb0 (by rw [hb1]; exact h1) (by rw [hb2]; exact h2)
       (by rw [hp1, hp2]; exact hp)
   · intro n hn
     obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hn
     obtain ⟨n0, h0, _, hb, _⟩ := X_revKey execution hv
     have h3 := hshape.2 n0 (List.mem_of_getElem? h0)
     rw [hb] at h3
     exact h3
 
 private theorem X_marker_shape {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
     {comp : List Nat} {candidate index : Nat} {node : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
     (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
       (node.border = -2 → node.clusterPath ≠ []) := by
   by_cases hplain : node.border = 0
   · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
   · obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hnode hplain
     obtain ⟨member0, hmember0, _, hborder, hpath⟩ := X_revKey execution hsource
     obtain ⟨hdisj, hne⟩ := measuredGraph_marker_shape execution.graph0_eq hmember0
     refine ⟨?_, ?_⟩
     · rcases hdisj with h0 | h2 | h2
       · exact Or.inl (hborder.symm.trans h0)
       · exact Or.inr (Or.inl (hborder.symm.trans h2))
       · exact Or.inr (Or.inr (hborder.symm.trans h2))
     · intro hgroup
       have h0 : member0.border = -2 := hborder.trans hgroup
       rw [← hpath]
       exact hne h0
 
 /-- `sizeProperPortsX` preserves the node count. -/
 private theorem X_sized_length (P : Params) (exact : List Nat) (p : Proper) :
     (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
   unfold sizeProperPortsX
   simp
 
 private theorem X_titled_alignment (P : Params) (exact : List Nat) {source : Proper}
     (h : source.nodes.length = source.rank.length) :
     (titleReservations (sizeProperPortsX P exact source)).nodes.length =
       (titleReservations (sizeProperPortsX P exact source)).rank.length := by
   rw [titleReservations_nodes]
   simp only [List.length_append, List.length_map, X_sized_length]
   have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
       source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
         (fun entry => rk source.rank entry.2) := by
     unfold titleReservations titleNodes sizeProperPortsX
     rfl
   rw [hrank]
   simp only [List.length_append, List.length_map]
   omega
 
 private theorem X_coordinate_alignment {P : Params} {exact : List Nat} {cg : Graph}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run) :
     ∃ labeled : Proper, coordinateGraphX P exact labeled = run.coordinateProper ∧
       NodeKeys cg labeled ∧ labeled.nodes.length = labeled.rank.length ∧
       (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
         (titleReservations (sizeProperPortsX P exact labeled)).rank.length := by
   obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := X_ranked_source h
   have haligned : labeled.nodes.length = labeled.rank.length := by
     rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
     exact (normalize_node_rank_alignment hn).1
   exact ⟨labeled, hc, addLabelNodes_keys _ _ _ (normalize_keys hn) hl,
     haligned, X_titled_alignment P exact haligned⟩
 
 private theorem X_sized_origin (P : Params) (exact : List Nat) (source : Proper)
     {index : Nat} {node : ProperNode}
     (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
     ∃ original : ProperNode, source.nodes[index]? = some original ∧
       node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
       node.node.clusterPath = original.node.clusterPath := by
   have hkey := sizeProperPortsX_key P exact source index
   rw [hnode] at hkey
   cases horiginal : source.nodes[index]? with
   | none => simp [horiginal] at hkey
   | some original =>
       simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
       exact ⟨original, rfl, hkey⟩
 private theorem X_titled_origin {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
     (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
     (hnode : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some node) :
     (∃ original : ProperNode, source.nodes[index]? = some original ∧
       node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
       node.node.clusterPath = original.node.clusterPath) ∨
     (node.dummy = false ∧ node.node.border = 3) := by
   rw [titleReservations_nodes] at hnode
   by_cases hi : index < (sizeProperPortsX P exact source).nodes.length
   · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
       List.getElem?_map] at hnode
     obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
     obtain ⟨original, horiginal, hd, hb, hp⟩ :=
       X_sized_origin P exact source hsized
     have ht := titleF_keys sized
     rw [heq] at ht
     exact Or.inl ⟨original, horiginal, ht.1.trans hd,
       ht.2.1.trans hb, ht.2.2.1.trans hp⟩
   · rw [List.getElem?_append_right (by
       simpa only [List.length_map] using Nat.le_of_not_gt hi),
       List.getElem?_map] at hnode
     obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
     obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
     obtain ⟨original, horiginal, hd, hb, _⟩ :=
       X_sized_origin P exact source hsized
     have hreal : original.dummy = false := by
       rcases hkeys entry.2 original horiginal with
         ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
       · exact hreal
       · rw [hplain] at hb
         omega
     right
     rw [← heq]
     exact ⟨hd.trans hreal, rfl⟩
 
 /-- Exact bordered-graph node classification. -/
 private theorem X_coordinateGraph0_lookup (P : Params) (exact : List Nat)
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
   have hlen := X_sized_length P exact p
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
 /-- One `extra` step preserves length and nonnegativity. -/
 private theorem X_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
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
 /-- Generic fold preservation for length and nonnegativity. -/
 private theorem X_foldl_preserves (step : List Int → (Node × Nat) → List Int)
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
 
 /-- The concrete `extra` step preserves length and nonnegativity (inlined `let`s). -/
 private theorem X_extra_step_concrete (cg : Graph) (exact : List Nat)
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
      obtain ⟨hlen', hpos'⟩ := X_extra_step_preserves acc _ _ hpos
      exact ⟨hlen'.trans hlen, hpos'⟩
 
 private theorem X_border_record {P : Params} {exact : List Nat} {cg : Graph}
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
 
 /-- Exact titled border readiness. -/
 private theorem X_titled_border_ready {cg : Graph} {P : Params} {exact : List Nat}
     {source : Proper}
     (hkeys : NodeKeys cg source) (hshape : CgShape cg)
     (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
       (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
         (node.border = -2 → node.clusterPath ≠ []))
     (haligned : source.nodes.length = source.rank.length) :
     OrderImpl.BorderConstructionReady
       (titleReservations (sizeProperPortsX P exact source)) := by
   refine ⟨?_, ?_, ?_, X_titled_alignment P _ haligned, ?_⟩
   · intro node hnode
     obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
     rcases X_titled_origin hkeys hindex with
       ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
     · rcases hkeys index original horiginal with
         ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
       · have hc := (hmarkers index before hbefore).1
         rw [hb, hborder]
         rcases hc with hc | hc | hc <;> omega
       · rw [hb, hborder]
         exact ⟨by decide, by decide⟩
     · rw [hb]
       exact ⟨by decide, by decide⟩
   · intro node hnode hgroup
     obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
     rcases X_titled_origin hkeys hindex with
       ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
     · rcases hkeys index original horiginal with
         ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
       · have hbeforeGroup : before.border = -2 := by omega
         rw [hp, hpath]
         exact (hmarkers index before hbefore).2 hbeforeGroup
       · omega
     · omega
   · intro a b na nb ha hb hgroupA hgroupB hpath
     rcases X_titled_origin hkeys ha with
       ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
     · rcases X_titled_origin hkeys hb with
         ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
       · apply labeled_topUnique hkeys hshape hoa hob
         · omega
         · omega
         · rw [← hpa, ← hpb]
           exact hpath
       · omega
     · omega
   · intro node hnode hdummy
     obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
     rcases X_titled_origin hkeys hindex with
       ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
     · rcases hkeys index original horiginal with
         ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
       · rw [hreal] at hd
         rw [hd] at hdummy
         cases hdummy
       · exact hb.trans hplain
     · rw [hd] at hdummy
       cases hdummy
 /-- Exact prepared titled source. -/
 private theorem X_prepared_titled_source {exactIds : List String} {inp : Input}
     {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRunX execution.params (exactDecls exactIds inp)
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run) :
     ∃ (rr : RankImpl.RankResult) (labeled : Proper),
       rankWithBudget (Compound.rankingGraph
         (componentCandidate execution.graph comp candidate)) = .ok rr ∧
       coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
         run.coordinateProper ∧
       NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
       OrderImpl.BorderConstructionReady (titleReservations
         (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
       (∀ (index : Nat) (node : Node),
         (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
           labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
       (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
         labeled.rank[index]? = some rank) := by
   obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := X_ranked_source hrun
   have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
   have haligned : labeled.nodes.length = labeled.rank.length := by
     rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
     exact (normalize_node_rank_alignment hn).1
   have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
     (X_cgShape execution) candidate
   have hready := X_titled_border_ready (P := execution.params)
     (exact := exactDecls exactIds inp) hk hshape
     (fun _ _ hnode => X_marker_shape execution hnode) haligned
   refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_⟩
   · intro index node hnode
     exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
   · intro index rank hrank
     rw [(Labels.addLabelNodes_metadata hl).2.1]
     exact normalize_rank_record hn hrank
 
 
 /-- Exact coordinate-graph node classification. -/
 private theorem X_coordinateGraph_lookup (P : Params) (exact : List Nat)
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
   obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
   rcases X_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
     ⟨i, q, hq, hv, h1, h2, h3⟩
   · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
     · have : m1.dummy = false := by rw [h1]; exact hf
       rw [hnd this]
       exact h3
     · rw [hh]
       exact h4 (by rw [← hb]; exact hbd)
   · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
   · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
     have : m1.dummy = false := by rw [h1]; exact hf
     rw [hnd this]
     exact h3

/-- Exact proxy frames are flat: a `±2` node of `coordinateGraphX` has height 0. -/
private theorem X_pc_frame_flat {P : Params} {exact : List Nat} {labeled : Proper}
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hb : nd.node.border = -2 ∨ nd.node.border = 2) : nd.node.h = 0 := by
  rcases X_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, _, _, hf⟩ | ⟨_, h1⟩ |
    ⟨i, q, hq, _, _, h1, _⟩
  · exact hf hb
  · omega
  · omega

/-- Exact coordinate record: every proper node has the same border and height
in the coordinate run, and the same cluster path when non-proxy. -/
private theorem X_fbs_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', -, hb', hh'⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [← hdrop]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  refine ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm, ?_⟩
  intro hnp
  obtain ⟨hfull, -⟩ := X_nonproxy_record hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

/-- Exact pre-reserve coordinates: unfold one `componentRunX` to expose the
rank-axis output, the proxy `ys`, and the `reserveExactRanks` equation that
produces the final `run.ys`/`run.top`. -/
private theorem X_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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

/-- Exact pre-reserve band fact: every proper node lies in its rank band for
the proxy `ys` and pre-reserve `top`. Mirrors `fbs_run_node_band`. -/
private theorem X_pre_band {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {y_pre top_pre ys_pre : List Int}
    (hry : rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre))
    (hyspre : proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre) :
    ∀ v, v < run.coordinateProper.nodes.length →
      top_pre.getD (rk run.coordinateProper.rank v).toNat 0 ≤ ys_pre.getD v 0 ∧
        ys_pre.getD v 0 + CoordsImpl.nodeH run.coordinateProper v ≤
          top_pre.getD (rk run.coordinateProper.rank v).toNat 0 +
            CoordsImpl.layerHeight run.coordinateProper
              (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
  obtain ⟨_, _, _, _, _, _, hcoord, _, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  have hflat : ∀ (v : Nat) (nvc : ProperNode), run.coordinateProper.nodes[v]? = some nvc →
      (nvc.node.border = -2 ∨ nvc.node.border = 2) → nvc.node.h = 0 := by
    intro v nvc hrec hb
    exact X_pc_frame_flat (by rw [hcoord]; exact hrec) hb
  obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
  have hcyLen : y_pre.length = run.coordinateProper.nodes.length := by
    rw [hy]; simp
  intro v hv
  have hvP : v < run.proper.nodes.length := by omega
  obtain ⟨nvp, hrec⟩ : ∃ nvp : ProperNode, run.proper.nodes[v]? = some nvp :=
    ⟨_, List.getElem?_eq_getElem hvP⟩
  have hvC : v < run.coordinateProper.nodes.length := hv
  have hvY : v < y_pre.length := by omega
  obtain ⟨nvc, hnc, hborderEq, hhEq, -⟩ := X_fbs_coordinate_record hrun hrec
  obtain ⟨lv, hly, hvIn, hrknn⟩ := hcov v hvP
  rw [hrankEq] at hrknn
  have hrkC : rk run.coordinateProper.rank v =
      ((rk run.coordinateProper.rank v).toNat : Int) := by omega
  have hlyC : run.layers[(rk run.coordinateProper.rank v).toNat]? = some lv := by
    rw [← hrankEq]; exact hly
  have hlyD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
    rw [List.getD_eq_getElem?_getD, hlyC]
    rfl
  have hnodeH : CoordsImpl.nodeH run.coordinateProper v = nvc.node.h := by
    simp only [CoordsImpl.nodeH, hnc]
  rw [← hyspre, proxyYs_getD run.coordinateProper run.layers top_pre
    y_pre hnc hvY]
  by_cases hb2 : nvc.node.border = -2 ∨ nvc.node.border = 2
  · have hnvcH : nvc.node.h = 0 := hflat v nvc hnc hb2
    have hlh : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lv :=
      CoordsImpl.layerHeight_nonneg _ _
    rcases hb2 with hb | hb
    · have hbeqT : (nvc.node.border == -2) = true := by rw [hb]; simp
      simp only [hbeqT, ↓reduceIte]
      rw [hlyD, hnodeH, hnvcH]
      constructor <;> omega
    · have hbeqF : (nvc.node.border == -2) = false := by rw [hb]; simp
      have hbeqT : (nvc.node.border == 2) = true := by rw [hb]; simp
      simp only [hbeqF, ↓reduceIte, hbeqT, ↓reduceIte]
      rw [hlyD, hnodeH, hnvcH]
      constructor <;> omega
  · obtain ⟨hrecFull, -⟩ := X_nonproxy_record hrun hnc hb2
    have hnvp : nvp = nvc := Option.some.inj (hrec.symm.trans hrecFull)
    have hf1 : (nvc.node.border == -2) = false := by
      cases hc : nvc.node.border == -2 with
      | true => exact absurd (Or.inl (beq_iff_eq.mp hc)) hb2
      | false => rfl
    have hf2 : (nvc.node.border == 2) = false := by
      cases hc : nvc.node.border == 2 with
      | true => exact absurd (Or.inr (beq_iff_eq.mp hc)) hb2
      | false => rfl
    simp only [hf1, hf2]
    rw [hnodeH, hlyD]
    have hnH2 : CoordsImpl.nodeH run.coordinateProper v = nvc.node.h := by
      simp only [CoordsImpl.nodeH, hnc]
    have hband := CoordsImpl.rankAxis_node_in_band hry hlyC hvIn hvC hrkC
    rw [hnH2] at hband
    exact hband

/-- The `extra` fold preserves length and nonnegativity. -/
private theorem X_extra_fold (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
    let extra := cg.nodes.zipIdx.foldl (fun (acc : List Int) (q : Node × Nat) =>
      if !exact.contains q.1.decl then acc
      else
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        if sizes.isEmpty then acc
        else
          let rank := (p.rank.getD q.2 0).toNat
          let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
          let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - heights.getD rank 0
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
    exact X_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
  have h := X_foldl_preserves (fun (acc : List Int) (q : Node × Nat) =>
    if !exact.contains q.1.decl then acc
    else
      let sizes := loopSizes cg.edges labels q.2 cg.slot
      if sizes.isEmpty then acc
      else
        let rank := (p.rank.getD q.2 0).toNat
        let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
        let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - heights.getD rank 0
        acc.set rank (max (acc.getD rank 0) needed)) top.length hstep
    cg.nodes.zipIdx (List.replicate top.length (0 : Int)) hbase hbasePos
  exact h

private theorem X_pairwise_getD_le {l : List Int} (hp : l.Pairwise (· ≤ ·))
    {i j : Nat} (hij : i < j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := by omega
  have hgi : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  have hgj : l[j]? = some l[j] := List.getElem?_eq_getElem hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hgi, hgj]
  simp only [Option.getD_some]
  exact hp.rel_getElem_of_lt hi hj hij

/-- Prefix sums stay pairwise nondecreasing when the folded elements are
nonnegative and the seed list is nondecreasing below the seed sum. -/
private theorem X_prefix_pairwise (es : List Int) (hpos : ∀ e ∈ es, 0 ≤ e)
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

/-- Prefix-sum length. -/
private theorem X_prefix_length (es : List Int) (s : Int) (out : List Int) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
      out.length + es.length := by
  induction es generalizing s out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

/-- Shift transfer: if `(ys, top)` satisfy the band facts and `shifts` is a
nondecreasing prefix-sum vector shifting each rank uniformly, then the
shifted `(ys', top')` satisfy them too. -/
private theorem X_shift_transfer {p : Proper} {layers : List (List Nat)}
    {ys top : List Int} {extra shifts : List Int} {ys' top' : List Int}
    (hin : ∀ (v : Nat), v < p.nodes.length →
      top.getD (p.rank.getD v 0).toNat 0 ≤ ys.getD v 0 ∧
      ys.getD v 0 + CoordsImpl.nodeH p v ≤
        top.getD (p.rank.getD v 0).toNat 0 +
          CoordsImpl.layerHeight p (layers.getD (p.rank.getD v 0).toNat []))
    (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top.getD r 0 + CoordsImpl.layerHeight p l ≤ top.getD r' 0)
    (hextraLen : extra.length = top.length)
    (hpos : ∀ e ∈ extra, 0 ≤ e)
    (hshifts : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (htopLen : top.length = layers.length)
    (hysLen : ys.length = p.nodes.length)
    (htop : ∀ (r : Nat), r < top.length → top'.getD r 0 = top.getD r 0 + shifts.getD r 0)
    (hys : ∀ (j : Nat), j < ys.length →
      ys'.getD j 0 = ys.getD j 0 + shifts.getD ((p.rank.getD j 0).toNat) 0) :
    (∀ (r : Nat) (l : List Nat) (v : Nat), layers[r]? = some l → v ∈ l →
      v < p.nodes.length → rk p.rank v = (r : Int) →
      top'.getD r 0 ≤ ys'.getD v 0 ∧
      ys'.getD v 0 + CoordsImpl.nodeH p v ≤ top'.getD r 0 + CoordsImpl.layerHeight p l) ∧
    (∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l → layers[r']? = some l' →
      top'.getD r 0 + CoordsImpl.layerHeight p l ≤ top'.getD r' 0) := by
  have hshiftsLen : shifts.length = top.length := by
    rw [hshifts, X_prefix_length]
    simp [hextraLen]
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hshifts]
    exact X_prefix_pairwise extra hpos 0 [] (by simp) (by simp)
  have hmono : ∀ i j, i < j → j < shifts.length →
      shifts.getD i 0 ≤ shifts.getD j 0 :=
    fun i j hij hj => X_pairwise_getD_le hpair hij hj
  constructor
  · intro r l v hly hvIn hltP hrk
    have hrTop : r < top.length := by
      rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
    have hvYs : v < ys.length := by rw [hysLen]; exact hltP
    have hrv : (p.rank.getD v 0).toNat = r := by
      have h2 : p.rank.getD v 0 = (r : Int) := hrk
      rw [h2]
      simp
    have h1 := hin v hltP
    have hll : layers.getD (p.rank.getD v 0).toNat [] = l := by
      rw [hrv, List.getD_eq_getElem?_getD, hly]
      rfl
    rw [hll, hrv] at h1
    have hlo : top.getD r 0 ≤ ys.getD v 0 := h1.1
    have hhi : ys.getD v 0 + CoordsImpl.nodeH p v ≤
        top.getD r 0 + CoordsImpl.layerHeight p l := h1.2
    have e1 := htop r hrTop
    have e2 := hys v hvYs
    rw [hrv] at e2
    rw [e1, e2]
    constructor <;> omega
  · intro r r' l l' hlt hly hly'
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

/-- Residual, exact reserved rank bands: for a successful `componentRunX`,
the reserved `run.top`/`run.ys` keep every layered node in its rank band
and keep distinct rank bands disjoint. This is the one-phase exact
counterpart of `rankAxis_node_in_band` + `rankAxis_bands_disjoint`,
stated over the reserved coordinates that `reserveExactRanks` produces.
It holds for executed exact layouts because `reserveExactRanks` shifts
each rank's `top`/`ys` entries by nondecreasing prefix sums, so in-band
inclusions survive and gaps only grow. -/
def X_ReserveBands (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run →
    (∀ (r : Nat) (l : List Nat) (v : Nat), run.layers[r]? = some l → v ∈ l →
      v < run.coordinateProper.nodes.length → rk run.coordinateProper.rank v = (r : Int) →
      run.top.getD r 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + CoordsImpl.nodeH run.coordinateProper v ≤
        run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l) ∧
    (∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l ≤
        run.top.getD r' 0)

/-- The reserved rank bands hold: `X_ReserveBands` is true. Pre-reserve bands
come from `X_pre_band` + `rankAxis_bands_disjoint`; `reserveExactRanks` shifts
each rank uniformly by nondecreasing prefix sums, so inclusions survive and
gaps only grow (`X_shift_transfer`). -/
theorem X_ReserveBands_holds (exactIds : List String) : X_ReserveBands exactIds := by
  intro P inp cg run labels orderOptions hrun
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := X_run_pre hrun
  have hin := X_pre_band hrun hry hyspre
  have hdisjPre : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      top_pre.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l ≤
        top_pre.getD r' 0 :=
    fun r r' l l' hlt hly hly' => CoordsImpl.rankAxis_bands_disjoint hry r r' l l' hlt hly hly'
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  have hylen : y_pre.length = run.coordinateProper.nodes.length :=
    (CoordsImpl.rankCoordsWith_length hry).1
  have hysLen : ys_pre.length = run.coordinateProper.nodes.length := by
    rw [← hyspre]
    unfold proxyYs
    rw [List.length_map, List.length_zipIdx]
    exact hylen
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htopM, h1⟩ := bind_ok hreserve
  obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
  have hpair := Except.ok.inj h2
  have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
  have hysNew_eq : ysNew = run.ys := congrArg Prod.fst hpair
  rw [htopNew_eq] at htopM
  rw [hysNew_eq] at hysM
  have hextra := X_extra_fold cg (exactDecls exactIds inp) labels run.coordinateProper
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
  have hshiftsLen : ((cg.nodes.zipIdx.foldl
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
      (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.length =
      top_pre.length := by
    rw [X_prefix_length, hextra.1]
    simp
  have hpairW : ((cg.nodes.zipIdx.foldl
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
      (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.Pairwise
      (· ≤ ·) :=
    X_prefix_pairwise _ hposM 0 [] (by simp) (by simp)
  have htop_eq : ∀ (r : Nat), r < top_pre.length → run.top.getD r 0 =
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
  have hys_eq : ∀ (j : Nat), j < ys_pre.length →
      run.ys.getD j 0 = ys_pre.getD j 0 +
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
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD
          ((run.coordinateProper.rank.getD j 0).toNat) 0 := by
    intro j hj
    have hjZ : j < (ys_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hj
    have hzin : (ys_pre.zipIdx)[j]? = some (ys_pre[j], j) := by
      have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ hysM
    obtain ⟨b, hb, hbr⟩ := hidx j _ hzin
    have hbeq : b = ys_pre[j] +
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
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD
          ((run.coordinateProper.rank.getD j 0).toNat) 0 :=
      Measure.checkedI32_ok hb
    have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
    have e3 : ys_pre.getD j 0 = ys_pre[j] := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    have e4 : run.ys.getD j 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq
  exact X_shift_transfer hin hdisjPre hextra.1 hposM rfl htopLen hysLen htop_eq hys_eq
 
 /-- Exact coordinate titles are unique per cluster path. -/
 private theorem X_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
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
     rcases X_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
       ⟨i, q, hq, hv, hqd, _, h4⟩
     · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
       · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
       · rw [hb] at h1; omega
     · omega
     · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
       have hk := sizeProperPortsX_key P exact labeled q.2
       rw [hs] at hk
       cases hp : labeled.nodes[q.2]? with
       | none => simp [hp] at hk
       | some mp =>
         simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
         obtain ⟨hk1, hk2, _⟩ := hk
         rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
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
 
 /-- Exact ordered intervals for non-proxy nodes. -/
 private theorem X_nonproxy_ordered_intervals {exactIds : List String}
     {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRunX execution.params (exactDecls exactIds inp)
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run)
     {layer : List Nat} (hlayer : layer ∈ run.layers)
     {i j a b : Nat} {first second : ProperNode}
     (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
     (hfirst : run.coordinateProper.nodes[a]? = some first)
     (hsecond : run.coordinateProper.nodes[b]? = some second)
     (hfirstBorder : ¬(first.node.border = -2 ∨ first.node.border = 2))
     (hsecondBorder : ¬(second.node.border = -2 ∨ second.node.border = 2)) :
     RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
       RouteImpl.leftOf run.proper run.xs b := by
   obtain ⟨_, _, _, hcoordinate, hkeys, _, _, _⟩ :=
     X_prepared_titled_source execution hcomp hrun
   have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
     (X_cgShape execution) candidate
   have huniq : ∀ (u v : Nat) (left right : ProperNode),
       run.coordinateProper.nodes[u]? = some left →
       run.coordinateProper.nodes[v]? = some right →
       left.node.border = 3 → right.node.border = 3 →
       left.node.clusterPath = right.node.clusterPath → u = v := by
     intro u v left right hleft hright hleftBorder hrightBorder hpath
     apply X_pc_title_unique hkeys hshape
       (by rw [hcoordinate]; exact hleft)
       (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
   obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRunX_spec hrun
   have hsep := cluster_all_pairs_separated hcross huniq layer hlayer i j a b
     first second hij ha hb hfirst hsecond
     (by omega) (by omega) (by omega) (by omega)
   obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
   obtain ⟨hfinalFirst, hxa⟩ := X_nonproxy_record hrun hfirst hfirstBorder
   obtain ⟨hfinalSecond, hxb⟩ := X_nonproxy_record hrun hsecond hsecondBorder
   have hwa : RouteImpl.nodeW run.proper a =
       RouteImpl.nodeW run.coordinateProper a := by
     simp only [RouteImpl.nodeW, hfinalFirst, hfirst]
   have hwb : RouteImpl.nodeW run.proper b =
       RouteImpl.nodeW run.coordinateProper b := by
     simp only [RouteImpl.nodeW, hfinalSecond, hsecond]
   have hga : RouteImpl.nodeW run.coordinateProper a ≤
       CoordsImpl.nodeW run.coordinateProper a := CoordsImpl.nodeW_ge_width _ _
   have hgb : RouteImpl.nodeW run.coordinateProper b ≤
       CoordsImpl.nodeW run.coordinateProper b := CoordsImpl.nodeW_ge_width _ _
   have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
     fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
   unfold CoordsImpl.coordSep at hsep
   simp only [e] at hsep
   simp only [RouteImpl.leftOf, RouteImpl.xAt, hxa, hxb, hwa, hwb, e]
   omega
 
 /-- For one executed exact part at pack index `k`: frames are contained. -/
 private theorem X_part_packed_frame
     {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     (packed : Pack.State)
     (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun part =>
         ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
     {k : Nat} {part : List Nat × Part}
     (hk : execution.componentsAcc.parts[k]? = some part)
     (hkLen : k < packed.boxes.length) :
     ∃ candidate run loops,
       componentRunX execution.params (exactDecls exactIds inp)
         (componentCandidate execution.graph part.1 candidate) execution.measured
         (candidateOrder candidate) = .ok run ∧
       (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
         packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y
           (shiftRect (0 - (placeBoundsX execution.params
               (componentCandidate execution.graph part.1 candidate) run execution.measured
               loops).minX)
             (-(placeBoundsX execution.params
               (componentCandidate execution.graph part.1 candidate) run execution.measured
               loops).minY)
             (frameRect execution.params
               (componentCandidate execution.graph part.1 candidate) run i)))) ∧
       (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
         execution.packedAcc.rects.getD key default =
           shiftRect packed.boxes[k].x packed.boxes[k].y
             (shiftRect (0 - (placeBoundsX execution.params
                 (componentCandidate execution.graph part.1 candidate) run execution.measured
                 loops).minX)
               (-(placeBoundsX execution.params
                 (componentCandidate execution.graph part.1 candidate) run execution.measured
                 loops).minY)
               (frameRect execution.params
                 (componentCandidate execution.graph part.1 candidate) run i))) := by
   have hbox : packed.boxes[k]? = some packed.boxes[k] :=
     List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
   obtain ⟨candidate, run, loops, _area, hrun, _hloops, hpartdef, hlookup⟩ :=
     part_frame_lookupX execution packed hpack hk hbox
   have hpartget := (List.getElem?_eq_some_iff.mp hk).2
   have hmapLen : k < (execution.componentsAcc.parts.map
       (fun part => Pack.Item.mk part.2.width part.2.height part.2.area)).length := by
     rw [List.length_map]
     exact (List.getElem?_eq_some_iff.mp hk).1
   obtain ⟨hw0, hh0⟩ := X_pack_box_dims hpack hkLen hmapLen
   have hitem : (execution.componentsAcc.parts.map
       (fun part => Pack.Item.mk part.2.width part.2.height part.2.area))[k] =
       Pack.Item.mk part.2.width part.2.height part.2.area := by
     rw [List.getElem_map, hpartget]
   have hwb : packed.boxes[k].w = part.2.width := by
     rw [hw0, hitem]
   have hhb : packed.boxes[k].h = part.2.height := by
     rw [hh0, hitem]
   have hwlink : part.2.width =
       (placeComponentExact execution.params
         (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).width := by
     have hcongr := congrArg Part.width hpartdef
     simpa using hcongr
   have hhlink : part.2.height =
       (placeComponentExact execution.params
         (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).height := by
     have hcongr := congrArg Part.height hpartdef
     simpa using hcongr
   refine ⟨candidate, run, loops, hrun, ?_, hlookup⟩
   intro i key hkey _
   have hi : i < (componentCandidate execution.graph part.1 candidate).nodes.length := by
     rw [componentCandidate_nodes]
     simp only [componentGraph, List.length_map]
     exact (List.getElem?_eq_some_iff.mp hkey).1
   have hplaced : (placeComponentExact execution.params
       (componentCandidate execution.graph part.1 candidate) run 0 execution.measured
       loops).rects[i]? =
     some (shiftRect (0 - (placeBoundsX execution.params
         (componentCandidate execution.graph part.1 candidate) run execution.measured loops).minX)
       (-(placeBoundsX execution.params
         (componentCandidate execution.graph part.1 candidate) run execution.measured loops).minY)
       (frameRect execution.params
         (componentCandidate execution.graph part.1 candidate) run i)) := by
     unfold placeComponentExact placeBoundsX
     simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
   have hmem := List.mem_of_getElem? hplaced
   have hb := placeComponentExact_rects_bounds execution.params
     (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops _
     hmem
   simp only [Rect.Contained, shiftRect] at hb ⊢
   rw [hwb, hhb, hwlink, hhlink]
   omega

/-- A node of an exact component at declaration position `pos` is the exact-graph
node of the declaration's box key (same as the plain `component_node_lookup`). -/
private theorem X_component_node_lookup {graph : Graph} {comp : List Nat} {cand : Nat}
    {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- Two distinct plain (border-0) nodes of one executed exact component run
have disjoint frame rectangles: same-layer nodes are separated horizontally
by the executed cross-coordinate pass (`X_nonproxy_ordered_intervals` with
the exact widths); different-layer nodes occupy disjoint reserved rank
bands (`X_ReserveBands`). Mirrors `componentRun_positions_disjoint`. -/
private theorem X_componentRun_positions_disjoint
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {u v : Nat} {nodeU nodeV : Node}
    (hnodeU : (componentCandidate execution.graph comp candidate).nodes[u]? = some nodeU)
    (hnodeV : (componentCandidate execution.graph comp candidate).nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v) :
    Disjoint (frameRect execution.params (componentCandidate execution.graph comp candidate) run u)
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run v) := by
  let cg := componentCandidate execution.graph comp candidate
  have hu' : u < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeU).1
  have hv' : v < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeV).1
  have hcovered := componentRunX_original_nodes_covered hrun
  have huP : u < run.proper.nodes.length := hcovered u hu'
  have hvP : v < run.proper.nodes.length := hcovered v hv'
  obtain ⟨actualU, hcoordU, hpropU, hbU0, _, _, _⟩ :=
    X_original_plain_record hrun hnodeU hbU
  obtain ⟨actualV, hcoordV, hpropV, hbV0, _, _, _⟩ :=
    X_original_plain_record hrun hnodeV hbV
  have hgetU : cg.nodes.getD u default = nodeU := by
    rw [List.getD_eq_getElem?_getD, hnodeU]
    rfl
  have hgetV : cg.nodes.getD v default = nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeU : frameRect execution.params cg run u = nodeRect cg run u := by
    unfold frameRect
    simp only []
    rw [hgetU, hbU]
    rfl
  have hframeV : frameRect execution.params cg run v = nodeRect cg run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hbV]
    rfl
  rw [hframeU, hframeV]
  have hrectU : nodeRect cg run u =
      ⟨run.xs.getD u 0 - Int.fdiv actualU.node.w 2, run.ys.getD u 0,
        actualU.node.w, actualU.node.h⟩ := by
    simp [nodeRect, hpropU]
  have hrectV : nodeRect cg run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  obtain ⟨_, _, _, q0, _, _, _, hord, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : u < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lU, hlyU, huIn, hrkU⟩ := hcov u huP
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v hvP
  let rU : Nat := (rk run.proper.rank u).toNat
  let rV : Nat := (rk run.proper.rank v).toNat
  have hrUdef : rU = (rk run.proper.rank u).toNat := rfl
  have hrVdef : rV = (rk run.proper.rank v).toNat := rfl
  have hrkU' : rk run.proper.rank u = (rU : Int) := by
    have h := Int.toNat_of_nonneg hrkU
    exact h.symm
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkCoordU : rk run.coordinateProper.rank u = (rU : Int) := by
    rw [← hranks]; exact hrkU'
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hlyU' : run.layers[rU]? = some lU := hlyU
  have hlyV' : run.layers[rV]? = some lV := hlyV
  rcases Nat.lt_trichotomy rU rV with hlt | heq | hgt
  · obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
    have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rU rV lU lV hlt hlyU' hlyV'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · rw [heq] at hlyU'
    obtain hlVeq : lV = lU := Option.some.inj (hlyV'.symm.trans hlyU')
    rw [hlVeq] at hvIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp huIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lU ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyU'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := X_nonproxy_ordered_intervals execution hcomp hrun (layer := lU) hlayerMem
        hplt hpu hpv hcoordU hcoordV
        (by simp [hbU0]) (by simp [hbV0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · have hsep := X_nonproxy_ordered_intervals execution hcomp hrun (layer := lU) hlayerMem
        hpgt hpv hpu hcoordV hcoordU
        (by simp [hbV0]) (by simp [hbU0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
  · obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
    have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rV rU lV lU hgt hlyV' hlyU'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

private theorem X_layoutX_c2_core (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (h : layoutX exactIds inp o = .ok res) :
    Validator.C2 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hpackedEq := execution.packed_eq
  unfold packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := bind_ok hpackedEq
  have hcompMap := (actual_components_parts_geometryX (by rfl)
    execution.components_eq).1
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    simp only [boxLines] at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        X_mapM_ok_len _ _ _ hl
      _ = inp.boxes.length := List.length_zipIdx
  intro b hb c hc hne hbex hcex _hpar
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hb hc
  obtain ⟨bi, hbi⟩ := hb
  obtain ⟨ci, hci⟩ := hc
  obtain ⟨sb, hsb, hbid, -, hbexS, hbrect⟩ := sceneBox_source_rectX execution hbi
  obtain ⟨sc, hsc, hcid, -, hcexS, hcrect⟩ := sceneBox_source_rectX execution hci
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  have hciLen : ci < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsc).1
  have hbiNe : bi ≠ ci := by
    intro heq
    subst heq
    have hss : sb = sc := Option.some.inj (hsb.symm.trans hsc)
    exact hne (by rw [hbid, hcid, hss])
  obtain ⟨partB, posB, kB, -, hkB, hposB⟩ :=
    key_part_positionX execution hbiLen
  obtain ⟨partA, posA, kA, -, hkA, hposA⟩ :=
    key_part_positionX execution hciLen
  have hkBlen := part_packed_box_lenX execution packed hpack hkB
  have hkAlen := part_packed_box_lenX execution packed hpack hkA
  by_cases hksame : kB = kA
  · subst hksame
    have hpartsSame : partA = partB := Option.some.inj (hkA.symm.trans hkB)
    rw [hpartsSame] at hposA
    have hposNe : posB ≠ posA := by
      intro heq
      rw [heq] at hposB
      exact hbiNe (Option.some.inj (hposB.symm.trans hposA))
    obtain ⟨candB, runB, _loopsB, hrunB, -, hlookupB⟩ :=
      X_part_packed_frame execution packed hpack hkB hkBlen
    obtain ⟨nodeB, hnodeBg, hborderB⟩ :=
      X_exclusive_source_border_zero execution hwf hlinesLen hsb
        (hbexS.symm.trans hbex)
    obtain ⟨nodeA, hnodeAg, hborderA⟩ :=
      X_exclusive_source_border_zero execution hwf hlinesLen hsc
        (hcexS.symm.trans hcex)
    have hnodeBlookup : (componentCandidate execution.graph partB.1 candB).nodes[posB]? =
        some nodeB := X_component_node_lookup hposB hnodeBg
    have hnodeAlookup : (componentCandidate execution.graph partB.1 candB).nodes[posA]? =
        some nodeA := X_component_node_lookup hposA hnodeAg
    have hcompSame : partB.1 ∈ components execution.graph := by
      rw [← hcompMap]
      exact List.mem_map.mpr ⟨partB, List.mem_of_getElem? hkB, rfl⟩
    have hdisjFrames := X_componentRun_positions_disjoint
      execution hcompSame hrunB
      hnodeBlookup hnodeAlookup hborderB hborderA hposNe
    rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupB posA ci hposA hciLen]
    intro hmeet
    exact hdisjFrames (meetsInterior_of_shiftRect
      (meetsInterior_of_shiftRect (meetsInterior_of_orientRect
        (meetsInterior_of_shiftRect hmeet))))
  · obtain ⟨_candA, _runA, _loopsA, -, hcontainA, hlookupA⟩ :=
      X_part_packed_frame execution packed hpack hkA hkAlen
    obtain ⟨_candB, _runB, _loopsB, -, hcontainB, hlookupB⟩ :=
      X_part_packed_frame execution packed hpack hkB hkBlen
    have hboxesDisj : ¬ (packed.boxes[kB]).meetsInterior (packed.boxes[kA]) :=
      Pack.pack_boxes_disjoint hpack kB kA hkBlen hkAlen hksame
    have hdisjShift := not_meetsInterior_shiftRect
      (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
      (not_meetsInterior_orientRect (d := o.direction)
        (h := execution.packedAcc.canvasH) hboxesDisj)
    have hx := contained_shiftRect_imp
      (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
      (contained_orientRect (d := o.direction)
        (h := execution.packedAcc.canvasH) (hcontainB posB bi hposB hbiLen))
    have hy := contained_shiftRect_imp
      (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
      (contained_orientRect (d := o.direction)
        (h := execution.packedAcc.canvasH) (hcontainA posA ci hposA hciLen))
    rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupA posA ci hposA hciLen]
    exact not_meetsInterior_of_contained hdisjShift hx hy

theorem layoutX_c2 (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hframed : framedParents inp = true)
    (h : layoutX exactIds inp o = .ok res) :
    Validator.C2 res.scene.layoutDump :=
  X_layoutX_c2_core exactIds hwf h

theorem flatC2B_layoutX (exactIds : List String) :
    FlatC2B (layoutX exactIds) := by
  intro inp o res hwf hok
  exact X_layoutX_c2_core exactIds hwf hok

end PipelineImpl
end Layered
end Elegant
