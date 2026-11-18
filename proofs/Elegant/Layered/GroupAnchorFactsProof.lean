import Elegant.Layered.FlatGroupEndpointsProof
import Elegant.Layered.GroupTopRank
import Elegant.Layered.GroupAnchors
import Elegant.Layered.Compound
import Elegant.Layered.CgShape
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.BracketInsideRankFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameClearanceBottomFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.BottomClearanceClosure
import Elegant.Layered.CoordGraph
import Elegant.Layered.BottomSeamsRank

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Anchor selection and top rank facts of group endpoints

`GroupAnchorSelection` (`FlatGroupEndpointsProof.lean`) is the measured-graph
anchor row: the line list covers the input boxes (as `boxLines` does for
executed layouts), and group boxes are not fixed-size (so `preparedBoxes`
keeps them groups, which carry title and bottom markers).  Both conjuncts are
proved below from the measured construction.
-/
/-! ### Bottom-marker positions

The appended bottom markers of `Compound.markNodes` sit, in order, at one
fixed offset per preceding group box.  The counting lemma below is the
converse of the private `bottom_node_decl` of `GroupAnchors.lean`: a bottom
node found at extras-position `k` declares the group box with exactly `k`
groups before it. -/

/-- If index `i` carries `p`, advancing the take bound by a nonzero amount
adds at least one to the count of `p`-true elements. -/
private theorem countP_take_add_one {α : Type} (p : α → Bool)
    {l : List α} {i n : Nat} (hn : n ≠ 0) (hi : i < l.length) (hpi : p l[i] = true) :
    (l.take i).countP p + 1 ≤ (l.take (i + n)).countP p := by
  have hsplit : (l.take (i + n)).countP p =
      (l.take i).countP p + ((l.drop i).take n).countP p := by
    rw [List.take_add, List.countP_append]
  rw [hsplit]
  have hwindow : l[i] ∈ (l.drop i).take n := by
    have h1 : (l.drop i)[0]? = some l[i] := by
      rw [List.getElem?_drop, Nat.add_zero]
      exact List.getElem?_eq_getElem hi
    have h2 : ((l.drop i).take n)[0]? = (l.drop i)[0]? := by
      rw [List.getElem?_take]
      simp [Nat.pos_of_ne_zero hn]
    have h0 : ((l.drop i).take n)[0]? = some l[i] := by rw [h2, h1]
    exact List.mem_of_getElem? h0
  have hge : 1 ≤ (((l.drop i).take n).filter p).length := by
    have hmem : p l[i] = true := hpi
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hwindow, hmem⟩
  simp only [List.countP_eq_length_filter]
  omega

/-- The synthetic bottom nodes of `markNodes`, with declaration indices
offset by `off` and paths computed against the full box list `full`. -/
private def bottomNodesOf (full sub : List ModelBox) (off : Nat) : List Node :=
  (sub.zipIdx off).filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0
        clusterPath := Compound.path full q.1 ++ [q.2], border := 2 }
    else none

/-- Every bottom node emitted by `bottomNodesOf` names the index of a group
box of `sub`, and its position counts exactly the group boxes before that
index. -/
private theorem bottomNodesOf_getElem?_decl {full sub : List ModelBox} {off k : Nat}
    {x : Node} (hx : (bottomNodesOf full sub off)[k]? = some x) :
    ∃ d g, sub[d]? = some g ∧ g.role = .group ∧ x.decl = d + off ∧
      ((sub.take d).filter fun b => b.role == .group).length = k := by
  induction sub generalizing off k with
  | nil => simp [bottomNodesOf] at hx
  | cons b bs ih =>
    unfold bottomNodesOf at hx
    rw [List.zipIdx_cons] at hx
    by_cases hb : b.role = .group
    · have hbeq : (b.role == .group) = true := beq_iff_eq.mpr hb
      simp only [hbeq, ↓reduceIte, List.filterMap_cons] at hx
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨0, b, List.getElem?_cons_zero, hb, by simp, by simp⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
        refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
        · simpa using hdg
        · have : d + 1 + off = d + (off + 1) := by omega
          rw [this]; exact hdecl
        · have htake : ((b :: bs).take (d + 1)).filter
              (fun b => b.role == .group) =
            b :: (bs.take d).filter (fun b => b.role == .group) := by
            rw [List.take_succ_cons]
            simp [hb]
          rw [htake, List.length_cons, hcount]
    · have hbf : (b.role == .group) = false := by
        cases hz : (b.role == .group) with
        | true => exact absurd (beq_iff_eq.mp hz) hb
        | false => rfl
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons] at hx
      obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
      refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
      · simpa using hdg
      · have : d + 1 + off = d + (off + 1) := by omega
        rw [this]; exact hdecl
      · have htake : ((b :: bs).take (d + 1)).filter
              (fun b => b.role == .group) =
          (bs.take d).filter (fun b => b.role == .group) := by
            rw [List.take_succ_cons]
            have hbf2 : (b.role == .group) = false := hbf
            simp only [hbf2, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
        rw [htake, hcount]

/-- The mapped source section of `markNodes` never carries `border = 2`:
every source node has `border = 0` in a measured graph, and `markOne`
preserves that. -/
private theorem markNodes_top_ne_two {boxesD : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes0 : List Node}
    (hmeta0 : ∀ (k : Nat) (m : Node), nodes0[k]? = some m → m.border = 0)
    {v : Nat} (hlt : v < nodes0.length)
    {n : Node} (hv : (Compound.markNodes boxesD pad titles nodes0)[v]? = some n) :
    n.border ≠ 2 := by
  rw [markNodes_eq] at hv
  have hlen : (nodes0.zipIdx.map (markOne boxesD pad titles)).length =
      nodes0.length := by
    simp only [List.length_map, List.length_zipIdx]
  rw [List.getElem?_append_left (by rw [hlen]; exact hlt)] at hv
  simp only [List.getElem?_map, List.getElem?_zipIdx] at hv
  cases hn : nodes0[v]? with
  | none => simp [hn] at hv
  | some m =>
    simp only [hn, Option.map_some, Option.some.injEq] at hv
    subst hv
    have h0 : m.border = 0 := hmeta0 v m hn
    apply markOne_border_ne_two
    show m.border ≠ 2
    rw [h0]; decide

/-- First conjunct of `GroupAnchorSelection`: with a covering line list,
every `border = 2` node of a measured graph sits at the `bottomIndex` of
its own declaration. -/
theorem groupAnchorSelectionTrue_borderTwo {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length) :
    ∀ {v : Nat} {n : Node}, graph.nodes[v]? = some n → n.border = 2 →
      v = Compound.bottomIndex (preparedBoxes inp) n.decl := by
  obtain ⟨nodes0, edges0, titles, hprep, hlen0, hmeta⟩ :=
    measuredGraph_prepared_source hgraph
  have hprep2 : graph = Compound.prepare (preparedBoxes inp) P.clusterPad titles
      { nodes := nodes0, edges := edges0, slot := P.slot } := hprep
  have hboxesLen : (preparedBoxes inp).length = inp.boxes.length := by
    simp [preparedBoxes]
  have hlen : nodes0.length = (preparedBoxes inp).length := by
    rw [hlen0, hlines, hboxesLen]
  intro v n hv hb
  have hvm : (Compound.markNodes (preparedBoxes inp) P.clusterPad titles
      nodes0)[v]? = some n := by
    have h1 : (Compound.prepare (preparedBoxes inp) P.clusterPad titles
        { nodes := nodes0, edges := edges0, slot := P.slot }).nodes[v]? = some n := by
      rw [← hprep2]; exact hv
    rwa [Compound.prepare_nodes] at h1
  by_cases hlt : v < nodes0.length
  · exact absurd hb (markNodes_top_ne_two (fun k m hk => (hmeta k m hk).2) hlt hvm)
  · obtain ⟨_, _, _, _, _, _, _, _⟩ :=
      Compound.markNodes_getElem?_bottom (preparedBoxes inp) P.clusterPad titles
        nodes0 v (by omega) hvm
    have hsplit : Compound.markNodes (preparedBoxes inp) P.clusterPad titles nodes0 =
        (nodes0.zipIdx.map (markOne (preparedBoxes inp) P.clusterPad titles)) ++
          markExtras (preparedBoxes inp) := markNodes_eq _ _ _ _
    have hlenMap : (nodes0.zipIdx.map
        (markOne (preparedBoxes inp) P.clusterPad titles)).length = nodes0.length := by
      simp only [List.length_map, List.length_zipIdx]
    have hle : (nodes0.zipIdx.map
        (markOne (preparedBoxes inp) P.clusterPad titles)).length ≤ v := by
      omega
    rw [hsplit, List.getElem?_append_right hle, hlenMap] at hvm
    have hme : markExtras (preparedBoxes inp) =
        bottomNodesOf (preparedBoxes inp) (preparedBoxes inp) 0 := rfl
    rw [hme] at hvm
    obtain ⟨d, g, _, _, hdecl, hcount⟩ := bottomNodesOf_getElem?_decl hvm
    simp only [Nat.add_zero] at hdecl
    unfold Compound.bottomIndex
    rw [hdecl]
    omega

/-- The synthetic bottom record `Compound.markNodes` appends for group box `j`. -/
private def bottomRecord (boxesD : List ModelBox) (j : Nat) (src : ModelBox) : Node :=
  { decl := j, w := 0, h := 0,
    clusterPath := Compound.path boxesD src ++ [j], border := 2 }

/-! ### Group tops share a component with their bottom markers

The compound constraints connect every group top to its bottom marker,
either directly (member-less, child-less groups) or through member and
child chains.  The fuel induction below follows the nesting argument of
`componentRun_cg_top_of_bottom` (`RouteProxyStart.lean`), at the global
graph level. -/

/-- The bottom `find?` used by `Compound.constraints` returns the measured
bottom marker at a known index. -/
private theorem graph_bottom_find_eq {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {d : Nat} {bm : Node} {bi : Nat}
    (hmem : graph.nodes[bi]? = some bm)
    (hbord : bm.border = 2) (hdecl : bm.decl = d) :
    (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == d) = some (bm, bi) := by
  have hzip : (bm, bi) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hmem
  have hex : ∃ cb : Node × Nat, (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == d) = some cb := by
    cases h : (graph.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == d) with
    | none =>
      have hall := (List.find?_eq_none.mp h) (bm, bi) hzip
      simp [hbord, hdecl] at hall
    | some cb => exact ⟨cb, rfl⟩
  obtain ⟨cb, hcb⟩ := hex
  have hcbmem : cb ∈ graph.nodes.zipIdx := List.mem_of_find?_eq_some hcb
  have hcbpred := List.find?_some hcb
  obtain ⟨hcbB, hcbD⟩ := Bool.and_eq_true_iff.mp hcbpred
  have hcbB' : cb.1.border = 2 := beq_iff_eq.mp hcbB
  have hcbD' : cb.1.decl = bm.decl := (beq_iff_eq.mp hcbD).trans hdecl.symm
  have heq : cb = (bm, bi) :=
    measuredGraph_bottom_pair_eq hgraph hcbmem hzip hcbB' hbord hcbD'
  rw [heq] at hcb
  exact hcb




/-- Tops of measured groups have short cluster paths: the ancestor chain
fits in the box list, and the node list is at least as long. -/
private theorem graph_top_path_bound {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (t : Node × Nat) (ht : t ∈ graph.nodes.zipIdx) (hg : t.1.border = -2) :
    t.1.clusterPath.length ≤ graph.nodes.length + 1 := by
  have hsource : graph.nodes[t.2]? = some t.1 := List.mem_zipIdx_iff_getElem?.mp ht
  obtain ⟨nodes0, edges0, titles, hprep, hlen0, _⟩ :=
    measuredGraph_prepared_source hgraph
  obtain ⟨_, box, _, _, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hg
  have hpath' : t.1.clusterPath =
      Compound.path (preparedBoxes inp) box ++ [t.1.decl] := hpath
  have hplen : (Compound.path (preparedBoxes inp) box).length ≤
      (preparedBoxes inp).length := by
    have h := ancestors_length_le (preparedBoxes inp)
      ((preparedBoxes inp).length) box.parent
    simpa [Compound.path] using h
  have hge : (preparedBoxes inp).length ≤ graph.nodes.length := by
    have h1 : nodes0.length = (preparedBoxes inp).length := by
      rw [hlen0, hlines]
      simp [preparedBoxes]
    have h2 := Compound.markNodes_length_ge (preparedBoxes inp) P.clusterPad titles nodes0
    have h3 : graph.nodes.length =
        (Compound.markNodes (preparedBoxes inp) P.clusterPad titles nodes0).length := by
      simp only [hprep, Compound.prepare_nodes, preparedBoxes]
    omega
  rw [hpath', List.length_append, List.length_singleton]
  omega

/-- Every group top shares its reported component with its bottom marker:
fuel induction over the nesting depth, following the constraint edges down
and the induction hypothesis back up. -/
private theorem graph_top_bottom_same_comp {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length)
    (fuel : Nat) :
    ∀ (t : Node × Nat), t ∈ graph.nodes.zipIdx → t.1.border = -2 →
    ∀ (b : Node × Nat),
    (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == t.1.decl) = some b →
    graph.nodes.length + 2 - t.1.clusterPath.length = fuel →
    ∃ comp ∈ components graph, t.2 ∈ comp ∧ b.2 ∈ comp := by
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro t ht hgroup b hb hfuel
    cases hmemCase : (graph.nodes.zipIdx.filter fun entry =>
        entry.1.border == 0 && entry.1.clusterPath.contains t.1.decl).isEmpty with
    | false =>
      have hmemNe : (graph.nodes.zipIdx.filter fun entry =>
          entry.1.border == 0 && entry.1.clusterPath.contains t.1.decl) ≠ [] := by
        intro hnil
        rw [hnil] at hmemCase
        simp at hmemCase
      obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _ hmemNe
      obtain ⟨hmZip, hmCond⟩ := List.mem_filter.mp hmember
      obtain ⟨hmPlain, hmInside⟩ := Bool.and_eq_true_iff.mp hmCond
      have hmPlain' : member.1.border = 0 := by simpa using hmPlain
      have hmInside' : member.1.clusterPath.contains t.1.decl = true := by
        simpa using hmInside
      obtain ⟨he₁, he₂⟩ := compound_member_constraint_edges (graph := graph)
        (top := t) (bottom := b) (member := member) ht hgroup hb
        hmZip hmPlain' hmInside'
      obtain ⟨cT, hcTmem, hcTt, hcTm⟩ :=
        components_edge_endpoints hbd (List.mem_append_right _ he₁)
      obtain ⟨cB, hcBmem, hcBt, hcBm⟩ :=
        components_edge_endpoints hbd (List.mem_append_right _ he₂)
      have hTT : cT = cB := components_shared_member_eq hcTmem hcBmem hcTm hcBt
      exact ⟨cT, hcTmem, hcTt, by rw [hTT]; exact hcBm⟩
    | true =>
      cases hchildCase : ((graph.nodes.zipIdx.filter fun entry =>
          entry.1.border == -2).filter fun entry =>
          entry.1.clusterPath.dropLast == t.1.clusterPath).isEmpty with
      | false =>
        have hchildNe : ((graph.nodes.zipIdx.filter fun entry =>
            entry.1.border == -2).filter fun entry =>
            entry.1.clusterPath.dropLast == t.1.clusterPath) ≠ [] := by
          intro hnil
          rw [hnil] at hchildCase
          simp at hchildCase
        obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _ hchildNe
        obtain ⟨hchildTops, hchildPathEq⟩ := List.mem_filter.mp hchildMem
        obtain ⟨hchildZip, hchildGroupB⟩ := List.mem_filter.mp hchildTops
        have hchildGroup : child.1.border = -2 := by simpa using hchildGroupB
        have hchildPath : child.1.clusterPath.dropLast = t.1.clusterPath := by
          simpa using hchildPathEq
        obtain ⟨_, _, hchildBoxL, hchildRole, _⟩ :=
          measuredGraph_group_origin hgraph
            (List.mem_zipIdx_iff_getElem?.mp hchildZip) hchildGroup
        have hdbound : child.1.decl < lines.length := by
          have hi := (List.getElem?_eq_some_iff.mp hchildBoxL).1
          have hml : (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node } else box).length = inp.boxes.length := by
            simp
          omega
        obtain ⟨_, childBot, _, hchildBotMem, _,
            hchildBotBorder, _, hchildBotDecl, _, _, _, _⟩ :=
          measuredGraph_paired_markers hgraph hdbound hchildBoxL hchildRole
        obtain ⟨cbIdx, hcbIdx⟩ := List.mem_iff_getElem?.mp hchildBotMem
        have hcbFind := graph_bottom_find_eq hgraph hcbIdx hchildBotBorder hchildBotDecl
        have hlenChild : child.1.clusterPath.length =
            t.1.clusterPath.length + 1 := by
          have hd := congrArg List.length hchildPath
          rw [List.length_dropLast] at hd
          have htsource : graph.nodes[t.2]? = some t.1 :=
            List.mem_zipIdx_iff_getElem?.mp ht
          have htne : t.1.clusterPath ≠ [] :=
            (measuredGraph_marker_shape hgraph htsource).2 hgroup
          have hcne : child.1.clusterPath ≠ [] := by
            intro hempty
            rw [hempty, List.dropLast_nil] at hchildPath
            exact htne hchildPath.symm
          have hchildLen := List.length_pos_iff.mpr hcne
          have htLen := List.length_pos_iff.mpr htne
          omega
        have hboundT := graph_top_path_bound hgraph hlines t ht hgroup
        have hboundC := graph_top_path_bound hgraph hlines child hchildZip hchildGroup
        have hpos : 0 < fuel := by omega
        have hfuelChild : graph.nodes.length + 2 - child.1.clusterPath.length =
            fuel - 1 := by
          omega
        obtain ⟨cC, hcCmem, hcCt, hcCb⟩ :=
          ih (fuel - 1) (by omega) child hchildZip hchildGroup
            (childBot, cbIdx) hcbFind hfuelChild
        obtain ⟨he₁, he₂⟩ := compound_child_constraint_edges (graph := graph)
          (parent := t) (parentBottom := b) (child := child)
          (childBottom := (childBot, cbIdx))
          ht hgroup hb hchildZip hchildGroup hchildPath hcbFind
        obtain ⟨cT, hcTmem, hcTt, hcTc⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he₁)
        obtain ⟨cB, hcBmem, hcBcb, hcBb⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he₂)
        have h1 : cT = cC := components_shared_member_eq hcTmem hcCmem hcTc hcCt
        have h2 : cB = cC := components_shared_member_eq hcBmem hcCmem hcBcb hcCb
        have h3 : cT = cB := h1.trans h2.symm
        exact ⟨cT, hcTmem, hcTt, by rw [h3]; exact hcBb⟩
      | true =>
        have he := compound_empty_group_constraint_edge (graph := graph)
          (top := t) (bottom := b) ht hgroup hb hmemCase hchildCase
        obtain ⟨c, hcMem, hcT, hcH⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he)
        exact ⟨c, hcMem, hcT, hcH⟩

/-- Second conjunct of `GroupAnchorSelection`: with a covering line
list, the title node of a fixed-free group box shares its reported
component with the group's bottom marker. -/
theorem groupAnchorSelectionTrue_topRow {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length) :
    ∀ {j : Nat} {src : ModelBox},
      inp.boxes[j]? = some src → src.role = .group →
      inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false →
      ∃ (top : Node) (comp : List Nat) (_ : comp ∈ components graph),
        graph.nodes[j]? = some top ∧ top.border = -2 ∧ top.decl = j ∧
          j ∈ comp ∧ Compound.bottomIndex (preparedBoxes inp) j ∈ comp := by
  obtain ⟨nodes0, edges0, titles, hprep, hlen0, hmeta⟩ :=
    measuredGraph_prepared_source hgraph
  have hprep2 : graph = Compound.prepare (preparedBoxes inp) P.clusterPad titles
      { nodes := nodes0, edges := edges0, slot := P.slot } := hprep
  have hboxesLen : (preparedBoxes inp).length = inp.boxes.length := by
    simp [preparedBoxes]
  have hlen : nodes0.length = (preparedBoxes inp).length := by
    rw [hlen0, hlines, hboxesLen]
  intro j src hsrc hrole hfixed
  have hbp : (preparedBoxes inp)[j]? = some src := by
    have h := preparedBoxes_lookup hsrc
    rw [hfixed] at h
    simpa using h
  have hjlen : j < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsrc).1
  have hjnodes : j < nodes0.length := by omega
  obtain ⟨top, htopLook, htopBorder, htopDecl⟩ :
      ∃ top : Node, graph.nodes[j]? = some top ∧ top.border = -2 ∧ top.decl = j := by
    have hrec := Compound.prepare_group_title_record (preparedBoxes inp) P.clusterPad titles
      { nodes := nodes0, edges := edges0, slot := P.slot } hjnodes hbp hrole
    have hdeclTop := Compound.prepare_group_decl (preparedBoxes inp) P.clusterPad titles
      { nodes := nodes0, edges := edges0, slot := P.slot } hjnodes hbp hrole hrec
    have hdj : (nodes0[j]'hjnodes).decl = j :=
      (hmeta j _ (List.getElem?_eq_getElem hjnodes)).1
    rw [← hprep2] at hrec
    refine ⟨_, hrec, rfl, ?_⟩
    rw [hdeclTop]
    exact hdj
  have hbotMem : (bottomRecord (preparedBoxes inp) j src) ∈ graph.nodes := by
    have h := Compound.prepare_bottom_exists (preparedBoxes inp) P.clusterPad titles
      { nodes := nodes0, edges := edges0, slot := P.slot } hbp hrole
    rw [← hprep2] at h
    exact h
  obtain ⟨bj, hbj⟩ := List.mem_iff_getElem?.mp hbotMem
  have hlit : (bottomRecord (preparedBoxes inp) j src).decl = j := rfl
  have hbjEq : bj = Compound.bottomIndex (preparedBoxes inp) j := by
    have hpos := groupAnchorSelectionTrue_borderTwo hgraph hlines hbj rfl
    rw [hlit] at hpos
    exact hpos
  have hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact measuredGraph_edges_bounded hgraph hlines e h
    · exact constraints_bounded graph e h
  have hfind := graph_bottom_find_eq hgraph hbj rfl hlit
  have hfind' : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) =
      some ((bottomRecord (preparedBoxes inp) j src), bj) := by
    rw [htopDecl]
    exact hfind
  obtain ⟨comp, hcomp, hjt, hbt⟩ := graph_top_bottom_same_comp hgraph hlines hbd
    (graph.nodes.length + 2 - top.clusterPath.length) (top, j)
    (List.mem_zipIdx_iff_getElem?.mpr htopLook) htopBorder
    ((bottomRecord (preparedBoxes inp) j src), bj) hfind' rfl

  exact ⟨top, comp, hcomp, htopLook, htopBorder, htopDecl, hjt,
    by rw [← hbjEq]; exact hbt⟩

/-- `GroupAnchorSelection` holds: both anchor rows from the measured
construction. -/
theorem groupAnchorSelection : GroupAnchorSelection := by
  intro P inp o lines graph hgraph hlines
  exact ⟨groupAnchorSelectionTrue_borderTwo hgraph hlines,
    groupAnchorSelectionTrue_topRow hgraph hlines⟩


/-! ### Group top subtree rank

`GroupTopSubtreeRankProper` (`GroupTopRank.lean`) is the executed rank
closure for group tops.  Its candidate-graph form
`GroupTopSubtreeRankCg` stays open: the ranking-graph interval facts
(`ranked_compound_member_interval`, `ranked_compound_child_interval`,
`componentRun_group_top_lt_bottom`) close it by border-case induction, but
that descent is not carried out here.  The executed transport from the
ranking graph to `run.proper` — through the coordinate graph, proxy
widths, and synthetic dropping — is proved here for every original node;
the derived nodes (dummies, side borders, title copies) stay open as
`ProperDerivedRank` below. -/

/-- Residual, executed rank bound for derived proper nodes: dummies, side
borders, and title copies whose cluster path contains a group top's
declaration rank at or below that top.  Dummies inherit the common path of
their chain endpoints and rank between them; side nodes sit between their
top and bottom band ranks; title copies share their top's rank. -/
def ProperDerivedRank : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    v < (componentCandidate graph comp candidate).nodes.length →
    ∀ {i : Nat}, i < run.proper.nodes.length →
    (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
    ((run.proper.nodes.getD i default).dummy = true ∨
      (run.proper.nodes.getD i default).node.border = -1 ∨
      (run.proper.nodes.getD i default).node.border = 1 ∨
      (run.proper.nodes.getD i default).node.border = 3) →
    rk run.proper.rank v ≤ rk run.proper.rank i

/-- Proxy widths rewrite only the width: the cluster path survives. -/
private theorem proxyWidths_path {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) {v : Nat} {nd qn : ProperNode}
    (hv : p.nodes[v]? = some nd) (hq : q.nodes[v]? = some qn) :
    qn.node.clusterPath = nd.node.clusterPath := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, hok⟩ := bind_ok h
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hu
  have hok2 : (Except.ok _ : Except LayoutError (Proper × List Int)) =
      Except.ok (q, xs') := hok
  have hqeq : q = { p with nodes := updated.map (·.1) } :=
    (Prod.mk.inj (Except.ok.inj hok2)).1.symm
  have hmem : (p.nodes.zipIdx)[v]? = some (nd, v) := by
    simp [List.getElem?_zipIdx, hv]
  obtain ⟨b, hb1, hb2⟩ := hidx v (nd, v) hmem
  have hqn : q.nodes[v]? = some b.1 := by
    have h0 : (updated.map (·.1))[v]? = some b.1 := by
      simp only [List.getElem?_map, hb2, Option.map_some]
    have h1 : ({ p with nodes := updated.map (·.1) } : Proper).nodes[v]? =
        some b.1 := h0
    rwa [← hqeq] at h1
  have hqnEq : qn = b.1 := Option.some.inj (hq.symm.trans hqn)
  dsimp only at hb1
  by_cases hcond : (nd.node.border == -2 || nd.node.border == 2) = true
  · simp only [hcond, ↓reduceIte] at hb1
    cases hl : nd.node.clusterPath.getLast? with
    | none => simp [hl] at hb1
    | some owner =>
      simp only [hl] at hb1
      obtain ⟨span, hspan, hb1⟩ := bind_ok hb1
      obtain ⟨width, hwidth, hb1⟩ := bind_ok hb1
      by_cases hw0 : width < 0
      · simp only [hw0, ↓reduceIte] at hb1
        simp [bind, Except.bind] at hb1
      · simp only [hw0, ↓reduceIte] at hb1
        obtain ⟨center, hcenter, hb1⟩ := bind_ok hb1
        have hb1' : (Except.ok _ : Except LayoutError (ProperNode × Int)) =
            Except.ok b := hb1
        have hb1'' := Except.ok.inj hb1'
        subst hb1''
        rw [hqnEq]
  · simp only [hcond] at hb1
    have hb1' : (Except.ok (nd, xs.getD v 0) : Except LayoutError (ProperNode × Int)) =
        Except.ok b := hb1
    have hb1'' := Except.ok.inj hb1'
    subst hb1''
    rw [hqnEq]

/-- Executed proper nodes share their coordinate records: synthetic dropping
only filters edges, and proxy widths preserve dummy flags, borders, and
cluster paths. -/
private theorem proper_coord_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = pn.dummy ∧
      cn.node.border = pn.node.border ∧
      cn.node.clusterPath = pn.node.clusterPath := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hord, hxs, hproxy, hdrop,
    hr, hrl, hy, hys, hroutes⟩ := componentRun_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by
    have h := congrArg Proper.nodes hdrop.symm
    simpa [OrderImpl.dropSynthetic] using h
  rw [hnodes] at hp
  have hlen : i < run.coordinateProper.nodes.length := by
    have h1 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hp).1
    have h2 := (proxyWidths_rel hproxy).2.2.1
    omega
  have hcn : run.coordinateProper.nodes[i]? =
      some (run.coordinateProper.nodes[i]'hlen) := List.getElem?_eq_getElem hlen
  obtain ⟨qn, hqn, hqdum, hqbord, _⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 i _ hcn
  have hqnEq : qn = pn := Option.some.inj (hqn.symm.trans hp)
  have hpath := proxyWidths_path hproxy hcn hp
  refine ⟨_, hcn, ?_, ?_, ?_⟩
  · rw [← hqnEq]; exact hqdum.symm
  · rw [← hqnEq]; exact hqbord.symm
  · exact hpath.symm

/-- Executed proper ranks agree with coordinate ranks index-wise. -/
private theorem proper_rank_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) (x : Nat) :
    rk run.proper.rank x = rk run.coordinateProper.rank x := by
  have h : run.proper.rank = run.coordinateProper.rank := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
      componentRun_spec hrun
    obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  rw [h]

/-- The executed rank closure from its two seams: the candidate-graph
closure `GroupTopSubtreeRankCg` handles every original node through the
rank-record transport, while `ProperDerivedRank` covers the derived
proper nodes (dummies, side borders, title copies). -/
theorem groupTopSubtreeRankProper_of_seams (hcg : GroupTopSubtreeRankCg)
    (hder : ProperDerivedRank) : GroupTopSubtreeRankProper := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
    orderOptions hrun v nd hnode hborder hvcg i hi hpath
  obtain ⟨rr, labeled, hrr, hcoord, hkeys, hranks, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  obtain ⟨rr2, hrr2, hclose⟩ := hcg hgraph hlines hwf hfp hcomp hrun hnode hborder
  have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
  subst hrrEq
  have erv : rk run.proper.rank v = rk (coordinateGraph P labeled).rank v := by
    rw [proper_rank_eq hrun v, hcoord]
  have eri : rk run.proper.rank i = rk (coordinateGraph P labeled).rank i := by
    rw [proper_rank_eq hrun i, hcoord]
  rw [erv, eri]
  have hpi : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  obtain ⟨cn, hcn, hcdum, hcbord, hcpath⟩ := proper_coord_record hrun hpi
  have hcpath' : cn.node.clusterPath.contains nd.decl = true := by
    have h := hpath
    rwa [← hcpath] at h
  have hci : (coordinateGraph P labeled).nodes[i]? = some cn := by
    rw [hcoord]; exact hcn
  rcases coordinateGraph_lookup P labeled hci with
    ⟨m, hm, hdm, _, hpm, _⟩ | ⟨_, hside⟩ | ⟨_, _, _, _, _, qb3, _⟩
  · by_cases hmD : m.dummy = false
    · rcases hkeys i m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
      · have hnlt : i < (componentCandidate graph comp candidate).nodes.length :=
          (List.getElem?_eq_some_iff.mp hn).1
        have hgetD : (componentCandidate graph comp candidate).nodes.getD i default =
            n := by
          rw [List.getD_eq_getElem?_getD, hn, Option.getD_some]
        have hnpath : ((componentCandidate graph comp candidate).nodes.getD i
            default).clusterPath.contains nd.decl = true := by
          rw [hgetD, ← hnp, ← hpm hmD]
          exact hcpath'
        have hrv : rk (coordinateGraph P labeled).rank v = rk rr.ranks v :=
          prepared_coordinate_original_rk hrr hranks hvcg
        have hri : rk (coordinateGraph P labeled).rank i = rk rr.ranks i :=
          prepared_coordinate_original_rk hrr hranks hnlt
        rw [hrv, hri]
        exact hclose i hnlt hnpath
      · simp [hmD] at hdT
    · have hmT : m.dummy = true := by
        cases hmd : m.dummy with
        | true => rfl
        | false => exact (hmD hmd).elim
      have hpnD : (run.proper.nodes.getD i default).dummy = true := by
        rw [← hcdum, hdm]
        exact hmT
      rw [← erv, ← eri]
      exact hder hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
        (Or.inl hpnD)
  · rcases hside with hs | hs
    · rw [← erv, ← eri]
      exact hder hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
        (Or.inr (Or.inl (by rw [← hcbord]; exact hs)))
    · rw [← erv, ← eri]
      exact hder hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
        (Or.inr (Or.inr (Or.inl (by rw [← hcbord]; exact hs))))
  · rw [← erv, ← eri]
    exact hder hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
      (Or.inr (Or.inr (Or.inr (by rw [← hcbord]; exact qb3))))

end Elegant.Layered.PipelineImpl
